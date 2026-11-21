//! A Rust implementation of the kernel conversion (kernel/cClosure.ml and
//! kernel/conversion.ml), called through [Rconv].

pub mod cbs;
pub mod closure;
pub mod constr;
pub mod conversion;
pub mod esubst;
pub mod ffi;
pub mod pattern;

use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::{c_char, CString};
use std::panic::AssertUnwindSafe;
use std::rc::Rc;

use cbs::*;
use closure::*;
use conversion::*;
use esubst::{el_id, Range};
use ffi::{call, fc_to_handle, handle_to_fc, OVal, OcamlExn, Value, A, VAL_UNIT};

extern "C" {
    fn caml_raise(v: Value) -> !;
    fn caml_failwith(msg: *const c_char) -> !;
}

fn guard(f: impl FnOnce() -> OVal) -> Value {
    let r = std::panic::catch_unwind(AssertUnwindSafe(f));
    ffi::flush_pending();
    match r {
        Ok(v) => {
            let raw = v.get();
            drop(v);
            raw
        }
        Err(p) => match p.downcast::<OcamlExn>() {
            Ok(e) => {
                let raw = e.0.get();
                drop(e);
                unsafe { caml_raise(raw) }
            }
            Err(p) => {
                let msg = if let Some(s) = p.downcast_ref::<&str>() {
                    s.to_string()
                } else if let Some(s) = p.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown error".to_string()
                };
                drop(p);
                let cs = CString::new(format!("Rust conversion: {}", msg)).unwrap();
                let ptr = cs.into_raw();
                unsafe { caml_failwith(ptr) }
            }
        },
    }
}

#[no_mangle]
pub extern "C" fn rconv_setup(_unit: Value) -> Value {
    ffi::setup();
    VAL_UNIT
}

#[no_mangle]
pub extern "C" fn rconv_constr_tag(c: Value) -> Value {
    if ffi::is_long(c) {
        ffi::val_long(-1)
    } else {
        ffi::val_long(unsafe { ffi::tag(c) } as isize)
    }
}

/// [args] is the tuple
/// (typed, reds, cv_pb, l2r, evars, env, graph, state, check, t1, t2)
#[no_mangle]
pub extern "C" fn rconv_conv(args: Value) -> Value {
    guard(|| {
        let a = OVal::new(args);
        let typed = a.field(0).as_bool();
        let reds = Flags::new(a.field(1));
        let cv_pb = a.field_int(2);
        let l2r = a.field(3).as_bool();
        let evars = a.field(4);
        let env = a.field(5);
        let graph = a.field(6);
        let state = a.field(7);
        let check = a.field(8);
        let t1 = a.field(9);
        let t2 = a.field(10);
        drop(a);
        let std = call(&STD_FLAGS, &[A::I(0)]);
        let share = call(&SHARE, &[A::O(&env)]).as_bool();
        let cache = Rc::new(Cache {
            env,
            evars,
            share,
            univs: graph,
            all: Flags::new(std.field(0)),
            betaiotazeta: Flags::new(std.field(1)),
            empty_inst: std.field(2),
            prim_cache: RefCell::new(HashMap::new()),
        });
        let empty = cache.empty_inst.clone();
        let inf = Infos { flags: reds, relevances: Range::empty(), cache };
        let ci = CInfos { inf, sh: Rc::new(ConvShared { typ: typed, lft_tab: create_tab(), rgt_tab: create_tab(), check }) };
        let f1 = injectu(&t1, &empty);
        let f2 = injectu(&t2, &empty);
        match ccnv(cv_pb, l2r, &ci, &el_id(), &el_id(), &f1, &f2, state) {
            Ok(s) => call(&RESULT_OK, &[A::O(&s)]),
            Err(NC::Plain) => call(&RESULT_ERROR, &[A::B(false), A::I(0)]),
            Err(NC::Trace(e)) => call(&RESULT_ERROR, &[A::B(true), A::O(&e)]),
        }
    })
}

/* Entries for [Primred.RedNative] on the OCaml side */

#[no_mangle]
pub extern "C" fn rconv_fc_get_atom(h: Value) -> Value {
    guard(|| {
        let fc = handle_to_fc(&OVal::new(h));
        let t = fc.term();
        match &*t {
            FTerm::Int(x) | FTerm::Float(x) | FTerm::String(x) => x.clone(),
            _ => panic!("assert false"),
        }
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_array_lift(h: Value) -> Value {
    guard(|| {
        let fc = handle_to_fc(&OVal::new(h));
        let t = fc.term();
        match &*t {
            FTerm::Array(_, _, _, lft) => OVal::int(*lft),
            _ => panic!("assert false"),
        }
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_array_parray(h: Value) -> Value {
    guard(|| {
        let fc = handle_to_fc(&OVal::new(h));
        let t = fc.term();
        match &*t {
            FTerm::Array(_, a, _, _) => a.clone(),
            _ => panic!("assert false"),
        }
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_lift(n: Value, h: Value) -> Value {
    guard(|| {
        let fc = handle_to_fc(&OVal::new(h));
        fc_to_handle(&lift_fconstr(ffi::long_val(n), &fc))
    })
}

/// [k] = 0: int, 1: float, 2: string
#[no_mangle]
pub extern "C" fn rconv_fc_mk_prim(k: Value, x: Value) -> Value {
    guard(|| {
        let x = OVal::new(x);
        let t = match ffi::long_val(k) {
            0 => FTerm::Int(x),
            1 => FTerm::Float(x),
            _ => FTerm::String(x),
        };
        fc_to_handle(&mk(Red::Cstr, t))
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_mk_construct(c: Value, u: Value) -> Value {
    guard(|| {
        let c = OVal::new(c);
        let u = UInst::new(OVal::new(u));
        fc_to_handle(&mk(Red::Cstr, FTerm::Construct(c, u, Rc::from(vec![]))))
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_mk_const(c: Value, u: Value) -> Value {
    guard(|| {
        let c = OVal::new(c);
        let u = UInst::new(OVal::new(u));
        fc_to_handle(&mk(Red::Ntrl, FTerm::Flex(TableKey::Const(c, u))))
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_mk_ind(i: Value, u: Value) -> Value {
    guard(|| {
        let i = OVal::new(i);
        let u = UInst::new(OVal::new(u));
        fc_to_handle(&mk(Red::Ntrl, FTerm::Ind(i, u)))
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_mkfapp(h: Value, args: Value) -> Value {
    guard(|| {
        let h = OVal::new(h);
        let args = OVal::new(args);
        let f = handle_to_fc(&h);
        let a: Rc<[FC]> = (0..args.size()).map(|i| handle_to_fc(&args.field(i))).collect();
        fc_to_handle(&mk_fapp(&f, &a))
    })
}

#[no_mangle]
pub extern "C" fn rconv_fc_mk_array(u: Value, t: Value, ty: Value) -> Value {
    guard(|| {
        let u = UInst::new(OVal::new(u));
        let t = OVal::new(t);
        let ty = handle_to_fc(&OVal::new(ty));
        fc_to_handle(&mk(Red::Cstr, FTerm::Array(u, t, ty, 0)))
    })
}
