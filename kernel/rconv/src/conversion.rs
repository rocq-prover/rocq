//! Port of kernel/conversion.ml (the [ccnv] cluster).

use std::rc::Rc;

use crate::cbs::*;
use crate::closure::*;
use crate::constr;
use crate::esubst::*;
use crate::ffi::{call, OVal, A};

pub const CONV: isize = 0;
pub const CUMUL: isize = 1;

pub enum NC {
    Plain,
    Trace(OVal),
}

pub type R<T> = Result<T, NC>;

struct MustExpand;

/// The parts of [conv_tab] that do not change during a conversion problem.
pub struct ConvShared {
    pub typ: bool,
    pub lft_tab: Tab,
    pub rgt_tab: Tab,
    pub check: OVal,
}

pub struct CInfosData {
    pub inf: Infos,
    pub sh: Rc<ConvShared>,
}

/// [conv_tab], shared: it is copied in every worklist item, and only
/// changes when crossing binders.
#[derive(Clone)]
pub struct CInfos(Rc<CInfosData>);

impl std::ops::Deref for CInfos {
    type Target = CInfosData;
    #[inline]
    fn deref(&self) -> &CInfosData {
        &self.0
    }
}

impl CInfos {
    pub fn new(inf: Infos, sh: Rc<ConvShared>) -> CInfos {
        CInfos(Rc::new(CInfosData { inf, sh }))
    }
    fn push_relevance(&self, na: &OVal) -> CInfos {
        CInfos::new(self.inf.push_relevance(na), self.sh.clone())
    }
    fn push_relevances(&self, nas: &[OVal]) -> CInfos {
        CInfos::new(self.inf.push_relevances(nas), self.sh.clone())
    }
    fn env(&self) -> &OVal {
        self.inf.env()
    }
}

fn nc<T>() -> R<T> {
    Err(NC::Plain)
}

fn is_empty_stack(s: &Stack) -> bool {
    let mut s = s;
    loop {
        match s.uncons() {
            None => return true,
            Some((Z::Update(_), tl)) | Some((Z::Shift(_), tl)) => s = tl,
            _ => return false,
        }
    }
}

fn el_stack(el: &Lift, stk: &Stack) -> Lift {
    let mut n = 0;
    let mut s = stk;
    while let Some((z, tl)) = s.uncons() {
        if let Z::Shift(k) = z {
            n += k;
        }
        s = tl;
    }
    el_shft(n, el)
}

#[inline(never)]
fn compare_stack_shape(s1: &Stack, s2: &Stack) -> bool {
    let mut bal: isize = 0;
    let mut a = s1;
    let mut b = s2;
    loop {
        match (a.uncons(), b.uncons()) {
            (None, None) => return bal == 0,
            (Some((Z::Update(_), t)), _) | (Some((Z::Shift(_), t)), _) => a = t,
            (_, Some((Z::Update(_), t))) | (_, Some((Z::Shift(_), t))) => b = t,
            (Some((Z::App(l), t)), _) => {
                bal += l.len() as isize;
                a = t
            }
            (_, Some((Z::App(l), t))) => {
                bal -= l.len() as isize;
                b = t
            }
            (Some((Z::Proj(..), t1)), Some((Z::Proj(..), t2))) | (Some((Z::CaseT(_), t1)), Some((Z::CaseT(_), t2))) => {
                if bal != 0 {
                    return false;
                }
                a = t1;
                b = t2;
            }
            (Some((Z::Fix(_, a1), t1)), Some((Z::Fix(_, a2), t2))) => {
                if bal != 0 || !compare_stack_shape(a1, a2) {
                    return false;
                }
                a = t1;
                b = t2;
            }
            (Some((Z::Primitive(op1, _, _, rargs1, _), t1)), Some((Z::Primitive(op2, _, _, rargs2, _), t2))) => {
                if !(bal == 0 && eq(EQ_PRIM, op1, op2) && rargs1.len() == rargs2.len()) {
                    return false;
                }
                a = t1;
                b = t2;
            }
            _ => return false,
        }
    }
}

type LF = (Lift, FC);

/// The arguments of a pure application level: segments of machine
/// arguments, each under its own lift, outermost first. The argument
/// arrays are shared with the machine stack.
#[derive(Clone)]
enum Args {
    One(Lift, Rc<[FC]>),
    Many(Vec<(Lift, Rc<[FC]>)>),
}

impl Args {
    fn len(&self) -> usize {
        match self {
            Args::One(_, a) => a.len(),
            Args::Many(v) => v.iter().map(|(_, a)| a.len()).sum(),
        }
    }
    fn get(&self, j: usize) -> (&Lift, &FC) {
        match self {
            Args::One(l, a) => (l, &a[j]),
            Args::Many(v) => {
                let mut j = j;
                for (l, a) in v {
                    if j < a.len() {
                        return (l, &a[j]);
                    }
                    j -= a.len();
                }
                panic!("index out of bounds")
            }
        }
    }
    /// [zlapp]: the new arguments come first.
    fn prepend(&mut self, l: Lift, a: Rc<[FC]>) {
        match self {
            Args::One(l0, a0) => *self = Args::Many(vec![(l, a), (l0.clone(), a0.clone())]),
            Args::Many(v) => v.insert(0, (l, a)),
        }
    }
}

#[derive(Clone)]
enum Zl {
    App(Args),
    Proj(OVal),
    Fix(LF, Vec<Zl>),
    Case(Rc<CaseData>, Lift),
    Primitive(OVal, Vec<LF>, Vec<(isize, LF)>),
}

const SMALL: usize = 32;

/// Returns the pure stack, top first.
fn pure_rec(lfts: &Lift, stk: &Stack) -> (Lift, Vec<Zl>) {
    /* The elements are processed from the bottom of the stack: collect
       them, on the Rust stack for small stacks. */
    let mut small: [Option<&Z>; SMALL] = [None; SMALL];
    let mut spill: Vec<&Z> = Vec::new();
    let mut n = 0;
    let mut s = stk;
    while let Some((z, tl)) = s.uncons() {
        if n < SMALL {
            small[n] = Some(z);
        } else {
            spill.push(z);
        }
        n += 1;
        s = tl;
    }
    let mut l = lfts.clone();
    let mut out: Vec<Zl> = vec![];
    for i in (0..n).rev() {
        let z = if i < SMALL { small[i].unwrap() } else { spill[i - SMALL] };
        match z {
            Z::Update(_) => (),
            Z::Shift(n) => l = el_shft(*n, &l),
            Z::App(a) => {
                assert!(!a.is_empty());
                if let Some(Zl::App(v2)) = out.last_mut() {
                    v2.prepend(l.clone(), a.clone());
                } else {
                    out.push(Zl::App(Args::One(l.clone(), a.clone())));
                }
            }
            Z::Proj(p, _) => out.push(Zl::Proj(p.clone())),
            Z::Fix(fx, a) => {
                let (lfx, pa) = pure_rec(&l, a);
                out.push(Zl::Fix((lfx, fx.clone()), pa));
            }
            Z::CaseT(cd) => out.push(Zl::Case(cd.clone(), l.clone())),
            Z::Primitive(op, _, _, rargs, kargs) => {
                let r = rargs.iter().map(|t| (l.clone(), t.clone())).collect();
                let k = kargs.iter().map(|(k, t)| (*k, (l.clone(), t.clone()))).collect();
                out.push(Zl::Primitive(op.clone(), r, k));
            }
        }
    }
    out.reverse();
    (l, out)
}

#[inline(never)]
fn pure_stack(lfts: &Lift, stk: &Stack) -> Vec<Zl> {
    pure_rec(lfts, stk).1
}

#[inline(never)]
fn fail_check(r: OVal) -> R<OVal> {
    if r.tag() == 0 {
        Ok(r.field(0))
    } else {
        match r.field(0).as_option() {
            None => Err(NC::Plain),
            Some(e) => Err(NC::Trace(e)),
        }
    }
}

fn sort_cmp_universes(infos: &CInfos, pb: isize, s0: &OVal, s1: &OVal, cuniv: &OVal) -> OVal {
    call(&COMPARE_SORTS, &[A::O(&infos.sh.check), A::I(pb), A::O(s0), A::O(s1), A::O(cuniv)])
}

fn convert_instances(infos: &CInfos, flex: bool, u: &OVal, u2: &OVal, cuniv: &OVal) -> OVal {
    call(&COMPARE_INSTANCES, &[A::O(&infos.sh.check), A::B(flex), A::O(u), A::O(u2), A::O(cuniv)])
}

fn convert_instances_cumul(infos: &CInfos, pb: isize, var: &OVal, u: &OVal, u2: &OVal, cuniv: &OVal) -> OVal {
    call(&COMPARE_CUMUL_INSTANCES, &[A::O(&infos.sh.check), A::I(pb), A::O(var), A::O(u), A::O(u2), A::O(cuniv)])
}

fn result_ok(s: &OVal) -> OVal {
    call(&RESULT_OK, &[A::O(s)])
}

fn convert_inductives(infos: &CInfos, cv_pb: isize, ind: &OVal, nargs: isize, u1: &OVal, u2: &OVal, s: &OVal) -> Result<OVal, MustExpand> {
    let info = call(&IND_CUMUL_INFO, &[A::O(infos.env()), A::O(ind)]);
    match info.field(0).as_option() {
        None => Ok(convert_instances(infos, false, u1, u2, s)),
        Some(variances) => {
            let num_param_arity = info.field_int(1);
            if num_param_arity != nargs {
                if instance_equal(u1, u2) {
                    Ok(result_ok(s))
                } else {
                    Err(MustExpand)
                }
            } else {
                Ok(convert_instances_cumul(infos, cv_pb, &variances, u1, u2, s))
            }
        }
    }
}

fn convert_constructors(infos: &CInfos, ctor: &OVal, nargs: isize, u1: &OVal, u2: &OVal, s: &OVal) -> Result<OVal, MustExpand> {
    let info = call(&CTOR_CUMUL_INFO, &[A::O(infos.env()), A::O(ctor)]);
    if !info.field(0).as_bool() {
        Ok(convert_instances(infos, false, u1, u2, s))
    } else {
        let num_cnstr_args = info.field_int(1);
        if num_cnstr_args != nargs {
            if instance_equal(u1, u2) {
                Ok(result_ok(s))
            } else {
                Err(MustExpand)
            }
        } else {
            let variance = call(&IRRELEVANT_VARIANCE, &[A::O(u1)]);
            Ok(convert_instances_cumul(infos, CONV, &variance, u1, u2, s))
        }
    }
}

#[inline(never)]
fn conv_table_key(infos: &CInfos, nargs: isize, k1: &TableKey, k2: &TableKey, cuniv: OVal) -> R<OVal> {
    match (k1, k2) {
        (TableKey::Const(cst, u), TableKey::Const(cst2, u2)) if eq(EQ_CONSTANT_CAN, cst, cst2) => {
            if instance_equal(&u.v, &u2.v) {
                Ok(cuniv)
            } else if nargs == 1 && call(&IS_ARRAY_TYPE, &[A::O(infos.env()), A::O(cst)]).as_bool() {
                Ok(cuniv)
            } else {
                let flex = call(&CONV_FLEX, &[A::O(infos.env()), A::O(&infos.inf.flags.v()), A::O(cst)]).as_bool();
                fail_check(convert_instances(infos, flex, &u.v, &u2.v, &cuniv))
            }
        }
        (TableKey::Var(id), TableKey::Var(id2)) if eq(EQ_ID, id, id2) => Ok(cuniv),
        (TableKey::Rel(n), TableKey::Rel(n2)) if n == n2 => Ok(cuniv),
        _ => nc(),
    }
}

#[inline(never)]
fn same_args_size(sk1: &Stack, sk2: &Stack) -> R<isize> {
    let n = stack_args_size(sk1);
    if n == stack_args_size(sk2) {
        Ok(n as isize)
    } else {
        nc()
    }
}

fn eta_expand_ind(infos: &CInfos, ind: &OVal, u: &UInst) -> FC {
    let c = call(&ETA_EXPAND_IND, &[A::O(infos.env()), A::O(ind), A::O(&u.v)]);
    injectu(&c, &infos.inf.cache.empty_inst)
}

fn eta_expand_constructor(infos: &CInfos, c: &OVal, u: &UInst) -> FC {
    let t = call(&ETA_EXPAND_CONSTRUCTOR, &[A::O(infos.env()), A::O(c), A::O(&u.v)]);
    injectu(&t, &infos.inf.cache.empty_inst)
}

#[inline(never)]
fn irr_flex(infos: &Infos, fl: &TableKey) -> bool {
    if let TableKey::Const(..) = fl {
        if !infos.cache.irr_consts {
            return false;
        }
    }
    let (tag, a, b) = key_args(fl);
    call(&IRR_FLEX, &[A::O(infos.env()), A::O(&infos.cache.evars), A::I(tag), A::O(&a), A::O(&b)]).as_bool()
}

fn eq_universes(e1: &USubs, e2: &USubs, u1: &OVal, u2: &OVal) -> bool {
    let a = usubst_instance(e1, u1);
    let b = usubst_instance(e2, u2);
    instance_equal(&a, &b)
}

fn eq_usubs_fast(e1: &USubs, e2: &USubs) -> bool {
    (e1.s.ptr_eq(&e2.s) || (is_subs_id(&e1.s) && is_subs_id(&e2.s))) && (e1.u.v.phys_eq(&e2.u.v) || instance_equal(&e1.u.v, &e2.u.v))
}

fn array_equal_norefl(a1: &OVal, a2: &OVal, f: &mut dyn FnMut(&OVal, &OVal) -> bool) -> bool {
    let n = a1.size();
    if n != a2.size() {
        return false;
    }
    for i in (0..n).rev() {
        if !f(&a1.field(i), &a2.field(i)) {
            return false;
        }
    }
    true
}

fn compare_under(e1: &USubs, c1: &OVal, e2: &USubs, c2: &OVal) -> bool {
    if c1.phys_eq(c2) && eq_usubs_fast(e1, e2) {
        return true;
    }
    let k1 = constr::kind(c1);
    let k2 = constr::kind(c2);
    if k1 == constr::CAST {
        return compare_under(e1, &c1.field(0), e2, c2);
    }
    if k2 == constr::CAST {
        return compare_under(e1, c1, e2, &c2.field(0));
    }
    if k1 != k2 {
        return false;
    }
    match k1 {
        constr::REL => match expand_rel(constr::dest_rel(c1), &e1.s) {
            Either::Inl(_) => false,
            Either::Inr((k, _)) => match expand_rel(constr::dest_rel(c2), &e2.s) {
                Either::Inl(_) => false,
                Either::Inr((k2, _)) => k == k2,
            },
        },
        constr::META => c1.field_int(0) == c2.field_int(0),
        constr::VAR => eq(EQ_ID, &c1.field(0), &c2.field(0)),
        constr::INT => eq(EQ_UINT63, &c1.field(0), &c2.field(0)),
        constr::FLOAT => eq(EQ_FLOAT64, &c1.field(0), &c2.field(0)),
        constr::STRING => eq(EQ_PSTRING, &c1.field(0), &c2.field(0)),
        constr::SORT => call(&SORT_EQ_UNDER, &[A::O(&e1.u.v), A::O(&c1.field(0)), A::O(&e2.u.v), A::O(&c2.field(0))]).as_bool(),
        constr::PROD | constr::LAMBDA => {
            compare_under(e1, &c1.field(1), e2, &c2.field(1)) && compare_under(&usubs_lift(e1), &c1.field(2), &usubs_lift(e2), &c2.field(2))
        }
        constr::LETIN => {
            compare_under(e1, &c1.field(1), e2, &c2.field(1)) && compare_under(&usubs_lift(e1), &c1.field(3), &usubs_lift(e2), &c2.field(3))
        }
        constr::APP => {
            let l1 = c1.field(1);
            let l2 = c2.field(1);
            l1.size() == l2.size()
                && compare_under(e1, &c1.field(0), e2, &c2.field(0))
                && array_equal_norefl(&l1, &l2, &mut |a, b| compare_under(e1, a, e2, b))
        }
        constr::PROJ => eq(EQ_PROJ_USER, &c1.field(0), &c2.field(0)) && compare_under(e1, &c1.field(2), e2, &c2.field(2)),
        constr::EVAR => false,
        constr::CONST => {
            let (a1, u1) = constr::dest_pref(c1);
            let (a2, u2) = constr::dest_pref(c2);
            eq(EQ_CONSTANT_USER, &a1, &a2) && eq_universes(e1, e2, &u1, &u2)
        }
        constr::IND => {
            let (a1, u1) = constr::dest_pref(c1);
            let (a2, u2) = constr::dest_pref(c2);
            eq(EQ_IND_USER, &a1, &a2) && eq_universes(e1, e2, &u1, &u2)
        }
        constr::CONSTRUCT => {
            let (a1, u1) = constr::dest_pref(c1);
            let (a2, u2) = constr::dest_pref(c2);
            eq(EQ_CONSTRUCT_USER, &a1, &a2) && eq_universes(e1, e2, &u1, &u2)
        }
        constr::CASE => {
            let ci1 = c1.field(0);
            let ci2 = c2.field(0);
            let p1 = c1.field(3).field(0);
            let p2 = c2.field(3).field(0);
            let nas1 = p1.field(0).size() as isize;
            let nas2 = p2.field(0).size() as isize;
            eq(EQ_IND_USER, &constr::ci_ind(&ci1), &constr::ci_ind(&ci2))
                && eq_universes(e1, e2, &c1.field(1), &c2.field(1))
                && array_equal_norefl(&c1.field(2), &c2.field(2), &mut |a, b| compare_under(e1, a, e2, b))
                && nas1 == nas2
                && compare_under(&usubs_liftn(nas1, e1), &p1.field(1), &usubs_liftn(nas2, e2), &p2.field(1))
                && compare_under(e1, &c1.field(5), e2, &c2.field(5))
                && array_equal_norefl(&c1.field(6), &c2.field(6), &mut |b1, b2| {
                    let n1 = b1.field(0).size() as isize;
                    let n2 = b2.field(0).size() as isize;
                    n1 == n2 && compare_under(&usubs_liftn(n1, e1), &b1.field(1), &usubs_liftn(n2, e2), &b2.field(1))
                })
        }
        constr::FIX => {
            let f1 = c1.field(0);
            let f2 = c2.field(0);
            let (h1, h2) = (f1.field(0), f2.field(0));
            let (d1, d2) = (f1.field(1), f2.field(1));
            let (ln1, ln2) = (h1.field(0), h2.field(0));
            h1.field_int(1) == h2.field_int(1)
                && ln1.size() == ln2.size()
                && (0..ln1.size()).all(|i| ln1.field_int(i) == ln2.field_int(i))
                && array_equal_norefl(&d1.field(1), &d2.field(1), &mut |a, b| compare_under(e1, a, e2, b))
                && {
                    let n = d1.field(1).size() as isize;
                    array_equal_norefl(&d1.field(2), &d2.field(2), &mut |a, b| compare_under(&usubs_liftn(n, e1), a, &usubs_liftn(n, e2), b))
                }
        }
        constr::COFIX => {
            let f1 = c1.field(0);
            let f2 = c2.field(0);
            let (d1, d2) = (f1.field(1), f2.field(1));
            f1.field_int(0) == f2.field_int(0)
                && array_equal_norefl(&d1.field(1), &d2.field(1), &mut |a, b| compare_under(e1, a, e2, b))
                && {
                    let n = d1.field(1).size() as isize;
                    array_equal_norefl(&d1.field(2), &d2.field(2), &mut |a, b| compare_under(&usubs_liftn(n, e1), a, &usubs_liftn(n, e2), b))
                }
        }
        constr::ARRAY => {
            array_equal_norefl(&c1.field(1), &c2.field(1), &mut |a, b| compare_under(e1, a, e2, b))
                && compare_under(e1, &c1.field(2), e2, &c2.field(2))
                && compare_under(e1, &c1.field(3), e2, &c2.field(3))
        }
        _ => false,
    }
}

#[inline(never)]
fn fast_test(lft1: &Lift, term1: &FC, lft2: &Lift, term2: &FC) -> bool {
    let mut lft1 = lft1.clone();
    let mut lft2 = lft2.clone();
    let mut term1 = term1.clone();
    let mut term2 = term2.clone();
    loop {
        let (n1, n2) = {
            let t1 = term1.term();
            let t2 = term2.term();
            match (&*t1, &*t2) {
                (FTerm::Lift(i, a), FTerm::Lift(..)) | (FTerm::Lift(i, a), FTerm::Clos(..)) => (Some((*i, a.clone())), None),
                (FTerm::Clos(..), FTerm::Lift(j, b)) => (None, Some((*j, b.clone()))),
                (FTerm::Clos(c1, e1), FTerm::Clos(c2, e2)) => return eq_lift(&lft1, &lft2) && compare_under(e1, c1, e2, c2),
                _ => return false,
            }
        };
        if let Some((i, a)) = n1 {
            lft1 = el_shft(i, &lft1);
            term1 = a;
        }
        if let Some((j, b)) = n2 {
            lft2 = el_shft(j, &lft2);
            term2 = b;
        }
    }
}

fn assert_reduced_constructor(s: &Stack) {
    if !s.is_nil() {
        anomaly(AN_CTOR_UNREDUCED);
    }
}

/* The [ccnv] / [eqappr] / [eqwhnf] cluster.

   The non-tail calls of the OCaml code (the sub-conversions performed by
   [convert_stacks], [convert_vect], the return clauses and branches...) are
   not performed through Rust recursion: they are pushed as [Item]s on an
   explicit worklist, in an order such that they are processed exactly in the
   order of the OCaml evaluation, the universe state being threaded from one
   item to the next. The [try ... with NotConvertible] of the (FFlex, FFlex)
   case is a [Catch] item: a failure discards the worklist up to the nearest
   [Catch], and resumes with its fallback.

   The tail calls of the OCaml code are explicit [become] calls, which requires
   all the functions involved to share the signature of [eqappr]. */

#[derive(Clone)]
pub struct Side {
    lft: Lift,
    hd: FC,
    stk: Stack,
}

/// The levels of a pair of pure stacks being compared by [cmp_rec], with
/// the number of arguments preceding each level when there is a mask.
pub struct Levels {
    p1: Vec<Zl>,
    p2: Vec<Zl>,
    nargs: Option<Vec<isize>>,
    mask: Option<OVal>,
}

pub enum Item {
    /// [ccnv cv_pb l2r infos l1 l2 t1 t2]
    Ccnv { cv_pb: isize, infos: CInfos, l1: Lift, t1: FC, l2: Lift, t2: FC },
    /// [convert_stacks ~mask l2r infos l1 l2 s1 s2]
    Stacks { mask: Option<OVal>, infos: CInfos, l1: Lift, l2: Lift, s1: Stack, s2: Stack },
    /// The levels [i], [i-1], ..., [0] of a [cmp_rec] traversal
    Level { infos: CInfos, lv: Rc<Levels>, i: usize },
    /// [raise NotConvertible]
    Fail,
    /// The handler of the first-order attempt of the (FFlex, FFlex) case,
    /// with the arguments of the fallback
    Catch { cv_pb: isize, infos: CInfos, a1: Side, a2: Side, cuniv: OVal },
}

pub struct Work {
    items: Vec<Item>,
}

impl Work {
    #[inline]
    fn push(&mut self, it: Item) {
        self.items.push(it)
    }
    /// Push items so that they are processed in the order of [v].
    fn push_seq(&mut self, v: Vec<Item>) {
        for it in v.into_iter().rev() {
            self.items.push(it);
        }
    }
}

fn ccnv_item(cv_pb: isize, infos: &CInfos, l1: &Lift, l2: &Lift, t1: &FC, t2: &FC) -> Item {
    Item::Ccnv { cv_pb, infos: infos.clone(), l1: l1.clone(), t1: t1.clone(), l2: l2.clone(), t2: t2.clone() }
}

fn stacks_item(infos: &CInfos, l1: &Lift, l2: &Lift, s1: &Stack, s2: &Stack) -> Item {
    Item::Stacks { mask: None, infos: infos.clone(), l1: l1.clone(), l2: l2.clone(), s1: s1.clone(), s2: s2.clone() }
}

/// Conversion between [lft1]term1 and [lft2]term2
pub fn ccnv(cv_pb: isize, l2r: bool, infos: &CInfos, lft1: &Lift, lft2: &Lift, term1: &FC, term2: &FC, cuniv: OVal) -> R<OVal> {
    let mut w = Work { items: vec![] };
    w.push(ccnv_item(cv_pb, infos, lft1, lft2, term1, term2));
    run(&mut w, l2r, cuniv)
}

fn run(w: &mut Work, l2r: bool, cuniv: OVal) -> R<OVal> {
    let mut cuniv = cuniv;
    loop {
        let Some(item) = w.items.pop() else { return Ok(cuniv) };
        let r = match item {
            Item::Ccnv { cv_pb, infos, l1, t1, l2, t2 } => {
                let s1 = Side { lft: l1, hd: t1, stk: Stack::nil() };
                let s2 = Side { lft: l2, hd: t2, stk: Stack::nil() };
                ccnv_tail(w, cv_pb, l2r, infos, s1, s2, cuniv)
            }
            Item::Stacks { mask, infos, l1, l2, s1, s2 } => push_stacks(w, mask, &infos, &l1, &l2, &s1, &s2).map(|()| cuniv),
            Item::Level { infos, lv, i } => level(w, l2r, infos, lv, i, cuniv),
            Item::Fail => nc(),
            Item::Catch { .. } => Ok(cuniv),
        };
        match r {
            Ok(c) => cuniv = c,
            Err(e) => {
                let mut e = e;
                loop {
                    match w.items.pop() {
                        None => return Err(e),
                        Some(Item::Catch { cv_pb, infos, a1, a2, cuniv: saved }) => {
                            match eq_flex_flex_unfold(w, cv_pb, l2r, infos, a1, a2, saved) {
                                Ok(c) => {
                                    cuniv = c;
                                    break;
                                }
                                Err(e2) => e = e2,
                            }
                        }
                        Some(_) => (),
                    }
                }
            }
        }
    }
}

/// [ccnv] on the heads of [st1] and [st2], whose stacks are empty.
#[inline(never)]
fn ccnv_tail(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, st1: Side, st2: Side, cuniv: OVal) -> R<OVal> {
    if fast_test(&st1.lft, &st1.hd, &st2.lft, &st2.hd) {
        return Ok(cuniv);
    }
    become eqappr(w, cv_pb, l2r, infos, st1, st2, cuniv)
}

/// Conversion between [lft1](hd1 v1) and [lft2](hd2 v2)
#[inline(never)]
fn eqappr(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, st1: Side, st2: Side, cuniv: OVal) -> R<OVal> {
    check_for_interrupt();
    let ninfos = infos.inf.with_reds(&infos.inf.cache.betaiotazeta);
    let (h1, v1) = whd_stack(&ninfos, &infos.sh.lft_tab, &st1.hd, &st1.stk);
    let (h2, v2) = whd_stack(&ninfos, &infos.sh.rgt_tab, &st2.hd, &st2.stk);
    drop(ninfos);
    let appr1 = Side { lft: st1.lft, hd: h1, stk: v1 };
    let appr2 = Side { lft: st2.lft, hd: h2, stk: v2 };
    become eqwhnf(w, cv_pb, l2r, infos, appr1, appr2, cuniv)
}

/// [Control.check_for_interrupt] does nothing unless one of these
/// references is set.
#[inline]
fn check_for_interrupt() {
    let set = unsafe {
        crate::ffi::field(INTERRUPT_REF.value(), 0) != crate::ffi::VAL_FALSE
            || crate::ffi::field(THREAD_DELAY_REF.value(), 0) != crate::ffi::VAL_FALSE
    };
    if set {
        call(&CHECK_FOR_INTERRUPT, &[A::I(0)]);
    }
}

fn all_transparent(infos: &Infos) -> Infos {
    let f = call(&ALL_TRANSPARENT, &[A::O(infos.flags.v())]);
    infos.with_reds(&Flags::new(f))
}

fn rel_relevance(infos: &Infos, n: isize) -> OVal {
    infos.relevances.get(n - 1)
}

/// [convert_stacks] in tail position
fn stacks(w: &mut Work, infos: &CInfos, a1: &Side, a2: &Side, cuniv: OVal) -> R<OVal> {
    w.push(stacks_item(infos, &a1.lft, &a2.lft, &a1.stk, &a2.stk));
    Ok(cuniv)
}

type Case = fn(&mut Work, isize, bool, CInfos, Side, Side, OVal) -> R<OVal>;

/// Assumes that appr1 and appr2 are in whnf
#[inline(never)]
fn eqwhnf(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    let t1 = appr1.hd.term();
    let t2 = appr2.hd.term();
    let case: Case = match (&*t1, &*t2) {
        (FTerm::Atom(_), FTerm::Atom(_)) => eq_atom,
        (FTerm::Evar(..), FTerm::Evar(..)) => eq_evar,
        (FTerm::Rel(_), FTerm::Rel(_)) => eq_rel,
        (FTerm::Flex(_), FTerm::Flex(_)) => eq_flex_flex,
        (FTerm::Proj(..), FTerm::Proj(..)) => eq_proj_proj,
        (FTerm::Proj(..), _) => eq_proj_left,
        (_, FTerm::Proj(..)) => eq_proj_right,
        (FTerm::Lambda(..), FTerm::Lambda(..)) => eq_lambda_lambda,
        (FTerm::Prod(..), FTerm::Prod(..)) => eq_prod_prod,
        (FTerm::Lambda(..), _) => eq_eta_left,
        (_, FTerm::Lambda(..)) => eq_eta_right,
        (FTerm::Flex(_), _) => eq_flex_left,
        (_, FTerm::Flex(_)) => eq_flex_right,
        (FTerm::Ind(..), FTerm::Ind(..)) => eq_ind,
        (FTerm::Construct(..), FTerm::Construct(..)) => eq_construct,
        (FTerm::Construct(..), _) => eq_record_left,
        (_, FTerm::Construct(..)) => eq_record_right,
        (FTerm::Fix(..), FTerm::Fix(..)) => eq_fix,
        (FTerm::CoFix(..), FTerm::CoFix(..)) => eq_cofix,
        (FTerm::Int(_), FTerm::Int(_)) | (FTerm::Float(_), FTerm::Float(_)) | (FTerm::String(_), FTerm::String(_)) => eq_prim_value,
        (FTerm::CaseInvert(..), FTerm::CaseInvert(..)) => eq_case_invert,
        (FTerm::Array(..), FTerm::Array(..)) => eq_array,
        (FTerm::Rel(_), FTerm::Irrelevant) | (FTerm::Irrelevant, FTerm::Rel(_)) => eq_rel_irr,
        (FTerm::Irrelevant, FTerm::Irrelevant) => eq_irr_irr,
        (FTerm::LetIn(..), _)
        | (FTerm::CaseT(..), _)
        | (FTerm::App(..), _)
        | (FTerm::Clos(..), _)
        | (FTerm::Lift(..), _)
        | (_, FTerm::LetIn(..))
        | (_, FTerm::CaseT(..))
        | (_, FTerm::App(..))
        | (_, FTerm::Clos(..))
        | (_, FTerm::Lift(..))
        | (FTerm::Locked, _)
        | (_, FTerm::Locked) => panic!("assert false"),
        _ => return nc(),
    };
    drop((t1, t2));
    become case(w, cv_pb, l2r, infos, appr1, appr2, cuniv)
}

/// The terms of the heads, copied: for the cases that reduce terms, which
/// may update the cells of the heads.
macro_rules! heads {
    ($t1:ident, $t2:ident, $a1:expr, $a2:expr) => {
        let $t1 = &$a1.hd.term_clone();
        let $t2 = &$a2.hd.term_clone();
    };
}

/// The terms of the heads, borrowed: for the cases that do not reduce any
/// term while they use them.
macro_rules! heads_ref {
    ($t1:ident, $t2:ident, $a1:expr, $a2:expr) => {
        let $t1 = $a1.hd.term();
        let $t2 = $a2.hd.term();
    };
}

fn eq_atom(w: &mut Work, cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Atom(a1), FTerm::Atom(a2)) = (&*t1, &*t2) else { unreachable!() };
    let k1 = constr::kind(a1);
    let k2 = constr::kind(a2);
    if k1 == constr::SORT && k2 == constr::SORT {
        if !(is_empty_stack(&appr1.stk) && is_empty_stack(&appr2.stk)) {
            return nc();
        }
        fail_check(sort_cmp_universes(&infos, cv_pb, &a1.field(0), &a2.field(0), &cuniv))
    } else if k1 == constr::META && k2 == constr::META {
        if a1.field_int(0) == a2.field_int(0) {
            stacks(w, &infos, &appr1, &appr2, cuniv)
        } else {
            nc()
        }
    } else {
        nc()
    }
}

fn eq_evar(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Evar(ev1, args1, env1), FTerm::Evar(ev2, args2, env2)) = (&*t1, &*t2) else { unreachable!() };
    if !eq(EQ_EVAR, ev1, ev2) {
        return nc();
    }
    let el1 = el_stack(&appr1.lft, &appr1.stk);
    let el2 = el_stack(&appr2.lft, &appr2.stk);
    let a1: Vec<FC> = args1.list_to_vec().iter().map(|a| mk_clos(env1, a)).collect();
    let a2: Vec<FC> = args2.list_to_vec().iter().map(|a| mk_clos(env2, a)).collect();
    let mut items = vec![stacks_item(&infos, &appr1.lft, &appr2.lft, &appr1.stk, &appr2.stk)];
    items.extend(convert_list(&infos, &el1, &el2, &a1, &a2));
    w.push_seq(items);
    Ok(cuniv)
}

fn eq_rel(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Rel(n), FTerm::Rel(m)) = (&*t1, &*t2) else { unreachable!() };
    let el1 = el_stack(&appr1.lft, &appr1.stk);
    let el2 = el_stack(&appr2.lft, &appr2.stk);
    let n = reloc_rel(*n, &el1);
    let m = reloc_rel(*m, &el2);
    let inf = &infos.inf;
    let rn = rel_relevance(inf, n);
    let rm = rel_relevance(inf, m);
    if is_irrelevant(inf, &rn) && is_irrelevant(inf, &rm) {
        let v1 = skip_irrelevant_stack(inf, &appr1.stk);
        let v2 = skip_irrelevant_stack(inf, &appr2.stk);
        w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &v1, &v2));
        Ok(cuniv)
    } else if n == m {
        stacks(w, &infos, &appr1, &appr2, cuniv)
    } else {
        nc()
    }
}

/// The (FFlex, FFlex) case: the body of the [try] is performed above a
/// [Catch] item holding the arguments of the [with] branch.
fn eq_flex_flex(w: &mut Work, cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    w.push(Item::Catch { cv_pb, infos: infos.clone(), a1: appr1.clone(), a2: appr2.clone(), cuniv: cuniv.clone() });
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Flex(fl1), FTerm::Flex(fl2)) = (&*t1, &*t2) else { unreachable!() };
    let nargs = same_args_size(&appr1.stk, &appr2.stk)?;
    let cuniv = conv_table_key(&infos, nargs, fl1, fl2, cuniv)?;
    if irr_flex(&infos.inf, fl1) {
        return nc();
    }
    let mask = if infos.sh.typ {
        match fl1 {
            TableKey::Const(..) => get_ref_mask(&infos.inf, &infos.sh.lft_tab, fl1),
            _ => None,
        }
    } else {
        None
    };
    w.push(Item::Stacks { mask, infos: infos.clone(), l1: appr1.lft.clone(), l2: appr2.lft.clone(), s1: appr1.stk.clone(), s2: appr2.stk.clone() });
    Ok(cuniv)
}

/// The [with NotConvertible ->] branch of the (FFlex, FFlex) case.
#[inline(never)]
fn eq_flex_flex_unfold(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, t2, appr1, appr2);
    let (FTerm::Flex(fl1), FTerm::Flex(fl2)) = (&*t1, &*t2) else { unreachable!() };
    let r1 = unfold_ref_with_args(&infos.inf, &infos.sh.lft_tab, fl1, &appr1.stk);
    let r2 = unfold_ref_with_args(&infos.inf, &infos.sh.rgt_tab, fl2, &appr2.stk);
    let (appr1, appr2) = match (r1, r2) {
        (None, None) => return nc(),
        (Some((t1, v1)), Some((t2, v2))) => {
            let ninfos = infos.inf.with_reds(&infos.inf.cache.betaiotazeta);
            check_for_interrupt();
            let ta = key_args(fl1);
            let tb = key_args(fl2);
            let unfold_left =
                call(&UNFOLD_LEFT, &[A::O(infos.env()), A::I(ta.0), A::O(&ta.1), A::I(tb.0), A::O(&tb.1), A::B(l2r)]).as_bool();
            if unfold_left {
                let (h, s) = whd_stack(&ninfos, &infos.sh.lft_tab, &t1, &v1);
                (Side { lft: appr1.lft, hd: h, stk: s }, appr2)
            } else {
                let (h, s) = whd_stack(&ninfos, &infos.sh.rgt_tab, &t2, &v2);
                (appr1, Side { lft: appr2.lft, hd: h, stk: s })
            }
        }
        (Some((t1, v1)), None) => {
            let all = all_transparent(&infos.inf);
            let (h, s) = whd_stack(&all, &infos.sh.lft_tab, &t1, &v1);
            (Side { lft: appr1.lft, hd: h, stk: s }, appr2)
        }
        (None, Some((t2, v2))) => {
            let all = all_transparent(&infos.inf);
            let (h, s) = whd_stack(&all, &infos.sh.rgt_tab, &t2, &v2);
            (appr1, Side { lft: appr2.lft, hd: h, stk: s })
        }
    };
    become eqwhnf(w, cv_pb, l2r, infos, appr1, appr2, cuniv)
}

fn eq_proj_proj(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, t2, appr1, appr2);
    let (FTerm::Proj(p1, r1, c1), FTerm::Proj(p2, r2, c2)) = (&*t1, &*t2) else { unreachable!() };
    match unfold_projection(&infos.inf, p1, r1) {
        Some(s1) => {
            let a1 = Side { lft: appr1.lft.clone(), hd: c1.clone(), stk: appr1.stk.cons(s1) };
            become eqappr(w, cv_pb, l2r, infos, a1, appr2, cuniv)
        }
        None => match unfold_projection(&infos.inf, p2, r2) {
            Some(s2) => {
                let a2 = Side { lft: appr2.lft.clone(), hd: c2.clone(), stk: appr2.stk.cons(s2) };
                become eqappr(w, cv_pb, l2r, infos, appr1, a2, cuniv)
            }
            None => {
                let (v1, v2) = (&appr1.stk, &appr2.stk);
                if eq(EQ_PROJ_REPR_CAN, &p1.field(0), &p2.field(0)) && compare_stack_shape(v1, v2) {
                    let el1 = el_stack(&appr1.lft, v1);
                    let el2 = el_stack(&appr2.lft, v2);
                    w.push_seq(vec![
                        ccnv_item(CONV, &infos, &el1, &el2, c1, c2),
                        stacks_item(&infos, &appr1.lft, &appr2.lft, v1, v2),
                    ]);
                    Ok(cuniv)
                } else {
                    nc()
                }
            }
        },
    }
}

fn eq_proj_left(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, t2, appr1, appr2);
    let FTerm::Proj(p1, r1, c1) = &*t1 else { unreachable!() };
    match unfold_projection(&infos.inf, p1, r1) {
        Some(s1) => {
            let a1 = Side { lft: appr1.lft.clone(), hd: c1.clone(), stk: appr1.stk.cons(s1) };
            become eqappr(w, cv_pb, l2r, infos, a1, appr2, cuniv)
        }
        None => match &*t2 {
            FTerm::Flex(fl2) => match unfold_ref_with_args(&infos.inf, &infos.sh.rgt_tab, fl2, &appr2.stk) {
                Some((h, s)) => {
                    let a2 = Side { lft: appr2.lft.clone(), hd: h, stk: s };
                    become eqappr(w, cv_pb, l2r, infos, appr1, a2, cuniv)
                }
                None => nc(),
            },
            _ => nc(),
        },
    }
}

fn eq_proj_right(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, t2, appr1, appr2);
    let FTerm::Proj(p2, r2, c2) = &*t2 else { unreachable!() };
    match unfold_projection(&infos.inf, p2, r2) {
        Some(s2) => {
            let a2 = Side { lft: appr2.lft.clone(), hd: c2.clone(), stk: appr2.stk.cons(s2) };
            become eqappr(w, cv_pb, l2r, infos, appr1, a2, cuniv)
        }
        None => match &*t1 {
            FTerm::Flex(fl1) => match unfold_ref_with_args(&infos.inf, &infos.sh.lft_tab, fl1, &appr1.stk) {
                Some((h, s)) => {
                    let a1 = Side { lft: appr1.lft.clone(), hd: h, stk: s };
                    become eqappr(w, cv_pb, l2r, infos, a1, appr2, cuniv)
                }
                None => nc(),
            },
            _ => nc(),
        },
    }
}

fn eq_lambda_lambda(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    let (v1, v2) = (&appr1.stk, &appr2.stk);
    if !(is_empty_stack(v1) && is_empty_stack(v2)) {
        anomaly(AN_LAMBDA_ILLTYPED);
    }
    let (x1, ty1, bd1) = dest_flambda(&appr1.hd);
    let (_, ty2, bd2) = dest_flambda(&appr2.hd);
    let el1 = el_stack(&appr1.lft, v1);
    let el2 = el_stack(&appr2.lft, v2);
    w.push_seq(vec![
        ccnv_item(CONV, &infos, &el1, &el2, &ty1, &ty2),
        ccnv_item(CONV, &infos.push_relevance(&x1), &el_lift(&el1), &el_lift(&el2), &bd1, &bd2),
    ]);
    Ok(cuniv)
}

fn eq_prod_prod(w: &mut Work, cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Prod(x1, c1, c2, e), FTerm::Prod(_, c12, c22, e2)) = (&*t1, &*t2) else { unreachable!() };
    let (v1, v2) = (&appr1.stk, &appr2.stk);
    if !(is_empty_stack(v1) && is_empty_stack(v2)) {
        return nc();
    }
    let el1 = el_stack(&appr1.lft, v1);
    let el2 = el_stack(&appr2.lft, v2);
    let x1 = usubst_binder(e, x1);
    let b1 = mk_clos(&usubs_lift(e), c2);
    let b2 = mk_clos(&usubs_lift(e2), c22);
    w.push_seq(vec![
        ccnv_item(CONV, &infos, &el1, &el2, c1, c12),
        ccnv_item(cv_pb, &infos.push_relevance(&x1), &el_lift(&el1), &el_lift(&el2), &b1, &b2),
    ]);
    Ok(cuniv)
}

fn eq_eta_left(w: &mut Work, _cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    if !appr1.stk.is_nil() {
        anomaly(AN_LAMBDA_UNREDUCED);
    }
    let (x1, _ty1, bd1) = dest_flambda(&appr1.hd);
    let infos = infos.push_relevance(&x1);
    let s2 = eta_expand_stack(&infos.inf, &x1, &appr2.stk);
    let a1 = Side { lft: el_lift(&appr1.lft), hd: bd1, stk: Stack::nil() };
    let a2 = Side { lft: el_lift(&appr2.lft), hd: appr2.hd, stk: s2 };
    become eqappr(w, CONV, l2r, infos, a1, a2, cuniv)
}

fn eq_eta_right(w: &mut Work, _cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    if !appr2.stk.is_nil() {
        anomaly(AN_LAMBDA_UNREDUCED);
    }
    let (x2, _ty2, bd2) = dest_flambda(&appr2.hd);
    let infos = infos.push_relevance(&x2);
    let s1 = eta_expand_stack(&infos.inf, &x2, &appr1.stk);
    let a1 = Side { lft: el_lift(&appr1.lft), hd: appr1.hd, stk: s1 };
    let a2 = Side { lft: el_lift(&appr2.lft), hd: bd2, stk: Stack::nil() };
    become eqappr(w, CONV, l2r, infos, a1, a2, cuniv)
}

fn eq_flex_left(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, t2, appr1, appr2);
    let FTerm::Flex(fl1) = &*t1 else { unreachable!() };
    match unfold_ref_with_args(&infos.inf, &infos.sh.lft_tab, fl1, &appr1.stk) {
        Some((def1, v1)) => {
            let all = all_transparent(&infos.inf);
            let (h, s) = whd_stack(&all, &infos.sh.lft_tab, &def1, &v1);
            let a1 = Side { lft: appr1.lft.clone(), hd: h, stk: s };
            drop((all, def1, v1));
            become eqwhnf(w, cv_pb, l2r, infos, a1, appr2, cuniv)
        }
        None => match &*t2 {
            FTerm::Construct(c, u2, args2) if c.field_int(1) == 1 => {
                assert_reduced_constructor(&appr2.stk);
                match eta_expand_ind_stack(&infos.inf, &c.field(0), u2, args2, &appr1.hd, &appr1.stk) {
                    Some((v2, v1)) => {
                        w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &v1, &v2));
                        Ok(cuniv)
                    }
                    None => nc(),
                }
            }
            _ => nc(),
        },
    }
}

fn eq_flex_right(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, t2, appr1, appr2);
    let FTerm::Flex(fl2) = &*t2 else { unreachable!() };
    match unfold_ref_with_args(&infos.inf, &infos.sh.rgt_tab, fl2, &appr2.stk) {
        Some((def2, v2)) => {
            let all = all_transparent(&infos.inf);
            let (h, s) = whd_stack(&all, &infos.sh.rgt_tab, &def2, &v2);
            let a2 = Side { lft: appr2.lft.clone(), hd: h, stk: s };
            drop((all, def2, v2));
            become eqwhnf(w, cv_pb, l2r, infos, appr1, a2, cuniv)
        }
        None => match &*t1 {
            FTerm::Construct(c, u1, args1) if c.field_int(1) == 1 => {
                assert_reduced_constructor(&appr1.stk);
                match eta_expand_ind_stack(&infos.inf, &c.field(0), u1, args1, &appr2.hd, &appr2.stk) {
                    Some((v1, v2)) => {
                        w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &v1, &v2));
                        Ok(cuniv)
                    }
                    None => nc(),
                }
            }
            _ => nc(),
        },
    }
}

fn eq_ind(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Ind(ind1, u1), FTerm::Ind(ind2, u2)) = (&*t1, &*t2) else { unreachable!() };
    if !eq(EQ_IND_CAN, ind1, ind2) {
        return nc();
    }
    if u1.empty || u2.empty {
        let cuniv = fail_check(convert_instances(&infos, false, &u1.v, &u2.v, &cuniv))?;
        return stacks(w, &infos, &appr1, &appr2, cuniv);
    }
    let nargs = same_args_size(&appr1.stk, &appr2.stk)?;
    match convert_inductives(&infos, cv_pb, ind1, nargs, &u1.v, &u2.v, &cuniv) {
        Ok(r) => {
            let cuniv = fail_check(r)?;
            stacks(w, &infos, &appr1, &appr2, cuniv)
        }
        Err(MustExpand) => {
            let a1 = Side { lft: appr1.lft.clone(), hd: eta_expand_ind(&infos, ind1, u1), stk: appr1.stk.clone() };
            let a2 = Side { lft: appr2.lft.clone(), hd: eta_expand_ind(&infos, ind2, u2), stk: appr2.stk.clone() };
            drop((t1, t2));
            drop((appr1, appr2));
            become eqappr(w, cv_pb, l2r, infos, a1, a2, cuniv)
        }
    }
}

fn eq_construct(w: &mut Work, cv_pb: isize, l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Construct(c1, u1, args1), FTerm::Construct(c2, u2, args2)) = (&*t1, &*t2) else { unreachable!() };
    assert_reduced_constructor(&appr1.stk);
    assert_reduced_constructor(&appr2.stk);
    let nargs = args1.len();
    if nargs != args2.len() {
        return nc();
    }
    let v1 = append_stack(args1, &appr1.stk);
    let v2 = append_stack(args2, &appr2.stk);
    if !(c1.field_int(1) == c2.field_int(1) && eq(EQ_IND_CAN, &c1.field(0), &c2.field(0))) {
        return nc();
    }
    if u1.empty || u2.empty {
        let cuniv = fail_check(convert_instances(&infos, false, &u1.v, &u2.v, &cuniv))?;
        w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &v1, &v2));
        return Ok(cuniv);
    }
    match convert_constructors(&infos, c1, nargs as isize, &u1.v, &u2.v, &cuniv) {
        Ok(r) => {
            let cuniv = fail_check(r)?;
            w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &v1, &v2));
            Ok(cuniv)
        }
        Err(MustExpand) => {
            let a1 = Side { lft: appr1.lft.clone(), hd: eta_expand_constructor(&infos, c1, u1), stk: v1 };
            let a2 = Side { lft: appr2.lft.clone(), hd: eta_expand_constructor(&infos, c2, u2), stk: v2 };
            drop((t1, t2));
            drop((appr1, appr2));
            become eqappr(w, cv_pb, l2r, infos, a1, a2, cuniv)
        }
    }
}

fn eq_record_left(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, _t2, appr1, appr2);
    let FTerm::Construct(c1, u1, args1) = &*t1 else { unreachable!() };
    assert_reduced_constructor(&appr1.stk);
    if c1.field_int(1) != 1 {
        return nc();
    }
    match eta_expand_ind_stack(&infos.inf, &c1.field(0), u1, args1, &appr2.hd, &appr2.stk) {
        Some((v1, v2)) => {
            w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &v1, &v2));
            Ok(cuniv)
        }
        None => nc(),
    }
}

fn eq_record_right(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(_t1, t2, appr1, appr2);
    let FTerm::Construct(c2, u2, args2) = &*t2 else { unreachable!() };
    assert_reduced_constructor(&appr2.stk);
    if c2.field_int(1) != 1 {
        return nc();
    }
    match eta_expand_ind_stack(&infos.inf, &c2.field(0), u2, args2, &appr1.hd, &appr1.stk) {
        Some((v2, v1)) => {
            w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &v1, &v2));
            Ok(cuniv)
        }
        None => nc(),
    }
}

fn eq_fix(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::Fix(f1, e1), FTerm::Fix(f2, e2)) = (&*t1, &*t2) else { unreachable!() };
    let (op1, op2) = (&f1.ri, &f2.ri);
    let same_op = op1.size() == op2.size() && (0..op1.size()).all(|i| op1.field_int(i) == op2.field_int(i));
    if f1.i == f2.i && same_op {
        let items = convert_fix(&infos, &appr1, &appr2, f1, e1, f2, e2)?;
        w.push_seq(items);
        Ok(cuniv)
    } else {
        nc()
    }
}

fn eq_cofix(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::CoFix(f1, e1), FTerm::CoFix(f2, e2)) = (&*t1, &*t2) else { unreachable!() };
    if f1.i == f2.i {
        let items = convert_fix(&infos, &appr1, &appr2, f1, e1, f2, e2)?;
        w.push_seq(items);
        Ok(cuniv)
    } else {
        nc()
    }
}

fn eq_prim_value(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let same = match (&*t1, &*t2) {
        (FTerm::Int(i1), FTerm::Int(i2)) => eq(EQ_UINT63, i1, i2),
        (FTerm::Float(f1), FTerm::Float(f2)) => eq(EQ_FLOAT64, f1, f2),
        (FTerm::String(s1), FTerm::String(s2)) => eq(EQ_PSTRING, s1, s2),
        _ => unreachable!(),
    };
    if same {
        stacks(w, &infos, &appr1, &appr2, cuniv)
    } else {
        nc()
    }
}

fn eq_case_invert(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(t1, t2, appr1, appr2);
    let (FTerm::CaseInvert(cd1, iv1, _), FTerm::CaseInvert(cd2, iv2, _)) = (&*t1, &*t2) else { unreachable!() };
    let ind = constr::ci_ind(&cd1.ci);
    if !eq(EQ_IND_CAN, &ind, &constr::ci_ind(&cd2.ci)) {
        return nc();
    }
    let el1 = el_stack(&appr1.lft, &appr1.stk);
    let el2 = el_stack(&appr2.lft, &appr2.stk);
    let (e1, e2) = (&cd1.e, &cd2.e);
    let u1 = usubst_instance(e1, &cd1.u);
    let u2 = usubst_instance(e2, &cd2.u);
    let cuniv = {
        let nargs = call(&IND_CUMUL_INFO, &[A::O(infos.env()), A::O(&ind)]).field_int(1);
        match convert_inductives(&infos, CONV, &ind, nargs, &u1, &u2, &cuniv) {
            Ok(r) => fail_check(r)?,
            Err(MustExpand) => panic!("rconv: uncaught MustExpand"),
        }
    };
    let pms1 = mk_clos_vect(e1, &cd1.pms);
    let pms2 = mk_clos_vect(e2, &cd2.pms);
    if pms1.len() != pms2.len() || iv1.len() != iv2.len() {
        panic!("Invalid_argument");
    }
    let mut items: Vec<Item> = vec![];
    for i in (0..pms1.len()).rev() {
        items.push(ccnv_item(CONV, &infos, &el1, &el2, &pms1[i], &pms2[i]));
    }
    for i in (0..iv1.len()).rev() {
        items.push(ccnv_item(CONV, &infos, &el1, &el2, &iv1[i], &iv2[i]));
    }
    items.push(convert_return_clause(&infos, &ind, e1, e2, &el1, &el2, &u1, &u2, &pms1, &pms2, &cd1.p, &cd2.p));
    items.extend(convert_branches(&infos, &ind, e1, e2, &el1, &el2, &u1, &u2, &pms1, &pms2, &cd1.br, &cd2.br));
    items.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &appr1.stk, &appr2.stk));
    w.push_seq(items);
    Ok(cuniv)
}

fn eq_array(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads_ref!(tm1, tm2, appr1, appr2);
    let (FTerm::Array(u1, t1, ty1, alft1), FTerm::Array(u2, t2, ty2, alft2)) = (&*tm1, &*tm2) else { unreachable!() };
    let (alft1, alft2) = (*alft1, *alft2);
    let len = call(&PARRAY_LENGTH, &[A::O(t1)]).as_int();
    if len != call(&PARRAY_LENGTH, &[A::O(t2)]).as_int() {
        return nc();
    }
    let var = call(&ARRAY_VARIANCE, &[A::I(0)]);
    let cuniv = fail_check(convert_instances_cumul(&infos, CONV, &var, &u1.v, &u2.v, &cuniv))?;
    let el1 = el_stack(&appr1.lft, &appr1.stk);
    let el2 = el_stack(&appr2.lft, &appr2.stk);
    let mut items = vec![ccnv_item(CONV, &infos, &el1, &el2, &lift_fconstr(alft1, ty1), &lift_fconstr(alft2, ty2))];
    let r1 = call(&PARRAY_TO_ARRAY, &[A::O(t1)]);
    let r2 = call(&PARRAY_TO_ARRAY, &[A::O(t2)]);
    let (a1, a2) = (r1.field(0), r2.field(0));
    if a1.size() != a2.size() {
        panic!("Parray.fold_left2");
    }
    for i in 0..a1.size() {
        let x1 = crate::ffi::handle_to_fc(&a1.field(i));
        let x2 = crate::ffi::handle_to_fc(&a2.field(i));
        items.push(ccnv_item(CONV, &infos, &el1, &el2, &lift_fconstr(alft1, &x1), &lift_fconstr(alft2, &x2)));
    }
    let d1 = crate::ffi::handle_to_fc(&r1.field(1));
    let d2 = crate::ffi::handle_to_fc(&r2.field(1));
    items.push(ccnv_item(CONV, &infos, &el1, &el2, &lift_fconstr(alft1, &d1), &lift_fconstr(alft2, &d2)));
    items.push(stacks_item(&infos, &appr1.lft, &appr2.lft, &appr1.stk, &appr2.stk));
    w.push_seq(items);
    Ok(cuniv)
}

/// (FRel n, FIrrelevant) and (FIrrelevant, FRel n)
fn eq_rel_irr(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    heads!(t1, t2, appr1, appr2);
    let (n, left) = match (&*t1, &*t2) {
        (FTerm::Rel(n), FTerm::Irrelevant) => (*n, true),
        (FTerm::Irrelevant, FTerm::Rel(n)) => (*n, false),
        _ => unreachable!(),
    };
    let s = if left { &appr1 } else { &appr2 };
    let n = reloc_rel(n, &el_stack(&s.lft, &s.stk));
    let inf = &infos.inf;
    let r = rel_relevance(inf, n);
    if !is_irrelevant(inf, &r) {
        return nc();
    }
    let v = skip_irrelevant_stack(inf, &s.stk);
    let (v1, v2) = if left { (&v, &appr2.stk) } else { (&appr1.stk, &v) };
    w.push(stacks_item(&infos, &appr1.lft, &appr2.lft, v1, v2));
    Ok(cuniv)
}

fn eq_irr_irr(w: &mut Work, _cv_pb: isize, _l2r: bool, infos: CInfos, appr1: Side, appr2: Side, cuniv: OVal) -> R<OVal> {
    stacks(w, &infos, &appr1, &appr2, cuniv)
}

/// The sub-conversions of the (FFix, FFix) and (FCoFix, FCoFix) cases.
#[allow(clippy::too_many_arguments)]
fn convert_fix(infos: &CInfos, appr1: &Side, appr2: &Side, f1: &FixData, e1: &USubs, f2: &FixData, e2: &USubs) -> R<Vec<Item>> {
    let (lft1, lft2, v1, v2) = (&appr1.lft, &appr2.lft, &appr1.stk, &appr2.stk);
    let (tys1, tys2) = (f1.types(), f2.types());
    let (cl1, cl2) = (f1.bodies(), f2.bodies());
    let n = cl1.size() as isize;
    let fty1: Vec<FC> = (0..tys1.size()).map(|i| mk_clos(e1, &tys1.field(i))).collect();
    let fty2: Vec<FC> = (0..tys2.size()).map(|i| mk_clos(e2, &tys2.field(i))).collect();
    let fcl1: Vec<FC> = (0..cl1.size()).map(|i| mk_clos(&usubs_liftn(n, e1), &cl1.field(i))).collect();
    let fcl2: Vec<FC> = (0..cl2.size()).map(|i| mk_clos(&usubs_liftn(n, e2), &cl2.field(i))).collect();
    let el1 = el_stack(lft1, v1);
    let el2 = el_stack(lft2, v2);
    let mut items = convert_vect(infos, &el1, &el2, &fty1, &fty2)?;
    let na1 = f1.names();
    let na1: Vec<OVal> = (0..na1.size()).map(|i| usubst_binder(e1, &na1.field(i))).collect();
    let binfos = infos.push_relevances(&na1);
    items.extend(convert_vect(&binfos, &el_liftn(n, &el1), &el_liftn(n, &el2), &fcl1, &fcl2)?);
    items.push(stacks_item(infos, lft1, lft2, v1, v2));
    Ok(items)
}

/// [convert_stacks]: check the shapes, and push the levels of the pure
/// stacks, to be processed from the bottom of the stacks.
#[allow(clippy::too_many_arguments)]
fn push_stacks(w: &mut Work, mask: Option<OVal>, infos: &CInfos, lft1: &Lift, lft2: &Lift, stk1: &Stack, stk2: &Stack) -> R<()> {
    if !compare_stack_shape(stk1, stk2) {
        return nc();
    }
    /* Same shape: if [stk1] has no argument nor elimination, neither has
       [stk2], and the pure stacks are empty. */
    if is_empty_stack(stk1) {
        return Ok(());
    }
    let mask = match mask {
        Some(m) if m.size() > 0 => Some(m),
        _ => None,
    };
    if only_apps(stk1) && only_apps(stk2) {
        push_app_stacks(w, mask.as_ref(), infos, lft1, lft2, stk1, stk2);
        return Ok(());
    }
    let nargs = if mask.is_none() { -1 } else { 0 };
    let p1 = pure_stack(lft1, stk1);
    let p2 = pure_stack(lft2, stk2);
    push_levels(w, infos, nargs, mask, p1, p2);
    Ok(())
}

/// Whether the stack only contains arguments, shifts and updates.
fn only_apps(s: &Stack) -> bool {
    let mut s = s;
    while let Some((z, tl)) = s.uncons() {
        match z {
            Z::App(_) | Z::Shift(_) | Z::Update(_) => s = tl,
            _ => return false,
        }
    }
    true
}

/// The arguments of a stack that only contains arguments, shifts and
/// updates, from the top, each with the lift that [pure_rec] gives it:
/// the initial one, shifted by the shifts below the argument.
struct ArgCursor<'a> {
    s: &'a Stack,
    base: &'a Lift,
    arr: Option<(&'a Rc<[FC]>, usize, Lift)>,
    above: isize,
    total: isize,
}

impl<'a> ArgCursor<'a> {
    fn new(base: &'a Lift, s: &'a Stack) -> ArgCursor<'a> {
        let mut total = 0;
        let mut t = s;
        while let Some((z, tl)) = t.uncons() {
            if let Z::Shift(k) = z {
                total += k;
            }
            t = tl;
        }
        ArgCursor { s, base, arr: None, above: 0, total }
    }
    fn next(&mut self) -> Option<(Lift, FC)> {
        loop {
            if let Some((a, i, l)) = &mut self.arr {
                if *i < a.len() {
                    let r = (l.clone(), a[*i].clone());
                    *i += 1;
                    return Some(r);
                }
                self.arr = None;
            }
            let (z, tl) = self.s.uncons()?;
            match z {
                Z::Shift(k) => self.above += k,
                Z::Update(_) => (),
                Z::App(a) => self.arr = Some((a, 0, el_shft(self.total - self.above, self.base))),
                _ => unreachable!(),
            }
            self.s = tl;
        }
    }
}

/// [convert_stacks] on stacks that only contain arguments: [cmp_rec] then
/// converts the arguments from the last one to the first one, skipping
/// those masked out.
fn push_app_stacks(w: &mut Work, mask: Option<&OVal>, infos: &CInfos, lft1: &Lift, lft2: &Lift, stk1: &Stack, stk2: &Stack) {
    let mut c1 = ArgCursor::new(lft1, stk1);
    let mut c2 = ArgCursor::new(lft2, stk2);
    let mlen = mask.map_or(0, |m| m.size());
    let mut j = 0;
    while let Some((l1, t1)) = c1.next() {
        let (l2, t2) = c2.next().expect("Invalid_argument");
        let skip = match mask {
            Some(m) => j < mlen && !m.field(j).as_bool(),
            None => false,
        };
        if !skip {
            w.push(Item::Ccnv { cv_pb: CONV, infos: infos.clone(), l1, t1, l2, t2 });
        }
        j += 1;
    }
    assert!(c2.next().is_none());
}

/// Start a [cmp_rec nargs p1 p2] traversal.
fn push_levels(w: &mut Work, infos: &CInfos, nargs: isize, mask: Option<OVal>, p1: Vec<Zl>, p2: Vec<Zl>) {
    let k = std::cmp::min(p1.len(), p2.len());
    if k == 0 {
        return;
    }
    let nargsv = if nargs < 0 {
        None
    } else {
        let mut v: Vec<isize> = Vec::with_capacity(k);
        let mut na = nargs;
        for z in p1.iter().take(k) {
            v.push(na);
            na = match z {
                Zl::App(a) => {
                    if na < 0 {
                        -1
                    } else {
                        na + a.len() as isize
                    }
                }
                _ => -1,
            };
        }
        Some(v)
    };
    let lv = Rc::new(Levels { p1, p2, nargs: nargsv, mask });
    w.push(Item::Level { infos: infos.clone(), lv, i: k - 1 });
}

fn lf_item(infos: &CInfos, a: &LF, b: &LF) -> Item {
    ccnv_item(CONV, infos, &a.0, &b.0, &a.1, &b.1)
}

/// One level of [cmp_rec]: the levels above it are processed afterwards.
fn level(w: &mut Work, _l2r: bool, infos: CInfos, lv: Rc<Levels>, i: usize, cuniv: OVal) -> R<OVal> {
    if i > 0 {
        w.push(Item::Level { infos: infos.clone(), lv: lv.clone(), i: i - 1 });
    }
    let nargs = lv.nargs.as_ref().map_or(-1, |v| v[i]);
    match (&lv.p1[i], &lv.p2[i]) {
        (Zl::App(a1), Zl::App(a2)) => {
            if nargs < 0 && a1.len() != a2.len() {
                panic!("Invalid_argument");
            }
            let mask = if nargs < 0 { None } else { lv.mask.as_ref() };
            let mlen = mask.map_or(0, |m| m.size() as isize);
            /* processed from the last argument to the first one */
            for j in 0..a1.len() {
                let idx = nargs + j as isize;
                if let Some(m) = mask {
                    if idx < mlen && !m.field(idx as usize).as_bool() {
                        continue;
                    }
                }
                let (l1, t1) = a1.get(j);
                let (l2, t2) = a2.get(j);
                w.push(ccnv_item(CONV, &infos, l1, l2, t1, t2));
            }
            Ok(cuniv)
        }
        (Zl::Proj(c1), Zl::Proj(c2)) => {
            if !eq(EQ_PROJ_REPR_CAN, c1, c2) {
                return nc();
            }
            Ok(cuniv)
        }
        (Zl::Fix(fx1, a1), Zl::Fix(fx2, a2)) => {
            push_levels(w, &infos, -1, None, a1.clone(), a2.clone());
            w.push(lf_item(&infos, fx1, fx2));
            Ok(cuniv)
        }
        (Zl::Case(cd1, l1), Zl::Case(cd2, l2)) => {
            let ind = constr::ci_ind(&cd1.ci);
            if !eq(EQ_IND_CAN, &ind, &constr::ci_ind(&cd2.ci)) {
                return nc();
            }
            let (e1, e2) = (&cd1.e, &cd2.e);
            let u1 = usubst_instance(e1, &cd1.u);
            let u2 = usubst_instance(e2, &cd2.u);
            let r = if constr::instance_is_empty(&u1) || constr::instance_is_empty(&u2) {
                convert_instances(&infos, false, &u1, &u2, &cuniv)
            } else {
                let info = call(&IND_CUMUL_INFO, &[A::O(infos.env()), A::O(&ind)]);
                match info.field(0).as_option() {
                    None => convert_instances(&infos, false, &u1, &u2, &cuniv),
                    Some(variances) => convert_instances_cumul(&infos, CONV, &variances, &u1, &u2, &cuniv),
                }
            };
            let cu = fail_check(r)?;
            let pms1 = mk_clos_vect(e1, &cd1.pms);
            let pms2 = mk_clos_vect(e2, &cd2.pms);
            if pms1.len() != pms2.len() {
                panic!("Invalid_argument");
            }
            let mut items: Vec<Item> = vec![];
            for j in (0..pms1.len()).rev() {
                items.push(ccnv_item(CONV, &infos, l1, l2, &pms1[j], &pms2[j]));
            }
            items.push(convert_return_clause(&infos, &ind, e1, e2, l1, l2, &u1, &u2, &pms1, &pms2, &cd1.p, &cd2.p));
            items.extend(convert_branches(&infos, &ind, e1, e2, l1, l2, &u1, &u2, &pms1, &pms2, &cd1.br, &cd2.br));
            w.push_seq(items);
            Ok(cu)
        }
        (Zl::Primitive(op1, rargs1, kargs1), Zl::Primitive(op2, rargs2, kargs2)) => {
            if !eq(EQ_PRIM, op1, op2) {
                return nc();
            }
            if rargs1.len() != rargs2.len() || kargs1.len() != kargs2.len() {
                panic!("Invalid_argument");
            }
            let mut items: Vec<Item> = vec![];
            for j in (0..rargs1.len()).rev() {
                items.push(lf_item(&infos, &rargs1[j], &rargs2[j]));
            }
            for j in (0..kargs1.len()).rev() {
                items.push(lf_item(&infos, &kargs1[j].1, &kargs2[j].1));
            }
            w.push_seq(items);
            Ok(cuniv)
        }
        _ => panic!("assert false"),
    }
}

fn convert_vect(infos: &CInfos, lft1: &Lift, lft2: &Lift, v1: &[FC], v2: &[FC]) -> R<Vec<Item>> {
    if v1.len() == v2.len() {
        Ok((0..v1.len()).map(|i| ccnv_item(CONV, infos, lft1, lft2, &v1[i], &v2[i])).collect())
    } else {
        nc()
    }
}

#[allow(clippy::too_many_arguments)]
fn convert_under_context(
    infos: &CInfos,
    e1: &USubs,
    e2: &USubs,
    lft1: &Lift,
    lft2: &Lift,
    ctx: Option<(OVal, USubs, USubs)>,
    b1: &OVal,
    b2: &OVal,
) -> Item {
    let (nas1, c1) = (b1.field(0), b1.field(1));
    let (nas2, c2) = (b2.field(0), b2.field(1));
    let n = nas1.size() as isize;
    assert!(n == nas2.size() as isize);
    let (nas, n, e1, e2): (Vec<OVal>, isize, USubs, USubs) = match ctx {
        None => (nas1.array_to_vec(), n, usubs_liftn(n, e1), usubs_liftn(n, e2)),
        Some((ctx, args1, args2)) => {
            let mut keep: Vec<bool> = ctx.list_to_vec().iter().map(|d| d.as_option().is_none()).collect();
            keep.reverse();
            let all = nas1.array_to_vec();
            assert!(keep.len() == all.len());
            let nas: Vec<OVal> = all.into_iter().zip(keep).filter(|(_, k)| *k).map(|(x, _)| x).collect();
            let (n1, e1) = esubst_of_context(&ctx, &args1, e1);
            let (n2, e2) = esubst_of_context(&ctx, &args2, e2);
            assert!(n1 == n2);
            assert!(n1 == nas.len() as isize);
            (nas, n1, e1, e2)
        }
    };
    let lft1 = el_liftn(n, lft1);
    let lft2 = el_liftn(n, lft2);
    let nas: Vec<OVal> = nas.iter().map(|na| usubst_binder(&e1, na)).collect();
    let infos = infos.push_relevances(&nas);
    ccnv_item(CONV, &infos, &lft1, &lft2, &mk_clos(&e1, &c1), &mk_clos(&e2, &c2))
}

#[allow(clippy::too_many_arguments)]
fn convert_return_clause(
    infos: &CInfos,
    ind: &OVal,
    e1: &USubs,
    e2: &USubs,
    l1: &Lift,
    l2: &Lift,
    u1: &OVal,
    u2: &OVal,
    pms1: &[FC],
    pms2: &[FC],
    p1: &OVal,
    p2: &OVal,
) -> Item {
    let letctx = call(&ARITY_LETCTX, &[A::O(infos.env()), A::O(ind)]);
    let ctx = match letctx.as_option() {
        None => None,
        Some(ctx) => {
            let params = mind_params(&infos.inf, ind);
            let s1 = inductive_subst(&params, u1, pms1);
            let s2 = inductive_subst(&params, u2, pms2);
            Some((ctx, s1, s2))
        }
    };
    convert_under_context(infos, e1, e2, l1, l2, ctx, &p1.field(0), &p2.field(0))
}

/// The branches are converted from the last one to the first one.
#[allow(clippy::too_many_arguments)]
fn convert_branches(
    infos: &CInfos,
    ind: &OVal,
    e1: &USubs,
    e2: &USubs,
    lft1: &Lift,
    lft2: &Lift,
    u1: &OVal,
    u2: &OVal,
    pms1: &[FC],
    pms2: &[FC],
    br1: &OVal,
    br2: &OVal,
) -> Vec<Item> {
    let n = call(&IND_NCONSTRUCTORS, &[A::O(infos.env()), A::O(ind)]).as_int();
    let mut items = vec![];
    for i in (0..n).rev() {
        let letctx = call(&CTOR_LETCTX, &[A::O(infos.env()), A::O(ind), A::I(i)]);
        let ctx = match letctx.as_option() {
            None => None,
            Some(ctx) => {
                let params = mind_params(&infos.inf, ind);
                let s1 = inductive_subst(&params, u1, pms1);
                let s2 = inductive_subst(&params, u2, pms2);
                Some((ctx, s1, s2))
            }
        };
        let c1 = br1.field(i as usize);
        let c2 = br2.field(i as usize);
        items.push(convert_under_context(infos, e1, e2, lft1, lft2, ctx, &c1, &c2));
    }
    items
}

/// [convert_list]: the common prefix is converted before failing on a
/// length mismatch.
fn convert_list(infos: &CInfos, lft1: &Lift, lft2: &Lift, v1: &[FC], v2: &[FC]) -> Vec<Item> {
    let n = std::cmp::min(v1.len(), v2.len());
    let mut items: Vec<Item> = (0..n).map(|i| ccnv_item(CONV, infos, lft1, lft2, &v1[i], &v2[i])).collect();
    if v1.len() != v2.len() {
        items.push(Item::Fail);
    }
    items
}

/// The conversion function used by [case_inversion].
pub fn conv_inner(info: &Infos, tab: &Tab, a: &FC, b: &FC) -> bool {
    let state = info.cache.univs.clone();
    let check = call(&CHECKED_UNIVERSES, &[A::O(&info.cache.evars)]);
    let ci = CInfos::new(info.clone(), Rc::new(ConvShared { typ: true, lft_tab: tab.clone(), rgt_tab: tab.clone(), check }));
    match ccnv(CONV, false, &ci, &el_id(), &el_id(), a, b, state) {
        Ok(_) => true,
        Err(NC::Plain) => false,
        Err(NC::Trace(_)) => panic!("assert false"),
    }
}
