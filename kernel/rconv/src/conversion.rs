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

#[derive(Clone)]
pub struct CInfos {
    pub inf: Infos,
    pub typ: bool,
    pub lft_tab: Tab,
    pub rgt_tab: Tab,
    pub check: OVal,
}

impl CInfos {
    fn push_relevance(&self, na: &OVal) -> CInfos {
        CInfos { inf: self.inf.push_relevance(na), ..self.clone() }
    }
    fn push_relevances(&self, nas: &[OVal]) -> CInfos {
        CInfos { inf: self.inf.push_relevances(nas), ..self.clone() }
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

fn compare_stack_shape(s1: &Stack, s2: &Stack) -> bool {
    let mut bal: isize = 0;
    let mut a = s1.clone();
    let mut b = s2.clone();
    loop {
        let za = a.uncons().map(|(z, t)| (z.clone(), t.clone()));
        let zb = b.uncons().map(|(z, t)| (z.clone(), t.clone()));
        match (za, zb) {
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
                if bal != 0 || !compare_stack_shape(&a1, &a2) {
                    return false;
                }
                a = t1;
                b = t2;
            }
            (Some((Z::Primitive(op1, _, _, rargs1, _), t1)), Some((Z::Primitive(op2, _, _, rargs2, _), t2))) => {
                if !(bal == 0 && eq(EQ_PRIM, &op1, &op2) && rargs1.len() == rargs2.len()) {
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

enum Zl {
    App(Vec<LF>),
    Proj(OVal),
    Fix(LF, Vec<Zl>),
    Case(Rc<CaseData>, Lift),
    Primitive(OVal, Vec<LF>, Vec<(isize, LF)>),
}

/// Returns the pure stack, top first.
fn pure_rec(lfts: &Lift, stk: &Stack) -> (Lift, Vec<Zl>) {
    let elems = stk.to_vec();
    let mut l = lfts.clone();
    let mut out: Vec<Zl> = vec![];
    for z in elems.iter().rev() {
        match z {
            Z::Update(_) => (),
            Z::Shift(n) => l = el_shft(*n, &l),
            Z::App(a) => {
                assert!(!a.is_empty());
                let items: Vec<LF> = a.iter().map(|t| (l.clone(), t.clone())).collect();
                if let Some(Zl::App(v2)) = out.last_mut() {
                    let mut items = items;
                    items.append(v2);
                    *v2 = items;
                } else {
                    out.push(Zl::App(items));
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

fn pure_stack(lfts: &Lift, stk: &Stack) -> Vec<Zl> {
    pure_rec(lfts, stk).1
}

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
    call(&COMPARE_SORTS, &[A::O(&infos.check), A::I(pb), A::O(s0), A::O(s1), A::O(cuniv)])
}

fn convert_instances(infos: &CInfos, flex: bool, u: &OVal, u2: &OVal, cuniv: &OVal) -> OVal {
    call(&COMPARE_INSTANCES, &[A::O(&infos.check), A::B(flex), A::O(u), A::O(u2), A::O(cuniv)])
}

fn convert_instances_cumul(infos: &CInfos, pb: isize, var: &OVal, u: &OVal, u2: &OVal, cuniv: &OVal) -> OVal {
    call(&COMPARE_CUMUL_INSTANCES, &[A::O(&infos.check), A::I(pb), A::O(var), A::O(u), A::O(u2), A::O(cuniv)])
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

fn conv_table_key(infos: &CInfos, nargs: isize, k1: &TableKey, k2: &TableKey, cuniv: OVal) -> R<OVal> {
    match (k1, k2) {
        (TableKey::Const(cst, u), TableKey::Const(cst2, u2)) if eq(EQ_CONSTANT_CAN, cst, cst2) => {
            if instance_equal(&u.v, &u2.v) {
                Ok(cuniv)
            } else if nargs == 1 && call(&IS_ARRAY_TYPE, &[A::O(infos.env()), A::O(cst)]).as_bool() {
                Ok(cuniv)
            } else {
                let flex = call(&CONV_FLEX, &[A::O(infos.env()), A::O(&infos.inf.flags.v), A::O(cst)]).as_bool();
                fail_check(convert_instances(infos, flex, &u.v, &u2.v, &cuniv))
            }
        }
        (TableKey::Var(id), TableKey::Var(id2)) if eq(EQ_ID, id, id2) => Ok(cuniv),
        (TableKey::Rel(n), TableKey::Rel(n2)) if n == n2 => Ok(cuniv),
        _ => nc(),
    }
}

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

fn irr_flex(infos: &Infos, fl: &TableKey) -> bool {
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

fn fast_test(lft1: &Lift, term1: &FC, lft2: &Lift, term2: &FC) -> bool {
    let mut lft1 = lft1.clone();
    let mut lft2 = lft2.clone();
    let mut term1 = term1.clone();
    let mut term2 = term2.clone();
    loop {
        let t1 = term1.term();
        let t2 = term2.term();
        match (&*t1, &*t2) {
            (FTerm::Lift(i, a), FTerm::Lift(..)) | (FTerm::Lift(i, a), FTerm::Clos(..)) => {
                lft1 = el_shft(*i, &lft1);
                term1 = a.clone();
            }
            (FTerm::Clos(..), FTerm::Lift(j, b)) => {
                lft2 = el_shft(*j, &lft2);
                term2 = b.clone();
            }
            (FTerm::Clos(c1, e1), FTerm::Clos(c2, e2)) => return eq_lift(&lft1, &lft2) && compare_under(e1, c1, e2, c2),
            _ => return false,
        }
    }
}

fn assert_reduced_constructor(s: &Stack) {
    if !s.is_nil() {
        anomaly(AN_CTOR_UNREDUCED);
    }
}

pub fn ccnv(cv_pb: isize, l2r: bool, infos: &CInfos, lft1: &Lift, lft2: &Lift, term1: &FC, term2: &FC, cuniv: OVal) -> R<OVal> {
    if fast_test(lft1, term1, lft2, term2) {
        return Ok(cuniv);
    }
    conv_loop(cv_pb, l2r, infos, lft1, lft2, term1, term2, cuniv)
}

#[derive(Clone)]
struct Side {
    lft: Lift,
    hd: FC,
    stk: Stack,
}

fn side(lft: &Lift, hd: &FC, stk: &Stack) -> Side {
    Side { lft: lft.clone(), hd: hd.clone(), stk: stk.clone() }
}

/// Arguments of the pending [eqappr] / [eqwhnf] call, updated in place.
struct ConvState {
    cv_pb: isize,
    infos: CInfos,
    a1: Side,
    a2: Side,
}

/// What to do next with the updated [ConvState]:
/// return, tail-call [eqappr], or tail-call [eqwhnf].
enum Step {
    Done(OVal),
    Appr(OVal),
    Whnf(OVal),
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn conv_loop(cv_pb: isize, l2r: bool, infos: &CInfos, lft1: &Lift, lft2: &Lift, term1: &FC, term2: &FC, cuniv: OVal) -> R<OVal> {
    let mut st = ConvState {
        cv_pb,
        infos: infos.clone(),
        a1: side(lft1, term1, &Stack::nil()),
        a2: side(lft2, term2, &Stack::nil()),
    };
    let mut cuniv = cuniv;
    let mut appr = true;
    loop {
        if appr {
            whd_both(&mut st);
        }
        match eqwhnf(l2r, &mut st, cuniv)? {
            Step::Done(c) => return Ok(c),
            Step::Appr(c) => {
                cuniv = c;
                appr = true;
            }
            Step::Whnf(c) => {
                cuniv = c;
                appr = false;
            }
        }
    }
}

/// The head-reduction part of [eqappr].
#[inline(never)]
fn whd_both(st: &mut ConvState) {
    call(&CHECK_FOR_INTERRUPT, &[A::I(0)]);
    let ninfos = st.infos.inf.with_reds(&st.infos.inf.cache.betaiotazeta);
    let (h1, v1) = whd_stack(&ninfos, &st.infos.lft_tab, &st.a1.hd, &st.a1.stk);
    let (h2, v2) = whd_stack(&ninfos, &st.infos.rgt_tab, &st.a2.hd, &st.a2.stk);
    st.a1.hd = h1;
    st.a1.stk = v1;
    st.a2.hd = h2;
    st.a2.stk = v2;
}

fn all_transparent(infos: &Infos) -> Infos {
    let f = call(&ALL_TRANSPARENT, &[A::O(&infos.flags.v)]);
    infos.with_reds(&Flags::new(f))
}

fn rel_relevance(infos: &Infos, n: isize) -> OVal {
    infos.relevances.get(n - 1)
}

fn stacks(l2r: bool, st: &ConvState, cuniv: OVal) -> R<Step> {
    let (a1, a2) = (&st.a1, &st.a2);
    Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &a1.lft, &a2.lft, &a1.stk, &a2.stk, cuniv)?))
}

/// [eqwhnf]: dispatch on the heads, each case is handled out of line so that
/// the recursive path only pays for the frame of the case it takes.
fn eqwhnf(l2r: bool, st: &mut ConvState, cuniv: OVal) -> R<Step> {
    let t1 = st.a1.hd.term();
    let t2 = st.a2.hd.term();
    match (&*t1, &*t2) {
        (FTerm::Atom(a1), FTerm::Atom(a2)) => eq_atom(l2r, st, a1, a2, cuniv),
        (FTerm::Evar(ev1, args1, env1), FTerm::Evar(ev2, args2, env2)) => eq_evar(l2r, st, ev1, args1, env1, ev2, args2, env2, cuniv),
        (FTerm::Rel(n), FTerm::Rel(m)) => eq_rel(l2r, st, *n, *m, cuniv),
        (FTerm::Flex(fl1), FTerm::Flex(fl2)) => eq_flex_flex(l2r, st, fl1, fl2, cuniv),
        (FTerm::Proj(p1, r1, c1), FTerm::Proj(p2, r2, c2)) => eq_proj_proj(l2r, st, p1, r1, c1, p2, r2, c2, cuniv),
        (FTerm::Proj(p1, r1, c1), t2) => eq_proj_left(st, p1, r1, c1, t2, cuniv),
        (t1, FTerm::Proj(p2, r2, c2)) => eq_proj_right(st, t1, p2, r2, c2, cuniv),
        (FTerm::Lambda(..), FTerm::Lambda(..)) => eq_lambda_lambda(l2r, st, cuniv),
        (FTerm::Prod(x1, c1, c2, e), FTerm::Prod(_, c12, c22, e2)) => eq_prod_prod(l2r, st, x1, c1, c2, e, c12, c22, e2, cuniv),
        (FTerm::Lambda(..), _) => eq_eta_left(st, cuniv),
        (_, FTerm::Lambda(..)) => eq_eta_right(st, cuniv),
        (FTerm::Flex(fl1), c2) => eq_flex_left(l2r, st, fl1, c2, cuniv),
        (c1, FTerm::Flex(fl2)) => eq_flex_right(l2r, st, c1, fl2, cuniv),
        (FTerm::Ind(ind1, u1), FTerm::Ind(ind2, u2)) => eq_ind(l2r, st, ind1, u1, ind2, u2, cuniv),
        (FTerm::Construct(c1, u1, args1), FTerm::Construct(c2, u2, args2)) => eq_construct(l2r, st, c1, u1, args1, c2, u2, args2, cuniv),
        (FTerm::Construct(c1, u1, args1), _) => eq_record_left(l2r, st, c1, u1, args1, cuniv),
        (_, FTerm::Construct(c2, u2, args2)) => eq_record_right(l2r, st, c2, u2, args2, cuniv),
        (FTerm::Fix(f1, e1), FTerm::Fix(f2, e2)) => {
            let (op1, op2) = (&f1.ri, &f2.ri);
            let same_op = op1.size() == op2.size() && (0..op1.size()).all(|i| op1.field_int(i) == op2.field_int(i));
            if f1.i == f2.i && same_op {
                Ok(Step::Done(convert_fix(l2r, &st.infos, &st.a1, &st.a2, f1, e1, f2, e2, cuniv)?))
            } else {
                nc()
            }
        }
        (FTerm::CoFix(f1, e1), FTerm::CoFix(f2, e2)) => {
            if f1.i == f2.i {
                Ok(Step::Done(convert_fix(l2r, &st.infos, &st.a1, &st.a2, f1, e1, f2, e2, cuniv)?))
            } else {
                nc()
            }
        }
        (FTerm::Int(i1), FTerm::Int(i2)) => eq_prim_value(l2r, st, EQ_UINT63, i1, i2, cuniv),
        (FTerm::Float(f1), FTerm::Float(f2)) => eq_prim_value(l2r, st, EQ_FLOAT64, f1, f2, cuniv),
        (FTerm::String(s1), FTerm::String(s2)) => eq_prim_value(l2r, st, EQ_PSTRING, s1, s2, cuniv),
        (FTerm::CaseInvert(cd1, iv1, _), FTerm::CaseInvert(cd2, iv2, _)) => eq_case_invert(l2r, st, cd1, iv1, cd2, iv2, cuniv),
        (FTerm::Array(u1, t1, ty1, alft1), FTerm::Array(u2, t2, ty2, alft2)) => eq_array(l2r, st, u1, t1, ty1, *alft1, u2, t2, ty2, *alft2, cuniv),
        (FTerm::Rel(n1), FTerm::Irrelevant) => eq_rel_irr(l2r, st, *n1, true, cuniv),
        (FTerm::Irrelevant, FTerm::Rel(n2)) => eq_rel_irr(l2r, st, *n2, false, cuniv),
        (FTerm::Irrelevant, FTerm::Irrelevant) => stacks(l2r, st, cuniv),
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
        _ => nc(),
    }
}

#[inline(never)]
fn eq_atom(l2r: bool, st: &mut ConvState, a1: &OVal, a2: &OVal, cuniv: OVal) -> R<Step> {
    let k1 = constr::kind(a1);
    let k2 = constr::kind(a2);
    if k1 == constr::SORT && k2 == constr::SORT {
        if !(is_empty_stack(&st.a1.stk) && is_empty_stack(&st.a2.stk)) {
            return nc();
        }
        Ok(Step::Done(fail_check(sort_cmp_universes(&st.infos, st.cv_pb, &a1.field(0), &a2.field(0), &cuniv))?))
    } else if k1 == constr::META && k2 == constr::META {
        if a1.field_int(0) == a2.field_int(0) {
            stacks(l2r, st, cuniv)
        } else {
            nc()
        }
    } else {
        nc()
    }
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn eq_evar(l2r: bool, st: &mut ConvState, ev1: &OVal, args1: &OVal, env1: &USubs, ev2: &OVal, args2: &OVal, env2: &USubs, cuniv: OVal) -> R<Step> {
    if eq(EQ_EVAR, ev1, ev2) {
        let infos = &st.infos;
        let el1 = el_stack(&st.a1.lft, &st.a1.stk);
        let el2 = el_stack(&st.a2.lft, &st.a2.stk);
        let cuniv = convert_stacks(None, l2r, infos, &st.a1.lft, &st.a2.lft, &st.a1.stk, &st.a2.stk, cuniv)?;
        let a1: Vec<FC> = args1.list_to_vec().iter().map(|a| mk_clos(env1, a)).collect();
        let a2: Vec<FC> = args2.list_to_vec().iter().map(|a| mk_clos(env2, a)).collect();
        Ok(Step::Done(convert_list(l2r, infos, &el1, &el2, &a1, &a2, cuniv)?))
    } else {
        nc()
    }
}

#[inline(never)]
fn eq_rel(l2r: bool, st: &mut ConvState, n: isize, m: isize, cuniv: OVal) -> R<Step> {
    let el1 = el_stack(&st.a1.lft, &st.a1.stk);
    let el2 = el_stack(&st.a2.lft, &st.a2.stk);
    let n = reloc_rel(n, &el1);
    let m = reloc_rel(m, &el2);
    let inf = &st.infos.inf;
    let rn = rel_relevance(inf, n);
    let rm = rel_relevance(inf, m);
    if is_irrelevant(inf, &rn) && is_irrelevant(inf, &rm) {
        let v1 = skip_irrelevant_stack(inf, &st.a1.stk);
        let v2 = skip_irrelevant_stack(inf, &st.a2.stk);
        Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, &v1, &v2, cuniv)?))
    } else if n == m {
        stacks(l2r, st, cuniv)
    } else {
        nc()
    }
}

#[inline(never)]
fn eq_flex_flex(l2r: bool, st: &mut ConvState, fl1: &TableKey, fl2: &TableKey, cuniv: OVal) -> R<Step> {
    let attempt = (|| -> R<OVal> {
        let infos = &st.infos;
        let nargs = same_args_size(&st.a1.stk, &st.a2.stk)?;
        let cuniv = conv_table_key(infos, nargs, fl1, fl2, cuniv.clone())?;
        if irr_flex(&infos.inf, fl1) {
            return nc();
        }
        let mask = if infos.typ {
            match fl1 {
                TableKey::Const(..) => get_ref_mask(&infos.inf, &infos.lft_tab, fl1),
                _ => None,
            }
        } else {
            None
        };
        convert_stacks(mask, l2r, infos, &st.a1.lft, &st.a2.lft, &st.a1.stk, &st.a2.stk, cuniv)
    })();
    if let Ok(c) = attempt {
        return Ok(Step::Done(c));
    }
    let r1 = unfold_ref_with_args(&st.infos.inf, &st.infos.lft_tab, fl1, &st.a1.stk);
    let r2 = unfold_ref_with_args(&st.infos.inf, &st.infos.rgt_tab, fl2, &st.a2.stk);
    match (r1, r2) {
        (None, None) => nc(),
        (Some((t1, v1)), Some((t2, v2))) => {
            let ninfos = st.infos.inf.with_reds(&st.infos.inf.cache.betaiotazeta);
            call(&CHECK_FOR_INTERRUPT, &[A::I(0)]);
            let ta = key_args(fl1);
            let tb = key_args(fl2);
            let unfold_left = call(
                &UNFOLD_LEFT,
                &[A::O(st.infos.env()), A::I(ta.0), A::O(&ta.1), A::I(tb.0), A::O(&tb.1), A::B(l2r)],
            )
            .as_bool();
            if unfold_left {
                let (h, s) = whd_stack(&ninfos, &st.infos.lft_tab, &t1, &v1);
                st.a1.hd = h;
                st.a1.stk = s;
            } else {
                let (h, s) = whd_stack(&ninfos, &st.infos.rgt_tab, &t2, &v2);
                st.a2.hd = h;
                st.a2.stk = s;
            }
            Ok(Step::Whnf(cuniv))
        }
        (Some((t1, v1)), None) => {
            let all = all_transparent(&st.infos.inf);
            let (h, s) = whd_stack(&all, &st.infos.lft_tab, &t1, &v1);
            st.a1.hd = h;
            st.a1.stk = s;
            Ok(Step::Whnf(cuniv))
        }
        (None, Some((t2, v2))) => {
            let all = all_transparent(&st.infos.inf);
            let (h, s) = whd_stack(&all, &st.infos.rgt_tab, &t2, &v2);
            st.a2.hd = h;
            st.a2.stk = s;
            Ok(Step::Whnf(cuniv))
        }
    }
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn eq_proj_proj(l2r: bool, st: &mut ConvState, p1: &OVal, r1: &OVal, c1: &FC, p2: &OVal, r2: &OVal, c2: &FC, cuniv: OVal) -> R<Step> {
    match unfold_projection(&st.infos.inf, p1, r1) {
        Some(s1) => {
            st.a1.stk = st.a1.stk.cons(s1);
            st.a1.hd = c1.clone();
            Ok(Step::Appr(cuniv))
        }
        None => match unfold_projection(&st.infos.inf, p2, r2) {
            Some(s2) => {
                st.a2.stk = st.a2.stk.cons(s2);
                st.a2.hd = c2.clone();
                Ok(Step::Appr(cuniv))
            }
            None => {
                let (v1, v2) = (&st.a1.stk, &st.a2.stk);
                if eq(EQ_PROJ_REPR_CAN, &p1.field(0), &p2.field(0)) && compare_stack_shape(v1, v2) {
                    let el1 = el_stack(&st.a1.lft, v1);
                    let el2 = el_stack(&st.a2.lft, v2);
                    let u1 = ccnv(CONV, l2r, &st.infos, &el1, &el2, c1, c2, cuniv)?;
                    stacks(l2r, st, u1)
                } else {
                    nc()
                }
            }
        },
    }
}

#[inline(never)]
fn eq_proj_left(st: &mut ConvState, p1: &OVal, r1: &OVal, c1: &FC, t2: &FTerm, cuniv: OVal) -> R<Step> {
    match unfold_projection(&st.infos.inf, p1, r1) {
        Some(s1) => {
            st.a1.stk = st.a1.stk.cons(s1);
            st.a1.hd = c1.clone();
            Ok(Step::Appr(cuniv))
        }
        None => match t2 {
            FTerm::Flex(fl2) => match unfold_ref_with_args(&st.infos.inf, &st.infos.rgt_tab, fl2, &st.a2.stk) {
                Some((h, s)) => {
                    st.a2.hd = h;
                    st.a2.stk = s;
                    Ok(Step::Appr(cuniv))
                }
                None => nc(),
            },
            _ => nc(),
        },
    }
}

#[inline(never)]
fn eq_proj_right(st: &mut ConvState, t1: &FTerm, p2: &OVal, r2: &OVal, c2: &FC, cuniv: OVal) -> R<Step> {
    match unfold_projection(&st.infos.inf, p2, r2) {
        Some(s2) => {
            st.a2.stk = st.a2.stk.cons(s2);
            st.a2.hd = c2.clone();
            Ok(Step::Appr(cuniv))
        }
        None => match t1 {
            FTerm::Flex(fl1) => match unfold_ref_with_args(&st.infos.inf, &st.infos.lft_tab, fl1, &st.a1.stk) {
                Some((h, s)) => {
                    st.a1.hd = h;
                    st.a1.stk = s;
                    Ok(Step::Appr(cuniv))
                }
                None => nc(),
            },
            _ => nc(),
        },
    }
}

#[inline(never)]
fn eq_lambda_lambda(l2r: bool, st: &mut ConvState, cuniv: OVal) -> R<Step> {
    let (v1, v2) = (&st.a1.stk, &st.a2.stk);
    if !(is_empty_stack(v1) && is_empty_stack(v2)) {
        anomaly(AN_LAMBDA_ILLTYPED);
    }
    let (x1, ty1, bd1) = dest_flambda(&st.a1.hd);
    let (_, ty2, bd2) = dest_flambda(&st.a2.hd);
    let el1 = el_stack(&st.a1.lft, v1);
    let el2 = el_stack(&st.a2.lft, v2);
    let cuniv = ccnv(CONV, l2r, &st.infos, &el1, &el2, &ty1, &ty2, cuniv)?;
    Ok(Step::Done(ccnv(CONV, l2r, &st.infos.push_relevance(&x1), &el_lift(&el1), &el_lift(&el2), &bd1, &bd2, cuniv)?))
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn eq_prod_prod(l2r: bool, st: &mut ConvState, x1: &OVal, c1: &FC, c2: &OVal, e: &USubs, c12: &FC, c22: &OVal, e2: &USubs, cuniv: OVal) -> R<Step> {
    let (v1, v2) = (&st.a1.stk, &st.a2.stk);
    if !(is_empty_stack(v1) && is_empty_stack(v2)) {
        return nc();
    }
    let el1 = el_stack(&st.a1.lft, v1);
    let el2 = el_stack(&st.a2.lft, v2);
    let cuniv = ccnv(CONV, l2r, &st.infos, &el1, &el2, c1, c12, cuniv)?;
    let x1 = usubst_binder(e, x1);
    let b1 = mk_clos(&usubs_lift(e), c2);
    let b2 = mk_clos(&usubs_lift(e2), c22);
    Ok(Step::Done(ccnv(st.cv_pb, l2r, &st.infos.push_relevance(&x1), &el_lift(&el1), &el_lift(&el2), &b1, &b2, cuniv)?))
}

#[inline(never)]
fn eq_eta_left(st: &mut ConvState, cuniv: OVal) -> R<Step> {
    if !st.a1.stk.is_nil() {
        anomaly(AN_LAMBDA_UNREDUCED);
    }
    let (x1, _ty1, bd1) = dest_flambda(&st.a1.hd);
    st.infos = st.infos.push_relevance(&x1);
    let s2 = eta_expand_stack(&st.infos.inf, &x1, &st.a2.stk);
    st.cv_pb = CONV;
    st.a1 = Side { lft: el_lift(&st.a1.lft), hd: bd1, stk: Stack::nil() };
    st.a2.lft = el_lift(&st.a2.lft);
    st.a2.stk = s2;
    Ok(Step::Appr(cuniv))
}

#[inline(never)]
fn eq_eta_right(st: &mut ConvState, cuniv: OVal) -> R<Step> {
    if !st.a2.stk.is_nil() {
        anomaly(AN_LAMBDA_UNREDUCED);
    }
    let (x2, _ty2, bd2) = dest_flambda(&st.a2.hd);
    st.infos = st.infos.push_relevance(&x2);
    let s1 = eta_expand_stack(&st.infos.inf, &x2, &st.a1.stk);
    st.cv_pb = CONV;
    st.a1.lft = el_lift(&st.a1.lft);
    st.a1.stk = s1;
    st.a2 = Side { lft: el_lift(&st.a2.lft), hd: bd2, stk: Stack::nil() };
    Ok(Step::Appr(cuniv))
}

#[inline(never)]
fn eq_flex_left(l2r: bool, st: &mut ConvState, fl1: &TableKey, c2: &FTerm, cuniv: OVal) -> R<Step> {
    match unfold_ref_with_args(&st.infos.inf, &st.infos.lft_tab, fl1, &st.a1.stk) {
        Some((def1, v1)) => {
            let all = all_transparent(&st.infos.inf);
            let (h, s) = whd_stack(&all, &st.infos.lft_tab, &def1, &v1);
            st.a1.hd = h;
            st.a1.stk = s;
            Ok(Step::Whnf(cuniv))
        }
        None => match c2 {
            FTerm::Construct(c, u2, args2) if c.field_int(1) == 1 => {
                assert_reduced_constructor(&st.a2.stk);
                match eta_expand_ind_stack(&st.infos.inf, &c.field(0), u2, args2, &st.a1.hd, &st.a1.stk) {
                    Some((v2, v1)) => Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, &v1, &v2, cuniv)?)),
                    None => nc(),
                }
            }
            _ => nc(),
        },
    }
}

#[inline(never)]
fn eq_flex_right(l2r: bool, st: &mut ConvState, c1: &FTerm, fl2: &TableKey, cuniv: OVal) -> R<Step> {
    match unfold_ref_with_args(&st.infos.inf, &st.infos.rgt_tab, fl2, &st.a2.stk) {
        Some((def2, v2)) => {
            let all = all_transparent(&st.infos.inf);
            let (h, s) = whd_stack(&all, &st.infos.rgt_tab, &def2, &v2);
            st.a2.hd = h;
            st.a2.stk = s;
            Ok(Step::Whnf(cuniv))
        }
        None => match c1 {
            FTerm::Construct(c, u1, args1) if c.field_int(1) == 1 => {
                assert_reduced_constructor(&st.a1.stk);
                match eta_expand_ind_stack(&st.infos.inf, &c.field(0), u1, args1, &st.a2.hd, &st.a2.stk) {
                    Some((v1, v2)) => Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, &v1, &v2, cuniv)?)),
                    None => nc(),
                }
            }
            _ => nc(),
        },
    }
}

#[inline(never)]
fn eq_ind(l2r: bool, st: &mut ConvState, ind1: &OVal, u1: &UInst, ind2: &OVal, u2: &UInst, cuniv: OVal) -> R<Step> {
    if !eq(EQ_IND_CAN, ind1, ind2) {
        return nc();
    }
    if u1.empty || u2.empty {
        let cuniv = fail_check(convert_instances(&st.infos, false, &u1.v, &u2.v, &cuniv))?;
        return stacks(l2r, st, cuniv);
    }
    let nargs = same_args_size(&st.a1.stk, &st.a2.stk)?;
    match convert_inductives(&st.infos, st.cv_pb, ind1, nargs, &u1.v, &u2.v, &cuniv) {
        Ok(r) => {
            let cuniv = fail_check(r)?;
            stacks(l2r, st, cuniv)
        }
        Err(MustExpand) => {
            st.a1.hd = eta_expand_ind(&st.infos, ind1, u1);
            st.a2.hd = eta_expand_ind(&st.infos, ind2, u2);
            Ok(Step::Appr(cuniv))
        }
    }
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn eq_construct(l2r: bool, st: &mut ConvState, c1: &OVal, u1: &UInst, args1: &Rc<[FC]>, c2: &OVal, u2: &UInst, args2: &Rc<[FC]>, cuniv: OVal) -> R<Step> {
    assert_reduced_constructor(&st.a1.stk);
    assert_reduced_constructor(&st.a2.stk);
    let nargs = args1.len();
    if nargs != args2.len() {
        return nc();
    }
    let v1 = append_stack(args1, &st.a1.stk);
    let v2 = append_stack(args2, &st.a2.stk);
    if !(c1.field_int(1) == c2.field_int(1) && eq(EQ_IND_CAN, &c1.field(0), &c2.field(0))) {
        return nc();
    }
    if u1.empty || u2.empty {
        let cuniv = fail_check(convert_instances(&st.infos, false, &u1.v, &u2.v, &cuniv))?;
        return Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, &v1, &v2, cuniv)?));
    }
    match convert_constructors(&st.infos, c1, nargs as isize, &u1.v, &u2.v, &cuniv) {
        Ok(r) => {
            let cuniv = fail_check(r)?;
            Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, &v1, &v2, cuniv)?))
        }
        Err(MustExpand) => {
            st.a1.hd = eta_expand_constructor(&st.infos, c1, u1);
            st.a1.stk = v1;
            st.a2.hd = eta_expand_constructor(&st.infos, c2, u2);
            st.a2.stk = v2;
            Ok(Step::Appr(cuniv))
        }
    }
}

#[inline(never)]
fn eq_record_left(l2r: bool, st: &mut ConvState, c1: &OVal, u1: &UInst, args1: &Rc<[FC]>, cuniv: OVal) -> R<Step> {
    assert_reduced_constructor(&st.a1.stk);
    if c1.field_int(1) != 1 {
        return nc();
    }
    match eta_expand_ind_stack(&st.infos.inf, &c1.field(0), u1, args1, &st.a2.hd, &st.a2.stk) {
        Some((v1, v2)) => Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, &v1, &v2, cuniv)?)),
        None => nc(),
    }
}

#[inline(never)]
fn eq_record_right(l2r: bool, st: &mut ConvState, c2: &OVal, u2: &UInst, args2: &Rc<[FC]>, cuniv: OVal) -> R<Step> {
    assert_reduced_constructor(&st.a2.stk);
    if c2.field_int(1) != 1 {
        return nc();
    }
    match eta_expand_ind_stack(&st.infos.inf, &c2.field(0), u2, args2, &st.a1.hd, &st.a1.stk) {
        Some((v2, v1)) => Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, &v1, &v2, cuniv)?)),
        None => nc(),
    }
}

#[inline(never)]
fn eq_prim_value(l2r: bool, st: &mut ConvState, k: isize, x1: &OVal, x2: &OVal, cuniv: OVal) -> R<Step> {
    if eq(k, x1, x2) {
        stacks(l2r, st, cuniv)
    } else {
        nc()
    }
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn eq_case_invert(l2r: bool, st: &mut ConvState, cd1: &CaseData, iv1: &Rc<[FC]>, cd2: &CaseData, iv2: &Rc<[FC]>, cuniv: OVal) -> R<Step> {
    let infos = &st.infos;
    let ind = constr::ci_ind(&cd1.ci);
    if !eq(EQ_IND_CAN, &ind, &constr::ci_ind(&cd2.ci)) {
        return nc();
    }
    let el1 = el_stack(&st.a1.lft, &st.a1.stk);
    let el2 = el_stack(&st.a2.lft, &st.a2.stk);
    let (e1, e2) = (&cd1.e, &cd2.e);
    let u1 = usubst_instance(e1, &cd1.u);
    let u2 = usubst_instance(e2, &cd2.u);
    let cuniv = {
        let nargs = call(&IND_CUMUL_INFO, &[A::O(infos.env()), A::O(&ind)]).field_int(1);
        match convert_inductives(infos, CONV, &ind, nargs, &u1, &u2, &cuniv) {
            Ok(r) => fail_check(r)?,
            Err(MustExpand) => panic!("rconv: uncaught MustExpand"),
        }
    };
    let pms1 = mk_clos_vect(e1, &cd1.pms);
    let pms2 = mk_clos_vect(e2, &cd2.pms);
    let mut cuniv = cuniv;
    if pms1.len() != pms2.len() {
        panic!("Invalid_argument");
    }
    for i in (0..pms1.len()).rev() {
        cuniv = ccnv(CONV, l2r, infos, &el1, &el2, &pms1[i], &pms2[i], cuniv)?;
    }
    if iv1.len() != iv2.len() {
        panic!("Invalid_argument");
    }
    for i in (0..iv1.len()).rev() {
        cuniv = ccnv(CONV, l2r, infos, &el1, &el2, &iv1[i], &iv2[i], cuniv)?;
    }
    let cuniv = convert_return_clause(l2r, infos, &ind, e1, e2, &el1, &el2, &u1, &u2, &pms1, &pms2, &cd1.p, &cd2.p, cuniv)?;
    let cuniv = convert_branches(l2r, infos, &ind, e1, e2, &el1, &el2, &u1, &u2, &pms1, &pms2, &cd1.br, &cd2.br, cuniv)?;
    stacks(l2r, st, cuniv)
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn eq_array(l2r: bool, st: &mut ConvState, u1: &UInst, t1: &OVal, ty1: &FC, alft1: isize, u2: &UInst, t2: &OVal, ty2: &FC, alft2: isize, cuniv: OVal) -> R<Step> {
    let infos = &st.infos;
    let len = call(&PARRAY_LENGTH, &[A::O(t1)]).as_int();
    if len != call(&PARRAY_LENGTH, &[A::O(t2)]).as_int() {
        return nc();
    }
    let var = call(&ARRAY_VARIANCE, &[A::I(0)]);
    let cuniv = fail_check(convert_instances_cumul(infos, CONV, &var, &u1.v, &u2.v, &cuniv))?;
    let el1 = el_stack(&st.a1.lft, &st.a1.stk);
    let el2 = el_stack(&st.a2.lft, &st.a2.stk);
    let mut cuniv = ccnv(CONV, l2r, infos, &el1, &el2, &lift_fconstr(alft1, ty1), &lift_fconstr(alft2, ty2), cuniv)?;
    let r1 = call(&PARRAY_TO_ARRAY, &[A::O(t1)]);
    let r2 = call(&PARRAY_TO_ARRAY, &[A::O(t2)]);
    let (a1, a2) = (r1.field(0), r2.field(0));
    if a1.size() != a2.size() {
        panic!("Parray.fold_left2");
    }
    for i in 0..a1.size() {
        let x1 = crate::ffi::handle_to_fc(&a1.field(i));
        let x2 = crate::ffi::handle_to_fc(&a2.field(i));
        cuniv = ccnv(CONV, l2r, infos, &el1, &el2, &lift_fconstr(alft1, &x1), &lift_fconstr(alft2, &x2), cuniv)?;
    }
    let d1 = crate::ffi::handle_to_fc(&r1.field(1));
    let d2 = crate::ffi::handle_to_fc(&r2.field(1));
    let cuniv = ccnv(CONV, l2r, infos, &el1, &el2, &lift_fconstr(alft1, &d1), &lift_fconstr(alft2, &d2), cuniv)?;
    stacks(l2r, st, cuniv)
}

/// [(FRel n, FIrrelevant)] when [left], [(FIrrelevant, FRel n)] otherwise.
#[inline(never)]
fn eq_rel_irr(l2r: bool, st: &mut ConvState, n: isize, left: bool, cuniv: OVal) -> R<Step> {
    let s = if left { &st.a1 } else { &st.a2 };
    let n = reloc_rel(n, &el_stack(&s.lft, &s.stk));
    let inf = &st.infos.inf;
    let r = rel_relevance(inf, n);
    if !is_irrelevant(inf, &r) {
        return nc();
    }
    let v = skip_irrelevant_stack(inf, &s.stk);
    let (v1, v2) = if left { (&v, &st.a2.stk) } else { (&st.a1.stk, &v) };
    Ok(Step::Done(convert_stacks(None, l2r, &st.infos, &st.a1.lft, &st.a2.lft, v1, v2, cuniv)?))
}

#[allow(clippy::too_many_arguments)]
fn convert_fix(l2r: bool, infos: &CInfos, appr1: &Side, appr2: &Side, f1: &FixData, e1: &USubs, f2: &FixData, e2: &USubs, cuniv: OVal) -> R<OVal> {
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
    let cuniv = convert_vect(l2r, infos, &el1, &el2, &fty1, &fty2, cuniv)?;
    let cuniv = {
        let na1 = f1.names();
        let na1: Vec<OVal> = (0..na1.size()).map(|i| usubst_binder(e1, &na1.field(i))).collect();
        let infos = infos.push_relevances(&na1);
        convert_vect(l2r, &infos, &el_liftn(n, &el1), &el_liftn(n, &el2), &fcl1, &fcl2, cuniv)?
    };
    convert_stacks(None, l2r, infos, lft1, lft2, v1, v2, cuniv)
}

#[allow(clippy::too_many_arguments)]
fn convert_stacks(mask: Option<OVal>, l2r: bool, infos: &CInfos, lft1: &Lift, lft2: &Lift, stk1: &Stack, stk2: &Stack, cuniv: OVal) -> R<OVal> {
    if compare_stack_shape(stk1, stk2) {
        let mask = match mask {
            Some(m) if m.size() > 0 => Some(m),
            _ => None,
        };
        let nargs = if mask.is_none() { -1 } else { 0 };
        cmp_rec(&mask, l2r, infos, nargs, &pure_stack(lft1, stk1), &pure_stack(lft2, stk2), cuniv)
    } else {
        nc()
    }
}

fn f_lf(l2r: bool, infos: &CInfos, a: &LF, b: &LF, cu: OVal) -> R<OVal> {
    ccnv(CONV, l2r, infos, &a.0, &b.0, &a.1, &b.1, cu)
}

#[allow(clippy::too_many_arguments)]
fn cmp_rec(mask: &Option<OVal>, l2r: bool, infos: &CInfos, nargs: isize, p1: &[Zl], p2: &[Zl], cuniv: OVal) -> R<OVal> {
    let k = std::cmp::min(p1.len(), p2.len());
    let mut nargsv: Vec<isize> = Vec::with_capacity(k);
    let mut na = nargs;
    for z in p1.iter().take(k) {
        nargsv.push(na);
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
    let mut cu = cuniv;
    for i in (0..k).rev() {
        let nargs = nargsv[i];
        cu = match (&p1[i], &p2[i]) {
            (Zl::App(a1), Zl::App(a2)) => {
                if nargs < 0 {
                    if a1.len() != a2.len() {
                        panic!("Invalid_argument");
                    }
                    let mut cu = cu;
                    for j in (0..a1.len()).rev() {
                        cu = f_lf(l2r, infos, &a1[j], &a2[j], cu)?;
                    }
                    cu
                } else {
                    let m = mask.as_ref().unwrap();
                    let mlen = m.size() as isize;
                    let mut cu = cu;
                    for j in (0..a1.len()).rev() {
                        let idx = nargs + j as isize;
                        if idx < mlen && !m.field(idx as usize).as_bool() {
                            continue;
                        }
                        cu = f_lf(l2r, infos, &a1[j], &a2[j], cu)?;
                    }
                    cu
                }
            }
            (Zl::Proj(c1), Zl::Proj(c2)) => {
                if !eq(EQ_PROJ_REPR_CAN, c1, c2) {
                    return nc();
                }
                cu
            }
            (Zl::Fix(fx1, a1), Zl::Fix(fx2, a2)) => {
                let cu2 = f_lf(l2r, infos, fx1, fx2, cu)?;
                cmp_rec(mask, l2r, infos, -1, a1, a2, cu2)?
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
                    convert_instances(infos, false, &u1, &u2, &cu)
                } else {
                    let info = call(&IND_CUMUL_INFO, &[A::O(infos.env()), A::O(&ind)]);
                    match info.field(0).as_option() {
                        None => convert_instances(infos, false, &u1, &u2, &cu),
                        Some(variances) => convert_instances_cumul(infos, CONV, &variances, &u1, &u2, &cu),
                    }
                };
                let mut cu = fail_check(r)?;
                let pms1 = mk_clos_vect(e1, &cd1.pms);
                let pms2 = mk_clos_vect(e2, &cd2.pms);
                if pms1.len() != pms2.len() {
                    panic!("Invalid_argument");
                }
                for j in (0..pms1.len()).rev() {
                    cu = ccnv(CONV, l2r, infos, l1, l2, &pms1[j], &pms2[j], cu)?;
                }
                let cu = convert_return_clause(l2r, infos, &ind, e1, e2, l1, l2, &u1, &u2, &pms1, &pms2, &cd1.p, &cd2.p, cu)?;
                convert_branches(l2r, infos, &ind, e1, e2, l1, l2, &u1, &u2, &pms1, &pms2, &cd1.br, &cd2.br, cu)?
            }
            (Zl::Primitive(op1, rargs1, kargs1), Zl::Primitive(op2, rargs2, kargs2)) => {
                if !eq(EQ_PRIM, op1, op2) {
                    return nc();
                }
                if rargs1.len() != rargs2.len() || kargs1.len() != kargs2.len() {
                    panic!("Invalid_argument");
                }
                let mut cu = cu;
                for j in (0..rargs1.len()).rev() {
                    cu = f_lf(l2r, infos, &rargs1[j], &rargs2[j], cu)?;
                }
                for j in (0..kargs1.len()).rev() {
                    cu = f_lf(l2r, infos, &kargs1[j].1, &kargs2[j].1, cu)?;
                }
                cu
            }
            _ => panic!("assert false"),
        };
    }
    Ok(cu)
}

fn convert_vect(l2r: bool, infos: &CInfos, lft1: &Lift, lft2: &Lift, v1: &[FC], v2: &[FC], cuniv: OVal) -> R<OVal> {
    if v1.len() == v2.len() {
        let mut cu = cuniv;
        for i in 0..v1.len() {
            cu = ccnv(CONV, l2r, infos, lft1, lft2, &v1[i], &v2[i], cu)?;
        }
        Ok(cu)
    } else {
        nc()
    }
}

#[allow(clippy::too_many_arguments)]
fn convert_under_context(
    l2r: bool,
    infos: &CInfos,
    e1: &USubs,
    e2: &USubs,
    lft1: &Lift,
    lft2: &Lift,
    ctx: Option<(OVal, USubs, USubs)>,
    b1: &OVal,
    b2: &OVal,
    cu: OVal,
) -> R<OVal> {
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
    ccnv(CONV, l2r, &infos, &lft1, &lft2, &mk_clos(&e1, &c1), &mk_clos(&e2, &c2), cu)
}

#[allow(clippy::too_many_arguments)]
fn convert_return_clause(
    l2r: bool,
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
    cu: OVal,
) -> R<OVal> {
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
    convert_under_context(l2r, infos, e1, e2, l1, l2, ctx, &p1.field(0), &p2.field(0), cu)
}

#[allow(clippy::too_many_arguments)]
fn convert_branches(
    l2r: bool,
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
    cuniv: OVal,
) -> R<OVal> {
    let n = call(&IND_NCONSTRUCTORS, &[A::O(infos.env()), A::O(ind)]).as_int();
    let mut cu = cuniv;
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
        cu = convert_under_context(l2r, infos, e1, e2, lft1, lft2, ctx, &c1, &c2, cu)?;
    }
    Ok(cu)
}

fn convert_list(l2r: bool, infos: &CInfos, lft1: &Lift, lft2: &Lift, v1: &[FC], v2: &[FC], cuniv: OVal) -> R<OVal> {
    let mut cu = cuniv;
    let mut i = 0;
    loop {
        match (v1.get(i), v2.get(i)) {
            (None, None) => return Ok(cu),
            (Some(c1), Some(c2)) => {
                cu = ccnv(CONV, l2r, infos, lft1, lft2, c1, c2, cu)?;
                i += 1;
            }
            _ => return nc(),
        }
    }
}

/// The conversion function used by [case_inversion].
pub fn conv_inner(info: &Infos, tab: &Tab, a: &FC, b: &FC) -> bool {
    let state = info.cache.univs.clone();
    let check = call(&CHECKED_UNIVERSES, &[A::O(&info.cache.evars)]);
    let ci = CInfos { inf: info.clone(), typ: true, lft_tab: tab.clone(), rgt_tab: tab.clone(), check };
    match ccnv(CONV, false, &ci, &el_id(), &el_id(), a, b, state) {
        Ok(_) => true,
        Err(NC::Plain) => false,
        Err(NC::Trace(_)) => panic!("assert false"),
    }
}
