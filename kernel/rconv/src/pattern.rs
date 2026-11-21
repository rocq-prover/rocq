//! Port of the [RedPattern] submodule of kernel/cClosure.ml.

use std::rc::Rc;

use crate::cbs::*;
use crate::closure::*;
use crate::constr;
use crate::esubst::*;
use crate::ffi::{call, fc_to_handle, handle_to_fc, OVal, A};

#[derive(Clone)]
pub enum PArg {
    Hole(isize),
    HoleIgnored,
    Rigid(Rc<HeadElim>),
}

pub struct HeadElim {
    pub head: HeadPat,
    pub elims: EList,
}

pub enum HeadPat {
    Rel(isize),
    Sort(OVal),
    Symbol(OVal, OVal),
    Ind(OVal, OVal),
    Constr(OVal, OVal),
    Int(OVal),
    Float(OVal),
    String(OVal),
    Lambda(Rc<[PArg]>, Rc<HeadElim>),
    Prod(Rc<[PArg]>, PArg),
}

#[derive(Clone)]
pub enum Elim {
    App(Rc<[PArg]>),
    Case(OVal, PArg, Rc<[PArg]>),
    Proj(OVal),
}

pub struct ECons {
    pub hd: Elim,
    pub tl: EList,
}

pub type EList = Option<Rc<ECons>>;

fn econs(hd: Elim, tl: &EList) -> EList {
    Some(Rc::new(ECons { hd, tl: tl.clone() }))
}

pub struct Rule {
    pub nvars: OVal,
    pub mask: OVal,
    pub elims: EList,
    pub rhs: OVal,
}

fn parse_arg(v: &OVal) -> PArg {
    if v.is_long() {
        PArg::HoleIgnored
    } else if v.tag() == 0 {
        PArg::Hole(v.field_int(0))
    } else {
        PArg::Rigid(Rc::new(parse_head_elim(&v.field(0))))
    }
}

fn parse_args(v: &OVal) -> Rc<[PArg]> {
    v.array_to_vec().iter().map(parse_arg).collect()
}

fn parse_head_elim(v: &OVal) -> HeadElim {
    HeadElim { head: parse_head(&v.field(0)), elims: parse_elims(&v.field(1)) }
}

fn parse_head(v: &OVal) -> HeadPat {
    match v.tag() {
        0 => HeadPat::Rel(v.field_int(0)),
        1 => HeadPat::Sort(v.field(0)),
        2 => HeadPat::Symbol(v.field(0), v.field(1)),
        3 => HeadPat::Ind(v.field(0), v.field(1)),
        4 => HeadPat::Constr(v.field(0), v.field(1)),
        5 => HeadPat::Int(v.field(0)),
        6 => HeadPat::Float(v.field(0)),
        7 => HeadPat::String(v.field(0)),
        8 => HeadPat::Lambda(parse_args(&v.field(0)), Rc::new(parse_head_elim(&v.field(1)))),
        9 => HeadPat::Prod(parse_args(&v.field(0)), parse_arg(&v.field(1))),
        _ => panic!("unknown head pattern"),
    }
}

fn parse_elim(v: &OVal) -> Elim {
    match v.tag() {
        0 => Elim::App(parse_args(&v.field(0))),
        1 => Elim::Case(v.field(0), parse_arg(&v.field(1)), parse_args(&v.field(2))),
        2 => Elim::Proj(v.field(0)),
        _ => panic!("unknown pattern elimination"),
    }
}

fn parse_elims(l: &OVal) -> EList {
    let v = l.list_to_vec();
    let mut res: EList = None;
    for e in v.iter().rev() {
        res = econs(parse_elim(e), &res);
    }
    res
}

pub fn parse_rules(l: &OVal) -> Vec<Rule> {
    l.list_to_vec()
        .iter()
        .map(|r| {
            let lhs = r.field(1);
            Rule { nvars: r.field(0), mask: lhs.field(0), elims: parse_elims(&lhs.field(1)), rhs: r.field(2) }
        })
        .collect()
}

#[derive(Clone)]
pub struct PSubst {
    pub subst: OVal,
    pub rhs: OVal,
}

type States = Vec<Option<PSubst>>;

pub enum Loc {
    Start { elims: Vec<Option<EList>>, depth: isize, head: FC, stack: Stack, next: Next },
    Arg { patterns: Vec<Option<PArg>>, depth: isize, arg: FC, next: Rc<Loc> },
}

#[derive(Clone)]
pub enum Next {
    Continue(Rc<Loc>),
    Return(bool, FC, Stack),
}

pub struct Resume {
    pub states: States,
    pub depth: isize,
    pub patterns: Vec<Option<Rc<HeadElim>>>,
    pub next: Rc<Loc>,
}

#[derive(Clone)]
pub enum PS {
    /// [Nil No] or [Nil Yes]
    Nil(bool),
    Cons(Rc<Resume>, Rc<PS>),
}

fn extract_or_kill<E>(mut f: impl FnMut(&E, &PSubst) -> Option<PSubst>, a: &[Option<E>], st: &States) -> States {
    assert!(a.len() == st.len());
    a.iter()
        .zip(st.iter())
        .map(|(e, s)| match (e, s) {
            (None, s) => s.clone(),
            (_, None) => None,
            (Some(e), Some(s)) => f(e, s),
        })
        .collect()
}

fn extract_or_kill2<E, P>(mut f: impl FnMut(&E, &PSubst) -> Option<(P, PSubst)>, a: &[Option<E>], st: &States) -> (Vec<Option<P>>, States) {
    assert!(a.len() == st.len());
    let mut r1 = vec![];
    let mut r2 = vec![];
    for (e, s) in a.iter().zip(st.iter()) {
        match (e, s) {
            (None, s) => {
                r1.push(None);
                r2.push(s.clone())
            }
            (_, None) => {
                r1.push(None);
                r2.push(None)
            }
            (Some(e), Some(s)) => match f(e, s) {
                None => {
                    r1.push(None);
                    r2.push(None)
                }
                Some((p, s)) => {
                    r1.push(Some(p));
                    r2.push(Some(s))
                }
            },
        }
    }
    (r1, r2)
}

type Kill3<P1, P2> = (Vec<Option<P1>>, Vec<Option<P2>>, States);

fn extract_or_kill3<E, P1, P2>(mut f: impl FnMut(&E, &PSubst) -> Option<(P1, P2, PSubst)>, a: &[Option<E>], st: &States) -> Kill3<P1, P2> {
    assert!(a.len() == st.len());
    let (mut r1, mut r2, mut r3) = (vec![], vec![], vec![]);
    for (e, s) in a.iter().zip(st.iter()) {
        match (e, s) {
            (None, s) => {
                r1.push(None);
                r2.push(None);
                r3.push(s.clone())
            }
            (_, None) => {
                r1.push(None);
                r2.push(None);
                r3.push(None)
            }
            (Some(e), Some(s)) => match f(e, s) {
                None => {
                    r1.push(None);
                    r2.push(None);
                    r3.push(None)
                }
                Some((p1, p2, s)) => {
                    r1.push(Some(p1));
                    r2.push(Some(p2));
                    r3.push(Some(s))
                }
            },
        }
    }
    (r1, r2, r3)
}

type Kill4<P1, P2, P3> = (Vec<Option<P1>>, Vec<Option<P2>>, Vec<Option<P3>>, States);

fn extract_or_kill4<E, P1, P2, P3>(mut f: impl FnMut(&E, &PSubst) -> Option<(P1, P2, P3, PSubst)>, a: &[Option<E>], st: &States) -> Kill4<P1, P2, P3> {
    assert!(a.len() == st.len());
    let (mut r1, mut r2, mut r3, mut r4) = (vec![], vec![], vec![], vec![]);
    for (e, s) in a.iter().zip(st.iter()) {
        match (e, s) {
            (None, s) => {
                r1.push(None);
                r2.push(None);
                r3.push(None);
                r4.push(s.clone())
            }
            (_, None) => {
                r1.push(None);
                r2.push(None);
                r3.push(None);
                r4.push(None)
            }
            (Some(e), Some(s)) => match f(e, s) {
                None => {
                    r1.push(None);
                    r2.push(None);
                    r3.push(None);
                    r4.push(None)
                }
                Some((p1, p2, p3, s)) => {
                    r1.push(Some(p1));
                    r2.push(Some(p2));
                    r3.push(Some(p3));
                    r4.push(Some(s))
                }
            },
        }
    }
    (r1, r2, r3, r4)
}

/// [Array.transpose (Array.map (Status.split_array n) a)]
fn transpose_split<T: Clone>(n: usize, a: &[Option<Rc<[T]>>]) -> Vec<Vec<Option<T>>> {
    for x in a.iter().flatten() {
        if x.len() != n {
            panic!("Status.split_array");
        }
    }
    (0..n).map(|j| a.iter().map(|x| x.as_ref().map(|v| v[j].clone())).collect()).collect()
}

fn all_dead(states: &States) -> bool {
    states.iter().all(|s| s.is_none())
}

fn match_main(info: &Infos, tab: &Tab, ps: PS, states: States, loc: &Rc<Loc>) -> St {
    if all_dead(&states) {
        return match_kill(info, tab, ps, loc);
    }
    match &**loc {
        Loc::Start { elims, depth, head, stack, next: next @ Next::Return(..) } => {
            let found = states.iter().zip(elims.iter()).find_map(|(s, e)| match (s, e) {
                (Some(s), Some(None)) => Some(s.clone()),
                _ => None,
            });
            match found {
                Some(PSubst { subst, rhs }) => {
                    let r = call(&PS_FINALIZE, &[A::O(&subst)]);
                    let terms = r.field(0);
                    let inst = r.field(1);
                    let mut s: Subs<SC> = subs_id(0);
                    for i in (0..terms.size()).rev() {
                        let t = terms.field(i);
                        s = subs_cons(SC::HigherOrder(t.field_int(0), handle_to_fc(&t.field(1))), &s);
                    }
                    let m2 = mk_clos(&USubs { s, u: UInst::new(inst) }, &rhs);
                    match ps {
                        PS::Nil(true) => St::Final(Some((m2, stack.clone()))),
                        _ => St::Kni(m2, stack.clone(), ps),
                    }
                }
                None => match_elim(info, tab, ps, next, *depth, states, elims, head, stack),
            }
        }
        Loc::Arg { patterns, depth, arg, next } => match_arg(info, tab, ps, next, *depth, states, patterns, arg),
        Loc::Start { elims, depth, head, stack, next } => match_elim(info, tab, ps, next, *depth, states, elims, head, stack),
    }
}

fn match_kill(info: &Infos, tab: &Tab, ps: PS, loc: &Rc<Loc>) -> St {
    let mut loc = loc.clone();
    loop {
        let l = loc.clone();
        match &*l {
            Loc::Arg { next, .. } => loc = next.clone(),
            Loc::Start { head, stack, next, .. } => {
                zip(head, stack);
                match next {
                    Next::Continue(n) => loc = n.clone(),
                    Next::Return(b, m, stk) => return try_unfoldfix(info, tab, ps, *b, m, stk),
                }
            }
        }
    }
}

fn match_endstack(info: &Infos, tab: &Tab, ps: PS, states: States, next: &Next) -> St {
    match next {
        Next::Continue(n) => match_main(info, tab, ps, states, n),
        Next::Return(b, m, stk) => {
            assert!(all_dead(&states));
            try_unfoldfix(info, tab, ps, *b, m, stk)
        }
    }
}

fn try_unfoldfix(_info: &Infos, _tab: &Tab, ps: PS, b: bool, m: &FC, stk: &Stack) -> St {
    if !b {
        return St::Ret(m.clone(), stk.clone(), true, ps);
    }
    let (rarg, stack) = strip_update_shift_absorb_app(m, stk);
    if let Some((Z::Fix(fx, par), s)) = stack.uncons() {
        let a: Rc<[FC]> = Rc::from(vec![rarg]);
        let stk2 = stack_app(par, &append_stack(&a, s));
        let (fxe, fxbd) = contract_fix_vect(&fx.term_clone());
        St::Knit(fxe, fxbd, stk2, ps)
    } else {
        St::Ret(m.clone(), stk.clone(), true, ps)
    }
}

fn elim_hd(e: &EList) -> Option<(&Elim, &EList)> {
    e.as_ref().map(|c| (&c.hd, &c.tl))
}

#[allow(clippy::too_many_arguments)]
fn match_elim(info: &Infos, tab: &Tab, ps: PS, next: &Next, depth: isize, states: States, elims: &[Option<EList>], head: &FC, stk: &Stack) -> St {
    let mut head = head.clone();
    let mut stk = stk.clone();
    loop {
        let (z, s) = match stk.uncons() {
            None => {
                let states = extract_or_kill(|e: &EList, s| if e.is_none() { Some(s.clone()) } else { None }, elims, &states);
                return match_endstack(info, tab, ps, states, next);
            }
            Some((z, s)) => (z.clone(), s.clone()),
        };
        match z {
            Z::App(args) => {
                let (pargselims, states) = extract_or_kill2(
                    |e: &EList, s| match elim_hd(e) {
                        Some((Elim::App(pargs), es)) => Some(((pargs.clone(), es.clone()), s.clone())),
                        _ => None,
                    },
                    elims,
                    &states,
                );
                let na = args.len();
                let np = pargselims.iter().flatten().fold(na, |a, (pargs, _)| std::cmp::min(a, pargs.len()));
                let (pargs, elims, states) = extract_or_kill3(
                    |(pargs, elims): &(Rc<[PArg]>, EList), subst| {
                        if pargs.len() == np {
                            Some((pargs.clone(), elims.clone(), subst.clone()))
                        } else {
                            let fst: Rc<[PArg]> = pargs[0..np].iter().cloned().collect();
                            let lst: Rc<[PArg]> = pargs[np..].iter().cloned().collect();
                            Some((fst, econs(Elim::App(lst), elims), subst.clone()))
                        }
                    },
                    &pargselims,
                    &states,
                );
                let fargs: Rc<[FC]> = args[0..np].iter().cloned().collect();
                let rest: Rc<[FC]> = args[np..].iter().cloned().collect();
                let head = mk_fapp(&head, &fargs);
                let stack = if !rest.is_empty() { s.cons(Z::App(rest)) } else { s };
                let mut loc = Rc::new(Loc::Start { elims, depth, head, stack, next: next.clone() });
                let tr = transpose_split(np, &pargs);
                for (j, patterns) in tr.into_iter().enumerate().rev() {
                    loc = Rc::new(Loc::Arg { patterns, depth, arg: fargs[j].clone(), next: loc });
                }
                return match_main(info, tab, ps, states, &loc);
            }
            Z::Shift(k) => {
                head = lift_fconstr(k, &head);
                stk = s;
            }
            Z::Update(m) => {
                update(&m, head.mark(), head.term_clone());
                stk = s;
            }
            Z::CaseT(cd) => {
                let mark = neutr(head.mark());
                let head = mk(mark, FTerm::CaseT(cd.clone(), head.clone()));
                let ci_ind = constr::ci_ind(&cd.ci);
                let (prets, pbrss, elims, states) = extract_or_kill4(
                    |e: &EList, subst| match elim_hd(e) {
                        Some((Elim::Case(pind, pret, pbrs), es)) => {
                            if !qeq(info, QEQ_IND, pind, &ci_ind) {
                                None
                            } else {
                                Some((pret.clone(), pbrs.clone(), es.clone(), subst.clone()))
                            }
                        }
                        _ => None,
                    },
                    elims,
                    &states,
                );
                let e = &cd.e;
                let params = mind_params(info, &ci_ind);
                let fpms: Vec<FC> = (0..cd.pms.size()).map(|j| mk_clos(e, &cd.pms.field(j))).collect();
                let ind_subst = inductive_subst(&params, &cd.u, &fpms);
                let mut loc = Rc::new(Loc::Start { elims, depth, head: head.clone(), stack: s, next: next.clone() });
                let nbrs = cd.br.size();
                let tr = transpose_split(nbrs, &pbrss);
                for (i, patterns) in tr.into_iter().enumerate().rev() {
                    let b = cd.br.field(i);
                    let brctx = b.field(0);
                    let br = b.field(1);
                    let letctx = call(&CTOR_LETCTX, &[A::O(info.env()), A::O(&ci_ind), A::I(i as isize)]);
                    let (brdepth, br_e) = match letctx.as_option() {
                        None => {
                            let brdepth = brctx.size() as isize;
                            (brdepth, usubs_liftn(brdepth, e))
                        }
                        Some(ctx) => esubst_of_context(&ctx, &ind_subst, e),
                    };
                    loc = Rc::new(Loc::Arg { patterns, depth: brdepth + depth, arg: mk_clos(&br_e, &br), next: loc });
                }
                let pctx = cd.p.field(0).field(0);
                let p = cd.p.field(0).field(1);
                let letctx = call(&ARITY_LETCTX, &[A::O(info.env()), A::O(&ci_ind)]);
                let (pdepth, pred_e) = match letctx.as_option() {
                    None => {
                        let pdepth = pctx.size() as isize;
                        (pdepth, usubs_liftn(pdepth, e))
                    }
                    Some(ctx) => esubst_of_context(&ctx, &ind_subst, e),
                };
                let loc = Rc::new(Loc::Arg { patterns: prets, depth: pdepth + depth, arg: mk_clos(&pred_e, &p), next: loc });
                return match_main(info, tab, ps, states, &loc);
            }
            Z::Proj(proj2, r) => {
                let mark = neutr(head.mark());
                let head = mk(mark, FTerm::Proj(proj_make(&proj2), r.clone(), head.clone()));
                let (elims, states) = extract_or_kill2(
                    |e: &EList, subst| match elim_hd(e) {
                        Some((Elim::Proj(proj), es)) => {
                            if !qeq(info, QEQ_PROJ_REPR, proj, &proj2) {
                                None
                            } else {
                                Some((es.clone(), subst.clone()))
                            }
                        }
                        _ => None,
                    },
                    elims,
                    &states,
                );
                let loc = Rc::new(Loc::Start { elims, depth, head, stack: s, next: next.clone() });
                return match_main(info, tab, ps, states, &loc);
            }
            Z::Fix(..) | Z::Primitive(..) => {
                let states = extract_or_kill(|_: &EList, _| None, elims, &states);
                zip(&head, &stk);
                return match_endstack(info, tab, ps, states, next);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn match_arg(info: &Infos, tab: &Tab, ps: PS, next: &Rc<Loc>, depth: isize, states: States, patterns: &[Option<PArg>], t: &FC) -> St {
    let mut match_deeper = false;
    let mut npatterns: Vec<Option<Rc<HeadElim>>> = vec![];
    let mut nstates: States = vec![];
    assert!(states.len() == patterns.len());
    for (state, pattern) in states.iter().zip(patterns.iter()) {
        match state {
            None => {
                npatterns.push(None);
                nstates.push(None)
            }
            Some(psubst) => match pattern {
                None => {
                    npatterns.push(None);
                    nstates.push(state.clone())
                }
                Some(PArg::Hole(i)) => {
                    let h = fc_to_handle(t);
                    let subst = call(&PS_ADD_TERM, &[A::I(*i), A::I(depth), A::O(&h), A::O(&psubst.subst)]);
                    npatterns.push(None);
                    nstates.push(Some(PSubst { subst, rhs: psubst.rhs.clone() }))
                }
                Some(PArg::HoleIgnored) => {
                    npatterns.push(None);
                    nstates.push(state.clone())
                }
                Some(PArg::Rigid(p)) => {
                    match_deeper = true;
                    npatterns.push(Some(p.clone()));
                    nstates.push(state.clone())
                }
            },
        }
    }
    if match_deeper {
        let ps = PS::Cons(Rc::new(Resume { states: nstates, depth, patterns: npatterns, next: next.clone() }), Rc::new(ps));
        St::Kni(t.clone(), Stack::nil(), ps)
    } else {
        match_main(info, tab, ps, nstates, next)
    }
}

fn instance_pattern_match(pu: &OVal, u: &OVal, subst: &OVal) -> Option<OVal> {
    call(&INSTANCE_PATTERN_MATCH, &[A::O(pu), A::O(u), A::O(subst)]).as_option()
}

#[allow(clippy::too_many_arguments)]
fn match_head(info: &Infos, tab: &Tab, ps: PS, next: &Rc<Loc>, depth: isize, states: &States, patterns: &[Option<Rc<HeadElim>>], t: &FC, stk: &Stack) -> St {
    let tm = &t.term_clone();
    let start = |elims: Vec<Option<EList>>, stack: Stack| {
        Rc::new(Loc::Start { elims, depth, head: t.clone(), stack, next: Next::Continue(next.clone()) })
    };
    match &*tm {
        FTerm::Ind(ind2, u) => {
            let (elims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Ind(ind, pu) => {
                        if !qeq(info, QEQ_IND, ind, ind2) {
                            return None;
                        }
                        instance_pattern_match(pu, &u.v, &psubst.subst)
                            .map(|subst| (he.elims.clone(), PSubst { subst, rhs: psubst.rhs.clone() }))
                    }
                    _ => None,
                },
                patterns,
                states,
            );
            let loc = start(elims, stk.clone());
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::Construct(c2, u, args) => {
            let (elims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Constr(c, pu) => {
                        if !qeq(info, QEQ_CONSTRUCT, c, c2) {
                            return None;
                        }
                        instance_pattern_match(pu, &u.v, &psubst.subst)
                            .map(|subst| (he.elims.clone(), PSubst { subst, rhs: psubst.rhs.clone() }))
                    }
                    _ => None,
                },
                patterns,
                states,
            );
            let loc = start(elims, append_stack(args, stk));
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::Atom(t2) => match constr::kind(t2) {
            constr::SORT => {
                let (elims, states) = extract_or_kill2(
                    |he: &Rc<HeadElim>, psubst| match &he.head {
                        HeadPat::Sort(sp) => call(&SORT_PATTERN_MATCH, &[A::O(sp), A::O(t2), A::O(&psubst.subst)])
                            .as_option()
                            .map(|subst| (he.elims.clone(), PSubst { subst, rhs: psubst.rhs.clone() })),
                        _ => None,
                    },
                    patterns,
                    states,
                );
                let loc = start(elims, stk.clone());
                match_main(info, tab, ps, states, &loc)
            }
            constr::META => {
                let (elims, states) = extract_or_kill2(|_: &Rc<HeadElim>, _| None::<(EList, PSubst)>, patterns, states);
                let loc = start(elims, stk.clone());
                match_main(info, tab, ps, states, &loc)
            }
            _ => panic!("assert false"),
        },
        FTerm::Flex(TableKey::Const(c2, u)) => {
            let (elims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Symbol(c, pu) => {
                        if !qeq(info, QEQ_CONSTANT, c, c2) {
                            return None;
                        }
                        instance_pattern_match(pu, &u.v, &psubst.subst)
                            .map(|subst| (he.elims.clone(), PSubst { subst, rhs: psubst.rhs.clone() }))
                    }
                    _ => None,
                },
                patterns,
                states,
            );
            let loc = start(elims, stk.clone());
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::Rel(n) => {
            let (elims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Rel(n2) if n == n2 => Some((he.elims.clone(), psubst.clone())),
                    _ => None,
                },
                patterns,
                states,
            );
            let loc = start(elims, stk.clone());
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::Int(i2) => {
            let (elims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Int(i) if eq(EQ_UINT63, i, i2) => Some((he.elims.clone(), psubst.clone())),
                    _ => None,
                },
                patterns,
                states,
            );
            let loc = start(elims, stk.clone());
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::Float(f2) => {
            let (elims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Float(f) if eq(EQ_FLOAT64, f, f2) => Some((he.elims.clone(), psubst.clone())),
                    _ => None,
                },
                patterns,
                states,
            );
            let loc = start(elims, stk.clone());
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::String(s2) => {
            let (elims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::String(s) if eq(EQ_PSTRING, s, s2) => Some((he.elims.clone(), psubst.clone())),
                    _ => None,
                },
                patterns,
                states,
            );
            let loc = start(elims, stk.clone());
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::Prod(_, ty, body, e) => {
            let (tysbodyelims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Prod(ptys, pbod) => Some(((ptys.clone(), pbod.clone(), he.elims.clone()), psubst.clone())),
                    _ => None,
                },
                patterns,
                states,
            );
            let (pty, pbody, elims, states) = extract_or_kill4(
                |(ptys, pbod, elims): &(Rc<[PArg]>, PArg, EList), psubst| match ptys.len() {
                    0 => panic!("assert false"),
                    1 => Some((ptys[0].clone(), pbod.clone(), elims.clone(), psubst.clone())),
                    _ => {
                        let rem: Rc<[PArg]> = ptys[1..].iter().cloned().collect();
                        let he = HeadElim { head: HeadPat::Prod(rem, pbod.clone()), elims: None };
                        Some((ptys[0].clone(), PArg::Rigid(Rc::new(he)), elims.clone(), psubst.clone()))
                    }
                },
                &tysbodyelims,
                &states,
            );
            let loc = start(elims, stk.clone());
            let loc = Rc::new(Loc::Arg { patterns: pbody, depth: 1 + depth, arg: mk_clos(&usubs_lift(e), body), next: loc });
            let loc = Rc::new(Loc::Arg { patterns: pty, depth, arg: ty.clone(), next: loc });
            match_main(info, tab, ps, states, &loc)
        }
        FTerm::Lambda(na, ntys, body, e) => {
            let na0 = *na as usize;
            let (tysbodyelims, states) = extract_or_kill2(
                |he: &Rc<HeadElim>, psubst| match &he.head {
                    HeadPat::Lambda(ptys, pbod) if ptys.len() <= na0 => Some(((ptys.clone(), pbod.clone(), he.elims.clone()), psubst.clone())),
                    _ => None,
                },
                patterns,
                states,
            );
            let na = tysbodyelims.iter().flatten().fold(na0, |a, (p1, _, _)| std::cmp::min(a, p1.len()));
            assert!(na > 0);
            let (ptys, pbody, elims, states) = extract_or_kill4(
                |(ptys, pbod, elims): &(Rc<[PArg]>, Rc<HeadElim>, EList), psubst| {
                    let np = ptys.len();
                    if np == na {
                        Some((ptys.clone(), PArg::Rigid(pbod.clone()), elims.clone(), psubst.clone()))
                    } else {
                        let fst: Rc<[PArg]> = ptys[0..na].iter().cloned().collect();
                        let lst: Rc<[PArg]> = ptys[na..].iter().cloned().collect();
                        let he = HeadElim { head: HeadPat::Lambda(lst, pbod.clone()), elims: None };
                        Some((fst, PArg::Rigid(Rc::new(he)), elims.clone(), psubst.clone()))
                    }
                },
                &tysbodyelims,
                &states,
            );
            let mut body = body.clone();
            for i in (na..ntys.len()).rev() {
                let (bna, bty) = ntys.get(i);
                body = call(&MK_LAMBDA, &[A::O(bna), A::O(bty), A::O(&body)]);
            }
            let tys: Vec<(isize, FC)> = (0..na).map(|n| (n as isize, mk_clos(&usubs_liftn(n as isize, e), &ntys.get(n).1))).collect();
            let loc = start(elims, stk.clone());
            let loc = Rc::new(Loc::Arg { patterns: pbody, depth: tys.len() as isize + depth, arg: mk_clos(&usubs_liftn(na as isize, e), &body), next: loc });
            let tr = transpose_split(na, &ptys);
            let mut loc = loc;
            for (j, patterns) in tr.into_iter().enumerate().rev() {
                let (ldepth, arg) = &tys[j];
                loc = Rc::new(Loc::Arg { patterns, depth: ldepth + depth, arg: arg.clone(), next: loc });
            }
            match_main(info, tab, ps, states, &loc)
        }
        _ => {
            let states = extract_or_kill(|_: &Rc<HeadElim>, _| None, patterns, states);
            zip(t, stk);
            match_main(info, tab, ps, states, next)
        }
    }
}

pub fn match_head_resume(info: &Infos, tab: &Tab, ps: PS, r: &Rc<Resume>, m: &FC, stk: &Stack) -> St {
    match_head(info, tab, ps, &r.next, r.depth, &r.states, &r.patterns, m, stk)
}

#[allow(clippy::too_many_arguments)]
pub fn match_symbol(info: &Infos, tab: &Tab, ps: PS, fl: &TableKey, u: &OVal, b: bool, rules: &Rc<Vec<Rule>>, stk: &Stack) -> St {
    let unfold_fix = b && info.flags.red_set(F_FIX);
    let mut states: States = vec![];
    let mut elims: Vec<Option<EList>> = vec![];
    for r in rules.iter() {
        let subst = call(&PS_MAKE, &[A::O(&r.nvars)]);
        match instance_pattern_match(&r.mask, u, &subst) {
            Some(subst) => {
                states.push(Some(PSubst { subst, rhs: r.rhs.clone() }));
                elims.push(Some(r.elims.clone()))
            }
            None => {
                states.push(None);
                elims.push(None)
            }
        }
    }
    let m = mk(Red::Red, FTerm::Flex(fl.clone()));
    let loc = Rc::new(Loc::Start { elims, depth: 0, head: m.clone(), stack: stk.clone(), next: Next::Return(unfold_fix, m, stk.clone()) });
    match_main(info, tab, ps, states, &loc)
}
