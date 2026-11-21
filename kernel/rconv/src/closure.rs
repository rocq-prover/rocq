//! Port of kernel/cClosure.ml, restricted to the conversion mode.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use crate::cbs::*;
use crate::constr::{self, Rel};
use crate::esubst::*;
use crate::ffi::{call, handle_to_fc, OVal, A};
use crate::pattern;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Red {
    Ntrl,
    Cstr,
    Red,
}

pub fn neutr(m: Red) -> Red {
    match m {
        Red::Ntrl => Red::Ntrl,
        Red::Red | Red::Cstr => Red::Red,
    }
}

pub fn is_red(m: Red) -> bool {
    m == Red::Red
}

pub struct FCell {
    mark: Cell<Red>,
    term: RefCell<FTerm>,
}

pub type FC = Rc<FCell>;

impl FCell {
    #[inline]
    pub fn mark(&self) -> Red {
        self.mark.get()
    }
    /// The term of the cell, borrowed: the cell must not be updated while
    /// the borrow is alive.
    #[inline]
    pub fn term(&self) -> std::cell::Ref<'_, FTerm> {
        self.term.borrow()
    }
    #[inline]
    pub fn term_clone(&self) -> FTerm {
        self.term.borrow().clone()
    }
}

#[inline]
pub fn mk(mark: Red, t: FTerm) -> FC {
    Rc::new(FCell { mark: Cell::new(mark), term: RefCell::new(t) })
}

#[inline]
pub fn update(v: &FC, mark: Red, t: FTerm) {
    v.mark.set(mark);
    *v.term.borrow_mut() = t;
}

#[inline]
pub fn set_ntrl(v: &FC) {
    v.mark.set(Red::Ntrl)
}

#[derive(Clone)]
pub struct UInst {
    pub v: OVal,
    pub empty: bool,
}

impl UInst {
    pub fn new(v: OVal) -> UInst {
        let empty = constr::instance_is_empty(&v);
        UInst { v, empty }
    }
}

#[derive(Clone)]
pub enum SC {
    Regular(FC),
    HigherOrder(isize, FC),
}

#[derive(Clone)]
pub struct USubs {
    pub s: Subs<SC>,
    pub u: UInst,
}

#[derive(Clone)]
pub enum TableKey {
    Const(OVal, UInst),
    Var(OVal),
    Rel(isize),
}

/// [fixpoint] = ((ri, i), rdcl) and [cofixpoint] = (i, rdcl), with rdcl = (names, types, bodies).
#[derive(Clone)]
pub struct FixData {
    pub ri: OVal,
    pub i: isize,
    pub rdcl: OVal,
}

impl FixData {
    pub fn of_fix(fx: &OVal) -> FixData {
        let h = fx.field(0);
        FixData { ri: h.field(0), i: h.field_int(1), rdcl: fx.field(1) }
    }
    pub fn of_cofix(fx: &OVal) -> FixData {
        FixData { ri: OVal::int(0), i: fx.field_int(0), rdcl: fx.field(1) }
    }
    pub fn names(&self) -> OVal {
        self.rdcl.field(0)
    }
    pub fn types(&self) -> OVal {
        self.rdcl.field(1)
    }
    pub fn bodies(&self) -> OVal {
        self.rdcl.field(2)
    }
    pub fn nbodies(&self) -> usize {
        self.rdcl.field(2).size()
    }
    pub fn rec_arg(&self, n: isize) -> isize {
        self.ri.field_int(n as usize)
    }
}

/// Shared data of [FCaseT], [FCaseInvert] and [ZcaseT]: ci, u, pms, p, br, e.
pub struct CaseData {
    pub ci: OVal,
    pub u: OVal,
    pub pms: OVal,
    pub p: OVal,
    pub br: OVal,
    pub e: USubs,
}

/// Binders of a [FLambda], outermost first.
#[derive(Clone)]
pub struct LamTys {
    pub v: Rc<Vec<(OVal, OVal)>>,
    pub start: usize,
}

impl LamTys {
    pub fn len(&self) -> usize {
        self.v.len() - self.start
    }
    pub fn hd(&self) -> &(OVal, OVal) {
        &self.v[self.start]
    }
    pub fn skipn(&self, n: usize) -> LamTys {
        LamTys { v: self.v.clone(), start: self.start + n }
    }
    pub fn get(&self, i: usize) -> &(OVal, OVal) {
        &self.v[self.start + i]
    }
}

#[derive(Clone)]
pub enum FTerm {
    Rel(isize),
    Atom(OVal),
    Flex(TableKey),
    Ind(OVal, UInst),
    Construct(OVal, UInst, Rc<[FC]>),
    App(FC, Rc<[FC]>),
    Proj(OVal, OVal, FC),
    Fix(FixData, USubs),
    CoFix(FixData, USubs),
    CaseT(Rc<CaseData>, FC),
    CaseInvert(Rc<CaseData>, Rc<[FC]>, FC),
    Lambda(isize, LamTys, OVal, USubs),
    Prod(OVal, FC, OVal, USubs),
    LetIn(OVal, FC, FC, OVal, USubs),
    Evar(OVal, OVal, USubs),
    Int(OVal),
    Float(OVal),
    String(OVal),
    Array(UInst, OVal, FC, isize),
    Lift(isize, FC),
    Clos(OVal, USubs),
    Irrelevant,
    Locked,
}

/* Stacks */

#[derive(Clone)]
pub enum Z {
    App(Rc<[FC]>),
    CaseT(Rc<CaseData>),
    Proj(OVal, OVal),
    Fix(FC, Stack),
    /// operator, constant, instance, arguments already seen (in reverse order), next arguments
    Primitive(OVal, OVal, UInst, Rc<Vec<FC>>, Rc<Vec<(isize, FC)>>),
    Shift(isize),
    Update(FC),
}

pub struct SNode {
    pub hd: Z,
    pub tl: Stack,
}

#[derive(Clone)]
pub struct Stack(pub Option<Rc<SNode>>);

impl Stack {
    #[inline]
    pub fn nil() -> Stack {
        Stack(None)
    }
    #[inline]
    pub fn cons(&self, z: Z) -> Stack {
        Stack(Some(Rc::new(SNode { hd: z, tl: self.clone() })))
    }
    #[inline]
    pub fn cons_owned(self, z: Z) -> Stack {
        Stack(Some(Rc::new(SNode { hd: z, tl: self })))
    }
    #[inline]
    pub fn is_nil(&self) -> bool {
        self.0.is_none()
    }
    #[inline]
    pub fn uncons(&self) -> Option<(&Z, &Stack)> {
        match &self.0 {
            None => None,
            Some(n) => Some((&n.hd, &n.tl)),
        }
    }
    pub fn ptr_eq(&self, o: &Stack) -> bool {
        match (&self.0, &o.0) {
            (None, None) => true,
            (Some(a), Some(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
    pub fn to_vec(&self) -> Vec<Z> {
        let mut v = vec![];
        let mut s = self;
        while let Some((z, tl)) = s.uncons() {
            v.push(z.clone());
            s = tl;
        }
        v
    }
    /// The elements of the stack, top first, by reference.
    pub fn to_refs(&self) -> Vec<&Z> {
        let mut v = vec![];
        let mut s = self;
        while let Some((z, tl)) = s.uncons() {
            v.push(z);
            s = tl;
        }
        v
    }
    /// [l @ self] where [l] is given top first
    pub fn prepend(&self, l: Vec<Z>) -> Stack {
        let mut s = self.clone();
        for z in l.into_iter().rev() {
            s = s.cons_owned(z);
        }
        s
    }
}

/// [a @ b]
pub fn stack_app(a: &Stack, b: &Stack) -> Stack {
    if a.is_nil() {
        return b.clone();
    }
    let mut s = b.clone();
    for z in a.to_refs().into_iter().rev() {
        s = s.cons_owned(z.clone());
    }
    s
}

pub fn append_stack(v: &Rc<[FC]>, s: &Stack) -> Stack {
    if v.is_empty() {
        return s.clone();
    }
    if let Some((Z::App(l), tl)) = s.uncons() {
        let mut w: Vec<FC> = Vec::with_capacity(v.len() + l.len());
        w.extend(v.iter().cloned());
        w.extend(l.iter().cloned());
        return tl.cons(Z::App(w.into()));
    }
    s.cons(Z::App(v.clone()))
}

pub fn zshift(n: isize, s: &Stack) -> Stack {
    if n == 0 {
        return s.clone();
    }
    if let Some((Z::Shift(k), tl)) = s.uncons() {
        return tl.cons(Z::Shift(n + k));
    }
    s.cons(Z::Shift(n))
}

pub fn stack_args_size(s: &Stack) -> usize {
    let mut n = 0;
    let mut s = s;
    loop {
        match s.uncons() {
            Some((Z::App(v), tl)) => {
                n += v.len();
                s = tl;
            }
            Some((Z::Shift(_), tl)) | Some((Z::Update(_), tl)) => s = tl,
            _ => return n,
        }
    }
}

/* Infos */

/// [RedFlags.reds] with its flag bits; one word.
#[derive(Clone)]
pub struct Flags(Rc<(OVal, isize)>);

pub const F_BETA: isize = 0b000001;
pub const F_DELTA: isize = 0b000010;
pub const F_MATCH: isize = 0b000100;
pub const F_FIX: isize = 0b001000;
pub const F_COFIX: isize = 0b010000;
pub const F_ZETA: isize = 0b100000;

impl Flags {
    pub fn new(v: OVal) -> Flags {
        let bits = v.field_int(0);
        Flags(Rc::new((v, bits)))
    }
    #[inline]
    pub fn v(&self) -> &OVal {
        &self.0 .0
    }
    #[inline]
    pub fn red_set(&self, f: isize) -> bool {
        self.0 .1 & f != 0
    }
}

pub struct Cache {
    pub env: OVal,
    pub evars: OVal,
    pub share: bool,
    pub univs: OVal,
    pub all: Flags,
    pub betaiotazeta: Flags,
    pub empty_inst: OVal,
    /// Whether the environment has irrelevant constants / inductives.
    pub irr_consts: bool,
    pub irr_inds: bool,
    pub prim_cache: RefCell<HashMap<isize, (isize, Rc<Vec<isize>>)>>,
}

#[derive(Clone)]
pub struct Infos {
    pub flags: Flags,
    pub relevances: Range<OVal>,
    pub cache: Rc<Cache>,
}

impl Infos {
    pub fn with_reds(&self, flags: &Flags) -> Infos {
        Infos { flags: flags.clone(), relevances: self.relevances.clone(), cache: self.cache.clone() }
    }
    pub fn env(&self) -> &OVal {
        &self.cache.env
    }
    pub fn push_relevance(&self, na: &OVal) -> Infos {
        Infos {
            flags: self.flags.clone(),
            relevances: self.relevances.cons(constr::binder_relevance(na)),
            cache: self.cache.clone(),
        }
    }
    pub fn push_relevances(&self, nas: &[OVal]) -> Infos {
        let mut r = self.relevances.clone();
        for na in nas {
            r = r.cons(constr::binder_relevance(na));
        }
        Infos { flags: self.flags.clone(), relevances: r, cache: self.cache.clone() }
    }
}

pub fn anomaly(k: isize) -> ! {
    call(&ANOMALY, &[A::I(k)]);
    unreachable!()
}

/// Equality of names: all the equalities below [EQ_UINT63] are reflexive,
/// and inductives are pairs of a [MutInd.t] and an integer.
pub fn eq(k: isize, a: &OVal, b: &OVal) -> bool {
    if k < EQ_UINT63 && a.phys_eq(b) {
        return true;
    }
    if (k == EQ_IND_CAN || k == EQ_IND_USER) && a.field_int(1) == b.field_int(1) && a.field(0).phys_eq(&b.field(0)) {
        return true;
    }
    call(&EQ, &[A::I(k), A::O(a), A::O(b)]).as_bool()
}

pub fn qeq(info: &Infos, k: isize, a: &OVal, b: &OVal) -> bool {
    call(&QEQ, &[A::O(info.env()), A::I(k), A::O(a), A::O(b)]).as_bool()
}

pub fn instance_equal(a: &OVal, b: &OVal) -> bool {
    if a.phys_eq(b) {
        return true;
    }
    call(&INSTANCE_EQUAL, &[A::O(a), A::O(b)]).as_bool()
}

pub fn is_irrelevant(info: &Infos, r: &OVal) -> bool {
    match constr::relevance(r) {
        Rel::Irrelevant => true,
        Rel::Var(q) => call(&QVAR_IRRELEVANT, &[A::O(&info.cache.evars), A::O(&q)]).as_bool(),
        Rel::Relevant => false,
    }
}

pub fn usubst_instance(e: &USubs, u: &OVal) -> OVal {
    if e.u.empty {
        u.clone()
    } else {
        call(&SUBST_INSTANCE_INSTANCE, &[A::O(&e.u.v), A::O(u)])
    }
}

pub fn usubst_relevance(e: &USubs, r: &OVal) -> OVal {
    if e.u.empty {
        r.clone()
    } else {
        call(&SUBST_RELEVANCE, &[A::O(&e.u.v), A::O(r)])
    }
}

pub fn usubst_binder(e: &USubs, na: &OVal) -> OVal {
    if e.u.empty {
        na.clone()
    } else {
        call(&USUBST_BINDER, &[A::O(&e.u.v), A::O(na)])
    }
}

pub fn usubs_shft(n: isize, e: &USubs) -> USubs {
    USubs { s: subs_shft(n, &e.s), u: e.u.clone() }
}

pub fn usubs_lift(e: &USubs) -> USubs {
    USubs { s: subs_lift(&e.s), u: e.u.clone() }
}

pub fn usubs_liftn(n: isize, e: &USubs) -> USubs {
    USubs { s: subs_liftn(n, &e.s), u: e.u.clone() }
}

pub fn usubs_cons(x: &FC, e: &USubs) -> USubs {
    USubs { s: subs_cons(SC::Regular(x.clone()), &e.s), u: e.u.clone() }
}

pub fn subs_consn(v: &[FC], i: usize, n: usize, s: &Subs<SC>) -> Subs<SC> {
    let mut s = s.clone();
    for x in &v[i..n] {
        s = subs_cons(SC::Regular(x.clone()), &s);
    }
    s
}

pub fn usubs_consn(v: &[FC], i: usize, n: usize, e: &USubs) -> USubs {
    USubs { s: subs_consn(v, i, n, &e.s), u: e.u.clone() }
}

pub fn usubs_consv(v: &[FC], e: &USubs) -> USubs {
    usubs_consn(v, 0, v.len(), e)
}

pub fn usubs_id(u: UInst) -> USubs {
    USubs { s: subs_id(0), u }
}

thread_local! {
    static IRRELEVANT: FC = mk(Red::Cstr, FTerm::Irrelevant);
}

pub fn mk_irrelevant() -> FC {
    IRRELEVANT.with(|x| x.clone())
}

/* Lifting */

pub fn lft_fconstr(n: isize, ft: &FC) -> FC {
    let mut n = n;
    let mut ft = ft.clone();
    loop {
        let next = {
            let t = ft.term();
            match &*t {
                FTerm::Ind(..)
                | FTerm::Flex(TableKey::Const(..))
                | FTerm::Flex(TableKey::Var(_))
                | FTerm::Int(_)
                | FTerm::Float(_)
                | FTerm::String(_)
                | FTerm::Irrelevant => None,
                FTerm::Construct(_, _, args) if args.is_empty() => None,
                FTerm::Rel(i) => return mk(ft.mark(), FTerm::Rel(i + n)),
                FTerm::Lambda(k, tys, f, e) => {
                    return mk(Red::Cstr, FTerm::Lambda(*k, tys.clone(), f.clone(), usubs_shft(n, e)))
                }
                FTerm::Fix(fx, e) => return mk(Red::Cstr, FTerm::Fix(fx.clone(), usubs_shft(n, e))),
                FTerm::CoFix(fx, e) => return mk(Red::Cstr, FTerm::CoFix(fx.clone(), usubs_shft(n, e))),
                FTerm::Lift(k, m) => Some((*k, m.clone())),
                FTerm::Construct(c, u, args) => {
                    let args: Rc<[FC]> = args.iter().map(|a| lft_fconstr(n, a)).collect();
                    return mk(Red::Cstr, FTerm::Construct(c.clone(), u.clone(), args));
                }
                FTerm::Array(u, ar, ty, l) => return mk(Red::Cstr, FTerm::Array(u.clone(), ar.clone(), ty.clone(), l + n)),
                FTerm::Locked => panic!("assert false"),
                FTerm::Flex(TableKey::Rel(_))
                | FTerm::Atom(_)
                | FTerm::App(..)
                | FTerm::Proj(..)
                | FTerm::CaseT(..)
                | FTerm::CaseInvert(..)
                | FTerm::Prod(..)
                | FTerm::LetIn(..)
                | FTerm::Evar(..)
                | FTerm::Clos(..) => return mk(ft.mark(), FTerm::Lift(n, ft.clone())),
            }
        };
        match next {
            None => return ft,
            Some((k, m)) => {
                n += k;
                ft = m;
            }
        }
    }
}

pub fn lift_fconstr(k: isize, f: &FC) -> FC {
    if k == 0 {
        f.clone()
    } else {
        lft_fconstr(k, f)
    }
}

fn lift_subs(n: isize, k: isize, s: &USubs) -> USubs {
    usubs_shft(n, &usubs_liftn(k, s))
}

fn with_term(v: &FC, t: FTerm) -> FC {
    mk(v.mark(), t)
}

fn case_data_with_e(cd: &CaseData, e: USubs) -> Rc<CaseData> {
    Rc::new(CaseData {
        ci: cd.ci.clone(),
        u: cd.u.clone(),
        pms: cd.pms.clone(),
        p: cd.p.clone(),
        br: cd.br.clone(),
        e,
    })
}

fn parray_map(t: &OVal, f: &mut dyn FnMut(&FC) -> FC) -> OVal {
    let r = call(&PARRAY_TO_ARRAY, &[A::O(t)]);
    let elems = r.field(0);
    let def = r.field(1);
    let n = elems.size();
    let mut hs: Vec<OVal> = Vec::with_capacity(n);
    for i in 0..n {
        let x = handle_to_fc(&elems.field(i));
        hs.push(crate::ffi::fc_to_handle(&f(&x)));
    }
    let def = crate::ffi::fc_to_handle(&f(&handle_to_fc(&def)));
    let arr = crate::ffi::alloc_array(&hs);
    call(&PARRAY_OF_ARRAY, &[A::O(&arr), A::O(&def)])
}

pub fn relift_fconstr(n: isize, k: isize, v: &FC) -> FC {
    let t = v.term();
    match &*t {
        FTerm::Rel(i) => {
            if *i <= k {
                v.clone()
            } else {
                with_term(v, FTerm::Rel(n + i))
            }
        }
        FTerm::Flex(TableKey::Rel(_)) => lft_fconstr(n, v),
        FTerm::App(f, ve) => {
            let f = relift_fconstr(n, k, f);
            let ve: Rc<[FC]> = ve.iter().map(|x| relift_fconstr(n, k, x)).collect();
            with_term(v, FTerm::App(f, ve))
        }
        FTerm::CaseT(cd, c) => {
            let env = lift_subs(n, k, &cd.e);
            with_term(v, FTerm::CaseT(case_data_with_e(cd, env), relift_fconstr(n, k, c)))
        }
        FTerm::CaseInvert(cd, indices, c) => {
            let env = lift_subs(n, k, &cd.e);
            let indices: Rc<[FC]> = indices.iter().map(|x| relift_fconstr(n, k, x)).collect();
            with_term(v, FTerm::CaseInvert(case_data_with_e(cd, env), indices, relift_fconstr(n, k, c)))
        }
        FTerm::Fix(fx, e) => with_term(v, FTerm::Fix(fx.clone(), lift_subs(n, k, e))),
        FTerm::CoFix(fx, e) => with_term(v, FTerm::CoFix(fx.clone(), lift_subs(n, k, e))),
        FTerm::Proj(p, r, c) => with_term(v, FTerm::Proj(p.clone(), r.clone(), relift_fconstr(n, k, c))),
        FTerm::Lambda(len, tys, f, e) => with_term(v, FTerm::Lambda(*len, tys.clone(), f.clone(), lift_subs(n, k, e))),
        FTerm::Prod(na, t, c, e) => {
            let e = lift_subs(n, k, e);
            with_term(v, FTerm::Prod(na.clone(), relift_fconstr(n, k, t), c.clone(), e))
        }
        FTerm::LetIn(na, b, t, f, e) => {
            let e = lift_subs(n, k, e);
            with_term(v, FTerm::LetIn(na.clone(), relift_fconstr(n, k, b), relift_fconstr(n, k, t), f.clone(), e))
        }
        FTerm::Evar(ev, args, env) => with_term(v, FTerm::Evar(ev.clone(), args.clone(), lift_subs(n, k, env))),
        FTerm::Lift(k2, a) => {
            assert!(*k2 >= k);
            with_term(v, FTerm::Lift(n + k2, a.clone()))
        }
        FTerm::Array(u, t, ty, lft) => {
            if *lft >= k {
                with_term(v, FTerm::Array(u.clone(), t.clone(), ty.clone(), lft + n))
            } else {
                let k2 = k - lft;
                let t = parray_map(t, &mut |x| relift_fconstr(n, k2, x));
                let ty = relift_fconstr(n, k2, ty);
                with_term(v, FTerm::Array(u.clone(), t, ty, *lft))
            }
        }
        FTerm::Clos(t, env) => with_term(v, FTerm::Clos(t.clone(), lift_subs(n, k, env))),
        FTerm::Flex(TableKey::Const(..))
        | FTerm::Flex(TableKey::Var(_))
        | FTerm::Ind(..)
        | FTerm::Construct(..)
        | FTerm::Atom(_)
        | FTerm::Int(_)
        | FTerm::Float(_)
        | FTerm::String(_) => v.clone(),
        FTerm::Irrelevant => v.clone(),
        FTerm::Locked => panic!("assert false"),
    }
}

pub fn clos_rel(e: &Subs<SC>, i: isize) -> SC {
    match expand_rel(i, e) {
        Either::Inl((n, SC::Regular(mt))) | Either::Inl((n, SC::HigherOrder(0, mt))) => SC::Regular(lift_fconstr(n, &mt)),
        Either::Inl((n, SC::HigherOrder(nargs, mt))) => SC::HigherOrder(nargs, relift_fconstr(n, nargs, &mt)),
        Either::Inr((k, None)) => SC::Regular(mk(Red::Ntrl, FTerm::Rel(k))),
        Either::Inr((k, Some(p))) => SC::Regular(lift_fconstr(k - p, &mk(Red::Red, FTerm::Flex(TableKey::Rel(p))))),
    }
}

/* Updates */

fn compact_stack(head: &FC, stk: &Stack) -> Stack {
    let mut depth = 0;
    let mut stk = stk.clone();
    loop {
        match stk.uncons() {
            Some((Z::Shift(k), s)) => {
                depth += k;
                stk = s.clone();
            }
            Some((Z::Update(m), s)) => {
                let h2 = lft_fconstr(depth, head);
                update(m, h2.mark(), h2.term_clone());
                stk = s.clone();
            }
            _ => return zshift(depth, &stk),
        }
    }
}

pub fn zupdate(info: &Infos, m: &FC, s: &Stack) -> Stack {
    if info.cache.share && is_red(m.mark()) {
        let s2 = compact_stack(m, s);
        *m.term.borrow_mut() = FTerm::Locked;
        s2.cons_owned(Z::Update(m.clone()))
    } else {
        s.clone()
    }
}

/* Closures */

pub fn mk_lambda(e: &USubs, t: &OVal) -> FTerm {
    let mut tys = vec![];
    let mut c = t.clone();
    loop {
        match constr::kind(&c) {
            constr::LAMBDA => {
                tys.push((c.field(0), c.field(1)));
                c = c.field(2);
            }
            constr::CAST => c = c.field(0),
            _ => break,
        }
    }
    let n = tys.len() as isize;
    FTerm::Lambda(n, LamTys { v: Rc::new(tys), start: 0 }, c, e.clone())
}

/// [destFLambda mk_clos t]
pub fn dest_flambda(t: &FC) -> (OVal, FC, FC) {
    let tm = t.term();
    match &*tm {
        FTerm::Lambda(n, tys, b, e) if tys.len() >= 1 => {
            let (na, ty) = tys.hd();
            let na = usubst_binder(e, na);
            let ty = mk_clos(e, ty);
            if tys.len() == 1 {
                (na, ty, mk_clos(&usubs_lift(e), b))
            } else {
                (na, ty, mk(t.mark(), FTerm::Lambda(n - 1, tys.skipn(1), b.clone(), usubs_lift(e))))
            }
        }
        _ => panic!("assert false"),
    }
}

fn usubst_punivs(e: &USubs, u: &OVal) -> UInst {
    if e.u.empty {
        UInst::new(u.clone())
    } else {
        UInst::new(call(&SUBST_INSTANCE_INSTANCE, &[A::O(&e.u.v), A::O(u)]))
    }
}

pub fn mk_clos(e: &USubs, t: &OVal) -> FC {
    match constr::kind(t) {
        constr::REL => match clos_rel(&e.s, constr::dest_rel(t)) {
            SC::Regular(v) => v,
            SC::HigherOrder(..) => anomaly(AN_PATTERN_VAR),
        },
        constr::VAR => mk(Red::Red, FTerm::Flex(TableKey::Var(t.field(0)))),
        constr::CONST => {
            let (c, u) = constr::dest_pref(t);
            mk(Red::Red, FTerm::Flex(TableKey::Const(c, usubst_punivs(e, &u))))
        }
        constr::SORT => {
            let s = if e.u.empty { t.clone() } else { call(&MK_SORT_SUBST, &[A::O(&e.u.v), A::O(t)]) };
            mk(Red::Ntrl, FTerm::Atom(s))
        }
        constr::META => mk(Red::Ntrl, FTerm::Atom(t.clone())),
        constr::IND => {
            let (c, u) = constr::dest_pref(t);
            mk(Red::Ntrl, FTerm::Ind(c, usubst_punivs(e, &u)))
        }
        constr::CONSTRUCT => {
            let (c, u) = constr::dest_pref(t);
            mk(Red::Cstr, FTerm::Construct(c, usubst_punivs(e, &u), Rc::from(vec![])))
        }
        constr::INT => mk(Red::Cstr, FTerm::Int(t.field(0))),
        constr::FLOAT => mk(Red::Cstr, FTerm::Float(t.field(0))),
        constr::STRING => mk(Red::Cstr, FTerm::String(t.field(0))),
        _ => mk(Red::Red, FTerm::Clos(t.clone(), e.clone())),
    }
}

pub fn injectu(c: &OVal, u: &OVal) -> FC {
    mk_clos(&usubs_id(UInst::new(u.clone())), c)
}

pub fn mk_clos_vect(e: &USubs, v: &OVal) -> Rc<[FC]> {
    let n = v.size();
    (0..n).map(|i| mk_clos(e, &v.field(i))).collect()
}

/* Reduction cache */

pub enum TableVal {
    Def(FC, Option<OVal>),
    Primitive(OVal),
    Symbol(OVal, bool, Rc<Vec<pattern::Rule>>),
    Undef,
}

pub struct Table {
    map: RefCell<HashMap<isize, Vec<(TableKey, Rc<TableVal>)>>>,
}

pub type Tab = Rc<Table>;

pub fn create_tab() -> Tab {
    Rc::new(Table { map: RefCell::new(HashMap::new()) })
}

fn hash_key(k: &TableKey) -> isize {
    match k {
        TableKey::Const(c, _) => 3 * call(&CONSTANT_HASH, &[A::O(c)]).as_int(),
        TableKey::Var(id) => {
            let mut h: isize = 0;
            for b in id.string_bytes() {
                h = h.wrapping_mul(31).wrapping_add(b as isize);
            }
            3 * h + 1
        }
        TableKey::Rel(n) => 3 * n + 2,
    }
}

fn eq_table_key(k1: &TableKey, k2: &TableKey) -> bool {
    match (k1, k2) {
        (TableKey::Const(c1, u1), TableKey::Const(c2, u2)) => {
            (c1.phys_eq(c2) || eq(EQ_CONSTANT_USER, c1, c2)) && instance_equal(&u1.v, &u2.v)
        }
        (TableKey::Var(i1), TableKey::Var(i2)) => i1.phys_eq(i2) || i1.string_bytes() == i2.string_bytes(),
        (TableKey::Rel(i), TableKey::Rel(j)) => i == j,
        _ => false,
    }
}

pub fn key_args(k: &TableKey) -> (isize, OVal, OVal) {
    match k {
        TableKey::Const(c, u) => (0, c.clone(), u.v.clone()),
        TableKey::Var(id) => (1, id.clone(), OVal::int(0)),
        TableKey::Rel(n) => (2, OVal::int(*n), OVal::int(0)),
    }
}

fn value_of(info: &Infos, k: &TableKey) -> TableVal {
    let (tag, a, b) = key_args(k);
    let r = call(
        &VALUE_OF,
        &[A::O(info.env()), A::O(&info.cache.evars), A::O(&info.flags.v()), A::I(tag), A::O(&a), A::O(&b)],
    );
    if r.is_long() {
        match r.as_int() {
            0 => TableVal::Def(mk_irrelevant(), None),
            _ => TableVal::Undef,
        }
    } else {
        match r.tag() {
            0 => {
                let c = r.field(0);
                let u = r.field(1);
                let mask = r.field(2);
                TableVal::Def(injectu(&c, &u), Some(mask))
            }
            1 => TableVal::Primitive(r.field(0)),
            _ => {
                let rules = pattern::parse_rules(&r.field(2));
                TableVal::Symbol(r.field(0), r.field(1).as_bool(), Rc::new(rules))
            }
        }
    }
}

pub fn table_lookup(info: &Infos, tab: &Tab, k: &TableKey) -> Rc<TableVal> {
    let h = hash_key(k);
    {
        let bucket = tab.map.borrow().get(&h).cloned();
        if let Some(b) = bucket {
            for (k2, v) in b.iter() {
                if eq_table_key(k2, k) {
                    return v.clone();
                }
            }
        }
    }
    let v = Rc::new(value_of(info, k));
    tab.map.borrow_mut().entry(h).or_default().push((k.clone(), v.clone()));
    v
}

/* Zip */

pub fn mk_fapp(h: &FC, args: &Rc<[FC]>) -> FC {
    if args.is_empty() {
        return h.clone();
    }
    let t = h.term();
    if let FTerm::Construct(c, u, args0) = &*t {
        let args: Rc<[FC]> = if args0.is_empty() {
            args.clone()
        } else {
            args0.iter().chain(args.iter()).cloned().collect()
        };
        return mk(Red::Cstr, FTerm::Construct(c.clone(), u.clone(), args));
    }
    mk(neutr(h.mark()), FTerm::App(h.clone(), args.clone()))
}

pub fn proj_make(p: &OVal) -> OVal {
    call(&PROJ_MAKE, &[A::O(p)])
}

/// The top node of a stack and the rest of it.
#[inline]
fn pop(stk: &Stack) -> Option<(Rc<SNode>, Stack)> {
    stk.0.as_ref().map(|nd| (nd.clone(), nd.tl.clone()))
}

pub fn zip(m: &FC, stk: &Stack) -> FC {
    let mut m = m.clone();
    let mut stk = stk.clone();
    loop {
        let Some((nd, s)) = pop(&stk) else { return m };
        match &nd.hd {
            Z::App(args) => {
                m = mk_fapp(&m, args);
                stk = s;
            }
            Z::CaseT(cd) => {
                let mark = neutr(m.mark());
                m = mk(mark, FTerm::CaseT(cd.clone(), m.clone()));
                stk = s;
            }
            Z::Proj(p, r) => {
                let mark = neutr(m.mark());
                m = mk(mark, FTerm::Proj(proj_make(p), r.clone(), m.clone()));
                stk = s;
            }
            Z::Fix(fx, par) => {
                let a: Rc<[FC]> = Rc::from(vec![m.clone()]);
                stk = stack_app(par, &append_stack(&a, &s));
                m = fx.clone();
            }
            Z::Shift(n) => {
                m = lift_fconstr(*n, &m);
                stk = s;
            }
            Z::Update(rf) => {
                update(rf, m.mark(), m.term_clone());
                m = rf.clone();
                stk = s;
            }
            Z::Primitive(_op, c, u, rargs, kargs) => {
                let mut args: Vec<FC> = rargs.iter().rev().cloned().collect();
                args.push(m.clone());
                args.extend(kargs.iter().map(|(_, a)| a.clone()));
                let f = mk(Red::Red, FTerm::Flex(TableKey::Const(c.clone(), u.clone())));
                m = mk(neutr(m.mark()), FTerm::App(f, args.into()));
                stk = s;
            }
        }
    }
}

/* Stripping */

pub fn strip_update_shift_absorb_app(head: &FC, stk: &Stack) -> (FC, Stack) {
    let mut h = head.clone();
    let mut stk = stk.clone();
    loop {
        let Some((nd, s)) = pop(&stk) else { return (h, stk) };
        match &nd.hd {
            Z::Shift(k) => h = lift_fconstr(*k, &h),
            Z::App(args) => h = mk_fapp(&h, args),
            Z::Update(m) => {
                update(m, h.mark(), h.term_clone());
                h = m.clone();
            }
            _ => return (h, stk),
        }
        stk = s;
    }
}

/// Returns (depth, h, List.rev rstk, stk)
pub fn strip_update_shift_app_red(head: &FC, stk: &Stack) -> (isize, FC, Stack, Stack) {
    let mut rstk: Vec<Z> = vec![];
    let mut h = head.clone();
    let mut depth = 0;
    let mut stk = stk.clone();
    while let Some((nd, s)) = pop(&stk) {
        match &nd.hd {
            Z::Shift(k) => {
                rstk.push(Z::Shift(*k));
                h = lift_fconstr(*k, &h);
                depth += k;
            }
            Z::App(args) => {
                h = mk_fapp(&h, args);
                rstk.push(Z::App(args.clone()));
            }
            Z::Update(m) => {
                update(m, h.mark(), h.term_clone());
                h = m.clone();
            }
            _ => break,
        }
        stk = s;
    }
    (depth, h, Stack::nil().prepend(rstk), stk)
}

pub fn strip_update_shift_app(head: &FC, stk: &Stack) -> (isize, FC, Stack, Stack) {
    assert!(!is_red(head.mark()));
    strip_update_shift_app_red(head, stk)
}

/// Returns (Some (pars, arg) | None, stk)
pub fn get_nth_arg(head: &FC, n: isize, stk: &Stack) -> (Option<(Stack, FC)>, Stack) {
    assert!(!is_red(head.mark()));
    let mut rstk: Vec<Z> = vec![];
    let mut h = head.clone();
    let mut n = n;
    let mut stk = stk.clone();
    while let Some((nd, s)) = pop(&stk) {
        match &nd.hd {
            Z::Shift(k) => {
                rstk.push(Z::Shift(*k));
                h = lift_fconstr(*k, &h);
            }
            Z::App(args) => {
                let q = args.len() as isize;
                if n >= q {
                    h = mk_fapp(&h, args);
                    rstk.push(Z::App(args.clone()));
                    n -= q;
                } else {
                    let nu = n as usize;
                    let bef: Rc<[FC]> = args[0..nu].iter().cloned().collect();
                    let aft: Rc<[FC]> = args[nu + 1..].iter().cloned().collect();
                    if n != 0 {
                        rstk.push(Z::App(bef));
                    }
                    let stk2 = Stack::nil().prepend(rstk);
                    return (Some((stk2, args[nu].clone())), append_stack(&aft, &s));
                }
            }
            Z::Update(m) => {
                update(m, h.mark(), h.term_clone());
                h = m.clone();
            }
            _ => break,
        }
        stk = s;
    }
    (None, stk.prepend(rstk))
}

pub enum Args {
    Subst(USubs),
    Lam(FC),
}

/// Beta reduction: look for an applied argument in the stack.
pub fn get_args(n: isize, tys: &LamTys, f: &OVal, e: &USubs, stk: &Stack) -> (Args, Stack) {
    let mut n = n;
    let mut tys = tys.clone();
    let mut e = e.clone();
    let mut stk = stk.clone();
    while let Some((nd, s)) = pop(&stk) {
        match &nd.hd {
            Z::Update(r) => {
                update(r, Red::Cstr, FTerm::Lambda(n, tys.clone(), f.clone(), e.clone()));
            }
            Z::Shift(k) => {
                e = usubs_shft(*k, &e);
            }
            Z::App(l) => {
                let na = l.len() as isize;
                if n == na {
                    return (Args::Subst(usubs_consn(l, 0, na as usize, &e)), s);
                } else if n < na {
                    let eargs: Rc<[FC]> = l[n as usize..].iter().cloned().collect();
                    return (Args::Subst(usubs_consn(l, 0, n as usize, &e)), s.cons(Z::App(eargs)));
                } else {
                    tys = tys.skipn(na as usize);
                    e = usubs_consn(l, 0, na as usize, &e);
                    n -= na;
                }
            }
            _ => break,
        }
        stk = s;
    }
    (Args::Lam(mk(Red::Cstr, FTerm::Lambda(n, tys, f.clone(), e))), stk)
}

/// Eta expansion: add a reference to implicit surrounding lambda at end of stack
pub fn eta_expand_stack(info: &Infos, na: &OVal, stk: &Stack) -> Stack {
    let arg = if is_irrelevant(info, &constr::binder_relevance(na)) {
        mk_irrelevant()
    } else {
        mk(Red::Ntrl, FTerm::Rel(1))
    };
    let tail = Stack::nil().cons(Z::App(Rc::from(vec![arg]))).cons(Z::Shift(1));
    stack_app(stk, &tail)
}

/* Native operators */

pub const KPARAM: isize = 0;
pub const KWHNF: isize = 1;

fn prim_info(info: &Infos, op: &OVal) -> (isize, Rc<Vec<isize>>) {
    let key = op.get();
    if op.is_long() {
        if let Some(r) = info.cache.prim_cache.borrow().get(&key) {
            return r.clone();
        }
    }
    let arity = call(&PRIM_ARITY, &[A::O(op)]).as_int();
    let kind: Vec<isize> = call(&PRIM_KIND, &[A::O(op)]).list_to_vec().iter().map(|k| k.as_int()).collect();
    let r = (arity, Rc::new(kind));
    if op.is_long() {
        info.cache.prim_cache.borrow_mut().insert(key, r.clone());
    }
    r
}

/// rargs in list order (head first)
fn skip_native_args(rargs: Vec<FC>, nargs: &[(isize, FC)]) -> (Vec<FC>, Vec<(isize, FC)>) {
    let mut rargs = rargs;
    let mut i = 0;
    while i < nargs.len() {
        let (kd, a) = &nargs[i];
        if *kd == KWHNF {
            return (rargs, nargs[i..].to_vec());
        }
        rargs.insert(0, a.clone());
        i += 1;
    }
    (rargs, vec![])
}

fn get_native_args(info: &Infos, op: &OVal, c: &TableKey, stk: &Stack) -> ((Vec<FC>, Vec<(isize, FC)>), Stack) {
    let (_, kargs0) = prim_info(info, op);
    /* rnargs: in list order, head is the last seen argument */
    let mut rnargs: Vec<(isize, FC)> = vec![];
    let mut kargs: Vec<isize> = kargs0.to_vec();
    let mut h = mk(Red::Red, FTerm::Flex(c.clone()));
    let mut stk = stk.clone();
    loop {
        let Some((nd, s)) = pop(&stk) else { panic!("assert false") };
        match &nd.hd {
            Z::Shift(k) => {
                rnargs = rnargs.iter().map(|(kd, f)| (*kd, lift_fconstr(*k, f))).collect();
                h = lift_fconstr(*k, &h);
                stk = s;
            }
            Z::App(args) => {
                let mut ai = 0;
                let mut ki = 0;
                while ki < kargs.len() && ai < args.len() {
                    rnargs.insert(0, (kargs[ki], args[ai].clone()));
                    ki += 1;
                    ai += 1;
                }
                let rest_k: Vec<isize> = kargs[ki..].to_vec();
                if rest_k.is_empty() {
                    let mut ordered = rnargs.clone();
                    ordered.reverse();
                    let r = skip_native_args(vec![], &ordered);
                    if ai == args.len() {
                        return (r, s);
                    } else {
                        let eargs: Rc<[FC]> = args[ai..].iter().cloned().collect();
                        return (r, s.cons(Z::App(eargs)));
                    }
                } else {
                    kargs = rest_k;
                    h = mk(h.mark(), FTerm::App(h.clone(), args.clone()));
                    stk = s;
                }
            }
            Z::Update(m) => {
                update(m, h.mark(), h.term_clone());
                h = m.clone();
                stk = s;
            }
            _ => panic!("assert false"),
        }
    }
}

fn get_native_args1(info: &Infos, op: &OVal, c: &TableKey, stk: &Stack) -> (Vec<FC>, FC, Vec<(isize, FC)>, Stack) {
    let ((rargs, nargs), stk) = get_native_args(info, op, c, stk);
    if nargs.is_empty() {
        panic!("assert false");
    }
    let (kd, a) = nargs[0].clone();
    assert!(kd == KWHNF);
    (rargs, a, nargs[1..].to_vec(), stk)
}

fn check_native_args(info: &Infos, op: &OVal, stk: &Stack) -> bool {
    let (nargs, _) = prim_info(info, op);
    nargs <= stack_args_size(stk) as isize
}

pub fn try_drop_parameters(n: isize, args: &Rc<[FC]>) -> Option<Rc<[FC]>> {
    let q = args.len() as isize;
    if n > q {
        None
    } else if q == 0 {
        Some(Rc::from(vec![]))
    } else {
        Some(args[n as usize..].iter().cloned().collect())
    }
}

pub fn drop_parameters(n: isize, args: &Rc<[FC]>) -> Rc<[FC]> {
    match try_drop_parameters(n, args) {
        Some(a) => a,
        None => anomaly(AN_PARTIAL_CTOR),
    }
}

/// [inductive_subst mib u pms] where [params] are the values of [mib.mind_params_ctxt]
pub fn inductive_subst(params: &OVal, u: &OVal, pms: &[FC]) -> USubs {
    let ctx = params.list_to_vec();
    let uinst = UInst::new(u.clone());
    fn mk_pms(i: isize, ctx: &[OVal], pms: &[FC], u: &UInst) -> Subs<SC> {
        if ctx.is_empty() {
            return subs_id(0);
        }
        match ctx[0].as_option() {
            None => {
                let subs = mk_pms(i - 1, &ctx[1..], pms, u);
                subs_cons(SC::Regular(pms[i as usize].clone()), &subs)
            }
            Some(c) => {
                let subs = mk_pms(i, &ctx[1..], pms, u);
                let v = mk_clos(&USubs { s: subs.clone(), u: u.clone() }, &c);
                subs_cons(SC::Regular(v), &subs)
            }
        }
    }
    let s = mk_pms(pms.len() as isize - 1, &ctx, pms, &uinst);
    USubs { s, u: uinst }
}

pub fn mind_params(info: &Infos, ind: &OVal) -> OVal {
    call(&MIND_PARAMS, &[A::O(info.env()), A::O(ind)])
}

/// [ctx] is a list of [constr option] (most recent first)
fn args_subst(ind_subst: &USubs, ctx: &OVal, args: &Rc<[FC]>, e: &USubs) -> USubs {
    let mut ctx = ctx.list_to_vec();
    ctx.reverse();
    let mut asub = e.clone();
    let mut isub = ind_subst.clone();
    let mut i = 0;
    for d in ctx {
        match d.as_option() {
            None => {
                let c = args[i].clone();
                asub = usubs_cons(&c, &asub);
                isub = usubs_cons(&c, &isub);
                i += 1;
            }
            Some(b) => {
                let c = mk_clos(&isub, &b);
                asub = usubs_cons(&c, &asub);
                isub = usubs_cons(&c, &isub);
            }
        }
    }
    assert!(args.len() == i);
    asub
}

/// [ctx] is a list of [constr option] (most recent first)
pub fn esubst_of_context(ctx: &OVal, args: &USubs, e: &USubs) -> (isize, USubs) {
    let mut ctx = ctx.list_to_vec();
    ctx.reverse();
    let mut lft = 0;
    let mut e = e.clone();
    let mut args = args.clone();
    for d in ctx {
        match d.as_option() {
            None => {
                lft += 1;
                e = usubs_lift(&e);
                args = usubs_lift(&args);
            }
            Some(c) => {
                let c = mk_clos(&args, &c);
                e = usubs_cons(&c, &e);
                args = usubs_cons(&c, &args);
            }
        }
    }
    (lft, e)
}

/// Iota-reduction: feed the arguments of the constructor to the branch
fn get_branch(info: &Infos, ci: &OVal, pms: &OVal, cstr: &OVal, u: &UInst, args: &Rc<[FC]>, br: &OVal, e: &USubs) -> (OVal, USubs) {
    let c = cstr.field_int(1);
    let i = (c - 1) as usize;
    let args = drop_parameters(constr::ci_npar(ci), args);
    let br = br.field(i).field(1);
    if constr::ci_cstr_ndecls(ci, i) == constr::ci_cstr_nargs(ci, i) {
        let e = usubs_consv(&args, e);
        (br, e)
    } else {
        let ind = cstr.field(0);
        let ctx = call(&CTOR_CTX, &[A::O(info.env()), A::O(&ind), A::I(i as isize)]);
        let params = mind_params(info, &ind);
        let fpms: Vec<FC> = (0..pms.size()).map(|j| mk_clos(e, &pms.field(j))).collect();
        let ind_subst = inductive_subst(&params, &u.v, &fpms);
        let e = args_subst(&ind_subst, &ctx, &args, e);
        (br, e)
    }
}

/// [eta_expand_ind_stack env (ind,u) args m'] where m' = (hd, stk)
pub fn eta_expand_ind_stack(info: &Infos, ind: &OVal, u: &UInst, args: &Rc<[FC]>, hd: &FC, stk: &Stack) -> Option<(Stack, Stack)> {
    let r = call(&ETA_RECORD, &[A::O(info.env()), A::O(ind), A::O(&u.v)]);
    let r = r.as_option()?;
    let pars = r.field_int(0);
    let projs = r.field(1);
    let right = zip(hd, stk);
    let argss = try_drop_parameters(pars, args)?;
    if projs.size() != argss.len() {
        return None;
    }
    let hstack: Rc<[FC]> = (0..projs.size())
        .map(|i| {
            let pr = projs.field(i);
            mk(Red::Red, FTerm::Proj(pr.field(0), pr.field(1), right.clone()))
        })
        .collect();
    Some((Stack::nil().cons(Z::App(argss)), Stack::nil().cons(Z::App(hstack))))
}

/// Iota reduction: expansion of a fixpoint.
pub fn contract_fix_vect(fix: &FTerm) -> (USubs, OVal) {
    let (fx, env, is_fix) = match fix {
        FTerm::Fix(fx, env) => (fx, env, true),
        FTerm::CoFix(fx, env) => (fx, env, false),
        _ => panic!("assert false"),
    };
    let bds = fx.bodies();
    let thisbody = bds.field(fx.i as usize);
    let nfix = bds.size();
    let mut s = env.s.clone();
    for j in 0..nfix {
        let fj = FixData { ri: fx.ri.clone(), i: j as isize, rdcl: fx.rdcl.clone() };
        let b = if is_fix {
            mk(Red::Cstr, FTerm::Fix(fj, env.clone()))
        } else {
            mk(Red::Cstr, FTerm::CoFix(fj, env.clone()))
        };
        s = subs_cons(SC::Regular(b), &s);
    }
    (USubs { s, u: env.u.clone() }, thisbody)
}

pub fn unfold_projection(info: &Infos, p: &OVal, r: &OVal) -> Option<Z> {
    let o = call(&UNFOLD_PROJECTION, &[A::O(&info.flags.v()), A::O(p)]);
    o.as_option().map(|repr| Z::Proj(repr, r.clone()))
}

pub fn skip_irrelevant_stack(info: &Infos, stk: &Stack) -> Stack {
    let mut stk = stk.clone();
    loop {
        let Some((nd, s)) = pop(&stk) else { return Stack::nil() };
        match &nd.hd {
            Z::Shift(_) | Z::App(_) => (),
            Z::Fix(..) | Z::Proj(..) => (),
            Z::CaseT(cd) => {
                let r = usubst_relevance(&cd.e, &cd.p.field(1));
                if !is_irrelevant(info, &r) {
                    return stk;
                }
            }
            Z::Primitive(..) => panic!("assert false"),
            Z::Update(m) => {
                let irr = mk_irrelevant();
                update(m, irr.mark(), irr.term_clone());
            }
        }
        stk = s;
    }
}

fn is_irrelevant_constructor(info: &Infos, cstr: &OVal, u: &UInst) -> bool {
    if !info.cache.irr_inds {
        return false;
    }
    let ind = cstr.field(0);
    let r = call(&IND_RELEVANCE, &[A::O(info.env()), A::O(&ind), A::O(&u.v)]);
    is_irrelevant(info, &r)
}

/* The head machine */

enum H {
    H(FC, Stack),
    T(USubs, OVal, Stack),
}

pub fn knh(info: &Infos, m: &FC, stk: &Stack) -> (FC, Stack) {
    knh_gen(info, H::H(m.clone(), stk.clone()))
}

pub fn knht(info: &Infos, e: &USubs, t: &OVal, stk: &Stack) -> (FC, Stack) {
    knh_gen(info, H::T(e.clone(), t.clone(), stk.clone()))
}

fn irr_ret(info: &Infos, stk: &Stack) -> (FC, Stack) {
    (mk_irrelevant(), skip_irrelevant_stack(info, stk))
}

fn knh_gen(info: &Infos, st: H) -> (FC, Stack) {
    let mut st = st;
    loop {
        st = match st {
            H::H(m, stk) => {
                /* The term of [m] is only borrowed while deciding what to do,
                   since [zupdate] overwrites it. */
                enum Act {
                    Go(H),
                    Ret(Stack),
                    Irr,
                    Absorb,
                    Clos(OVal, USubs),
                    App(FC, Rc<[FC]>),
                    CaseT(Rc<CaseData>, FC),
                    Proj(FC, Z),
                }
                let act = {
                    let t = m.term();
                    match &*t {
                        FTerm::Lift(k, a) => Act::Go(H::H(a.clone(), zshift(*k, &stk))),
                        FTerm::Clos(t, e) => Act::Clos(t.clone(), e.clone()),
                        FTerm::Locked => panic!("assert false"),
                        FTerm::App(a, b) => Act::App(a.clone(), b.clone()),
                        FTerm::CaseT(cd, t) => {
                            let r2 = usubst_relevance(&cd.e, &cd.p.field(1));
                            if is_irrelevant(info, &r2) {
                                Act::Irr
                            } else {
                                Act::CaseT(cd.clone(), t.clone())
                            }
                        }
                        FTerm::Fix(fx, e) => {
                            let na = fx.names().field(fx.i as usize);
                            if is_irrelevant(info, &usubst_relevance(e, &constr::binder_relevance(&na))) {
                                Act::Irr
                            } else {
                                let rarg = fx.rec_arg(fx.i);
                                drop(t);
                                match get_nth_arg(&m, rarg, &stk) {
                                    (Some((pars, arg)), stk2) => Act::Go(H::H(arg, stk2.cons_owned(Z::Fix(m.clone(), pars)))),
                                    (None, stk2) => Act::Ret(stk2),
                                }
                            }
                        }
                        FTerm::Proj(p, r, c) => {
                            if is_irrelevant(info, r) {
                                Act::Irr
                            } else {
                                match unfold_projection(info, p, r) {
                                    None => Act::Ret(stk.clone()),
                                    Some(z) => Act::Proj(c.clone(), z),
                                }
                            }
                        }
                        FTerm::Construct(..) => Act::Absorb,
                        _ => Act::Ret(stk.clone()),
                    }
                };
                match act {
                    Act::Go(h) => h,
                    Act::Ret(stk) => return (m, stk),
                    Act::Irr => return irr_ret(info, &stk),
                    Act::Absorb => return strip_update_shift_absorb_app(&m, &stk),
                    Act::Clos(t, e) => {
                        let s = zupdate(info, &m, &stk);
                        H::T(e, t, s)
                    }
                    Act::App(a, b) => {
                        let s = zupdate(info, &m, &stk);
                        H::H(a, append_stack(&b, &s))
                    }
                    Act::CaseT(cd, t) => {
                        let s = zupdate(info, &m, &stk);
                        H::H(t, s.cons_owned(Z::CaseT(cd)))
                    }
                    Act::Proj(c, z) => {
                        let s2 = zupdate(info, &m, &stk);
                        H::H(c, s2.cons_owned(z))
                    }
                }
            }
            H::T(e, t, stk) => match constr::kind(&t) {
                constr::REL => match clos_rel(&e.s, constr::dest_rel(&t)) {
                    SC::Regular(v) => H::H(v, stk),
                    SC::HigherOrder(..) => anomaly(AN_PATTERN_VAR),
                },
                constr::APP => {
                    let (f, args) = constr::dest_app(&t);
                    if constr::kind(&f) == constr::REL {
                        let n = constr::dest_rel(&f);
                        let args = mk_clos_vect(&e, &args);
                        match clos_rel(&e.s, n) {
                            SC::Regular(t) => H::H(t, append_stack(&args, &stk)),
                            SC::HigherOrder(nargs, term) => {
                                let nargs = nargs as usize;
                                let subs1 = &args[0..nargs];
                                let rest: Rc<[FC]> = args[nargs..].iter().cloned().collect();
                                let mut s: Subs<SC> = subs_id(info.relevances.length());
                                for v in subs1 {
                                    s = subs_cons(SC::Regular(v.clone()), &s);
                                }
                                let head = resubst(&s, &term);
                                H::H(head, append_stack(&rest, &stk))
                            }
                        }
                    } else {
                        let args = mk_clos_vect(&e, &args);
                        H::T(e.clone(), f, append_stack(&args, &stk))
                    }
                }
                constr::CASE => {
                    let p = t.field(3);
                    let r = p.field(1);
                    if is_irrelevant(info, &usubst_relevance(&e, &r)) {
                        return irr_ret(info, &stk);
                    }
                    let iv = t.field(4);
                    let cd = Rc::new(CaseData {
                        ci: t.field(0),
                        u: t.field(1),
                        pms: t.field(2),
                        p,
                        br: t.field(6),
                        e: e.clone(),
                    });
                    if iv.is_long() {
                        H::T(e, t.field(5), stk.cons(Z::CaseT(cd)))
                    } else {
                        let indices = iv.field(0);
                        let c = mk_clos(&e, &t.field(5));
                        let indices = mk_clos_vect(&e, &indices);
                        return (mk(Red::Red, FTerm::CaseInvert(cd, indices, c)), stk);
                    }
                }
                constr::FIX => {
                    let fx = FixData::of_fix(&t.field(0));
                    let na = fx.names().field(fx.i as usize);
                    if is_irrelevant(info, &usubst_relevance(&e, &constr::binder_relevance(&na))) {
                        return irr_ret(info, &stk);
                    }
                    H::H(mk(Red::Cstr, FTerm::Fix(fx, e)), stk)
                }
                constr::CAST => H::T(e, t.field(0), stk),
                constr::PROJ => {
                    let p = t.field(0);
                    let r = usubst_relevance(&e, &t.field(1));
                    if is_irrelevant(info, &r) {
                        return irr_ret(info, &stk);
                    }
                    match unfold_projection(info, &p, &r) {
                        None => {
                            let c = mk_clos(&e, &t.field(2));
                            return (mk(Red::Red, FTerm::Proj(p, r, c)), stk);
                        }
                        Some(s) => H::T(e, t.field(2), stk.cons(s)),
                    }
                }
                constr::CONSTRUCT => H::H(mk_clos(&e, &t), stk),
                constr::IND | constr::CONST | constr::VAR | constr::META | constr::SORT | constr::INT | constr::FLOAT | constr::STRING => {
                    return (mk_clos(&e, &t), stk)
                }
                constr::COFIX => {
                    let fx = FixData::of_cofix(&t.field(0));
                    return (mk(Red::Cstr, FTerm::CoFix(fx, e)), stk);
                }
                constr::LAMBDA => return (mk(Red::Cstr, mk_lambda(&e, &t)), stk),
                constr::PROD => {
                    let dom = mk_clos(&e, &t.field(1));
                    return (mk(Red::Ntrl, FTerm::Prod(t.field(0), dom, t.field(2), e)), stk);
                }
                constr::LETIN => {
                    let ty = mk_clos(&e, &t.field(2));
                    let b = mk_clos(&e, &t.field(1));
                    return (mk(Red::Red, FTerm::LetIn(t.field(0), b, ty, t.field(3), e)), stk);
                }
                constr::EVAR => {
                    let ev = t.field(0);
                    let r = call(&EVAR_EXPAND, &[A::O(&info.cache.evars), A::O(&ev)]);
                    if r.tag() == 0 {
                        H::T(e, r.field(0), stk)
                    } else {
                        let evk = r.field(0);
                        let args = r.field(1);
                        assert!(e.u.empty);
                        if call(&EVAR_IRRELEVANT, &[A::O(&info.cache.evars), A::O(&ev)]).as_bool() {
                            return irr_ret(info, &stk);
                        }
                        return (mk(Red::Ntrl, FTerm::Evar(evk, args, e)), stk);
                    }
                }
                constr::ARRAY => {
                    let u = UInst::new(usubst_instance(&e, &t.field(0)));
                    let elems = t.field(1);
                    let ty = mk_clos(&e, &t.field(3));
                    let hs: Vec<OVal> = (0..elems.size()).map(|i| crate::ffi::fc_to_handle(&mk_clos(&e, &elems.field(i)))).collect();
                    let def = crate::ffi::fc_to_handle(&mk_clos(&e, &t.field(2)));
                    let arr = crate::ffi::alloc_array(&hs);
                    let pa = call(&PARRAY_OF_ARRAY, &[A::O(&arr), A::O(&def)]);
                    H::H(mk(Red::Cstr, FTerm::Array(u, pa, ty, 0)), stk)
                }
                _ => panic!("unknown constr tag"),
            },
        }
    }
}

/* Substitution of pattern variables (rewrite rules) */

fn lift_union(k: isize, x: &SC) -> SC {
    match x {
        SC::Regular(v) => SC::Regular(lift_fconstr(k, v)),
        SC::HigherOrder(n, v) => SC::HigherOrder(*n, relift_fconstr(k, *n, v)),
    }
}

fn resubst_union(subs: &Subs<SC>, x: &SC) -> SC {
    match x {
        SC::Regular(v) => SC::Regular(resubst(subs, v)),
        SC::HigherOrder(..) => panic!("assert false"),
    }
}

fn comp_subs(subs: &Subs<SC>, s: &USubs) -> USubs {
    let s2 = comp(&mut |s1: &Subs<SC>, x: &SC| resubst_union(s1, x), &mut |k, x: &SC| lift_union(k, x), subs, &s.s);
    USubs { s: s2, u: s.u.clone() }
}

pub fn resubst(subs: &Subs<SC>, v: &FC) -> FC {
    let t = v.term();
    match &*t {
        FTerm::Rel(i) => match clos_rel(subs, *i) {
            SC::Regular(v) => v,
            SC::HigherOrder(..) => anomaly(AN_PATTERN_VAR),
        },
        FTerm::App(f, ve) => {
            let ft = f.term();
            if let FTerm::Rel(i) = &*ft {
                let args: Vec<FC> = ve.iter().map(|x| resubst(subs, x)).collect();
                match clos_rel(subs, *i) {
                    SC::Regular(t) => with_term(v, FTerm::App(t, args.into())),
                    SC::HigherOrder(nargs, term) => {
                        let nargs = nargs as usize;
                        let mut s: Subs<SC> = subs_id(0);
                        for x in &args[0..nargs] {
                            s = subs_cons(SC::Regular(x.clone()), &s);
                        }
                        let rest: Rc<[FC]> = args[nargs..].iter().cloned().collect();
                        let head = resubst(&s, &term);
                        with_term(v, FTerm::App(head, rest))
                    }
                }
            } else {
                let f2 = resubst(subs, f);
                let ve: Rc<[FC]> = ve.iter().map(|x| resubst(subs, x)).collect();
                with_term(v, FTerm::App(f2, ve))
            }
        }
        FTerm::CaseT(cd, c) => {
            let env = comp_subs(subs, &cd.e);
            with_term(v, FTerm::CaseT(case_data_with_e(cd, env), resubst(subs, c)))
        }
        FTerm::CaseInvert(cd, indices, c) => {
            let env = comp_subs(subs, &cd.e);
            let indices: Rc<[FC]> = indices.iter().map(|x| resubst(subs, x)).collect();
            with_term(v, FTerm::CaseInvert(case_data_with_e(cd, env), indices, resubst(subs, c)))
        }
        FTerm::Fix(fx, e) => with_term(v, FTerm::Fix(fx.clone(), comp_subs(subs, e))),
        FTerm::CoFix(fx, e) => with_term(v, FTerm::CoFix(fx.clone(), comp_subs(subs, e))),
        FTerm::Proj(p, r, c) => with_term(v, FTerm::Proj(p.clone(), r.clone(), resubst(subs, c))),
        FTerm::Lambda(len, tys, f, e) => with_term(v, FTerm::Lambda(*len, tys.clone(), f.clone(), comp_subs(subs, e))),
        FTerm::Prod(na, t, c, e) => {
            let e = comp_subs(subs, e);
            with_term(v, FTerm::Prod(na.clone(), resubst(subs, t), c.clone(), e))
        }
        FTerm::LetIn(na, b, t, f, e) => {
            let e = comp_subs(subs, e);
            with_term(v, FTerm::LetIn(na.clone(), resubst(subs, b), resubst(subs, t), f.clone(), e))
        }
        FTerm::Evar(ev, args, env) => with_term(v, FTerm::Evar(ev.clone(), args.clone(), comp_subs(subs, env))),
        FTerm::Lift(k, a) => resubst(&subs_popn(*k, subs), a),
        FTerm::Array(u, t, ty, lft) => {
            let subs = subs_popn(*lft, subs);
            let t = parray_map(t, &mut |x| resubst(&subs, x));
            let ty = resubst(&subs, ty);
            with_term(v, FTerm::Array(u.clone(), t, ty, 0))
        }
        FTerm::Clos(t, env) => with_term(v, FTerm::Clos(t.clone(), comp_subs(subs, env))),
        FTerm::Flex(TableKey::Rel(_)) => v.clone(),
        FTerm::Flex(_) | FTerm::Ind(..) | FTerm::Construct(..) | FTerm::Atom(_) | FTerm::Int(_) | FTerm::Float(_) | FTerm::String(_) => v.clone(),
        FTerm::Irrelevant => v.clone(),
        FTerm::Locked => panic!("assert false"),
    }
}

/* The reduction machine */

pub enum St {
    Kni(FC, Stack, pattern::PS),
    Knit(USubs, OVal, Stack, pattern::PS),
    Ret(FC, Stack, bool, pattern::PS),
    Final(Option<(FC, Stack)>),
}

pub fn kn_loop(info: &Infos, tab: &Tab, st: St) -> Option<(FC, Stack)> {
    let mut st = st;
    loop {
        st = match st {
            St::Kni(m, stk, ps) => {
                let (hm, s) = knh(info, &m, &stk);
                knr(info, tab, ps, &hm, &s)
            }
            St::Knit(e, t, stk, ps) => {
                let (ht, s) = knht(info, &e, &t, &stk);
                knr(info, tab, ps, &ht, &s)
            }
            St::Ret(m, stk, failed, ps) => match ps {
                pattern::PS::Cons(patt, rest) => pattern::match_head_resume(info, tab, (*rest).clone(), &patt, &m, &stk),
                pattern::PS::Nil(yes) => {
                    if yes && failed {
                        return None;
                    } else {
                        return Some((m, stk));
                    }
                }
            },
            St::Final(r) => return r,
        }
    }
}

pub fn kni(info: &Infos, tab: &Tab, m: &FC, stk: &Stack) -> (FC, Stack) {
    kn_loop(info, tab, St::Kni(m.clone(), stk.clone(), pattern::PS::Nil(false))).unwrap()
}

fn knr(info: &Infos, tab: &Tab, ps: pattern::PS, m: &FC, stk: &Stack) -> St {
    /* A copy: stripping the stack may update [m] itself, e.g. for the
       [Zupdate a] pushed by [unfold_ref_with_args]. */
    let t = &m.term_clone();
    match t {
        FTerm::Lambda(n, tys, f, e) if info.flags.red_set(F_BETA) => match get_args(*n, tys, f, e, stk) {
            (Args::Subst(e2), s) => St::Knit(e2, f.clone(), s, ps),
            (Args::Lam(lam), s) => St::Ret(lam, s, false, ps),
        },
        FTerm::Flex(fl) if info.flags.red_set(F_DELTA) => {
            let v = table_lookup(info, tab, fl);
            match &*v {
                TableVal::Def(v, _) => St::Kni(v.clone(), stk.clone(), ps),
                TableVal::Primitive(op) => {
                    if check_native_args(info, op, stk) {
                        let (c, u) = match fl {
                            TableKey::Const(c, u) => (c.clone(), u.clone()),
                            _ => panic!("assert false"),
                        };
                        let (rargs, a, nargs, stk) = get_native_args1(info, op, fl, stk);
                        St::Kni(a, stk.cons(Z::Primitive(op.clone(), c, u, Rc::new(rargs), Rc::new(nargs))), ps)
                    } else {
                        St::Ret(m.clone(), stk.clone(), false, ps)
                    }
                }
                TableVal::Symbol(u, b, r) => pattern::match_symbol(info, tab, ps, fl, u, *b, r, stk),
                TableVal::Undef => {
                    set_ntrl(m);
                    St::Ret(m.clone(), stk.clone(), false, ps)
                }
            }
        }
        FTerm::Construct(c, u, args) => {
            let use_match = info.flags.red_set(F_MATCH);
            let use_fix = info.flags.red_set(F_FIX);
            match stk.uncons() {
                Some((Z::Shift(_), _)) | Some((Z::Update(_), _)) | Some((Z::App(_), _)) => panic!("assert false"),
                Some((Z::CaseT(cd), s)) if use_match => {
                    let (br, e) = get_branch(info, &cd.ci, &cd.pms, c, u, args, &cd.br, &cd.e);
                    St::Knit(e, br, s.clone(), ps)
                }
                Some((Z::Fix(fx, par), s)) if use_fix => {
                    let a: Rc<[FC]> = Rc::from(vec![m.clone()]);
                    let stk2 = stack_app(par, &append_stack(&a, s));
                    let (fxe, fxbd) = contract_fix_vect(&fx.term());
                    St::Knit(fxe, fxbd, stk2, ps)
                }
                Some((Z::Proj(p, _), s)) if use_match => {
                    let rargs = drop_parameters(p.field_int(1), args);
                    let rarg = rargs[p.field_int(2) as usize].clone();
                    St::Kni(rarg, s.clone(), ps)
                }
                _ => {
                    if is_irrelevant_constructor(info, c, u) {
                        St::Ret(mk_irrelevant(), skip_irrelevant_stack(info, stk), false, ps)
                    } else {
                        St::Ret(m.clone(), stk.clone(), false, ps)
                    }
                }
            }
        }
        FTerm::CoFix(fx, e) => {
            let na = fx.names().field(fx.i as usize);
            if is_irrelevant(info, &usubst_relevance(e, &constr::binder_relevance(&na))) {
                St::Ret(mk_irrelevant(), skip_irrelevant_stack(info, stk), false, ps)
            } else if info.flags.red_set(F_COFIX) {
                let (_, _, args, stk2) = strip_update_shift_app(m, stk);
                match stk2.uncons() {
                    Some((Z::CaseT(_), _)) | Some((Z::Proj(..), _)) => {
                        let (fxe, fxbd) = contract_fix_vect(&m.term());
                        St::Knit(fxe, fxbd, stack_app(&args, &stk2), ps)
                    }
                    _ => St::Ret(m.clone(), stack_app(&args, &stk2), false, ps),
                }
            } else {
                St::Ret(m.clone(), stk.clone(), false, ps)
            }
        }
        FTerm::LetIn(_, v, _, bd, e) if info.flags.red_set(F_ZETA) => St::Knit(usubs_cons(v, e), bd.clone(), stk.clone(), ps),
        FTerm::Int(_) | FTerm::Float(_) | FTerm::String(_) | FTerm::Array(..) => {
            let (depth, m2, _, stk2) = strip_update_shift_app(m, stk);
            if let Some((Z::Primitive(op, c, u, rargs, nargs), s)) = stk2.uncons() {
                let mut ra: Vec<FC> = rargs.to_vec();
                ra.insert(0, m2.clone());
                let (rargs, nargs) = skip_native_args(ra, nargs);
                if nargs.is_empty() {
                    let hs: Vec<OVal> = rargs.iter().rev().map(crate::ffi::fc_to_handle).collect();
                    let arr = crate::ffi::alloc_array(&hs);
                    let r = call(&RED_PRIM, &[A::O(info.env()), A::O(op), A::O(&u.v), A::O(&arr)]);
                    match r.as_option() {
                        Some(h) => St::Kni(handle_to_fc(&h), s.clone(), ps),
                        None => panic!("assert false"),
                    }
                } else {
                    let (kd, a) = nargs[0].clone();
                    assert!(kd == KWHNF);
                    let z = Z::Primitive(op.clone(), c.clone(), u.clone(), Rc::new(rargs), Rc::new(nargs[1..].to_vec()));
                    St::Kni(a, s.cons(z), ps)
                }
            } else {
                St::Ret(m.clone(), zshift(depth, &stk2), false, ps)
            }
        }
        FTerm::CaseInvert(cd, iv, _c) if info.flags.red_set(F_MATCH) => {
            match case_inversion(info, tab, cd, iv) {
                Some(c) => St::Knit(cd.e.clone(), c, stk.clone(), ps),
                None => St::Ret(m.clone(), stk.clone(), false, ps),
            }
        }
        FTerm::Irrelevant => {
            let stk = skip_irrelevant_stack(info, stk);
            St::Ret(m.clone(), stk, false, ps)
        }
        FTerm::Prod(..)
        | FTerm::Atom(_)
        | FTerm::Ind(..)
        | FTerm::CaseInvert(..)
        | FTerm::Proj(..)
        | FTerm::Fix(..)
        | FTerm::Evar(..)
        | FTerm::Lambda(..)
        | FTerm::Flex(_)
        | FTerm::Rel(_)
        | FTerm::LetIn(..) => St::Ret(m.clone(), stk.clone(), false, ps),
        FTerm::Locked | FTerm::Clos(..) | FTerm::App(..) | FTerm::CaseT(..) | FTerm::Lift(..) => panic!("assert false"),
    }
}

fn case_inversion(info: &Infos, tab: &Tab, cd: &CaseData, indices: &Rc<[FC]>) -> Option<OVal> {
    let brs = &cd.br;
    if brs.size() == 0 {
        return None;
    }
    if brs.size() != 1 || brs.field(0).field(0).size() != 0 {
        panic!("assert false");
    }
    let v = brs.field(0).field(1);
    if indices.is_empty() {
        return Some(v);
    }
    let env = &cd.e;
    let u = UInst::new(usubst_instance(env, &cd.u));
    let pms = mk_clos_vect(env, &cd.pms);
    let npar = constr::ci_npar(&cd.ci) as usize;
    let psubst = subs_consn(&pms, 0, npar, &subs_id(0));
    let ind = constr::ci_ind(&cd.ci);
    let bidx = call(&INVERSION_INDICES, &[A::O(info.env()), A::O(&ind), A::I(npar as isize)]);
    let pe = USubs { s: psubst, u };
    let branch_indices: Vec<FC> = (0..bidx.size()).map(|i| mk_clos(&pe, &bidx.field(i))).collect();
    let irr = mk_irrelevant();
    let branch_subs = usubs_cons(&irr, &usubs_consv(&branch_indices, env));
    let external_subs = usubs_cons(&irr, &usubs_consv(indices, env));
    let p = cd.p.field(0).field(1);
    let branch_type = mk_clos(&branch_subs, &p);
    let external_type = mk_clos(&external_subs, &p);
    let info2 = info.with_reds(&info.cache.all);
    if crate::conversion::conv_inner(&info2, tab, &branch_type, &external_type) {
        Some(v)
    } else {
        None
    }
}

pub fn whd_stack(infos: &Infos, tab: &Tab, m: &FC, stk: &Stack) -> (FC, Stack) {
    match m.mark() {
        Red::Ntrl => knh(infos, m, stk),
        Red::Red | Red::Cstr => {
            let (m2, stk2) = kni(infos, tab, m, stk);
            if infos.cache.share && !(Rc::ptr_eq(m, &m2) && stk.ptr_eq(&stk2)) {
                zip(&m2, &stk2);
            }
            (m2, stk2)
        }
    }
}

pub fn unfold_ref_with_args(infos: &Infos, tab: &Tab, fl: &TableKey, v: &Stack) -> Option<(FC, Stack)> {
    let tv = table_lookup(infos, tab, fl);
    match &*tv {
        TableVal::Def(def, _) => Some((def.clone(), v.clone())),
        TableVal::Primitive(op) if check_native_args(infos, op, v) => {
            let (c, u) = match fl {
                TableKey::Const(c, u) => (c.clone(), u.clone()),
                _ => panic!("assert false"),
            };
            let (rargs, a, nargs, v) = get_native_args1(infos, op, fl, v);
            let s = v.cons(Z::Primitive(op.clone(), c, u, Rc::new(rargs), Rc::new(nargs))).cons(Z::Update(a.clone()));
            Some((a, s))
        }
        TableVal::Symbol(u, b, r) => {
            let infos2 = infos.with_reds(&infos.cache.all);
            let st = pattern::match_symbol(&infos2, tab, pattern::PS::Nil(true), fl, u, *b, r, v);
            kn_loop(&infos2, tab, st)
        }
        _ => None,
    }
}

#[inline(never)]
pub fn get_ref_mask(info: &Infos, tab: &Tab, fl: &TableKey) -> Option<OVal> {
    match &*table_lookup(info, tab, fl) {
        TableVal::Def(_, mask) => mask.clone(),
        _ => None,
    }
}
