//! Port of kernel/esubst.ml (lifts and explicit substitutions).

use std::rc::Rc;

/* Lifts */

pub enum LiftNode {
    Shft(Lift, isize),
    Lft(isize, Lift),
}

/// [ELID] is [None]; one word.
#[derive(Clone)]
pub struct Lift(Option<Rc<LiftNode>>);

fn shft(el: Lift, n: isize) -> Lift {
    Lift(Some(Rc::new(LiftNode::Shft(el, n))))
}

fn lft(n: isize, el: Lift) -> Lift {
    Lift(Some(Rc::new(LiftNode::Lft(n, el))))
}

pub fn el_id() -> Lift {
    Lift(None)
}

pub fn eq_lift(a: &Lift, b: &Lift) -> bool {
    match (&a.0, &b.0) {
        (None, None) => true,
        (Some(x), Some(y)) => match (&**x, &**y) {
            (LiftNode::Shft(a, i), LiftNode::Shft(b, j)) => i == j && eq_lift(a, b),
            (LiftNode::Lft(i, a), LiftNode::Lft(j, b)) => i == j && eq_lift(a, b),
            _ => false,
        },
        _ => false,
    }
}

fn el_shft_rec(n: isize, el: &Lift) -> Lift {
    if let Some(x) = &el.0 {
        if let LiftNode::Shft(el2, k) = &**x {
            return shft(el2.clone(), k + n);
        }
    }
    shft(el.clone(), n)
}

pub fn el_shft(n: isize, el: &Lift) -> Lift {
    if n == 0 {
        el.clone()
    } else {
        el_shft_rec(n, el)
    }
}

fn el_liftn_rec(n: isize, el: &Lift) -> Lift {
    match &el.0 {
        None => Lift(None),
        Some(x) => match &**x {
            LiftNode::Lft(k, el2) => lft(n + k, el2.clone()),
            LiftNode::Shft(..) => lft(n, el.clone()),
        },
    }
}

pub fn el_liftn(n: isize, el: &Lift) -> Lift {
    if n == 0 {
        el.clone()
    } else {
        el_liftn_rec(n, el)
    }
}

pub fn el_lift(el: &Lift) -> Lift {
    el_liftn_rec(1, el)
}

pub fn reloc_rel(n: isize, el: &Lift) -> isize {
    let mut n = n;
    let mut el = el;
    let mut acc = 0;
    loop {
        match &el.0 {
            None => return n + acc,
            Some(x) => match &**x {
                LiftNode::Lft(k, e) => {
                    if n <= *k {
                        return n + acc;
                    } else {
                        n -= k;
                        acc += k;
                        el = e;
                    }
                }
                LiftNode::Shft(e, k) => {
                    n += k;
                    el = e;
                }
            },
        }
    }
}

/* Substitutions */

pub enum OrVar<T> {
    Arg(T),
    Var(isize),
}

impl<T: Clone> Clone for OrVar<T> {
    fn clone(&self) -> Self {
        match self {
            OrVar::Arg(x) => OrVar::Arg(x.clone()),
            OrVar::Var(i) => OrVar::Var(*i),
        }
    }
}

pub enum Tree<T> {
    Leaf(isize, OrVar<T>),
    Node(isize, OrVar<T>, Rc<Tree<T>>, Rc<Tree<T>>, isize),
}

pub enum SubsNode<T> {
    Nil(isize, isize),
    Cons(isize, Rc<Tree<T>>, Subs<T>),
}

pub struct Subs<T>(pub Rc<SubsNode<T>>);

impl<T> Clone for Subs<T> {
    fn clone(&self) -> Self {
        Subs(self.0.clone())
    }
}

impl<T> Subs<T> {
    pub fn ptr_eq(&self, o: &Subs<T>) -> bool {
        Rc::ptr_eq(&self.0, &o.0)
    }
}

pub enum Either<A, B> {
    Inl(A),
    Inr(B),
}

fn eval<T>(t: &Tree<T>) -> isize {
    match t {
        Tree::Leaf(w, _) => *w,
        Tree::Node(w1, _, _, _, w2) => w1 + w2,
    }
}

fn leaf<T>(x: OrVar<T>) -> Tree<T> {
    Tree::Leaf(0, x)
}

fn node<T>(x: OrVar<T>, t1: Rc<Tree<T>>, t2: Rc<Tree<T>>) -> Tree<T> {
    let w = eval(&t1) + eval(&t2);
    Tree::Node(0, x, t1, t2, w)
}

fn tree_get<T: Clone>(h: isize, w: isize, t: &Tree<T>, i: isize) -> (isize, OrVar<T>) {
    let mut h = h;
    let mut w = w;
    let mut t = t;
    let mut i = i;
    loop {
        match t {
            Tree::Leaf(w2, x) => {
                let w = w + w2;
                if i == 0 {
                    return (w, x.clone());
                } else {
                    panic!("assert false")
                }
            }
            Tree::Node(w2, x, t1, t2, _) => {
                w += w2;
                if i == 0 {
                    return (w, x.clone());
                }
                h /= 2;
                if i <= h {
                    t = t1;
                    i -= 1;
                } else {
                    w += eval(t1);
                    t = t2;
                    i = i - h - 1;
                }
            }
        }
    }
}

fn get<T: Clone>(l: &Subs<T>, i: isize) -> (isize, Either<OrVar<T>, isize>) {
    let mut w = 0;
    let mut l = l;
    let mut i = i;
    loop {
        match &*l.0 {
            SubsNode::Nil(w2, n) => {
                let w = w + w2;
                if i < *n {
                    return (w, Either::Inl(OrVar::Var(i + 1)));
                } else {
                    return (n + w, Either::Inr(i - n));
                }
            }
            SubsNode::Cons(h, t, rem) => {
                if i < *h {
                    let (w, x) = tree_get(*h, w, t, i);
                    return (w, Either::Inl(x));
                } else {
                    w = eval(t) + w;
                    i -= h;
                    l = rem;
                }
            }
        }
    }
}

fn tree_write<T: Clone>(w: isize, t: &Tree<T>) -> Tree<T> {
    match t {
        Tree::Leaf(w2, x) => Tree::Leaf(w + w2, x.clone()),
        Tree::Node(w2, x, t1, t2, wt) => Tree::Node(w + w2, x.clone(), t1.clone(), t2.clone(), *wt),
    }
}

fn write<T: Clone>(w: isize, l: &Subs<T>) -> Subs<T> {
    match &*l.0 {
        SubsNode::Nil(w2, n) => Subs(Rc::new(SubsNode::Nil(w + w2, *n))),
        SubsNode::Cons(h, t, rem) => Subs(Rc::new(SubsNode::Cons(*h, Rc::new(tree_write(w, t)), rem.clone()))),
    }
}

fn cons<T: Clone>(x: OrVar<T>, l: &Subs<T>) -> Subs<T> {
    if let SubsNode::Cons(h1, t1, l2) = &*l.0 {
        if let SubsNode::Cons(h2, t2, rem) = &*l2.0 {
            if h1 == h2 {
                return Subs(Rc::new(SubsNode::Cons(1 + h1 + h2, Rc::new(node(x, t1.clone(), t2.clone())), rem.clone())));
            } else {
                return Subs(Rc::new(SubsNode::Cons(1, Rc::new(leaf(x)), l.clone())));
            }
        }
    }
    Subs(Rc::new(SubsNode::Cons(1, Rc::new(leaf(x)), l.clone())))
}

/// [Inl (k, v)] or [Inr (k, None|Some p)]
pub fn expand_rel<T: Clone>(n: isize, s: &Subs<T>) -> Either<(isize, T), (isize, Option<isize>)> {
    let (k, v) = get(s, n - 1);
    match v {
        Either::Inl(OrVar::Arg(v)) => Either::Inl((k, v)),
        Either::Inl(OrVar::Var(i)) => Either::Inr((k + i, None)),
        Either::Inr(i) => Either::Inr((k + i + 1, Some(i + 1))),
    }
}

pub fn is_subs_id<T>(s: &Subs<T>) -> bool {
    match &*s.0 {
        SubsNode::Nil(w, _) => *w == 0,
        SubsNode::Cons(..) => false,
    }
}

pub fn subs_cons<T: Clone>(v: T, s: &Subs<T>) -> Subs<T> {
    cons(OrVar::Arg(v), s)
}

fn push_vars_until<T: Clone>(i: isize, k: isize, s: Subs<T>) -> Subs<T> {
    let mut k = k;
    let mut s = s;
    while k != i {
        s = cons(OrVar::Var(k), &s);
        k -= 1;
    }
    s
}

pub fn subs_liftn<T: Clone>(n: isize, s: &Subs<T>) -> Subs<T> {
    if n == 0 {
        return s.clone();
    }
    match &*s.0 {
        SubsNode::Nil(0, m) => Subs(Rc::new(SubsNode::Nil(0, m + n))),
        _ => {
            let s = write(n, s);
            push_vars_until(0, n, s)
        }
    }
}

pub fn subs_lift<T: Clone>(s: &Subs<T>) -> Subs<T> {
    match &*s.0 {
        SubsNode::Nil(0, m) => Subs(Rc::new(SubsNode::Nil(0, m + 1))),
        _ => cons(OrVar::Var(1), &write(1, s)),
    }
}

pub fn subs_id<T>(n: isize) -> Subs<T> {
    Subs(Rc::new(SubsNode::Nil(0, n)))
}

pub fn subs_shft<T: Clone>(n: isize, s: &Subs<T>) -> Subs<T> {
    write(n, s)
}

fn tree_pop<T: Clone>(h: isize, n: isize, i: isize, rem: Subs<T>, s: &Rc<Tree<T>>) -> (isize, Subs<T>) {
    let (mut h, mut n, mut i, mut rem, mut s) = (h, n, i, rem, s.clone());
    loop {
        if n == 0 {
            return (i, Subs(Rc::new(SubsNode::Cons(h, s, rem))));
        }
        match &*s.clone() {
            Tree::Leaf(..) => {
                if n == 1 {
                    return (i, rem);
                } else {
                    panic!("assert false")
                }
            }
            Tree::Node(w, _, t1, t2, _) => {
                h = ((h as usize) >> 1) as isize;
                n -= 1;
                i += w;
                if n - 1 >= h {
                    n -= h;
                    i += eval(t1);
                    s = t2.clone();
                } else {
                    rem = Subs(Rc::new(SubsNode::Cons(h, t2.clone(), rem)));
                    s = t1.clone();
                }
            }
        }
    }
}

pub fn subs_pop_rec<T: Clone>(n: isize, i: isize, s: &Subs<T>) -> (isize, Subs<T>) {
    let (mut n, mut i, mut s) = (n, i, s.clone());
    loop {
        if n == 0 {
            return (i, s);
        }
        match &*s.0.clone() {
            SubsNode::Nil(w, m) => return (i + n, Subs(Rc::new(SubsNode::Nil(*w, m - n)))),
            SubsNode::Cons(h, t, rem) => {
                if n >= *h {
                    n -= h;
                    i += eval(t);
                    s = rem.clone();
                } else {
                    return tree_pop(*h, n, i, rem.clone(), t);
                }
            }
        }
    }
}

pub fn subs_popn<T: Clone>(n: isize, e: &Subs<T>) -> Subs<T> {
    let (k, e) = subs_pop_rec(n, 0, e);
    write(k, &e)
}

fn resize<T: Clone>(m: isize, s: &Subs<T>) -> Subs<T> {
    match &*s.0 {
        SubsNode::Nil(w, _) => {
            if m < 0 {
                panic!("assert false")
            } else {
                Subs(Rc::new(SubsNode::Nil(*w, m)))
            }
        }
        SubsNode::Cons(h, t, rem) => Subs(Rc::new(SubsNode::Cons(*h, t.clone(), resize(m - h, rem)))),
    }
}

fn apply_subs<T: Clone, U: Clone>(
    mk: &mut dyn FnMut(&Subs<T>, &U) -> T,
    lft: &mut dyn FnMut(isize, &T) -> T,
    s1: &Subs<T>,
    x: &OrVar<U>,
) -> OrVar<T> {
    match x {
        OrVar::Arg(v) => OrVar::Arg(mk(s1, v)),
        OrVar::Var(i) => match expand_rel(*i, s1) {
            Either::Inl((k, x)) => OrVar::Arg(lft(k, &x)),
            Either::Inr((i, _)) => OrVar::Var(i),
        },
    }
}

fn tree_comp<T: Clone, U: Clone>(
    mk: &mut dyn FnMut(&Subs<T>, &U) -> T,
    lft: &mut dyn FnMut(isize, &T) -> T,
    s1: &Subs<T>,
    t: &Tree<U>,
) -> (Tree<T>, Subs<T>) {
    match t {
        Tree::Leaf(w, x) => {
            let (n, s1) = subs_pop_rec(*w, 0, s1);
            let x = apply_subs(mk, lft, &s1, x);
            (Tree::Leaf(n, x), s1)
        }
        Tree::Node(w, x, t1, t2, _) => {
            let (n, s1) = subs_pop_rec(*w, 0, s1);
            let x = apply_subs(mk, lft, &s1, x);
            let (t1, s1) = tree_comp(mk, lft, &s1, t1);
            let (t2, s1) = tree_comp(mk, lft, &s1, t2);
            let wt = eval(&t1) + eval(&t2);
            (Tree::Node(n, x, Rc::new(t1), Rc::new(t2), wt), s1)
        }
    }
}

/// [comp mk lft s1 s2]
pub fn comp<T: Clone, U: Clone>(
    mk: &mut dyn FnMut(&Subs<T>, &U) -> T,
    lft: &mut dyn FnMut(isize, &T) -> T,
    s1: &Subs<T>,
    s2: &Subs<U>,
) -> Subs<T> {
    match &*s2.0 {
        SubsNode::Nil(w, m) => {
            let (n, s1) = subs_pop_rec(*w, 0, s1);
            write(n, &resize(*m, &s1))
        }
        SubsNode::Cons(h, t, rem) => {
            let (t, s1) = tree_comp(mk, lft, s1, t);
            let rem = comp(mk, lft, &s1, rem);
            Subs(Rc::new(SubsNode::Cons(*h, Rc::new(t), rem)))
        }
    }
}

/* Range: skewed lists, port of clib/range.ml (only what is needed) */

pub enum RTree<T> {
    Leaf(T),
    Node(T, Rc<RTree<T>>, Rc<RTree<T>>),
}

pub enum RangeNode<T> {
    Nil,
    Cons(isize, Rc<RTree<T>>, Range<T>),
}

pub struct Range<T>(pub Rc<RangeNode<T>>);

impl<T> Clone for Range<T> {
    fn clone(&self) -> Self {
        Range(self.0.clone())
    }
}

impl<T: Clone> Range<T> {
    pub fn empty() -> Range<T> {
        Range(Rc::new(RangeNode::Nil))
    }
    pub fn cons(&self, x: T) -> Range<T> {
        if let RangeNode::Cons(h1, t1, l2) = &*self.0 {
            if let RangeNode::Cons(h2, t2, rem) = &*l2.0 {
                if h1 == h2 {
                    return Range(Rc::new(RangeNode::Cons(
                        1 + h1 + h2,
                        Rc::new(RTree::Node(x, t1.clone(), t2.clone())),
                        rem.clone(),
                    )));
                }
            }
        }
        Range(Rc::new(RangeNode::Cons(1, Rc::new(RTree::Leaf(x)), self.clone())))
    }
    pub fn get(&self, i: isize) -> T {
        let mut l = self;
        let mut i = i;
        loop {
            match &*l.0 {
                RangeNode::Nil => panic!("index out of bounds"),
                RangeNode::Cons(h, t, rem) => {
                    if i < *h {
                        let mut h = *h;
                        let mut t: &RTree<T> = t;
                        loop {
                            match t {
                                RTree::Leaf(x) => {
                                    if i == 0 {
                                        return x.clone();
                                    } else {
                                        panic!("index out of bounds")
                                    }
                                }
                                RTree::Node(x, t1, t2) => {
                                    if i == 0 {
                                        return x.clone();
                                    }
                                    h /= 2;
                                    if i <= h {
                                        t = t1;
                                        i -= 1;
                                    } else {
                                        t = t2;
                                        i = i - h - 1;
                                    }
                                }
                            }
                        }
                    } else {
                        i -= h;
                        l = rem;
                    }
                }
            }
        }
    }
    pub fn length(&self) -> isize {
        let mut acc = 0;
        let mut l = self;
        while let RangeNode::Cons(h, _, rem) = &*l.0 {
            acc += h;
            l = rem;
        }
        acc
    }
}
