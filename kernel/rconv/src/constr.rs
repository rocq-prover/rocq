//! Direct access to the memory representation of [Constr.t] and a few other
//! kernel datatypes. The layout is checked at initialization time by
//! [Rconv.check_layout] on the OCaml side.

use crate::ffi::OVal;

pub const REL: u8 = 0;
pub const VAR: u8 = 1;
pub const META: u8 = 2;
pub const EVAR: u8 = 3;
pub const SORT: u8 = 4;
pub const CAST: u8 = 5;
pub const PROD: u8 = 6;
pub const LAMBDA: u8 = 7;
pub const LETIN: u8 = 8;
pub const APP: u8 = 9;
pub const CONST: u8 = 10;
pub const IND: u8 = 11;
pub const CONSTRUCT: u8 = 12;
pub const CASE: u8 = 13;
pub const FIX: u8 = 14;
pub const COFIX: u8 = 15;
pub const PROJ: u8 = 16;
pub const INT: u8 = 17;
pub const FLOAT: u8 = 18;
pub const STRING: u8 = 19;
pub const ARRAY: u8 = 20;

#[inline]
pub fn kind(c: &OVal) -> u8 {
    c.tag()
}

/// [Rel n]
pub fn dest_rel(c: &OVal) -> isize {
    c.field_int(0)
}

/// [App (f, args)]
pub fn dest_app(c: &OVal) -> (OVal, OVal) {
    (c.field(0), c.field(1))
}

/// [(c, u)] for [Const], [Ind], [Construct]
pub fn dest_pref(c: &OVal) -> (OVal, OVal) {
    let p = c.field(0);
    (p.field(0), p.field(1))
}

/// Universe instances are pairs of arrays.
pub fn instance_is_empty(u: &OVal) -> bool {
    u.field(0).size() == 0 && u.field(1).size() == 0
}

/// Relevance: [Relevant] = 0, [Irrelevant] = 1, [RelevanceVar q] block.
pub enum Rel {
    Relevant,
    Irrelevant,
    Var(OVal),
}

pub fn relevance(r: &OVal) -> Rel {
    if r.is_long() {
        if r.as_int() == 0 {
            Rel::Relevant
        } else {
            Rel::Irrelevant
        }
    } else {
        Rel::Var(r.field(0))
    }
}

/// [binder_annot] record: { binder_name; binder_relevance }
pub fn binder_relevance(na: &OVal) -> OVal {
    na.field(1)
}

/// [case_info] record
pub fn ci_ind(ci: &OVal) -> OVal {
    ci.field(0)
}
pub fn ci_npar(ci: &OVal) -> isize {
    ci.field_int(1)
}
pub fn ci_cstr_ndecls(ci: &OVal, i: usize) -> isize {
    ci.field(2).field_int(i)
}
pub fn ci_cstr_nargs(ci: &OVal, i: usize) -> isize {
    ci.field(3).field_int(i)
}

/// Lists
pub fn list_length(l: &OVal) -> usize {
    let mut n = 0;
    let mut l = l.clone();
    while !l.is_long() {
        n += 1;
        l = l.field(1);
    }
    n
}
