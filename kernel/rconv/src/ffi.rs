use std::cell::RefCell;
use std::num::NonZeroUsize;
use std::ffi::{c_char, c_int, c_void};
use std::rc::Rc;
use std::sync::atomic::{AtomicPtr, Ordering};

pub type Value = isize;

extern "C" {
    fn boxroot_create(v: Value) -> *mut Value;
    fn boxroot_delete(r: *mut Value);
    fn boxroot_setup() -> bool;
    fn caml_named_value(name: *const c_char) -> *const Value;
    fn caml_callbackN_exn(closure: Value, narg: c_int, args: *mut Value) -> Value;
    fn caml_alloc_custom(ops: *const CustomOps, size: usize, mem: usize, max: usize) -> Value;
    fn caml_alloc(wosize: usize, tag: c_int) -> Value;
    fn caml_initialize(fp: *mut Value, v: Value);
}

/// Allocate an OCaml array holding the given values.
pub fn alloc_array(xs: &[OVal]) -> OVal {
    unsafe {
        let v = caml_alloc(xs.len(), 0);
        for (i, x) in xs.iter().enumerate() {
            caml_initialize((v as *mut Value).add(i), x.get());
        }
        OVal::new(v)
    }
}

pub const VAL_UNIT: Value = 1;
pub const VAL_FALSE: Value = 1;
pub const VAL_TRUE: Value = 3;

#[inline]
pub fn is_long(v: Value) -> bool {
    v & 1 != 0
}
#[inline]
pub fn long_val(v: Value) -> isize {
    v >> 1
}
#[inline]
pub fn val_long(n: isize) -> Value {
    (n << 1) + 1
}
#[inline]
pub fn val_bool(b: bool) -> Value {
    if b {
        VAL_TRUE
    } else {
        VAL_FALSE
    }
}
#[inline]
pub unsafe fn hd(v: Value) -> usize {
    *((v as *const usize).offset(-1))
}
#[inline]
pub unsafe fn tag(v: Value) -> u8 {
    (hd(v) & 0xFF) as u8
}
#[inline]
pub unsafe fn wosize(v: Value) -> usize {
    hd(v) >> 10
}
#[inline]
pub unsafe fn field(v: Value, i: usize) -> Value {
    *((v as *const Value).add(i))
}

/// A GC root to an OCaml value, in one word. Immediate values are stored as
/// is (their low bit is set) and are not rooted. Other values are rooted by a
/// boxroot owned by the [OVal]: the address of a boxroot slot is a pointer to
/// a word, so its low bit is 0. Cloning creates a new boxroot.
pub struct OVal(NonZeroUsize);

impl Clone for OVal {
    #[inline]
    fn clone(&self) -> OVal {
        if self.0.get() & 1 != 0 {
            OVal(self.0)
        } else {
            OVal::root(self.get())
        }
    }
}

impl Drop for OVal {
    #[inline]
    fn drop(&mut self) {
        if self.0.get() & 1 == 0 {
            unsafe { boxroot_delete(self.0.get() as *mut Value) }
        }
    }
}

impl OVal {
    #[inline]
    fn root(v: Value) -> OVal {
        let r = unsafe { boxroot_create(v) };
        if r.is_null() {
            panic!("rconv: boxroot allocation failure");
        }
        OVal(unsafe { NonZeroUsize::new_unchecked(r as usize) })
    }
    #[inline]
    pub fn new(v: Value) -> OVal {
        if is_long(v) {
            OVal(unsafe { NonZeroUsize::new_unchecked(v as usize) })
        } else {
            OVal::root(v)
        }
    }
    #[inline]
    pub fn int(n: isize) -> OVal {
        OVal::new(val_long(n))
    }
    #[inline]
    pub fn get(&self) -> Value {
        if self.0.get() & 1 != 0 {
            self.0.get() as Value
        } else {
            unsafe { *(self.0.get() as *const Value) }
        }
    }
    #[inline]
    pub fn is_long(&self) -> bool {
        self.0.get() & 1 != 0
    }
    #[inline]
    pub fn as_int(&self) -> isize {
        long_val(self.get())
    }
    #[inline]
    pub fn as_bool(&self) -> bool {
        self.get() != VAL_FALSE
    }
    #[inline]
    pub fn tag(&self) -> u8 {
        unsafe { tag(self.get()) }
    }
    #[inline]
    pub fn size(&self) -> usize {
        unsafe { wosize(self.get()) }
    }
    #[inline]
    pub fn field(&self, i: usize) -> OVal {
        OVal::new(unsafe { field(self.get(), i) })
    }
    #[inline]
    pub fn field_int(&self, i: usize) -> isize {
        long_val(unsafe { field(self.get(), i) })
    }
    #[inline]
    pub fn field_is_long(&self, i: usize) -> bool {
        is_long(unsafe { field(self.get(), i) })
    }
    #[inline]
    pub fn phys_eq(&self, o: &OVal) -> bool {
        self.get() == o.get()
    }
    /// Elements of an OCaml list.
    pub fn list_to_vec(&self) -> Vec<OVal> {
        let mut res = vec![];
        let mut l = self.clone();
        while !l.is_long() {
            res.push(l.field(0));
            l = l.field(1);
        }
        res
    }
    /// Elements of an OCaml (non-float) array.
    pub fn array_to_vec(&self) -> Vec<OVal> {
        let n = self.size();
        (0..n).map(|i| self.field(i)).collect()
    }
    /// For [option] values: [None] is the immediate 0.
    pub fn as_option(&self) -> Option<OVal> {
        if self.is_long() {
            None
        } else {
            Some(self.field(0))
        }
    }
    pub fn string_bytes(&self) -> Vec<u8> {
        unsafe {
            let v = self.get();
            let wsz = wosize(v) * std::mem::size_of::<Value>();
            let p = v as *const u8;
            let last = *p.add(wsz - 1) as usize;
            let len = wsz - 1 - last;
            std::slice::from_raw_parts(p, len).to_vec()
        }
    }
}

/// OCaml exception being propagated through Rust frames.
pub struct OcamlExn(pub OVal);

unsafe impl Send for OcamlExn {}

pub fn raise_ocaml(e: OVal) -> ! {
    std::panic::resume_unwind(Box::new(OcamlExn(e)))
}

pub struct Callback {
    name: &'static [u8],
    ptr: AtomicPtr<Value>,
}

impl Callback {
    pub const fn new(name: &'static [u8]) -> Callback {
        Callback { name, ptr: AtomicPtr::new(std::ptr::null_mut()) }
    }
    /// The registered value itself (for registered references).
    pub fn value(&self) -> Value {
        self.closure()
    }
    fn closure(&self) -> Value {
        let mut p = self.ptr.load(Ordering::Relaxed);
        if p.is_null() {
            p = unsafe { caml_named_value(self.name.as_ptr() as *const c_char) } as *mut Value;
            if p.is_null() {
                panic!("rconv: unregistered callback {}", String::from_utf8_lossy(self.name));
            }
            self.ptr.store(p, Ordering::Relaxed);
        }
        unsafe { *p }
    }
}

/// Argument of a callback: rooted values are dereferenced only once all
/// arguments are ready, so that no allocation can happen in-between.
pub enum A<'a> {
    O(&'a OVal),
    I(isize),
    B(bool),
}

pub fn call(cb: &Callback, args: &[A]) -> OVal {
    let mut raw: [Value; 16] = [0; 16];
    assert!(args.len() <= 16);
    for (i, a) in args.iter().enumerate() {
        raw[i] = match a {
            A::O(v) => v.get(),
            A::I(n) => val_long(*n),
            A::B(b) => val_bool(*b),
        };
    }
    let f = cb.closure();
    let r = unsafe { caml_callbackN_exn(f, args.len() as c_int, raw.as_mut_ptr()) };
    if r & 3 == 2 {
        let e = OVal::new(r & !3);
        raise_ocaml(e)
    }
    OVal::new(r)
}

#[macro_export]
macro_rules! cb {
    ($name:ident, $s:expr) => {
        pub static $name: $crate::ffi::Callback = $crate::ffi::Callback::new(concat!($s, "\0").as_bytes());
    };
}

/* Custom blocks wrapping Rust objects for use as opaque OCaml values. */

#[repr(C)]
pub struct CustomOps {
    identifier: *const c_char,
    finalize: Option<unsafe extern "C" fn(Value)>,
    compare: *const c_void,
    hash: *const c_void,
    serialize: *const c_void,
    deserialize: *const c_void,
    compare_ext: *const c_void,
    fixed_length: *const c_void,
}

unsafe impl Sync for CustomOps {}

thread_local! {
    static PENDING: RefCell<Vec<*const crate::closure::FCell>> = const { RefCell::new(Vec::new()) };
}

unsafe extern "C" fn finalize_fc(v: Value) {
    let p = *((v as *const *const crate::closure::FCell).add(1));
    if !p.is_null() {
        PENDING.with(|q| q.borrow_mut().push(p));
    }
}

static FC_OPS: CustomOps = CustomOps {
    identifier: b"rocq.rconv.fconstr\0".as_ptr() as *const c_char,
    finalize: Some(finalize_fc),
    compare: std::ptr::null(),
    hash: std::ptr::null(),
    serialize: std::ptr::null(),
    deserialize: std::ptr::null(),
    compare_ext: std::ptr::null(),
    fixed_length: std::ptr::null(),
};

/// Release the Rust objects whose OCaml handles were collected. Must not be
/// called from inside a GC.
pub fn flush_pending() {
    loop {
        let v = PENDING.with(|q| std::mem::take(&mut *q.borrow_mut()));
        if v.is_empty() {
            break;
        }
        for p in v {
            unsafe { drop(Rc::from_raw(p)) }
        }
    }
}

pub fn fc_to_handle(fc: &crate::closure::FC) -> OVal {
    let p = Rc::into_raw(fc.clone());
    unsafe {
        let v = caml_alloc_custom(&FC_OPS, std::mem::size_of::<*const c_void>(), 0, 1);
        *((v as *mut *const crate::closure::FCell).add(1)) = p;
        OVal::new(v)
    }
}

pub unsafe fn handle_to_fc_raw(v: Value) -> crate::closure::FC {
    let p = *((v as *const *const crate::closure::FCell).add(1));
    Rc::increment_strong_count(p);
    Rc::from_raw(p)
}

pub fn handle_to_fc(v: &OVal) -> crate::closure::FC {
    unsafe { handle_to_fc_raw(v.get()) }
}

pub fn setup() {
    unsafe {
        boxroot_setup();
    }
}
