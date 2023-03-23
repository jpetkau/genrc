//! Sh<T> is very similar to `std::rc::Rc<T>`, but with some capabilities like
//! C++'s `shared_ptr`.
//!
//! If you have an `Sh<T>`, and `T` contains some subobject of type `U`, then
//! you can construct an `Sh<U>` that shares ownership with the original object,
//! by calling `Sh::derived()`.
//!
//! E.g.
//!
//!     use ash::sh::{Sh, Weak};
//!     let a: Sh<[i32; 3]> = Sh::new([1, 2, 3]);
//!     let w: Weak<[i32; 3]> = Sh::downgrade(&a);
//!
//!     // convert the sized array into a slice
//!     let b: Sh<[i32]> = Sh::derived(a, |x| &x[..]);
//!
//!     // get a reference to one element of the array
//!     let c: Sh<i32> = Sh::derived(b, |x| &x[1]);
//!
//!     // `c` is keeping the whole object alive
//!     assert!(w.upgrade().is_some());
//!     drop(c);
//!     assert!(w.upgrade().is_none());
//!
//! ## Differences from std::rc::Rc
//!
//! If you leak so many Sh objects that the refcount overflows, Rc will abort.
//! Sh does not, because there is no `abort()` with `no_std`.
//!
//! Implicit conversion from `Sh<T>` to `Sh<dyn Trait>` is not supported,
//! because that requires some unstable traits. However you can do the
//! conversion explicitly with `Sh::derived`.
//!
//! `Sh::from_box` does not copy the object from the original box. Instead it
//! takes ownership of the box as-is, with the counts in a separate allocation.
//!
//! ## See also
//!
//! `Ash<T>` in this crate is similar to `Sh<T>`, but for multithreaded use like
//! `std::sync::Arc`.
use std::{
    cell::Cell,
    fmt,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::Deref,
    ptr,
};

// Counts and destructors for objects owned by Sh. Unlike with Rc<T>, there is
// not necessarily any relationship between the pointer type and the actual
// stored type.
struct ShHeader {
    strong: Cell<usize>,
    weak: Cell<usize>,
    drop_header: unsafe fn(*mut ShHeader),
    drop_value: unsafe fn(*mut ShHeader),
}

struct ShBox<T> {
    header: ShHeader,
    value: MaybeUninit<T>,
}

pub struct Sh<T: ?Sized> {
    header: ptr::NonNull<ShHeader>,
    ptr: ptr::NonNull<T>,
    phantom: PhantomData<T>,
}

pub struct Weak<T: ?Sized> {
    header: ptr::NonNull<ShHeader>,
    ptr: ptr::NonNull<T>,
}

impl<T: ?Sized> Deref for Sh<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.ptr()
    }
}

impl<T> Sh<T> {
    pub fn new(value: T) -> Sh<T> {
        let b = Box::leak(Box::new(ShBox {
            header: ShHeader {
                strong: Cell::new(1),
                weak: Cell::new(1),
                drop_header: drop_header::<T>,
                drop_value: drop_value::<T>,
            },
            value: MaybeUninit::new(value),
        }));
        Sh {
            header: (&b.header).into(),
            ptr: unsafe { b.value.assume_init_ref() }.into(),
            phantom: PhantomData,
        }
    }

    /// Constructs a new `Sh<T>` while giving you a `Weak<T>` to the allocation,
    /// to allow you to construct a `T` which holds a weak pointer to itself.
    ///
    /// See `std::rc::Rc::new_cyclic` for more details.
    pub fn new_cyclic<F>(data_fn: F) -> Sh<T>
    where
        F: FnOnce(&Weak<T>) -> T,
    {
        // Construct the inner in the "uninitialized" state with a single weak
        // reference. We don't set strong=1 yet so taht if `f` panics, we don't
        // try to drop the uninitialized value.
        let b = Box::leak(Box::new(ShBox {
            header: ShHeader {
                strong: Cell::new(0),
                weak: Cell::new(1),
                drop_header: drop_header::<T>,
                drop_value: drop_value::<T>,
            },
            value: MaybeUninit::uninit(),
        }));
        let weak = Weak {
            header: (&b.header).into(),
            ptr: unsafe { ptr::NonNull::new_unchecked(b.value.as_ptr() as *mut _) },
        };

        // Safety: we just allocated with `value` uninitialized
        unsafe { ptr::write(b.value.as_mut_ptr(), data_fn(&weak)) };

        // Now that the inner is initialized, we can set the strong count to 1.
        let h = weak.header();
        debug_assert_eq!(h.strong.get(), 0, "No prior strong references should exist");
        h.strong.set(1);
        let strong = Sh {
            header: weak.header,
            ptr: weak.ptr,
            phantom: PhantomData,
        };

        // Strong references collectively own a shared weak reference, so don't
        // run the destructor for our old weak reference.
        mem::forget(weak);
        strong
    }
}

impl<T: ?Sized> Sh<T> {
    /// Return a `Sh<T>` for a boxed value. Unlike `Rc<T>`, this reuses the
    /// original box allocation rather than copying it, and only allocates space
    /// for the header with the reference counts.
    pub fn from_box(value: Box<T>) -> Sh<T> {
        Sh::derived(Sh::new(value), |x| &**x)
    }

    /// Return a `Sh<U>` for any type U contained within T, e.g. an element of a
    /// slice, or &dyn view of an object.
    pub fn derived<U: ?Sized, F: for<'a> FnOnce(&'a T) -> &'a U>(s: Self, f: F) -> Sh<U> {
        let u = Sh {
            header: s.header,
            ptr: f(&*s).into(),
            phantom: PhantomData,
        };
        // Forget s so it doesn't decrement the refcount, since we moved it
        // into u.
        mem::forget(s);
        u
    }

    /// Convert `Sh<T>` to `Sh<U>`, as long as &T converts to &U.
    ///
    /// This should be spelled `from()`, but that conflicts with the blanket
    /// impl converting T->T.
    ///
    /// TODO: this doesn't work for slices; there's no blanket impl
    /// `for<'a> &'a [T]: From<&'a [T; N]>` and I don't know why.
    /// So for now you must call `derived()` explicitly.
    pub fn cast<U: ?Sized>(this: Sh<T>) -> Sh<U> where for<'a> &'a U: From<&'a T> {
        Sh::derived(this, |x| From::from(x))
    }

    /// Return a `sh::Weak` pointer to this object.
    pub fn downgrade(this: &Self) -> Weak<T> {
        let h = this.header();
        h.weak.set(h.weak.get() + 1);
        Weak {
            header: this.header,
            ptr: this.ptr,
        }
    }

    fn ptr(&self) -> &T {
        // Safety: ptr is always a valid reference, there's just no
        // way to spell the lifetime in Rust.
        unsafe { self.ptr.as_ref() }
    }

    fn header(&self) -> &ShHeader {
        // Safety: header is always a valid reference, there's just no
        // way to spell the lifetime in Rust.
        unsafe { self.header.as_ref() }
    }

    // Get the current strong count of this pointer
    pub fn strong_count(p: &Self) -> usize {
        p.header().strong.get()
    }

    // Get the current weak count of this pointer
    pub fn weak_count(p: &Self) -> usize {
        // Subtract one to hide the implicit weak pointer owned by the strong
        // pointers, which is an implementation detail.
        p.header().weak.get() - 1
    }
}

impl<T: ?Sized> Weak<T> {
    pub fn upgrade(&self) -> Option<Sh<T>> {
        let h = self.header();
        let s = h.strong.get();
        if s == 0 {
            None
        } else {
            h.strong.set(s + 1);
            Some(Sh {
                header: self.header,
                ptr: self.ptr,
                phantom: PhantomData,
            })
        }
    }

    // Get the current strong count of this pointer
    pub fn strong_count(&self) -> usize {
        self.header().strong.get()
    }

    // Get the current weak count of this pointer.
    pub fn weak_count(&self) -> usize {
        // Subtract one to hide the implicit weak pointer owned by the strong
        // pointers, which is an implementation detail.
        self.header().weak.get() - 1
    }

    // Returns true if all strong pointers have been dropped,
    // so `upgrade` will return None.
    pub fn is_dangling(&self) -> bool {
        self.strong_count() == 0
    }

    fn header(&self) -> &ShHeader {
        // Safety: header is always a valid reference
        unsafe { self.header.as_ref() }
    }
}

impl<T: ?Sized> Clone for Sh<T> {
    fn clone(&self) -> Self {
        let h = self.header();
        h.strong.set(h.strong.get() + 1);
        Sh {
            header: self.header,
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<T: ?Sized> Clone for Weak<T> {
    fn clone(&self) -> Self {
        let h = self.header();
        h.weak.set(h.weak.get() + 1);
        Weak {
            header: self.header,
            ptr: self.ptr,
        }
    }
}

impl<T: ?Sized> Drop for Sh<T> {
    fn drop(&mut self) {
        let h = self.header();
        let s = h.strong.get() - 1;
        h.strong.set(s);
        if s == 0 {
            // last strong pointer was just dropped
            unsafe {
                (h.drop_value)(self.header.as_ptr());
            }
            let w = h.weak.get() - 1;
            if w != 0 {
                h.weak.set(w);
            } else {
                // last weak pointer was just dropped
                unsafe {
                    (h.drop_header)(self.header.as_ptr());
                }
            }
        }
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Sh<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(Weak)")
    }
}

unsafe fn drop_header<T>(ptr: *mut ShHeader) {
    let _ = Box::from_raw(ptr as *mut ShBox<T>);
}

unsafe fn drop_value<T>(ptr: *mut ShHeader) {
    let hptr = ptr as *mut ShBox<T>;
    // let _ = Box::from_raw(hptr);
    let dptr = ptr::addr_of_mut!((*hptr).value);
    (&mut *dptr).assume_init_drop();
}

#[cfg(test)]
mod tests {
    use super::*;

    struct DropCounter<'a, T>(T, &'a mut usize);
    impl<'a, T> Drop for DropCounter<'a, T> {
        fn drop(&mut self) {
            *self.1 += 1;
        }
    }

    #[test]
    fn test_simple() {
        let x = Sh::new(2);
        let y = x.clone();
        assert_eq!(*x, 2);
        assert_eq!(&*x as *const i32, &*y as *const i32);
        drop(x);
        assert_eq!(*y, 2);
    }

    #[test]
    fn test_derived() {
        let mut n = 0;
        {
            let x = Sh::new(DropCounter((1, 2), &mut n));
            let y = Sh::derived(x.clone(), |x| &x.0 .0);
            let z = Sh::derived(x.clone(), |x| &x.0 .1);
            assert_eq!(*y, 1);
            assert_eq!(*z, 2);
            assert_eq!(Sh::strong_count(&z), 3);
            assert_eq!(Sh::weak_count(&z), 0);
            drop(x);
            drop(y);
            assert_eq!(Sh::strong_count(&z), 1);
            assert_eq!(Sh::weak_count(&z), 0);
            drop(z);
        }
        assert_eq!(n, 1);

        // Updating the mut ref to `n` above looks sketchy. Confirm that Rc
        // allows the same thing.
        {
            let x = std::rc::Rc::new(DropCounter((1, 2), &mut n));
            let y = x.clone();
            let z = y.clone();
            //assert_eq!(n, 0);
            drop(x);
            drop(y);
            //assert_eq!(n, 0);
            drop(z);
        }
        assert_eq!(n, 2);
    }

    #[test]
    fn test_trait_obj() {
        let x = Sh::new(2);
        let d = Sh::derived(x.clone(), |p| p as &dyn std::fmt::Debug);
        assert_eq!(format!("{:?}", d), "2");
    }

    #[test]
    fn test_array_to_slice() {
        let x: Sh<[i32; 3]> = Sh::new([1, 2, 3]);
        let y: Sh<[i32]> = Sh::derived(x.clone(), |p| &p[..]);
        let z: Sh<i32> = Sh::derived(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_vec_to_slice() {
        // Note unlike Arc/Rc, this uses the existing Box/Vec allocation rather
        // than copying, and allocates space for the header separately.
        let x: Sh<Box<[i32]>> = Sh::new(vec![1, 2, 3].into());
        let y: Sh<[i32]> = Sh::derived(x.clone(), |p| &p[..]);
        let z: Sh<i32> = Sh::derived(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_cyclic() {
        struct Cyclic(Weak<Cyclic>);
        let x = Sh::new_cyclic(|p| Cyclic(p.clone()));
        assert_eq!(Sh::strong_count(&x), 1);
        assert_eq!(Sh::weak_count(&x), 1);
    }

    #[test]
    fn test_oopsie() {
       let a: Sh<[i32; 3]> = Sh::new([1, 2, 3]);
       let w: Weak<[i32; 3]> = Sh::downgrade(&a);
       assert_eq!(w.strong_count(), 1);

       // convert the sized array into a slice
       let b: Sh<[i32]> = Sh::derived(a, |x| &x[..]);

       // get a reference to one element of the array
       let c: Sh<i32> = Sh::derived(b, |x| &x[1]);
       assert_eq!(w.strong_count(), 1);

       // `c` is keeping the whole object alive
       assert!(w.upgrade().is_some());
       assert_eq!(w.strong_count(), 1);
       drop(c);
       assert_eq!(w.strong_count(), 0);
       assert!(w.upgrade().is_none());
    }
}
