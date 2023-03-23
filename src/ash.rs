//! Ash<T> is very similar to `std::sync::Arc<T>`, but with some capabilities
//! like C++'s `shared_ptr`.
//!
//! If you have an `Ash<T>`, and `T` contains some subobject of type `U`, then
//! you can construct an `Ash<U>` that shares ownership with the original
//! object, by calling `Ash::derived()`.
//!
//! E.g.
//!
//!     use ash::{Ash, Weak};
//!     let a: Ash<[i32; 3]> = Ash::new([1, 2, 3]);
//!     let w: Weak<[i32; 3]> = Ash::downgrade(&a);
//!
//!     // convert the sized array into a slice
//!     let b: Ash<[i32]> = Ash::derived(a, |x| &x[..]);
//!
//!     // get a reference to one element of the array
//!     let c: Ash<i32> = Ash::derived(b, |x| &x[1]);
//!
//!     // `c` is keeping the whole object alive
//!     assert!(w.upgrade().is_some());
//!     drop(c);
//!     assert!(w.upgrade().is_none());
//!
//! ## Differences from std::sync::Arc
//!
//! `Ash` is one pointer fatter than `Arc`, because it has separate pointers to
//! the value and the header with the reference counts.
//!
//! If you leak so many Ash objects that the refcount overflows, Arc will abort.
//! Ash does not, because there is no `abort()` with `no_std`.
//!
//! Implicit conversion from `Ash<T>` to `Ash<dyn Trait>` is not supported,
//! because that requires some unstable traits. However you can do the
//! conversion explicitly with `Ash::derived`.
//!
//! `Ash::from_box` does not copy the object from the original box. Instead it
//! takes ownership of the box as-is, with the counts in a separate allocation.
//!
//! ## See also
//!
//! `Sh<T>` in this crate is similar to `Ash<T>`, but for single-threaded use
//! like `std::rc::Rc`.
use core::borrow;
use core::{
    fmt,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::Deref,
    ptr,
    sync::atomic::{
        self,
        Ordering::{Acquire, Relaxed, Release, SeqCst},
    },
};
use std::iter;

// Counts and destructors for objects owned by Ash. Unlike with Arc<T>, there is
// not necessarily any relationship between the pointer type and the actual
// stored type.
struct AshHeader {
    strong: atomic::AtomicUsize,
    weak: atomic::AtomicUsize,
    drop_header: unsafe fn(*mut AshHeader),
    drop_value: unsafe fn(*mut AshHeader),
}

struct AshBox<T> {
    header: AshHeader,
    value: MaybeUninit<T>,
}

unsafe fn drop_header<T>(ptr: *mut AshHeader) {
    let _ = Box::from_raw(ptr as *mut AshBox<T>);
}

unsafe fn drop_value<T>(ptr: *mut AshHeader) {
    let hptr = ptr as *mut AshBox<T>;
    let dptr = ptr::addr_of_mut!((*hptr).value);
    (&mut *dptr).assume_init_drop();
}

pub struct Ash<T: ?Sized> {
    header: ptr::NonNull<AshHeader>,
    ptr: ptr::NonNull<T>,
    phantom: PhantomData<T>,
}

pub struct Weak<T: ?Sized> {
    header: ptr::NonNull<AshHeader>,
    ptr: ptr::NonNull<T>,
}

impl<T: ?Sized> Deref for Ash<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.ptr()
    }
}

impl<T> Ash<T> {
    pub fn new(value: T) -> Ash<T> {
        let b = Box::leak(Box::new(AshBox {
            header: AshHeader {
                strong: atomic::AtomicUsize::new(1),
                weak: atomic::AtomicUsize::new(1),
                drop_header: drop_header::<T>,
                drop_value: drop_value::<T>,
            },
            value: MaybeUninit::new(value),
        }));
        Ash {
            header: (&b.header).into(),
            ptr: unsafe { b.value.assume_init_ref() }.into(),
            phantom: PhantomData,
        }
    }

    /// Constructs a new `Ash<T>` while giving you a `Weak<T>` to the allocation,
    /// to allow you to construct a `T` which holds a weak pointer to itself.
    ///
    /// See `std::rc::Arc::new_cyclic` for more details.
    pub fn new_cyclic<F>(data_fn: F) -> Ash<T>
    where
        F: FnOnce(&Weak<T>) -> T,
    {
        // Construct the inner in the "uninitialized" state with a single weak
        // reference. We don't set strong=1 yet so taht if `f` panics, we don't
        // try to drop the uninitialized value.
        let b = Box::leak(Box::new(AshBox {
            header: AshHeader {
                strong: atomic::AtomicUsize::new(0),
                weak: atomic::AtomicUsize::new(1),
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
        let old_strong = h.strong.fetch_add(1, Relaxed);
        debug_assert_eq!(old_strong, 0, "No prior strong references should exist");
        let strong = Ash {
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

impl<T: ?Sized> Ash<T> {
    /// Return a `Ash<T>` for a boxed value. Unlike `Arc<T>`, this reuses the
    /// original box allocation rather than copying it, and only allocates space
    /// for the header with the reference counts.
    pub fn from_box(value: Box<T>) -> Ash<T> {
        Ash::derived(Ash::new(value), |x| &**x)
    }

    /// Return a `Ash<U>` for any type U contained within T, e.g. an element of a
    /// slice, or &dyn view of an object.
    pub fn derived<U: ?Sized, F: for<'a> FnOnce(&'a T) -> &'a U>(s: Self, f: F) -> Ash<U> {
        let u = Ash {
            header: s.header,
            ptr: f(&*s).into(),
            phantom: PhantomData,
        };
        // Forget s so it doesn't decrement the refcount, since we moved it
        // into u.
        mem::forget(s);
        u
    }

    /// Convert `Ash<T>` to `Ash<U>`, as long as &T converts to &U.
    ///
    /// This should be spelled `from()`, but that conflicts with the blanket
    /// impl converting T->T.
    ///
    /// TODO: this doesn't work for slices; there's no blanket impl
    /// `for<'a> &'a [T]: From<&'a [T; N]>` and I don't know why.
    /// So for now you must call `derived()` explicitly.
    pub fn cast<U: ?Sized>(this: Ash<T>) -> Ash<U> where for<'a> &'a U: From<&'a T> {
        Ash::derived(this, |x| From::from(x))
    }

    /// Return a `sh::Weak` pointer to this object.
    pub fn downgrade(this: &Self) -> Weak<T> {
        let h = this.header();
        h.weak.fetch_add(1, Relaxed);
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

    fn header(&self) -> &AshHeader {
        // Safety: header is always a valid reference, there's just no
        // way to spell the lifetime in Rust.
        unsafe { self.header.as_ref() }
    }

    // Get the current strong count of this pointer.
    pub fn strong_count(p: &Self) -> usize {
        p.header().strong.load(SeqCst)
    }

    // Get the current weak count of this pointer
    pub fn weak_count(p: &Self) -> usize {
        // Subtract one to hide the implicit weak pointer owned by the strong
        // pointers, which is an implementation detail.
        p.header().weak.load(SeqCst) - 1
    }
}

impl<T: ?Sized> Weak<T> {
    pub fn upgrade(self: &Self) -> Option<Ash<T>> {
        let h = self.header();
        // See Arc<T> for explanation of atomic logic
        let s = h.strong.fetch_update(Acquire, Relaxed, |n| {
            if n == 0 { None } else { Some(n + 1) }
        });

        match s {
            Ok(_) => Some(Ash {
                header: self.header,
                ptr: self.ptr,
                phantom: PhantomData,
            }),
            Err(_) => None,
        }
    }

    // Get the current strong count of this pointer
    pub fn strong_count(&self) -> usize {
        self.header().strong.load(SeqCst)
    }

    // Get the current weak count of this pointer.
    pub fn weak_count(&self) -> usize {
        // Subtract one to hide the implicit weak pointer owned by the strong
        // pointers, which is an implementation detail.
        self.header().weak.load(SeqCst) - 1
    }

    // Returns true if all strong pointers have been dropped,
    // so `upgrade` will return None.
    pub fn is_dangling(&self) -> bool {
        self.strong_count() == 0
    }

    fn header(&self) -> &AshHeader {
        // Safety: header is always a valid reference
        unsafe { self.header.as_ref() }
    }
}

impl<T: ?Sized> Clone for Ash<T> {
    fn clone(&self) -> Self {
        let h = self.header();
        h.strong.fetch_add(1, Relaxed);
        Ash {
            header: self.header,
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<T: ?Sized> Clone for Weak<T> {
    fn clone(&self) -> Self {
        let h = self.header();
        h.weak.fetch_add(1, Relaxed);
        Weak {
            header: self.header,
            ptr: self.ptr,
        }
    }
}

impl<T: ?Sized> Drop for Ash<T> {
    fn drop(&mut self) {
        let h = self.header();
        if h.strong.fetch_sub(1, Release) != 1 {
            return;
        }
        // last strong pointer was just dropped
        atomic::fence(Acquire);
        unsafe {
            (h.drop_value)(self.header.as_ptr());
        }

        // decrement weak count owned by strong ptrs
        if h.weak.fetch_sub(1, Release) != 1 {
            return;
        }
        unsafe {
            (h.drop_header)(self.header.as_ptr());
        }
    }
}

impl<T: ?Sized> borrow::Borrow<T> for Ash<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> AsRef<T> for Ash<T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Ash<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(Weak)")
    }
}

// Can't implement this because it conflicts with the blanket `T: From<T>` impl.
// Note sure how to avoid that?
//
// impl<'a, T: ?Sized, U: ?Sized> From<Ash<T>> for Ash<U> where &'a U: From<&'a T> {
//    fn from(x: Ash<T>) -> Ash<U> { Ash::derived(x, |p| U::from(p)) }
// }

impl<T> std::iter::FromIterator<T> for Ash<[T]> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Self {
        Ash::from_box(iter.into_iter().collect())
    }
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
        let x = Ash::new(2);
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
            let x = Ash::new(DropCounter((1, 2), &mut n));
            let y = Ash::derived(x.clone(), |x| &x.0 .0);
            let z = Ash::derived(x.clone(), |x| &x.0 .1);
            assert_eq!(*y, 1);
            assert_eq!(*z, 2);
            assert_eq!(Ash::strong_count(&z), 3);
            assert_eq!(Ash::weak_count(&z), 0);
            drop(x);
            drop(y);
            assert_eq!(Ash::strong_count(&z), 1);
            assert_eq!(Ash::weak_count(&z), 0);
            drop(z);
        }
        assert_eq!(n, 1);
    }

    #[test]
    fn test_trait_obj() {
        let x = Ash::new(2);
        let d = Ash::derived(x.clone(), |p| p as &dyn std::fmt::Debug);
        assert_eq!(format!("{:?}", d), "2");
    }

    #[test]
    fn test_array_to_slice() {
        let x: Ash<[i32; 3]> = Ash::new([1, 2, 3]);
        let y: Ash<[i32]> = Ash::derived(x.clone(), |p| &p[..]);
        let z: Ash<i32> = Ash::derived(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_vec_to_slice() {
        // Note unlike Arc/Arc, this uses the existing Box/Vec allocation rather
        // than copying, and allocates space for the header separately.
        let x: Ash<Box<[i32]>> = Ash::new(vec![1, 2, 3].into());
        let y: Ash<[i32]> = Ash::derived(x.clone(), |p| &p[..]);
        let z: Ash<i32> = Ash::derived(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_cyclic() {
        struct Cyclic(Weak<Cyclic>);
        let x = Ash::new_cyclic(|p| Cyclic(p.clone()));
        assert_eq!(Ash::strong_count(&x), 1);
        assert_eq!(Ash::weak_count(&x), 1);
    }
}
