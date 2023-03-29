//! `ash::arc::Arc<T>` is very similar to `std::sync::Arc<T>`, but with some
//! capabilities like C++'s `shared_ptr`.
//!
//! If you have an `Arc<T>`, and `T` contains some subobject of type `U`, then
//! you can construct an `Arc<U>` that shares ownership with the original
//! object, by calling `Arc::project()`.
//!
//! E.g.
//!
//!     use ash::arc::{Arc, Weak};
//!     let a: Arc<[i32; 3]> = Arc::new([1, 2, 3]);
//!     let w: Weak<[i32; 3]> = Arc::downgrade(&a);
//!
//!     // convert the sized array into a slice
//!     let b: Arc<[i32]> = Arc::project(a, |x| &x[..]);
//!
//!     // get a reference to one element of the array
//!     let c: Arc<i32> = Arc::project(b, |x| &x[1]);
//!
//!     // `c` is keeping the whole object alive
//!     assert!(w.upgrade().is_some());
//!     drop(c);
//!     assert!(w.upgrade().is_none());
//!
//! ## Differences from std::sync::Arc
//!
//! `ash::arc::Arc` is one pointer fatter than `std::sync::Arc`, because it has
//! separate pointers to the value and the header with the reference counts.
//!
//! If you leak so many `Arc` objects that the refcount overflows,
//! `std::sync::Arc` will abort. `ash::arc::Arc` does not, because there is no
//! `abort()` available with `no_std`. TODO: it should set some flag in the
//! refcount so the object is never freed
//!
//! Implicit conversion from `Arc<T>` to `Arc<dyn Trait>` is not supported,
//! because that requires some unstable traits. However you can do the
//! conversion explicitly with `Arc::project`.
//!
//! `Arc::from_box` does not copy the object from the original box. Instead it
//! takes ownership of the box as-is, with the counts in a separate allocation.
//!
//! TODO: static variables. TODO: no_std / custom allocators
//!
//! ## See also
//!
//! `ash::rc::Rc<T>` in this crate is the nonatomic version for single-threaded
//! use.
//!
//! The `shared-rc` crate provides a nearly identical API. I would not have
//! written this crate had I realied that `shared-rc` already existed. That
//! said, there are some differences:
//! * `shared-rc` uses the std versions of `Arc` and `Rc` under the hood, so it
//!   cannot support custom allocators or references to static variables.
//! * `shared-rc` includes an `Owner` type param, with an explicit `erase_owner`
//!   method to hide it. `ash::arc::Arc` always type-erases the owner.
use core::borrow;
use core::iter;
use core::{
    cmp, fmt,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::Deref,
    ptr,
    sync::atomic::{
        self,
        Ordering::{Acquire, Relaxed, Release, SeqCst},
    },
};

// Counts and destructors for objects owned by Arc. Unlike with Arc<T>, there is
// not necessarily any relationship between the pointer type and the actual
// stored type.
struct ArcHeader {
    strong: atomic::AtomicUsize,
    weak: atomic::AtomicUsize,
    drop_header: unsafe fn(*mut ArcHeader),
    drop_value: unsafe fn(*mut ArcHeader),
}

struct ArcBox<T> {
    header: ArcHeader,
    value: MaybeUninit<T>,
}

unsafe fn drop_header<T>(ptr: *mut ArcHeader) {
    let _ = Box::from_raw(ptr as *mut ArcBox<T>);
}

unsafe fn drop_value<T>(ptr: *mut ArcHeader) {
    let hptr = ptr as *mut ArcBox<T>;
    let dptr = ptr::addr_of_mut!((*hptr).value);
    (&mut *dptr).assume_init_drop();
}

pub struct Arc<T: ?Sized> {
    header: ptr::NonNull<ArcHeader>,
    ptr: ptr::NonNull<T>,
    phantom: PhantomData<T>,
}

pub struct Weak<T: ?Sized> {
    header: ptr::NonNull<ArcHeader>,
    ptr: ptr::NonNull<T>,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Arc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Send for Weak<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Arc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Weak<T> {}
impl<T: core::panic::RefUnwindSafe + ?Sized> core::panic::UnwindSafe for Arc<T> {}
impl<T: core::panic::RefUnwindSafe + ?Sized> core::panic::UnwindSafe for Weak<T> {}

impl<T: ?Sized> Deref for Arc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.ptr()
    }
}

impl<T> Arc<T> {
    pub fn new(value: T) -> Arc<T> {
        let b = Box::leak(Box::new(ArcBox {
            header: ArcHeader {
                strong: atomic::AtomicUsize::new(1),
                weak: atomic::AtomicUsize::new(1),
                drop_header: drop_header::<T>,
                drop_value: drop_value::<T>,
            },
            value: MaybeUninit::new(value),
        }));
        Arc {
            header: (&b.header).into(),
            ptr: unsafe { b.value.assume_init_ref() }.into(),
            phantom: PhantomData,
        }
    }

    /// Constructs a new `Arc<T>` while giving you a `Weak<T>` to the allocation,
    /// to allow you to construct a `T` which holds a weak pointer to itself.
    ///
    /// See `std::sync::Arc::new_cyclic` for more details.
    pub fn new_cyclic<F>(data_fn: F) -> Arc<T>
    where
        F: FnOnce(&Weak<T>) -> T,
    {
        // Construct the inner in the "uninitialized" state with a single weak
        // reference. We don't set strong=1 yet so that if `f` panics, we don't
        // try to drop the uninitialized value.
        let b = Box::leak(Box::new(ArcBox {
            header: ArcHeader {
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
        let strong = Arc {
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

impl<T: ?Sized> Arc<T> {
    /// Return an `Arc<T>` for a boxed value. Unlike `std::sync::Arc<T>`, this
    /// reuses the original box allocation rather than copying it. It still has
    /// to do a separate allocation for the (small) header object.
    pub fn from_box(value: Box<T>) -> Arc<T> {
        Arc::project(Arc::new(value), |x| &**x)
    }

    /// Return an `Arc<U>` for any type U contained within T, e.g. an element of a
    /// slice, or &dyn view of an object.
    pub fn project<U: ?Sized, F: for<'a> FnOnce(&'a T) -> &'a U>(s: Self, f: F) -> Arc<U> {
        let u = Arc {
            header: s.header,
            ptr: f(&*s).into(),
            phantom: PhantomData,
        };
        // Forget s so it doesn't decrement the refcount, since we moved it
        // into u.
        mem::forget(s);
        u
    }

    /// Convert `Arc<T>` to `Arc<U>`, as long as &T converts to &U.
    ///
    /// This should be spelled `from()`, but that conflicts with the blanket
    /// impl converting T->T.
    ///
    /// TODO: this doesn't work for slices; there's no blanket impl
    /// `for<'a> &'a [T]: From<&'a [T; N]>` and I don't know why.
    /// So for now you must call `project()` explicitly.
    pub fn cast<U: ?Sized>(this: Arc<T>) -> Arc<U>
    where
        for<'a> &'a U: From<&'a T>,
    {
        Arc::project(this, |x| From::from(x))
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

    fn header(&self) -> &ArcHeader {
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
    pub fn upgrade(self: &Self) -> Option<Arc<T>> {
        let h = self.header();
        // See Arc<T> for explanation of atomic logic
        let s = h.strong.fetch_update(
            Acquire,
            Relaxed,
            |n| {
                if n == 0 {
                    None
                } else {
                    Some(n + 1)
                }
            },
        );

        match s {
            Ok(_) => Some(Arc {
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

    fn header(&self) -> &ArcHeader {
        // Safety: header is always a valid reference
        unsafe { self.header.as_ref() }
    }
}

impl<T: ?Sized> Clone for Arc<T> {
    fn clone(&self) -> Self {
        let h = self.header();
        h.strong.fetch_add(1, Relaxed);
        Arc {
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

impl<T: ?Sized> Drop for Arc<T> {
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
        //
        // note: the Acquire in `Weak::drop` is to ensure that it happens-after
        // this Release, and therefore after `h.drop_value` is done.
        if h.weak.fetch_sub(1, Release) != 1 {
            return;
        }
        unsafe {
            (h.drop_header)(self.header.as_ptr());
        }
    }
}

impl<T: ?Sized> Drop for Weak<T> {
    fn drop(&mut self) {
        let h = self.header();
        if h.weak.fetch_sub(1, Release) != 1 {
            return;
        }
        // If we free the header, ensure that it happens-after `drop_value` has
        // completed in Arc::drop.
        h.weak.load(Acquire);
        unsafe {
            (h.drop_header)(self.header.as_ptr());
        }
    }
}

impl<T: ?Sized> borrow::Borrow<T> for Arc<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> AsRef<T> for Arc<T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Arc<T> {
    #[inline]
    fn eq(&self, other: &Arc<T>) -> bool {
        // TODO: MarkerEq shenanigans for optimized
        // comparisons in the face of float idiocy.
        *(*self) == *(*other)
    }

    #[inline]
    fn ne(&self, other: &Arc<T>) -> bool {
        *(*self) != *(*other)
    }
}

impl<T: ?Sized + PartialOrd> PartialOrd for Arc<T> {
    fn partial_cmp(&self, other: &Arc<T>) -> Option<cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }

    fn lt(&self, other: &Arc<T>) -> bool {
        *(*self) < *(*other)
    }

    fn le(&self, other: &Arc<T>) -> bool {
        *(*self) <= *(*other)
    }

    fn gt(&self, other: &Arc<T>) -> bool {
        *(*self) > *(*other)
    }

    fn ge(&self, other: &Arc<T>) -> bool {
        *(*self) >= *(*other)
    }
}

impl<T: ?Sized + Ord> cmp::Ord for Arc<T> {
    fn cmp(&self, other: &Arc<T>) -> cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + Eq> Eq for Arc<T> {}

impl<T: ?Sized + fmt::Display> fmt::Display for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized> fmt::Pointer for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(&**self as *const T), f)
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
// impl<'a, T: ?Sized, U: ?Sized> From<Arc<T>> for Arc<U> where &'a U: From<&'a T> {
//    fn from(x: Arc<T>) -> Arc<U> { Arc::project(x, |p| U::from(p)) }
// }

impl<T> iter::FromIterator<T> for Arc<[T]> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Self {
        Arc::from_box(iter.into_iter().collect())
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
        let x = Arc::new(2);
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
            let x = Arc::new(DropCounter((1, 2), &mut n));
            let y = Arc::project(x.clone(), |x| &x.0 .0);
            let z = Arc::project(x.clone(), |x| &x.0 .1);
            assert_eq!(*y, 1);
            assert_eq!(*z, 2);
            assert_eq!(Arc::strong_count(&z), 3);
            assert_eq!(Arc::weak_count(&z), 0);
            drop(x);
            drop(y);
            assert_eq!(Arc::strong_count(&z), 1);
            assert_eq!(Arc::weak_count(&z), 0);
            drop(z);
        }
        assert_eq!(n, 1);
    }

    #[test]
    fn test_trait_obj() {
        let x = Arc::new(2);
        let d = Arc::project(x.clone(), |p| p as &dyn std::fmt::Debug);
        assert_eq!(format!("{:?}", d), "2");
    }

    #[test]
    fn test_array_to_slice() {
        let x: Arc<[i32; 3]> = Arc::new([1, 2, 3]);
        let y: Arc<[i32]> = Arc::project(x.clone(), |p| &p[..]);
        let z: Arc<i32> = Arc::project(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_vec_to_slice() {
        // Note unlike Arc/Arc, this uses the existing Box/Vec allocation rather
        // than copying, and allocates space for the header separately.
        let x: Arc<Box<[i32]>> = Arc::new(vec![1, 2, 3].into());
        let y: Arc<[i32]> = Arc::project(x.clone(), |p| &p[..]);
        let z: Arc<i32> = Arc::project(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_cyclic() {
        struct Cyclic(Weak<Cyclic>);
        let x = Arc::new_cyclic(|p| Cyclic(p.clone()));
        assert_eq!(Arc::strong_count(&x), 1);
        assert_eq!(Arc::weak_count(&x), 1);
    }
}
