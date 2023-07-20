//! `genrc::Genrc<T, C>` implements `Arc` and `Rc` generically across the count type
//! (atomic vs. nonatomic).
//!
//! See module docs for detailed API
//!
//! ## See also
//!
//! `genrc::arc::Arc<T>` in this crate is atomic version for sharing data across
//! threads.
//!
//! `genrc::rc::Rc<T>` in this crate is nonatomic version for single-threaded use.
use alloc::boxed::Box;
use core::{
    borrow, cmp, fmt,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::{self, NonNull},
};

#[cfg(feature = "allocator_api")]
use {alloc::alloc::Global, core::alloc::Allocator};

#[cfg(not(feature = "allocator_api"))]
mod dummy_alloc {
    #[derive(Clone)]
    pub(crate) struct Global;
    pub(crate) trait Allocator {}
    impl Allocator for Global {}
}
#[cfg(not(feature = "allocator_api"))]
use dummy_alloc::*;

/// Trait to distinguish [`Rc<T>`][crate::Rc] from [`Arc<T>`][crate::Arc]. The
/// only implementers are [`Atomic`][crate::Atomic] and [`Nonatomic`][crate::Nonatomic].
///
/// It is `pub` so you can write code that's generic over atomicity, but there's
/// no reason to implement it for any other types.
///
/// # Safety
/// Trait is private.
pub unsafe trait Atomicity: private::Sealed {
    #[doc(hidden)]
    fn new(v: usize) -> Self;
    #[doc(hidden)]
    fn get(&self) -> usize;
    #[doc(hidden)]
    fn inc_relaxed(&self) -> usize;
    #[doc(hidden)]
    fn set_release(&self, value: usize);
    #[doc(hidden)]
    fn inc_if_nonzero(&self) -> bool;
    #[doc(hidden)]
    fn dec(&self) -> usize;
    #[doc(hidden)]
    fn acquire_fence(&self);
}

// Counts and destructors for objects owned by Genrc.
struct Header<C> {
    strong: C,
    weak: C,
    drop_header: unsafe fn(*mut Header<C>),
    drop_value: unsafe fn(*mut Header<C>),
}

#[repr(C)]
struct Alloc<T, C, A> {
    header: Header<C>,
    alloc: MaybeUninit<A>,
    value: MaybeUninit<T>,
}

/// Generic implementation behind `Rc`, `Rcl`, `RcBox`, `Arc`, `Arcl`,
/// and `ArcBox`.
pub struct Genrc<'a, T: ?Sized, C: Atomicity, const UNIQ: bool = false> {
    header: ptr::NonNull<Header<C>>,
    ptr: ptr::NonNull<T>,
    phantom: PhantomData<(&'a (), T)>,
}

/// Generic implementation behind `rc::Weak` and `arc::Weak`, distinguished
/// by `Atomicity`.
pub struct Weak<'a, T: ?Sized, C: Atomicity> {
    header: ptr::NonNull<Header<C>>,
    ptr: ptr::NonNull<T>,
    phantom: PhantomData<&'a T>,
}

impl<'a, T, C: Atomicity, const UNIQ: bool> Genrc<'a, T, C, UNIQ> {
    /// Constructs a new `GenRc<T>` with the given value.
    ///
    /// The returned pointer is known to be unique, so it
    /// implements [`std::ops::DerefMut`]
    pub fn new_unique(value: T) -> Genrc<'a, T, C, true> {
        Genrc::<T, C, true>::new(value)
    }

    /// Constructs a new `GenRc<T>` with the given value.
    pub fn new(value: T) -> Self {
        let initial_strong_count = if UNIQ { 0 } else { 1 };
        let b = Box::into_raw(Box::new(Alloc {
            header: Header {
                strong: C::new(initial_strong_count),
                weak: C::new(1),
                drop_header: drop_header::<T, C, Global>,
                drop_value: drop_value::<T, C, Global>,
            },
            alloc: MaybeUninit::new(Global),
            value: MaybeUninit::new(value),
        }));
        let h = b as *mut Header<C>;
        let v = unsafe { ptr::addr_of!((*b).value) as *mut T };
        Genrc {
            header: unsafe { ptr::NonNull::new_unchecked(h) },
            ptr: unsafe { ptr::NonNull::new_unchecked(v) },
            phantom: PhantomData,
        }
    }

    /// Constructs a new `Genrc<T, C>` while giving you a `Weak<T, C>` to the allocation,
    /// to allow you to construct a `T` which holds a weak pointer to itself.
    ///
    /// See `std::rc::Rc::new_cyclic` for more details.
    ///
    /// Note that `RcBox<T>` (or `ArcBox<T>`) enable easier construction of
    /// cyclic values; this is here mostly for `std` compatibility.
    /// See the main crate documentation for examples.
    pub fn new_cyclic<F>(data_fn: F) -> Genrc<'a, T, C>
    where
        F: FnOnce(&Weak<'a, T, C>) -> T,
        T: 'a,
    {
        // Construct the inner in the "uninitialized" state with a single weak
        // reference. We don't set strong=1 yet so that if `f` panics, we don't
        // try to drop the uninitialized value.
        let b = Box::into_raw(Box::new(Alloc {
            header: Header {
                strong: C::new(0),
                weak: C::new(1),
                drop_header: drop_header::<T, C, Global>,
                drop_value: drop_value::<T, C, Global>,
            },
            alloc: MaybeUninit::new(Global),
            value: MaybeUninit::uninit(),
        }));
        let weak = Weak {
            header: unsafe { ptr::NonNull::new_unchecked(b as *mut Header<C>) },
            ptr: unsafe { ptr::NonNull::new_unchecked(ptr::addr_of!((*b).value) as *mut _) },
            phantom: PhantomData,
        };

        // Safety: we just allocated with `value` uninitialized
        unsafe { ptr::write((*b).value.as_mut_ptr(), data_fn(&weak)) };

        // Now that the inner is initialized, we can set the strong count to 1.
        let h = weak.header();
        let old_strong = h.strong.inc_relaxed();
        debug_assert_eq!(old_strong, 0, "No prior strong references should exist");
        let strong = Genrc {
            header: weak.header,
            ptr: weak.ptr,
            phantom: PhantomData,
        };

        // Strong references collectively own a shared weak reference, so don't
        // run the destructor for our old weak reference.
        mem::forget(weak);
        strong
    }

    #[cfg(feature = "allocator_api")]
    pub fn new_in<A>(value: T, alloc: A) -> Self
    where
        A: Allocator + Clone + 'a,
    {
        let initial_strong_count = if UNIQ { 0 } else { 1 };
        let b = Box::into_raw(Box::new_in(
            Alloc {
                header: Header {
                    strong: C::new(initial_strong_count),
                    weak: C::new(1),
                    drop_header: drop_header::<T, C, A>,
                    drop_value: drop_value::<T, C, A>,
                },
                alloc: MaybeUninit::new(alloc.clone()),
                value: MaybeUninit::new(value),
            },
            alloc,
        ));

        let h = b as *mut Header<C>;
        let v = unsafe { ptr::addr_of!((*b).value) as *mut T };
        Genrc {
            header: unsafe { ptr::NonNull::new_unchecked(h) },
            ptr: unsafe { ptr::NonNull::new_unchecked(v) },
            phantom: PhantomData,
        }
    }

    /// Constructs a new `Pin<Rc<T>>`. If `T` does not implement `Unpin`, then
    /// `value` will be pinned in memory and unable to be moved.
    #[cfg(not(no_global_oom_handling))]
    pub fn pin(value: T) -> Pin<Self> {
        let rc: Self = Self::new(value);
        unsafe { Pin::new_unchecked(rc) }
    }
}

impl<'a, T: ?Sized, C: Atomicity> Genrc<'a, T, C> {
    /// Return a `Genrc<T, C>` for a boxed value. Unlike `std::Rc`, this reuses
    /// the original box allocation rather than copying it. However it still has
    /// to do a small allocation for the header with the reference counts.
    #[cfg(not(feature = "allocator_api"))]
    pub fn from_box(value: Box<T>) -> Self
    where
        T: 'a,
    {
        Genrc::project(Genrc::<Box<T>, C>::new(value), |x| &**x)
    }

    /// Return a `Genrc<T, C>` for a boxed value. Unlike `std::Rc`, this reuses
    /// the original box allocation rather than copying it. However it still has
    /// to do a small allocation for the header with the reference counts.
    ///
    /// If the box uses a custom allocator, the same allocator will be used for
    /// the Rc. If that isn't the desired behavior, you can call `Rc::new` or
    /// `new_in` to specify the allocator you want, and then `project` to hide
    /// the box.
    #[cfg(feature = "allocator_api")]
    pub fn from_box<A>(value: Box<T, A>) -> Self
    where
        A: Allocator + Clone + 'a,
    {
        let alloc = Box::allocator(&value).clone();
        Genrc::project(Genrc::<Box<T, A>, C>::new_in(value, alloc), |x| &**x)
    }

    /// Constructs a new `Genrc<T, ...>` from a reference without copying.
    ///
    /// ```
    /// use genrc::Rcl;
    /// let x = 5;
    /// let p : Rcl<i32> = Rcl::from_ref(&x);
    /// assert!(std::ptr::eq(&*p, &x));
    /// ```
    pub fn from_ref(value: &'a T) -> Self {
        Genrc::project(Genrc::<'a, &'a T, C>::new(value), Deref::deref)
    }

    /// Convert `Genrc<T>` to `Genrc<U>`, as long as &T converts to &U.
    ///
    /// This should be spelled `from()`, but that conflicts with the blanket
    /// impl converting T->T.
    ///
    /// TODO: this doesn't work for slices; there's no blanket impl
    /// `for<'a> &'a [T]: From<&'a [T; N]>` and I don't know why.
    /// So for now you must call `project()` explicitly.
    pub fn cast<U: ?Sized>(this: Genrc<'a, T, C>) -> Genrc<'a, U, C>
    where
        T: 'a,
        U: 'a,
        for<'u> &'u U: From<&'u T>,
    {
        Genrc::project(this, |x| From::from(x))
    }

    /// Returns true if two `Genrc` pointers point to the same object. Note that
    /// this is is not the same as sharing the same allocation: e.g. both might
    /// point to the same static object due to project(), or both might point
    /// to different subobjects of the same root pointer.
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr == other.ptr
    }

    /// Returns true if two `Genrc` pointers point to the same allocation, i.e.
    /// they share reference counts. Note that they may point to different
    /// subobjects within that allocation due to `project()`.
    pub fn root_ptr_eq(this: &Self, other: &Self) -> bool {
        this.header == other.header
    }
}

impl<'a, T: ?Sized, C: Atomicity> Genrc<'a, T, C, true> {
    /// Return an `RcBox<U>` for any type U contained within T, e.g. an element
    /// of a slice, or &dyn view of an object.
    pub fn project_mut<'b, U: ?Sized, F: FnOnce(&mut T) -> &mut U>(
        mut s: Self,
        f: F,
    ) -> Genrc<'b, U, C, true>
    where
        T: 'a,
        U: 'b,
        'a: 'b,
    {
        let u = Genrc {
            header: s.header,
            ptr: f(&mut *s).into(),
            phantom: PhantomData,
        };
        // Forget s so it doesn't adjust the refcount, since we moved it
        // into u.
        mem::forget(s);
        u
    }

    /// Constructs a new `RcBox<T, ...>` from a reference without copying.
    ///
    /// ```
    /// use genrc::RcBox;
    /// let mut x = 5;
    /// {
    ///     let mut p : RcBox<i32> = RcBox::from_mut_ref(&mut x);
    ///     *p = 6;
    /// }
    /// assert_eq!(x, 6);
    /// ```
    pub fn from_mut_ref(value: &'a mut T) -> Self {
        Genrc::project_mut(Genrc::<&'a mut T, C, true>::new(value), DerefMut::deref_mut)
    }

    /// A unique ("Box") pointer can be lowered to a normal shared pointer
    pub fn shared(this: Genrc<'a, T, C, true>) -> Genrc<'a, T, C, false> {
        // At this point, we may have weak pointers in other threads, so we need
        // to synchronize with them possibly being upgraded to strong pointers.
        // upgrade does an acquire on the strong count, so we need to increment
        // it (from 0 -> 1) with a release.
        debug_assert_eq!(this.header().strong.get(), 0);
        this.header().strong.set_release(1);
        let header = this.header;
        let ptr = this.ptr;
        // Forget `this` so it doesn't adjust the refcount
        mem::forget(this);
        Genrc {
            header,
            ptr,
            phantom: PhantomData,
        }
    }
}

impl<'a, T: ?Sized, C: Atomicity, const UNIQ: bool> Genrc<'a, T, C, UNIQ> {
    /// Return a `Genrc<U>` for any type U contained within T, e.g. an element of
    /// a slice, or &dyn view of an object.
    ///
    /// Calling `project()` on an `RcBox` or `ArcBox` will downgrade it to a
    /// normal `Rc` or `Arc`. Use `project_mut()` if you need to preserve
    /// uniqueness.
    pub fn project<'u, U: ?Sized, F: FnOnce(&T) -> &U>(this: Self, f: F) -> Genrc<'u, U, C, false> {
        let ptr = f(this.ptr()).into();
        Self::projected(this, ptr)
    }

    /// Fallible version of `project()`.
    pub fn try_project<'u, U: ?Sized, F: FnOnce(&T) -> Option<&U>>(
        this: Self,
        f: F,
    ) -> Option<Genrc<'u, U, C, false>> {
        match f(this.ptr()) {
            None => None,
            Some(u) => {
                let ptr = u.into();
                Some(Self::projected(this, ptr))
            }
        }
    }

    fn projected<'u, U: ?Sized>(this: Self, ptr: NonNull<U>) -> Genrc<'u, U, C, false> {
        if UNIQ {
            // original pointer is an RcBox and we're downgrading to Rc
            debug_assert_eq!(this.header().strong.get(), 0);
            this.header().strong.set_release(1);
        }
        let u = Genrc {
            header: this.header,
            ptr,
            phantom: PhantomData,
        };
        // Forget s so it doesn't adjust the refcount, since we moved it into u.
        mem::forget(this);
        u
    }

    /// Return a [`Weak`] pointer to this object.
    pub fn downgrade(this: &Genrc<T, C, UNIQ>) -> Weak<'a, T, C> {
        let h = this.header();
        h.weak.inc_relaxed();
        Weak {
            header: this.header,
            ptr: this.ptr,
            phantom: PhantomData,
        }
    }

    /// Returns a mutable reference into the given `Rc`, without any check.
    ///
    /// See also [`get_mut`], which is safe and does appropriate checks.
    ///
    /// [`get_mut`]: Genrc::get_mut
    ///
    /// # Safety
    ///
    /// If any other `Rc` or [`Weak`] pointers to the same allocation exist,
    /// then they must not be dereferenced or have active borrows for the
    /// duration of the returned borrow, and their inner type must be exactly
    /// the same as the inner type of this Rc (including lifetimes). This is
    /// trivially the case if no such pointers exist, for example immediately
    /// after `Rc::new`.
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        unsafe { this.ptr.as_mut() }
    }

    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if Genrc::is_unique(this) {
            unsafe { Some(Genrc::get_mut_unchecked(this)) }
        } else {
            None
        }
    }

    /// Returns `true` if are no other `Rc` or [`Weak`] pointers to this
    /// allocation.
    ///
    /// If this is a unique pointer (`RcBox` or `ArcBox`) then is_unique always
    /// returns true, even if weak pointers exist, since those weak pointers
    /// cannot (yet) be upgraded.
    #[inline]
    fn is_unique(this: &Self) -> bool {
        UNIQ || (Genrc::weak_count(this) == 0 && Genrc::strong_count(this) == 1)
    }

    fn ptr(&self) -> &'a T {
        // Safety: ptr is always a valid reference, there's just no way to
        // spell the lifetime in Rust, so callers manage it with refcounts.
        unsafe { self.ptr.as_ref() }
    }

    fn header(&self) -> &Header<C> {
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

impl<'a, T: ?Sized, C: Atomicity> Weak<'a, T, C> {
    pub fn upgrade(&self) -> Option<Genrc<'a, T, C>> {
        let h = self.header();
        if h.strong.inc_if_nonzero() {
            Some(Genrc {
                header: self.header,
                ptr: self.ptr,
                phantom: PhantomData,
            })
        } else {
            None
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

    fn header(&self) -> &Header<C> {
        // Safety: header is always a valid reference
        unsafe { self.header.as_ref() }
    }
}

impl<'a, T: ?Sized, C: Atomicity, const UNIQ: bool> AsRef<T> for Genrc<'a, T, C, UNIQ> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized, C: Atomicity, const UNIQ: bool> borrow::Borrow<T> for Genrc<'a, T, C, UNIQ> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<'a, T: ?Sized, C: Atomicity> Clone for Genrc<'a, T, C> {
    fn clone(&self) -> Self {
        let h = self.header();
        h.strong.inc_relaxed();
        Genrc {
            header: self.header,
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<'a, T: ?Sized, C: Atomicity> Clone for Weak<'a, T, C> {
    fn clone(&self) -> Self {
        let h = self.header();
        h.weak.inc_relaxed();
        Weak {
            header: self.header,
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

impl<'a, T: Default, C: Atomicity, const UNIQ: bool> Default for Genrc<'a, T, C, UNIQ> {
    fn default() -> Self {
        Genrc::new(T::default())
    }
}

impl<'a, T: ?Sized, C: Atomicity, const UNIQ: bool> Deref for Genrc<'a, T, C, UNIQ> {
    type Target = T;

    fn deref(&self) -> &T {
        self.ptr()
    }
}

/// If we still have a unique reference, we can safely mutate the
/// contents.
impl<'a, T: 'a + ?Sized, C: Atomicity> DerefMut for Genrc<'a, T, C, true> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: ptr is always a valid reference, there's just no
        // way to spell the lifetime in Rust. Since we're a unique
        // RC, it's also safe to convert to mut ref.
        unsafe { self.ptr.as_mut() }
    }
}

impl<'a, T: ?Sized, C: Atomicity, const UNIQ: bool> Drop for Genrc<'a, T, C, UNIQ> {
    fn drop(&mut self) {
        let h = self.header();
        if !UNIQ && h.strong.dec() != 1 {
            return;
        }
        // last strong pointer was just dropped
        h.strong.acquire_fence();
        unsafe {
            let f = h.drop_value;
            f(self.header.as_ptr());
        }

        // decrement weak count owned by strong ptrs
        //
        // note: the Acquire in `Weak::drop` is to ensure that it happens-after
        // this Release, and therefore after `h.drop_value` is done.
        //
        // We drop ourselves here rather than constructing a Weak to do it,
        // because in this case we know we're on the same thread and can skip
        // the Acquire.
        if h.weak.dec() != 1 {
            return;
        }
        unsafe {
            // last weak pointer was just dropped
            let h = self.header.as_mut();
            let f = h.drop_header;
            f(self.header.as_ptr());
        }
    }
}

impl<'a, T: ?Sized, C: Atomicity> Drop for Weak<'a, T, C> {
    fn drop(&mut self) {
        let h = self.header();
        if h.weak.dec() != 1 {
            return;
        }
        // If we free the header, ensure that it happens-after `drop_value` has
        // completed in Arc::drop.
        h.weak.acquire_fence();
        unsafe {
            let f = h.drop_header;
            f(self.header.as_ptr());
        }
    }
}

/// A unique pointer can be lowered to a shared pointer.
impl<'a, T: 'a, C: Atomicity> From<Genrc<'a, T, C, true>> for Genrc<'a, T, C, false> {
    fn from(uniq: Genrc<'a, T, C, true>) -> Self {
        Genrc::<'a, T, C, true>::shared(uniq)
    }
}

impl<'a, T: ?Sized + PartialEq, C: Atomicity, const Q1: bool, const Q2: bool>
    PartialEq<Genrc<'a, T, C, Q2>> for Genrc<'a, T, C, Q1>
{
    #[inline]
    fn eq(&self, other: &Genrc<T, C, Q2>) -> bool {
        // TODO: MarkerEq shenanigans for optimized
        // comparisons in the face of float idiocy.
        *(*self) == *(*other)
    }
}

impl<'a, T: ?Sized + PartialOrd, C: Atomicity, const Q1: bool, const Q2: bool>
    PartialOrd<Genrc<'a, T, C, Q2>> for Genrc<'a, T, C, Q1>
{
    fn partial_cmp(&self, other: &Genrc<T, C, Q2>) -> Option<cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }

    fn lt(&self, other: &Genrc<T, C, Q2>) -> bool {
        *(*self) < *(*other)
    }

    fn le(&self, other: &Genrc<T, C, Q2>) -> bool {
        *(*self) <= *(*other)
    }

    fn gt(&self, other: &Genrc<T, C, Q2>) -> bool {
        *(*self) > *(*other)
    }

    fn ge(&self, other: &Genrc<T, C, Q2>) -> bool {
        *(*self) >= *(*other)
    }
}

impl<'a, T: 'a + ?Sized + Ord, C: Atomicity, const UNIQ: bool> cmp::Ord for Genrc<'a, T, C, UNIQ> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<'a, T: 'a + ?Sized + Eq, C: Atomicity, const UNIQ: bool> Eq for Genrc<'a, T, C, UNIQ> {}

impl<'a, T: 'a + ?Sized + fmt::Display, C: Atomicity, const UNIQ: bool> fmt::Display
    for Genrc<'a, T, C, UNIQ>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<'a, T: 'a + ?Sized + fmt::Debug, C: Atomicity, const UNIQ: bool> fmt::Debug
    for Genrc<'a, T, C, UNIQ>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: 'a + ?Sized, C: Atomicity, const UNIQ: bool> fmt::Pointer for Genrc<'a, T, C, UNIQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(&**self as *const T), f)
    }
}

impl<'a, T: ?Sized + fmt::Debug, C: Atomicity> fmt::Debug for Weak<'a, T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(Weak)")
    }
}

unsafe fn drop_header<T, C, A: Allocator>(ptr: *mut Header<C>) {
    let ptr = ptr as *mut Alloc<T, C, A>;
    #[cfg(not(feature = "allocator_api"))]
    let _ = Box::from_raw(ptr);
    #[cfg(feature = "allocator_api")]
    {
        let alloc = (&mut *ptr).alloc.assume_init_read();
        let _ = Box::from_raw_in(ptr as *mut Alloc<T, C, A>, alloc);
    }
}

unsafe fn drop_value<T, C, A>(ptr: *mut Header<C>) {
    let bptr = ptr as *mut Alloc<T, C, A>;
    let bref = &mut *bptr;
    bref.value.assume_init_drop();
}

pub(crate) mod private {
    pub trait Sealed {}
}
