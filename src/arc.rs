//! `ash::rc::Rc<T>` is very similar to `std::rc::Rc<T>`, but with some
//! capabilities like C++'s `shared_ptr`.
//!
//! See module docs for detailed API, as it's mostly the same as
//! `ash::arc::Arc<T>`.
//!
//! ## See also
//!
//! `ash::arc::Arc<T>` in this crate is atomic version for sharing
//! data across threads.
use crate::ash;

use core::sync::atomic::{
    AtomicUsize,
    Ordering::{Acquire, Relaxed, Release},
};

unsafe impl ash::Count for AtomicUsize {
    fn new(v: usize) -> Self {
        AtomicUsize::new(v)
    }

    fn get(&self) -> usize {
        // relaxed ordering as this is only advisory
        self.load(Relaxed)
    }

    fn inc_relaxed(&self) -> usize {
        self.fetch_add(1, Relaxed)
    }

    fn set_release(&self, value: usize) {
        self.store(value, Release)
    }

    fn inc_if_nonzero(&self) -> bool {
        // See std::sync::Arc<T> for explanation of atomic logic
        self.fetch_update(
            Acquire,
            Relaxed,
            |n| {
                if n == 0 {
                    None
                } else {
                    Some(n + 1)
                }
            },
        )
        .is_ok()
    }

    fn dec(&self) -> usize {
        self.fetch_sub(1, Release)
    }

    fn acquire_fence(&self) {
        // either `fence()` or `load()` would work here, and either may be more
        // performant depending on platform details.
        self.load(Acquire);
    }
}

pub type Arc<T> = ash::Ash<T, AtomicUsize, false>;
pub type ArcBox<T> = ash::Ash<T, AtomicUsize, true>;
pub type Weak<T> = ash::Weak<T, AtomicUsize>;

#[cfg(test)]
mod tests {
    use super::*;

    fn counts<T>(x: &Arc<T>) -> (usize, usize) {
        (Arc::strong_count(x), Arc::weak_count(x))
    }
    fn wcounts<T>(x: &Weak<T>) -> (usize, usize) {
        (Weak::strong_count(x), Weak::weak_count(x))
    }

    struct DropCounter<'a, T>(T, &'a mut usize);
    impl<'a, T> Drop for DropCounter<'a, T> {
        fn drop(&mut self) {
            *self.1 += 1;
        }
    }

    #[test]
    fn test_simpler() {
        let x = Arc::new(2);
        assert_eq!(*x, 2);
        drop(x);
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
    fn test_weak() {
        let x = Arc::new(2);
        let y = Arc::downgrade(&x);
        assert_eq!(wcounts(&y), (1, 1));
        drop(x);
        drop(y);
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
            assert_eq!(counts(&z), (3, 0));
            drop(x);
            drop(y);
            assert_eq!(counts(&z), (1, 0));
            drop(z);
        }
        assert_eq!(n, 1);

        // Updating the mut ref to `n` above looks sketchy. Confirm that std Arc
        // allows the same thing.
        {
            let x = std::sync::Arc::new(DropCounter((1, 2), &mut n));
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

    #[test]
    fn test_oopsie() {
        let a: Arc<[i32; 3]> = Arc::new([1, 2, 3]);
        let w: Weak<[i32; 3]> = Arc::downgrade(&a);
        assert_eq!(w.strong_count(), 1);

        // convert the sized array into a slice
        let b: Arc<[i32]> = Arc::project(a, |x| &x[..]);

        // get a reference to one element of the array
        let c: Arc<i32> = Arc::project(b, |x| &x[1]);
        assert_eq!(w.strong_count(), 1);

        // `c` is keeping the whole object alive
        assert!(w.upgrade().is_some());
        assert_eq!(w.strong_count(), 1);
        drop(c);
        assert_eq!(w.strong_count(), 0);
        assert!(w.upgrade().is_none());
    }
}
