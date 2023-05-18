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
use std::cell::Cell;

unsafe impl ash::Count for Cell<usize> {
    fn new(v: usize) -> Self {
        Cell::new(v)
    }

    fn get(&self) -> usize {
        Cell::get(self)
    }

    fn inc_relaxed(&self) -> usize {
        let i = self.get();
        self.set(i + 1);
        i
    }

    fn inc_if_nonzero(&self) -> bool {
        let i = self.get();
        if i != 0 {
            self.set(i + 1);
            true
        } else {
            false
        }
    }

    fn set_release(&self, old: usize, new: usize) {
        assert_eq!(self.get(), old);
        self.set(new);
    }

    fn dec(&self) -> usize {
        let i = self.get();
        self.set(i - 1);
        i
    }

    fn acquire_fence(&self) {}
}

pub type Rc<T, const UNIQ: bool = false> = ash::Ash<T, Cell<usize>, UNIQ>;
pub type RcBox<T> = Rc<T, true>;
pub type Weak<T> = ash::Weak<T, Cell<usize>>;

#[cfg(test)]
mod tests {
    use super::*;

    fn counts<T>(x: &Rc<T>) -> (usize, usize) {
        (Rc::strong_count(x), Rc::weak_count(x))
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
        let x = Rc::new(2);
        assert_eq!(*x, 2);
        drop(x);
    }

    #[test]
    fn test_simple() {
        let x = Rc::new(2);
        let y = x.clone();
        assert_eq!(*x, 2);
        assert_eq!(&*x as *const i32, &*y as *const i32);
        drop(x);
        assert_eq!(*y, 2);
    }

    #[test]
    fn test_weak() {
        let x = Rc::new(2);
        let y = Rc::downgrade(&x);
        assert_eq!(wcounts(&y), (1, 1));
        drop(x);
        drop(y);
    }

    #[test]
    fn test_derived() {
        let mut n = 0;
        {
            let x = Rc::new(DropCounter((1, 2), &mut n));
            let y = Rc::project(x.clone(), |x| &x.0 .0);
            let z = Rc::project(x.clone(), |x| &x.0 .1);
            assert_eq!(*y, 1);
            assert_eq!(*z, 2);
            assert_eq!(counts(&z), (3, 0));
            drop(x);
            drop(y);
            assert_eq!(counts(&z), (1, 0));
            drop(z);
        }
        assert_eq!(n, 1);

        // Updating the mut ref to `n` above looks sketchy. Confirm that rc::Rc
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
        let x = Rc::new(2);
        let d = Rc::project(x.clone(), |p| p as &dyn std::fmt::Debug);
        assert_eq!(format!("{:?}", d), "2");
    }

    #[test]
    fn test_array_to_slice() {
        let x: Rc<[i32; 3]> = Rc::new([1, 2, 3]);
        let y: Rc<[i32]> = Rc::project(x.clone(), |p| &p[..]);
        let z: Rc<i32> = Rc::project(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_vec_to_slice() {
        // Note unlike Arc/Rc, this uses the existing Box/Vec allocation rather
        // than copying, and allocates space for the header separately.
        let x: Rc<Box<[i32]>> = Rc::new(vec![1, 2, 3].into());
        let y: Rc<[i32]> = Rc::project(x.clone(), |p| &p[..]);
        let z: Rc<i32> = Rc::project(y.clone(), |p| &p[1]);
        assert_eq!(format!("{:?}", y), "[1, 2, 3]");
        assert_eq!(format!("{:?}", z), "2");
    }

    #[test]
    fn test_cyclic() {
        struct Cyclic(Weak<Cyclic>);
        let x = Rc::new_cyclic(|p| Cyclic(p.clone()));
        assert_eq!(Rc::strong_count(&x), 1);
        assert_eq!(Rc::weak_count(&x), 1);
    }

    #[test]
    fn test_oopsie() {
        let a: Rc<[i32; 3]> = Rc::new([1, 2, 3]);
        let w: Weak<[i32; 3]> = Rc::downgrade(&a);
        assert_eq!(w.strong_count(), 1);

        // convert the sized array into a slice
        let b: Rc<[i32]> = Rc::project(a, |x| &x[..]);

        // get a reference to one element of the array
        let c: Rc<i32> = Rc::project(b, |x| &x[1]);
        assert_eq!(w.strong_count(), 1);

        // `c` is keeping the whole object alive
        assert!(w.upgrade().is_some());
        assert_eq!(w.strong_count(), 1);
        drop(c);
        assert_eq!(w.strong_count(), 0);
        assert!(w.upgrade().is_none());
    }

    #[test]
    fn test_cmp() {
        let a = Rc::new(1);
        let b = Rc::new(2);
        assert!(a < b);
    }

    #[test]
    fn test_new_unique() {
        // Example of creating a tree with weak parent pointers, without having
        // to use Cell or RefCell, in a simpler way than new_cyclic.
        struct Tree {
            parent: Option<Weak<Tree>>,
            children: Vec<Rc<Tree>>,
        }
        let mut root = Rc::new_unique(Tree {
            parent: None,
            children: vec![],
        });
        for _ in 1..3 {
            let c = Rc::new(Tree {
                parent: Some(Rc::downgrade(&root)),
                children: vec![],
            });
            root.children.push(c);
        }

        // we still have a unique handle on the parent, so attempting to upgrade
        // weak pointers will fail.
        let p = root.children[0].parent.clone();
        assert!(p.clone().unwrap().upgrade().is_none());

        let root: Rc<_> = root.into();
        // now we have a normal Rc to the parent, so we can upgrade child pointers
        assert!(Rc::ptr_eq(&p.unwrap().upgrade().unwrap(), &root));
    }
}
