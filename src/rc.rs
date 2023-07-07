//! `ash::rc::Rc<T>` is very similar to `std::rc::Rc<T>`, but with some
//! capabilities like C++'s `shared_ptr`.
//!
//! See module docs for detailed API, as it's mostly the same as
//! `ash::arc::Arc<T>`.
use crate::ash;
use std::cell::Cell;

#[repr(transparent)]
pub struct Nonatomic(Cell<usize>);

unsafe impl ash::Count for Nonatomic {
    fn new(v: usize) -> Self {
        Nonatomic(Cell::new(v))
    }

    fn get(&self) -> usize {
        Cell::get(&self.0)
    }

    fn inc_relaxed(&self) -> usize {
        let i = self.get();
        self.0.set(i + 1);
        i
    }

    fn inc_if_nonzero(&self) -> bool {
        let i = self.get();
        if i != 0 {
            self.0.set(i + 1);
            true
        } else {
            false
        }
    }

    fn set_release(&self, value: usize) {
        self.0.set(value);
    }

    fn dec(&self) -> usize {
        let i = self.get();
        self.0.set(i - 1);
        i
    }

    fn acquire_fence(&self) {}
}

pub type Rcl<'a, T> = ash::Ash<'a, T, Nonatomic, false>;
pub type Weakl<'a, T> = ash::Weak<'a, T, Nonatomic>;
pub type Rc<T> = Rcl<'static, T>;
pub type Weak<T> = Weakl<'static, T>;
pub type RcBox<'a, T> = ash::Ash<'a, T, Nonatomic, true>;

#[cfg(test)]
mod tests {
    use super::*;

    fn counts<T>(x: &Rcl<T>) -> (usize, usize) {
        (Rcl::strong_count(x), Rcl::weak_count(x))
    }
    fn wcounts<T>(x: &Weakl<T>) -> (usize, usize) {
        (Weakl::strong_count(x), Weakl::weak_count(x))
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
            let x = Rcl::new(DropCounter((1, 2), &mut n));
            let y = Rcl::project(x.clone(), |x| &x.0 .0);
            let z = Rcl::project(x.clone(), |x| &x.0 .1);
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
        let w = Rc::downgrade(&a);
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
    fn test_ptr_eq() {
        // pointer equality is based the address of the subobject.
        // Unlike for `std::rc::Rc` this is not the same thing
        // as sharing the same allocation.

        // normal case
        let a = Rc::new(1);
        let b = Rc::new(1);
        let c = a.clone();
        assert!(!Rc::ptr_eq(&a, &b));
        assert!(Rc::ptr_eq(&a, &c));

        // two pointers with the same allocation but different addresses
        let a = Rc::new([1, 1]);
        let b = Rc::project(a.clone(), |x| &x[0]);
        let c = Rc::project(a.clone(), |x| &x[1]);
        assert!(!Rc::ptr_eq(&b, &c));

        {
            // two objects with different allocations but the same address
            let obj = 1;
            let p1: Rcl<&i32> = Rcl::new(&obj);
            let p2: Rcl<i32> = Rcl::project(p1, |x| &**x);
            let p3 = Rcl::new(&obj);
            let p4 = Rcl::project(p3, |x| &**x);
            assert!(Rcl::ptr_eq(&p2, &p4));
        };
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
        // to use Cell or RefCell, in a simpler way than new_cyclic. Uses
        // [`Rc::new_unique`] to get a unique Rc to the parent during
        // construction.
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
                parent: Some(RcBox::downgrade(&root)),
                children: vec![],
            });
            root.children.push(c);
        }

        // we still have a unique handle on the parent, so attempting to upgrade
        // weak pointers will fail.
        let p = root.children[0].parent.clone();
        assert!(p.clone().unwrap().upgrade().is_none());

        // Convert the root pointer to a normal Rc.
        let root = RcBox::shared(root);

        // now we have a normal Rc to the parent, so we can upgrade child pointers
        assert!(Rcl::ptr_eq(&p.unwrap().upgrade().unwrap(), &root));
    }
}
