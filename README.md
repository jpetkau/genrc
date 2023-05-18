# ash

This crate provides alternatives to `Arc` and `Rc` that allow refcounted
pointers to subobjects, like C++'s `shared_ptr`.

If you have an `Rc<T>`, and `T` contains some subobject of type `U`, then
you can construct an `Rc<U>` that shares ownership with the original
object, by calling `Rc::project()`.

```rust
    use ash::rc::{Rc, Weak};
    let a: Rc<[i32; 3]> = Rc::new([1, 2, 3]);
    let w: Weak<[i32; 3]> = Rc::downgrade(&a);

    // convert the sized array into a slice
    let b: Rc<[i32]> = Rc::project(a, |x| &x[..]);

    // get a reference to one element of the array
    let c: Rc<i32> = Rc::project(b, |x| &x[1]);

    // `c` is keeping the whole object alive
    assert!(w.upgrade().is_some());
    drop(c);
    assert!(w.upgrade().is_none());
```

Unlike `std`, references can point to const or static data without
copying:

```rust
    # use ash::rc::{Rc, Weak};

    const bigbuf: [u8; 1024] = [1; 1024];

    let p: Rc<()> = Rc::new(());
    let p: Rc<[u8]> = Rc::project(p, |_| &bigbuf[..]);
```


### Differences from `std::sync::Arc` and `std::rc::Rc`

`Rc::from_box` does not copy the object from the original box. Instead it
takes ownership of the box as-is, with the counts in a separate allocation.

If you leak so many Rc objects that the refcount overflows, the std
pointers will abort. `ash` does not, because there is no `abort()`
function in `no_std`.

Implicit conversion from `Rc<T>` to `Rc<dyn Trait>` is not supported,
because that requires some unstable traits. However you can do the
conversion explicitly with `Rc::project`. TODO: support this behind a
nightly-requiring feature.

The std pointers have various `MaybeUninit`-related methods for initializing
objects after allocation. That API isn't possible in Ash, because the initial
object is type-erased. However, `project` allows you to do the same thing
entirely safely with `Option`:

```skip
    # use ash::rc::{Rc, Weak};
    let obj : Rc<Option<i32>> = Rc::new(None);
    Rc::get_mut(&mut obj).unwrap().replace(5);
    let obj : Rc<i32> = Rc::project(obj, |x| x.as_ref().unwrap());

    assert_eq!(*obj, 5);
```


### Related Crates

- [`shared-rc`](https://lib.rs/crates/shared-rc): Similar to this crate, but
  uses the std versions of `Arc` and `Rc` under the hood.
- [`rc-box`](https://lib.rs/crates/rc-box): Known unique versions of Rc and Arc.
- [`erasable`](https://lib.rs/crates/erasable): Erase pointers of their concrete type.
- [`ptr-union`](https://lib.rs/crates/ptr-union): Pointer unions the size of a pointer.
- [`rc-borrow`](https://lib.rs/crates/rc-borrow): Borrowed forms of `Rc` and `Arc`.
- [`slice-dst`](https://lib.rs/crates/slice-dst): Support for custom slice-based DSTs.

The `shared-rc` crate provides a nearly identical API. I would not have
written this crate had I realied that `shared-rc` already existed. That
said, there are some differences:

* `shared-rc` uses the std versions of `Arc` and `Rc` under the hood, so it
  cannot (yet) support custom allocators.

* `shared-rc` includes an `Owner` type param, with an explicit `erase_owner`
  method to hide it. `ash::arc::Arc` always type-erases the owner.


### Todo

Better test coverage, including tsan

Implement the various Unsize traits behind a feature. (They require nightly even
though they've been unchanged since 1.0, and are required to fully implement
smart ptrs.)

Add something like `rc-box` as built-in functionality. The `rc-box` crate adds a
nice API around std Arc/Rc: immediately after creating one, you know you have
the unique pointer to it, so put that in a wrapper type that implements
`DerefMut`. This is more convenient and more powerful than `new_cyclic`.

Make behavior closer to std: abort on count overflow unless no_std

License: MIT OR Apache-2.0
