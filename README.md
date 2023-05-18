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

Unlike `std`, references can point to static data without
copying, again using `project()`:

```rust
    # use ash::rc::{Rc, Weak};
    static BIGBUF: [u8; 1024] = [1; 1024];

    let p: Rc<()> = Rc::new(());
    let p: Rc<[u8]> = Rc::project(p, |_| &BIGBUF[..]);

    assert!(std::ptr::eq(&BIGBUF[..], &*p));
```

There are also types `RcBox<T>` (and `ArcBox<T>`) that are returned
from `new_unique()`, which take advantage of the fact that the
initially created pointer is still unique so can be used mutably.
This allows you to create cyclic data structures without `Cell` or
using `new_cyclic()`:

```rust
    use ash::rc::{Rc, RcBox, Weak};
    struct Node {
        edges: Vec<Weak<Node>>,
    }

    // Make a graph
    let mut graph: Vec<RcBox<Node>> = (0..5).map(|_| {
        Rc::new_unique(Node { edges: vec![] })
    }).collect();

    // Make some random edges in the graph
    for i in 0..5 {
        for d in 1..3 {
            let j = (i + d) % 5;

            let link = Rc::downgrade(&graph[j]);
            graph[i].edges.push(link);
        }
    }

    // we still have unique handles on the nodes, so attempting to upgrade
    // weak pointers will fail.
    let p = graph[1].edges[0].clone();
    assert!(p.upgrade().is_none());

    // convert `RcBox` to a normal `Rc` with `into()`.
    let graph: Vec<Rc<Node>> = graph.into_iter().map(Into::into).collect();

    // now the weak pointers are valid - we've made a graph with (weak)
    // cycles, no unsafe or internal mutation required.
    assert!(Rc::ptr_eq(&graph[0].edges[1].upgrade().unwrap(), &graph[2]));
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

```rust
    # use ash::rc::{Rc, RcBox, Weak};
    let mut obj : RcBox<Option<i32>> = Rc::new_unique(None);
    // ... later ...
    obj.replace(5);
    let obj : Rc<i32> = Rc::project(obj, |x| x.as_ref().unwrap());

    assert_eq!(*obj, 5);
```

Unlike in std, `Rc` and `Arc` (and `RcBox` and `ArcBox`) share a single generic
implementation. `Rc<T>` is an alias `Ash<T, Cell<usize>>` and `Arc<T>` is an
alias for `Ash<T, AtomicUsize>`.


### Differences from [`shared-rc`](https://lib.rs/crates/shared-rc)

`shared-rc` is a very similar crate to this one; I would not have written
this if I'd known that shared-rc already existed. That said, there are some
differences:

* `shared-rc` uses the std versions of `Arc` and `Rc` under the hood, so it
  cannot (yet) support zero-alloc usage. (But this crate doesn't suppor that
  yet either, although it's possible.)

* `shared-rc` includes an `Owner` type param, with an explicit `erase_owner`
  method to hide it. `ash::arc::Arc` always type-erases the owner. This
  adds one word of overhead in the pointer when a type-erased `shared-rc` is
  pointing to an unsized type.
  (e.g. `shared_rc::rc::[u8]` is 32 bytes, but `ash::rc::[u8]` is 24.)

### Differences from [`rc-box`](https://lib.rs/crates/rc-box)

The `rc-box` crate adds a nice API around std Arc/Rc: immediately after
creating one, you know you have the unique pointer to it, so put that in
a wrapper type that implements `DerefMut`. This crate copies that API.

* Since `rc-box` is built on top of the std types, it would be unsafe
  to allow weak pointers to its `RcBox` types, so it cannot replace
  `new_cyclic`.

* The implementation in `ash` is generic over whether the pointer is
  unique or not (`RcBox<T>` is `Rc<T, true>`). This allows writing
  code generic over the uniqueness of the pointer, which may be useful
  for initialization (like the graph-creating example above, where the
  graph is a `Vec<RcBox<Node>>` during initialization, then gets converted
  to a `Vec<Rc<Node>>`.)

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

Make behavior closer to std: abort on count overflow unless no_std

License: MIT OR Apache-2.0
