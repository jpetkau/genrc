/*!
This crate provides alternatives to [`std::sync::Arc`] and [`std::rc::Rc`] which
are (almost) drop-in replacements, but allow refcounted pointers to subobjects,
like C++'s [`shared_ptr`](https://en.cppreference.com/w/cpp/memory/shared_ptr).

The main feature, which adds a surprising amount of flexibility: if you have an
`Rc<T>`, and `T` contains some subobject of type `U`, then you can construct an
`Rc<U>` that shares ownership with the original object by calling
`Rc::project()`.

```rust
    use genrc::rc::{Rc, Weak};
    let a: Rc<[i32; 3]> = Rc::new([1, 2, 3]);

    // convert the sized array into a slice
    let b: Rc<[i32]> = Rc::project(a, |x| &x[..]);

    // get a reference to one element of the array
    let c: Rc<i32> = Rc::project(b, |x| &x[1]);
```

There are also types [`RcBox<T>`] (and [`ArcBox<T>`]) that are returned from
[`new_unique()`][Rc::new_unique], which take advantage of the fact that a newly
created refcounted pointer is still unique, so can be used mutably.


# Uses

## Easier and safer initialization

You can use `RcBox<Option<T>>` to indicate not-yet-initialized types instead of
the the various unsafe `MaybeInit`-related APIs in `std::rc`. After the object
is initialized, you can use `project` to convert it to a plain `Rc<T>`:

```
    # use genrc::rc::{Rc, RcBox, Weak};
    // construct the object initially uninitialized
    // we could use `Rc::get_mut` instead of `RcBox` here.
    let mut obj : RcBox<Option<i32>> = Rc::new_unique(None);

    // ... later ...
    // initialize the object
    obj.replace(5);

    // project to the inner value that we just created
    let obj : Rc<i32> = RcBox::project(obj, |x| x.as_ref().unwrap());

    assert_eq!(*obj, 5);
```

You can also create cyclic data structures without needing
[`RefCell`][std::cell::RefCell] or [`new_cyclic`][std::rc::Rc::new_cyclic]:


```
    use genrc::rc::{Rc, RcBox, Weak};
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

            let link = RcBox::downgrade(&graph[j]);
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

## Static data

Unlike `std`, references can point to static data without copying, again using
`project()`:

```
    # use genrc::rc::Rc;
    static BIGBUF: [u8; 1024] = [1; 1024];

    let p: Rc<()> = Rc::new(());
    let p: Rc<[u8]> = Rc::project(p, |_| &BIGBUF[..]);

    assert!(std::ptr::eq(&BIGBUF[..], &*p));
```

So you can use `Rc` to keep track of possibly-owned, possibly-static data,
similar to `Cow`.


# Notes

# Lifetime stuff

`std::rc::Rc` allows you to create an `Rc` pointing to a local variable.
E.g. this is legal:

```
    use std::{cell::Cell, rc::Rc};
    let x = Cell::new(1);
    let y : Rc<&Cell<i32>> = Rc::new(&x);
    x.set(2);
    assert_eq!(y.get(), 2);
```

The type of such an `Rc` is `Rc<&'a T>`, where `'a` is the lifetime of the
referent, so the `Rc` can't outlive the referent.

But `project()` lets you turn `genrc::Rc<&'a T>` into an `Rc<T>` pointing to the
same object. The latter type has nowhere for the lifetime `'a` to go, so if
allowed this would let the reference live too long and be a soundness bug.

To avoid this, the type [`Rcl`] adds a lifetime parameter to `Rc`.

(In fact [`Rc<T>`] is just an alias for `Rcl<'static, T>`, and [`Arc<T>`] is an
alias for `Arcl<'static, T>`. And all of them are aliases for [`genrc::Genrc`],
which is generic over lifetime, referent type, uniqueness, and atomicity.)

To use `project()` such on a short-lived reference, you must use
`Rcl::project()`, which returns an `Rcl` with a non-static lifetime.

```
    use genrc::rc::Rcl;

    // Imagine we have some JSON data that we loaded from a file
    // (or data allocated in an arena, etc)
    let bigdata : Vec<u8> = b"Not really json, use your imagination".to_vec();

    // buf points directly into `bigdata`, not a copy
    let buf : Rcl<[u8]> = Rcl::from_ref(&bigdata[..]);
    assert!(std::ptr::eq(&*buf, &bigdata[..]));

    let word : Rcl<[u8]> = Rcl::project(buf, |x| &x[4..10]);
    assert!(std::ptr::eq(&*word, &bigdata[4..10]));
```

## Differences from `std::sync::Arc` and `std::rc::Rc`

`Rc::from_box` does not copy the object from the original box. Instead it
takes ownership of the box as-is, with the counts in a separate allocation.

If you leak so many Rc objects that the refcount overflows, the std pointers
will abort. `genrc` does not, because there is no `abort()` function in
`no_std`.

Implicit conversion from `Rc<T>` to `Rc<dyn Trait>` is not supported, because
that requires some unstable traits. However you can do the conversion explicitly
with `Rc::project`. [TODO: support this behind a nightly-requiring feature.]

The std pointers have various `MaybeUninit`-related methods for initializing
objects after allocation. That API isn't possible in Genrc, because the initial
object is type-erased. However, `project` allows you to do the same thing
entirely safely with `Option`:

```
    # use genrc::rc::{Rc, RcBox, Weak};
    // construct the object initially uninitialized
    // we could use `Rc::get_mut` instead of `RcBox` here.
    let mut obj : RcBox<Option<i32>> = Rc::new_unique(None);

    // ... later ...
    // initialize the object
    obj.replace(5);

    // project to the inner value that we just created
    let obj : Rc<i32> = RcBox::project(obj, |x| x.as_ref().unwrap());

    assert_eq!(*obj, 5);
```

Unlike in std, `Rc` and `Arc` (and `RcBox` and `ArcBox`) share a single generic
implementation. `Rc<T>` is an alias `Genrc<'static, T, Nonatomic>` and `Arc<T>`
is an alias for `Genrc<'static, T, Atomic>`. This does make the documentation a
little uglier, since it's all on struct `Genrc` instead of the actual types you
normally care about.

`std::rc::Rc::ptr_eq(a,b)` returns true if a and b share the same allocation,
which is the same as asking if they're equal pointers. But in `genrc`,
these are two different questions: you can have pointers to two different
subobjects from the same allocation, or pointers that came from two different
allocations that are pointing to the same object! (E.g. they may have been
projected to a static object). So here we have `Rc::ptr_eq` which is equivalent
to `std::ptr::eq(&*a, &*b)`, and `Rc::root_ptr_eq` which checks if the counts
are shared.

`from_raw` and `into_raw` are not available because there may be no relationship
between the returned pointer and the original allocation.

## Differences from [`shared-rc`](https://lib.rs/crates/shared-rc)

`shared-rc` is a very similar crate to this one; I would not have written
this if I'd known that shared-rc already existed. That said, there are some
differences:

* `shared-rc` uses the std versions of `Arc` and `Rc` under the hood, so it
  cannot support zero-alloc usage.

* `shared-rc` includes an `Owner` type param, with an explicit `erase_owner`
  method to hide it. `genrc::arc::Arc` always type-erases the owner. This
  saves one word of overhead in the pointer when a type-erased `shared-rc` is
  pointing to an unsized type.
  (e.g. `shared_rc::rc::[u8]` is 32 bytes, but `genrc::rc::[u8]` is 24.)

* `genrc` is generic over atomic vs. shared. `shared-rc` uses macros for that,
  which makes the rustdocs harder to read but "go to definition" easier to
  read.


## Differences from [`rc-box`](https://lib.rs/crates/rc-box)

The `rc-box` crate adds a nice API around std Arc/Rc: immediately after
creating one, you know you have the unique pointer to it, so put that in
a wrapper type that implements `DerefMut`. This crate copies that API.

* Since `rc-box` is built on top of the std types, it would be unsafe
  to allow weak pointers to its `RcBox` types, so it cannot replace
  `new_cyclic` as in the graph example above.

* The implementation in `genrc` is generic over whether the pointer is
  unique or not (the UNIQ parameter to GenRc). This allows writing
  code generic over the uniqueness of the pointer, which may be useful
  for initialization (like the graph-creating example above, where the
  graph is a `Vec<RcBox<Node>>` during initialization, then gets converted
  to a `Vec<Rc<Node>>`.)


## Related Crates

- [`shared-rc`](https://lib.rs/crates/shared-rc): Similar to this crate, but
  wraps the std versions of `Arc` and `Rc` rather than reimplementing them.
- [`rc-box`](https://lib.rs/crates/rc-box): Known unique versions of Rc and Arc.
- [`erasable`](https://lib.rs/crates/erasable): Erase pointers of their concrete type.
- [`rc-borrow`](https://lib.rs/crates/rc-borrow): Borrowed forms of `Rc` and `Arc`.


## Todo

Allocator support. (Important, because unlike `std::Rc` this allows erasing the
allocator so interoperability

Implement the various Unsize traits behind a feature. (They require nightly even
though they've been unchanged since 1.0, and are required to fully implement
smart ptrs.)

Make behavior match std if count overflows

Implement `Pin` or `Unpin` or whatever pointers are supposed to do. (Not hard,
I just don't use async so haven't bothered yet).

More doc examples.
*/
#![no_std]
#[cfg(test)]
extern crate std;

extern crate alloc;

pub mod arc;
pub mod genrc;
pub mod rc;

pub use self::arc::{Arc, ArcBox, Arcl, Atomic};
pub use self::genrc::{Atomicity, Genrc};
pub use self::rc::{Nonatomic, Rc, RcBox, Rcl};
