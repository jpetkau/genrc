# genrc

This crate provides alternatives to `Arc` and `Rc` which are (almost) drop-in
replacements, but allow refcounted pointers to subobjects, like C++'s
`shared_ptr`.

The main feature, which adds a surprising amount of flexibility: if you have an
`Rc<T>`, and `T` contains some subobject of type `U`, then you can construct an
`Rc<U>` that shares ownership with the original object, by calling
`Rc::project()`.

```rust
    use genrc::rc::{Rc, Weak};
    let a: Rc<[i32; 3]> = Rc::new([1, 2, 3]);

    // convert the sized array into a slice
    let b: Rc<[i32]> = Rc::project(a, |x| &x[..]);

    // get a reference to one element of the array
    let c: Rc<i32> = Rc::project(b, |x| &x[1]);
```

Unlike `std`, references can point to static data without copying, again using
`project()`:

```rust
    # usegenrcc::rc::Rc;
    static BIGBUF: [u8; 1024] = [1; 1024];

    let p: Rc<()> = Rc::new(());
    let p: Rc<[u8]> = Rc::project(p, |_| &BIGBUF[..]);

    assert!(std::ptr::eq(&BIGBUF[..], &*p));
```

There are also types [`rc::RcBox<T>`] (and [`arc::ArcBox<T>`]) that are returned
from [`rc::Rc::new_unique()`], which take advantage of the fact that a newly created
pointer is still unique so can be used mutably. This allows you to create
cyclic data structures without needing [`std::cell::RefCell`] or [`std::rc::Rc::new_cyclic`]:


```rust
    usegenrcc::rc::{Rc, RcBox, Weak};
    struct Node {
        edges: Vec<Weak<Node>>,
    }

    // Make a graph
    let mut graph: Vec<_> = (0..5).map(|_| {
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


### Lifetime stuff

`std::rc::Rc` allows you to create an `Rc` pointing to a local variable.
E.g. this is legal:

```rust
    use std::{cell::Cell, rc::Rc};
    let x = Cell::new(1);
    let y : Rc<&Cell<i32>> = Rc::new(&x);
    x.set(2);
    assert_eq!(y.get(), 2);
```

The type of such an `Rc` is `Rc<&'a T>`, where `'a` is the lifetime of the
referent, so the `Rc` can't outlive the referent.

But `project()` lets you turn genrcc::Rc<&'a T>` into an `Rc<T>` pointing to the
same object. The latter type has nowhere for the lifetime `'a` to go, so
if allowed this would let the reference live too long and be a soundness
bug.

To avoid this, the type [genrcc::Rcl`] adds a lifetime parameter to `Rc`.
In fact [genrcc::Rc<T>`] is just a type alias for [genrcc::Rcl<'static, T>`],
and [genrcc::Arc<T>`] is a type alias for [genrcc::Arcl<'static, T>`].

(And all of them are type aliases for [genrcc::Genrc`], which is generic over
lifetime, referent type, uniqueness, and thread-safety. So you can write
functions that are generic over `Arc` vs. `Rc` if desired.

But doing this is limited in usefulness, since now you have to use `Rc<&'a T>`
everywhere instead of just `Rc<T>`, so the `Rc` isn't really keeping an object
alive. You might as well just use `&'a T` directly.

But with `project`, you can convert the `Rc<&T>` into an `Rc<T>` and use it
normally. Except you can't _quite_ do that--that would be unsafe, as the
lifetime is lost. You need to use `Rcl<T>` instead, which is the same as `Rc`
but with a lifetime parameter. (`Rc<T>` is just a type alias for
`Rcl<'static, T>`.)

```rust
    usegenrcc::rc::Rcl;

    // Imagine we have some JSON data that we loaded from a file
    // (or data allocated in an arena, etc)
    let bigdata : Vec<u8> = b"Not really json, use your imagination".to_vec();

    // buf points directly into `bigdata`, not a copy
    let buf : Rcl<[u8]> = Rcl::project(Rcl::new(&bigdata[..]), |x| *x);
    assert!(std::ptr::eq(&bigdata[..], &*buf));
```


There are a few ways this could be addressed:
1. `project` could only be allowed if the source type is outlives the
  return type. That would disallow the `Rc<&'a T> -> Rc<T>` conversion.
  For most use backwards-compatible cases, that's fine; `Rc<T>` almost
  always has `T: static` anyway.

  But `project` make the problem case *useful*: you can use `Rc` to
  manage a group of objects whose overall lifetime is still restricted
  to a stack or arena allocation. So this would be a significant loss.

2. Add a new type, call it `RcGeneral`, that has the lifetime parameter,
  and define `type Rc<T> = RcGeneral<'static, T>`. That makes the it a
  drop-in for the usual case, but fails in cases where the type `T` is
  not `'static`.

3. Just add the type parameter to `Rc`. Usually it can be inferred, but
  in type definitions it will need to be explicit. This is the approach
  this crate takes, which unfortunately makes it less of a drop-in
  replacement since you have to add `<'static>` here and there. If there
  was a way to infer the lifetime parameter in type definitions, that
  would be avoidable.


### Differences from `std::sync::Arc` and `std::rc::Rc`

`Rc::from_box` does not copy the object from the original box. Instead it
takes ownership of the box as-is, with the counts in a separate allocation.

If you leak so many Rc objects that the refcount overflows, the std
pointers will abort. genrcc` does not, because there is no `abort()`
function in `no_std`.

Implicit conversion from `Rc<T>` to `Rc<dyn Trait>` is not supported,
because that requires some unstable traits. However you can do the
conversion explicitly with `Rc::project`. [TODO: support this behind a
nightly-requiring feature.]

The std pointers have various `MaybeUninit`-related methods for initializing
objects after allocation. That API isn't possible in Genrc, because the initial
object is type-erased. However, `project` allows you to do the same thing
entirely safely with `Option`:

```rust
    # usegenrcc::rc::{Rc, RcBox, Weak};
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
implementation. `Rc<T>` is an alias `Genrc<T, Nonatomic>` and `Arc<T>` is an
alias for `Genrc<T, Atomic>`. This does make the documentation a little
uglier, since it's all on struct `Genrc` instead of the actual types you normally
use.


### Differences from [`shared-rc`](https://lib.rs/crates/shared-rc)

`shared-rc` is a very similar crate to this one; I would not have written
this if I'd known that shared-rc already existed. That said, there are some
differences:

* `shared-rc` uses the std versions of `Arc` and `Rc` under the hood, so it
  cannot support zero-alloc usage.

* `shared-rc` includes an `Owner` type param, with an explicit `erase_owner`
  method to hide it. genrcc::arc::Arc` always type-erases the owner. This
  saves one word of overhead in the pointer when a type-erased `shared-rc` is
  pointing to an unsized type.
  (e.g. `shared_rc::rc::[u8]` is 32 bytes, but genrcc::rc::[u8]` is 24.)

* genrcc` is generic over atomic vs. shared. `shared-rc` uses macros for that,
  which makes the rustdocs harder to read but "go to definition" easier to
  read.


### Differences from [`rc-box`](https://lib.rs/crates/rc-box)

The `rc-box` crate adds a nice API around std Arc/Rc: immediately after
creating one, you know you have the unique pointer to it, so put that in
a wrapper type that implements `DerefMut`. This crate copies that API.

* Since `rc-box` is built on top of the std types, it would be unsafe
  to allow weak pointers to its `RcBox` types, so it cannot replace
  `new_cyclic` as in the graph example above.

* The implementation in genrcc` is generic over whether the pointer is
  unique or not (`RcBox<T>` is `Rc<T, true>`). This allows writing
  code generic over the uniqueness of the pointer, which may be useful
  for initialization (like the graph-creating example above, where the
  graph is a `Vec<RcBox<Node>>` during initialization, then gets converted
  to a `Vec<Rc<Node>>`.)


### Related Crates

- [`shared-rc`](https://lib.rs/crates/shared-rc): Similar to this crate, but
  wraps the std versions of `Arc` and `Rc` rather than reimplementing them.
- [`rc-box`](https://lib.rs/crates/rc-box): Known unique versions of Rc and Arc.
- [`erasable`](https://lib.rs/crates/erasable): Erase pointers of their concrete type.
- [`rc-borrow`](https://lib.rs/crates/rc-borrow): Borrowed forms of `Rc` and `Arc`.


### Todo

Implement the various Unsize traits behind a feature. (They require nightly even
though they've been unchanged since 1.0, and are required to fully implement
smart ptrs.)

Make behavior match if count overflows

License: MIT OR Apache-2.0
