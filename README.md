This crate provides a alternatives to `Arc` and `Rc` that allow refcounted
pointers to subobjects, like C++'s `shared_ptr`.

```rust
    use ash::{Ash, Weak};
    let a: Ash<[i32; 3]> = Ash::new([1, 2, 3]);

    // convert the sized array into a slice
    let b: Ash<[i32]> = Ash::derived(a, |x| &x[..]);

    // get a reference to one element of the array
    let c: Ash<i32> = Ash::derived(b, |x| &x[1]);
```
