This crate provides a alternatives to `Arc` and `Rc` that allow refcounted
pointers to subobjects, like C++'s `shared_ptr`.

```rust
    use ash::arc::{Arc, Weak};
    let a: Arc<[i32; 3]> = Arc::new([1, 2, 3]);

    // convert the sized array into a slice
    let b: Arc<[i32]> = Arc::derived(a, |x| &x[..]);

    // get a reference to one element of the array
    let c: Arc<i32> = Arc::derived(b, |x| &x[1]);
```
