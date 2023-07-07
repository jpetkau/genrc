Better test coverage, including tsan

Implement the various Unsize traits behind a feature. (They require nightly even
though they've been unchanged since 1.0, and are required to fully implement
smart ptrs.)

Make behavior closer to std abort on count overflow unless no_std
(Guess it could panic!() instead?)


This still does a small allocation on `Rc::new` to hold the refcounts.
You can get it all the way to zero by providing this object yourself:

```skip
    todo!("implement from_static");
    use genrc::{rc::Rc,arc::Arc};
    const BIGBUF: [u8; 1024] = [1; 1024];

    // This object can be used to create `Arc`s without any copying. But note
    // that if you use the same COUNTS object for many objects on different
    // threads, you may create contention on the refcount.
    static ARC_COUNTS: arc::ArcStatic = arc::ArcStatic::new();
    let p1: Arc<[u8]> = Arc::from_static_with(&BIGBUF, &ARC_COUNTS);

    // `rc::from_static` allocates one (dummy) count per thread, so it doesn't
    // work in no_std, but can still be useful if you want to create many `Rc`s
    // from the same static data without unnecessary allocation.
    let p2: Rc<[u8]> = Rc::from_static(&BIGBUF);
```
