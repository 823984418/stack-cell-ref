# Stack Cell Ref
Share a reference in thread inner.

# Examples
```
use std::cell::Cell;

use stack_cell_ref::CellRef;

struct Foo {
    x: Cell<i32>,
}

thread_local! {
    static S: CellRef<Foo> = CellRef::new();
}

fn set_foo(x: i32) {
    S.with(|c| {
        c.read(|f| {
            f.unwrap().x.set(x);
        });
    });
}

let foo = Foo { x: Cell::new(0) };

S.with(|c| {
    c.with(&foo, || {
        set_foo(1);
    });
    assert_eq!(c.get_ptr(), None);
});
assert_eq!(foo.x.get(), 1);
```

