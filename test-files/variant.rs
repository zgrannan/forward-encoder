#[allow(dead_code)]

enum Thing {
    A(u32),
    B(bool),
    C(i32)
}

fn go(thing: Thing) -> bool {
    match thing {
        Thing::A(x) => x == 7,
        Thing::B(b) => !b,
        Thing::C(c) => c > 0
    }
}

fn main(){}
