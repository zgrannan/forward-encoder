#[analyzer::run]
#[allow(dead_code)]
fn foo(x: u32) -> u32 {
    if x + 5 < 3{
        1
    } else {
        2
    }
}

fn main(){}
