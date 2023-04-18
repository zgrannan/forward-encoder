#[analyzer::run]
#[allow(dead_code)]
fn foo(x: u32) -> u32 {
    if x > 2 {
        3
    } else {
        4   
    }
}

fn main(){}
