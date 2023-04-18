#[allow(dead_code)]
#[analyzer::run]
fn foo(x: u32) -> u32 {
    if x > 2 {
        3
    } else {
        4   
    }
}

fn main(){}
