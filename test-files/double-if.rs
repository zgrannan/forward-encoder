#[allow(dead_code)]
fn double_if(x: u32, y: u32) -> u32 {
    let z = if x > 5 {
       1
    } else {
       2
    };

    let g = if y < 6 {
        3
    } else {
        z
    };

    z + g
}

fn main(){}
