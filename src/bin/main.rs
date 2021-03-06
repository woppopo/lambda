#![feature(box_patterns)]

extern crate lambda;

use lambda::parse::parse;
use lambda::BUILTIN;

fn main() {
    if let Some(src) = std::env::args().nth(1) {
        let src = format!("{}{}", BUILTIN, src);
        let (expr, defines) = parse(&src);
        expr.reductions_iter(Some(&defines))
            .last()
            .unwrap()
            .into_iter()
            .enumerate()
            .for_each(|(i, e)| println!("[{}]: {}", i, e.to_string()));
    } else {
        sample();
    }
}

fn sample() {
    let src = format!("{}{}", BUILTIN, "PLUS 1 2");
    println!("SOURCE: {}", src);

    let (expr, defines) = parse(&src);
    expr.reductions_iter(Some(&defines))
        .take(100)
        .last()
        .unwrap()
        .into_iter()
        .enumerate()
        .for_each(|(i, e)| println!("[{}]: {:?}", i, e.to_string()));

    let src = format!("{}{}", BUILTIN, "CDR (CONS 4 7)");
    println!("SOURCE: {}", src);

    let (expr, defines) = parse(&src);
    expr.reductions_iter(Some(&defines))
        .last()
        .unwrap()
        .into_iter()
        .enumerate()
        .for_each(|(i, e)| println!("[{}]: {:?}", i, e.to_string()));
}
