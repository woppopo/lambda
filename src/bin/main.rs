#![feature(box_patterns)]
#![feature(iter_map_while)]

extern crate lambda;

use lambda::parse::parse;

fn main() {
    if let Some(src) = std::env::args().nth(1) {
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
    let src = r#"
        PLUS := λm n f x. m f (n f x)
        1 := λf x. f x
        2 := λf x. f (f x)
        3 := λf x. f (f (f x))
        PLUS 1 2
    "#;
    println!("SOURCE: {}", src);

    let (expr, defines) = parse(src);
    expr.reductions_iter(Some(&defines))
        .take(100)
        .last()
        .unwrap()
        .into_iter()
        .enumerate()
        .for_each(|(i, e)| println!("[{}]: {:?}", i, e.church_number()));

    let src = r#"
        I := λx.x
        K := λx y.x
        S := λx y z.x z (y z)
        X := λx.((x S) K)
        Y := S (K (S I I)) (S (S (K S) K) (K (S I I)))
        Y := λg. (λx. g (x x)) (λx. g (x x))
        t := S K S K
        t
    "#;
    println!("SOURCE: {}", src);

    let (expr, defines) = parse(src);
    expr.reductions_iter(Some(&defines))
        .last()
        .unwrap()
        .into_iter()
        .enumerate()
        .for_each(|(i, e)| println!("[{}]: {:?}", i, e.to_string()));
}
