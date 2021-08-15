use crate::Expression;

#[derive(Debug, PartialEq)]
enum Token {
    ParOpen,
    ParClose,
    Lambda,
    Dot,
    Define,
    Number(u64),
    Identifier(String),
}

fn read_number(src: &str) -> Option<(u64, usize)> {
    let num_string: String = src
        .chars()
        .into_iter()
        .take_while(|ch| ch.is_ascii_digit())
        .collect();

    let num = num_string.parse().ok()?;
    Some((num, num_string.len()))
}

fn read_ident(src: &str) -> String {
    if src.starts_with(|ch: char| ch.is_ascii_lowercase()) {
        src[0..1].to_string()
    } else {
        src.chars()
            .into_iter()
            .take_while(|ch| ch.is_ascii_uppercase())
            .collect()
    }
}

fn tokenize_line(src: &str) -> Vec<Token> {
    if src.is_empty() || src.starts_with("#") {
        return Vec::new();
    }

    if src.starts_with(char::is_whitespace) {
        return tokenize_line(&src[1..]);
    }

    for symbol in ["<", ">"] {
        if src.starts_with(symbol) {
            return tokenize_line(&src[symbol.len()..]);
        }
    }

    for (symbol, token) in [
        ("(", Token::ParOpen),
        (")", Token::ParClose),
        (")", Token::ParClose),
        ("/", Token::Lambda),
        ("\\", Token::Lambda),
        ("λ", Token::Lambda),
        (".", Token::Dot),
        (":=", Token::Define),
        ("=", Token::Define),
    ] {
        if src.starts_with(symbol) {
            let mut res = tokenize_line(&src[symbol.len()..]);
            res.insert(0, token);
            return res;
        }
    }

    if let Some((num, len)) = read_number(src) {
        let mut res = tokenize_line(&src[len..]);
        res.insert(0, Token::Number(num));
        return res;
    };

    let ident = read_ident(src);
    if ident.len() > 0 {
        let mut res = tokenize_line(&src[ident.len()..]);
        res.insert(0, Token::Identifier(ident));
        return res;
    }

    unreachable!("{:?}", src);
}

pub fn parse(src: &str) -> (Expression, Vec<(String, Expression)>) {
    let lines: Vec<&str> = src.trim().split("\n").collect();
    let (expr, defines) = lines.split_last().expect("");

    let defines: Vec<_> = defines
        .into_iter()
        .map(|src| tokenize_line(src))
        .flat_map(|tokens| {
            if tokens.is_empty() {
                None
            } else {
                let (name, def, _) = parse_definition(&tokens).expect("");
                Some((name, def))
            }
        })
        .collect();

    let tokens = tokenize_line(expr);
    let (expr, tokens) = parse_expression(&tokens).expect("");
    assert!(tokens.is_empty());

    let expr = defines
        .iter()
        .rev()
        .fold(expr, |expr, (name, def)| expr.apply(name, def.clone()));

    (expr, defines)
}

fn parse_definition(tokens: &[Token]) -> Option<(String, Expression, &[Token])> {
    if let Some(Token::Identifier(ident)) = tokens.first() {
        if tokens.get(1) == Some(&Token::Define) {
            let (expr, tokens) = parse_expression(&tokens[2..])?;
            Some((ident.clone(), expr, tokens))
        } else {
            None
        }
    } else {
        None
    }
}

fn parse_expression(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    parse_application(tokens)
        .or_else(|| parse_abstraction(tokens))
        .or_else(|| parse_identifier(tokens))
        .or_else(|| parse_number(tokens))
        .or_else(|| parse_par(tokens))
}

fn parse_par(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    if tokens.first() == Some(&Token::ParOpen) {
        let (expr, tokens) = parse_expression(&tokens[1..])?;
        assert!(tokens.first() == Some(&Token::ParClose));
        Some((expr, &tokens[1..]))
    } else {
        None
    }
}

fn parse_abstraction(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    if tokens.first() == Some(&Token::Lambda) {
        let idents: Vec<String> = tokens[1..]
            .iter()
            .map_while(|tk| {
                if let Token::Identifier(ident) = tk {
                    Some(ident.clone())
                } else {
                    None
                }
            })
            .collect();

        assert!(idents.len() > 0);
        assert!(tokens.get(1 + idents.len()) == Some(&Token::Dot));

        let tokens = &tokens[(2 + idents.len())..];
        let (expr, tokens) = parse_expression(tokens)?;

        let abstraction = idents.into_iter().rev().fold(expr, |expr, ident| {
            Expression::Abstraction(ident, Box::new(expr))
        });

        Some((abstraction, tokens))
    } else {
        None
    }
}

fn parse_application(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    fn parse_expression_without_application(tokens: &[Token]) -> Option<(Expression, &[Token])> {
        parse_par(tokens)
            .or_else(|| parse_abstraction(tokens))
            .or_else(|| parse_identifier(tokens))
            .or_else(|| parse_number(tokens))
    }

    std::iter::successors(
        parse_expression_without_application(tokens),
        |(prev, tokens)| {
            let (expr, tokens) = parse_expression_without_application(tokens)?;
            Some((
                Expression::Application(Box::new(prev.clone()), Box::new(expr)),
                tokens,
            ))
        },
    )
    .last()
}

fn parse_number(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    if let Some(Token::Number(num)) = tokens.first() {
        let f = Expression::Identifier("f".to_string());
        let x = Expression::Identifier("x".to_string());

        let mut expr = x;
        for _ in 0..(*num) {
            expr = Expression::Application(Box::new(f.clone()), Box::new(expr));
        }

        Some((
            Expression::Abstraction(
                "f".to_string(),
                Box::new(Expression::Abstraction("x".to_string(), Box::new(expr))),
            ),
            &tokens[1..],
        ))
    } else {
        None
    }
}

fn parse_identifier(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    if let Some(Token::Identifier(ident)) = tokens.first() {
        Some((Expression::Identifier(ident.clone()), &tokens[1..]))
    } else {
        None
    }
}
