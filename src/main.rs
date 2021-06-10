#![feature(box_patterns)]
#![feature(iter_map_while)]

use std::collections::HashSet;

#[derive(Debug, Clone, Eq, Hash)]
enum Expression {
    Identifier(String),
    Abstraction(String, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        match (self.clone().alpha(0), other.clone().alpha(0)) {
            (Expression::Identifier(ident1), Expression::Identifier(ident2)) => {
                ident1 == ident2
            }
            (Expression::Abstraction(_, box expr1), Expression::Abstraction(_, box expr2)) => {
                expr1 == expr2       
            }
            (Expression::Application(box expr1, box arg1), Expression::Application(box expr2, box arg2)) => {
                expr1 == expr2 && arg1 == arg2
            }
            _ => false,
        }
    }
}

impl ToString for Expression {
    fn to_string(&self) -> String {
        match self {
            Self::Identifier(ident) => {
                ident.clone()
            }
            Self::Abstraction(bound, expr) => {
                format!("λ{}.{}", bound, expr.to_string())
            }
            Self::Application(expr, arg) => {
                let expr = if expr.is_identifier() {
                    expr.to_string()
                } else {
                    format!("({})", expr.to_string())
                };
                let arg = if arg.is_identifier() {
                    arg.to_string()
                } else {
                    format!("({})", arg.to_string())
                };
                format!("{} {}", expr, arg)
            }
        }
    }
}

impl Expression {
    pub const fn is_identifier(&self) -> bool {
        match self {
            Self::Identifier(_) => true,
            _ => false,
        }
    }

    pub const fn is_abstraction(&self) -> bool {
        match self {
            Expression::Abstraction(_, _) => true,
            _ => false,
        }
    }

    pub const fn is_application(&self) -> bool {
        match self {
            Self::Application(_, _) => true,
            _ => false,
        }
    }

    const fn count_bound(&self) -> u64 {
        match self {
            Self::Abstraction(_, expr) => 1 + expr.count_bound(),
            _ => 0,
        }
    }

    fn has_free_variable(&self, var: &str) -> bool {
        match self {
            Self::Identifier(ident) => ident == var,
            Self::Abstraction(bound, expr) if bound != var => expr.has_free_variable(var),
            Self::Application(expr, arg) => expr.has_free_variable(var) || arg.has_free_variable(var),
            _ => false,
        }
    }

    fn apply(self, var: &str, to: Self) -> Self {
        match self {
            Self::Identifier(ident) if ident == var => to,
            Self::Abstraction(bound, box expr) if bound != var => {
                Self::Abstraction(bound, Box::new(expr.apply(var, to)))
            }
            Self::Application(expr, arg) => {
                let expr = expr.apply(var, to.clone());
                let arg = arg.apply(var, to);
                Self::Application(Box::new(expr), Box::new(arg))
            }
            other => other,
        }
    }

    fn rename_free_variable(self, from: &str, to: &str) -> Self {
        self.apply(from, Self::Identifier(to.to_string()))
    }

    fn alpha(self, num_offset: u64) -> Self {
        match self {
            Self::Abstraction(old_bound, expr) => {
                let new_bound = format!("%{}", num_offset);
                let expr = expr.rename_free_variable(&old_bound, &new_bound).alpha(num_offset + 1);
                Self::Abstraction(new_bound, Box::new(expr))
            },
            Self::Application(expr, arg) => {
                let expr = expr.alpha(num_offset);
                let arg = arg.alpha(num_offset + expr.count_bound());
                Self::Application(Box::new(expr), Box::new(arg))
            }
            other => other,
        }
    }

    // (λx.E1)E2 -> E1[x := E2]
    fn beta(self) -> Result<Self, Self> {
        match self {
            Self::Application(box Self::Abstraction(bound, expr), box arg) => Ok(expr.apply(&bound, arg)),
            other => Err(other),
        }
    }

    // λx.Ex (if x isn't free in E) -> E
    fn eta(self) -> Result<Self, Self> {
        match self {
            Self::Abstraction(bound, box Self::Application(box expr, box Self::Identifier(arg))) if !expr.has_free_variable(&bound) && bound == arg => {
                Ok(expr)
            }
            other => Err(other),
        }
    }

    fn reductions(self) -> HashSet<Self> {
        let mut reductions = HashSet::new();

        if let Ok(expr) = self.clone().beta() {
            reductions.insert(expr);
        }

        if let Ok(expr) = self.clone().eta() {
            reductions.insert(expr);
        }

        match self {
            Self::Abstraction(bound, expr) => {
                expr.reductions().into_iter().for_each(|expr| {
                    reductions.insert(Self::Abstraction(bound.clone(), Box::new(expr)));
                });
            }
            Self::Application(expr, arg) => {
                expr.clone().reductions().into_iter().for_each(|expr| {
                    reductions.insert(Self::Application(Box::new(expr), arg.clone()));
                });
                arg.clone().reductions().into_iter().for_each(|arg| {
                    reductions.insert(Self::Application(expr.clone(), Box::new(arg)));
                });
            }
            _ => {}
        }

        reductions
    }

    fn reductions_iter(self) -> impl Iterator<Item = HashSet<Self>> {
        let mut reductions = HashSet::new();
        reductions.insert(self.alpha(0));

        std::iter::successors(Some(reductions), |prev| {
            let val: HashSet<_> = prev.clone()
                .into_iter()
                .map(Expression::reductions)
                .flatten()
                .collect();

            if val.is_empty() {
                None
            } else {
                Some(val)
            }
        })
    }

    fn replace_by_pattern(self, pattern: &Self, to: Self) -> Self {
        if &self == pattern {
            to
        } else {
            match self {
                Self::Abstraction(bound, box expr) => {
                    let expr = expr.replace_by_pattern(pattern, to);
                    Expression::Abstraction(bound, Box::new(expr))
                }
                Self::Application(box expr, box arg) => {
                    let expr = expr.replace_by_pattern(pattern, to.clone());
                    let arg = arg.replace_by_pattern(pattern, to);
                    Self::Application(Box::new(expr), Box::new(arg))
                }
                other => other,
            }
        }
    }

    fn make_readable(self, defines: &Vec<(String, Expression)>) -> Self {
        defines.iter().rev().flat_map(|(name, def)| {
            let reductions1 = def.clone().reductions_iter().nth(1);
            let reductions2 = def.clone().reductions_iter().nth(2);
            std::iter::once(def.clone())
                .chain(reductions1.into_iter().flatten())
                .chain(reductions2.into_iter().flatten())
                .map(move |e| (name.clone(), e))
        }).fold(self, |expr, (name, def)| {
            expr.replace_by_pattern(&def, Expression::Identifier(name.clone()))
        })
    }
}

#[derive(Debug, PartialEq)]
enum Token {
    ParOpen,
    ParClose,
    Lambda,
    Dot,
    Identifier(String),
    Define,
}

const fn is_ascii_ident(ch: &char) -> bool {
    *ch == '_' || *ch == '?' || ch.is_ascii_alphanumeric() 
}

fn read_ident(src: &str) -> String {
    src.chars()
        .into_iter()
        .take_while(is_ascii_ident)
        .collect()
}

fn tokenize_line(src: &str) -> Vec<Token> {
    if src.is_empty() || src.starts_with("#") {
        return Vec::new();
    }

    if src.starts_with(char::is_whitespace) {
        return tokenize_line(&src[1..]);
    }

    for symbol in [
        "<",
        ">",
    ] {
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

    let ident = read_ident(src);
    if ident.len() > 0 {
        let mut res = tokenize_line(&src[ident.len()..]);
        res.insert(0, Token::Identifier(ident));
        return res;
    }

    unreachable!("{:?}", src);
}

fn parse_application(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    fn parse_expression_without_application(tokens: &[Token]) -> Option<(Expression, &[Token])> {
        parse_par(tokens)
            .or_else(|| parse_abstraction(tokens))
            .or_else(|| parse_identifier(tokens))
    }

    std::iter::successors(parse_expression_without_application(tokens), |(prev, tokens)| {
        let (expr, tokens) = parse_expression_without_application(tokens)?;
        Some((Expression::Application(Box::new(prev.clone()), Box::new(expr)), tokens))
    }).last()
}

fn parse_identifier(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    if let Some(Token::Identifier(ident)) = tokens.first() {
        Some((Expression::Identifier(ident.clone()), &tokens[1..]))
    } else {
        None
    }
}

fn parse_abstraction(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    if tokens.first() == Some(&Token::Lambda) {
        let idents: Vec<String> = tokens[1..].iter().map_while(|tk| if let Token::Identifier(ident) = tk {
            Some(ident.clone())
        } else {
            None
        }).collect();
    
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

fn parse_par(tokens: &[Token]) ->  Option<(Expression, &[Token])> {
    if tokens.first() == Some(&Token::ParOpen) {
        let (expr, tokens) = parse_expression(&tokens[1..])?;
        assert!(tokens.first() == Some(&Token::ParClose));
        Some((expr, &tokens[1..]))
    } else {
        None
    }
}

fn parse_expression(tokens: &[Token]) -> Option<(Expression, &[Token])> {
    parse_application(tokens)
        .or_else(|| parse_abstraction(tokens))
        .or_else(|| parse_identifier(tokens))
        .or_else(|| parse_par(tokens))
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

fn parse(src: &str) -> impl Iterator<Item = HashSet<Expression>> {
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
        }).collect();

    let tokens = tokenize_line(expr);
    let (expr, tokens) = parse_expression(&tokens).expect("");
    assert!(tokens.is_empty());

    let expr = defines.iter()
        .rev()
        .fold(expr, |expr, (name, def)| {
            expr.apply(name, def.clone())
        });

    expr.reductions_iter()
        .map(move |candidates| {
            candidates.into_iter()
                .map(|expr| expr.make_readable(&defines))
                .collect()
        })
}

fn main() {
    let src = r#"
        PLUS := λm n f x. m f (n f x)
        1 := λf x. f xd
        2 := λf x. f (f x)
        3 := λf x. f (f (f x))
        PLUS 1 2
    "#;
    parse(src)
        .take(100)
        .last()
        .unwrap()
        .into_iter()
        .enumerate()
        .for_each(|(i, e)| println!("[{}]: {}", i, e.to_string()));

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
    parse(src)
        .take(100)
        .last()
        .unwrap()
        .into_iter()
        .enumerate()
        .for_each(|(i, e)| println!("[{}]: {:?}", i, e.to_string()));
}