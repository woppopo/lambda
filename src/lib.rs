#![feature(box_patterns)]
#![feature(iter_map_while)]

pub mod parse;

use std::collections::HashSet;

#[derive(Debug, Clone, Eq, Hash)]
pub enum Expression {
    Identifier(String),
    Abstraction(String, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        match (self.clone().alpha(0), other.clone().alpha(0)) {
            (Expression::Identifier(ident1), Expression::Identifier(ident2)) => ident1 == ident2,
            (Expression::Abstraction(_, box expr1), Expression::Abstraction(_, box expr2)) => {
                expr1 == expr2
            }
            (
                Expression::Application(box expr1, box arg1),
                Expression::Application(box expr2, box arg2),
            ) => expr1 == expr2 && arg1 == arg2,
            _ => false,
        }
    }
}

impl ToString for Expression {
    fn to_string(&self) -> String {
        match self {
            Self::Identifier(ident) => ident.clone(),
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
            Self::Application(expr, arg) => {
                expr.has_free_variable(var) || arg.has_free_variable(var)
            }
            _ => false,
        }
    }

    fn rename_free_variable(&self, from: &str, to: &str) -> Self {
        self.apply(from, Self::Identifier(to.to_string()))
    }

    pub fn apply(&self, var: &str, to: Self) -> Self {
        match self {
            Self::Identifier(ident) if ident == var => to,
            Self::Abstraction(bound, box expr) if bound != var => {
                Self::Abstraction(bound.clone(), Box::new(expr.apply(var, to)))
            }
            Self::Application(expr, arg) => {
                let expr = expr.apply(var, to.clone());
                let arg = arg.apply(var, to);
                Self::Application(Box::new(expr), Box::new(arg))
            }
            _ => self.clone(),
        }
    }

    pub fn alpha(&self, num_offset: u64) -> Self {
        match self {
            Self::Abstraction(old_bound, expr) => {
                let new_bound = format!("%{}", num_offset);
                let expr = expr
                    .rename_free_variable(&old_bound, &new_bound)
                    .alpha(num_offset + 1);
                Self::Abstraction(new_bound, Box::new(expr))
            }
            Self::Application(expr, arg) => {
                let expr = expr.alpha(num_offset);
                let arg = arg.alpha(num_offset + expr.count_bound());
                Self::Application(Box::new(expr), Box::new(arg))
            }
            _ => self.clone(),
        }
    }

    // (λx.E1)E2 -> E1[x := E2]
    pub fn beta(&self) -> Result<Self, Self> {
        match self {
            Self::Application(box Self::Abstraction(bound, expr), box arg) => {
                Ok(expr.apply(&bound, arg.clone()))
            }
            _ => Err(self.clone()),
        }
    }

    // λx.Ex (if x isn't free in E) -> E
    pub fn eta(&self) -> Result<Self, Self> {
        match self {
            Self::Abstraction(
                bound,
                box Self::Application(box expr, box Self::Identifier(arg)),
            ) if !expr.has_free_variable(&bound) && bound == arg => Ok(expr.clone()),
            _ => Err(self.clone()),
        }
    }

    pub fn reductions(&self) -> HashSet<Self> {
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

    pub fn reductions_iter(&self) -> impl Iterator<Item = HashSet<Self>> {
        let mut reductions = HashSet::new();
        reductions.insert(self.alpha(0));

        std::iter::successors(Some(reductions), |prev| {
            let val: HashSet<_> = prev.iter().map(Expression::reductions).flatten().collect();

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
        defines
            .iter()
            .rev()
            .flat_map(|(name, def)| {
                let reductions1 = def.clone().reductions_iter().nth(1);
                let reductions2 = def.clone().reductions_iter().nth(2);
                std::iter::once(def.clone())
                    .chain(reductions1.into_iter().flatten())
                    .chain(reductions2.into_iter().flatten())
                    .map(move |e| (name.clone(), e))
            })
            .fold(self, |expr, (name, def)| {
                expr.replace_by_pattern(&def, Expression::Identifier(name.clone()))
            })
    }
}
