#![feature(box_patterns)]

pub mod parse;

use std::collections::HashSet;

pub const BUILTIN: &'static str = r#"
    SUCC := λnfx.f(nfx)
    PLUS := λmn.mSUCCn
    MULT := λmnf.m(nf)
    PRED := λnfx.n(λgh.h(gf))(λu.x)(λu.u)
    TRUE := λxy.x
    FALSE := λxy.y
    AND := λxy.xyFALSE
    OR := λxy.xTRUEy
    NOT := λp.p FALSE TRUE
    IF := λctf.ctf
    CONS := λsbf.fsb
    CAR := λp.pTRUE
    CDR := λp.pFALSE
    Y := λg.(λx.g(xx))(λx.g(xx))
    I := λx.x
    K := λxy.x
    S := λxyz.xz(yz)
"#;

#[derive(Debug, Clone, Eq, Hash)]
pub enum Expression {
    Identifier(String),
    Abstraction(String, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        match (self.alpha(0), other.alpha(0)) {
            (Self::Identifier(ident1), Self::Identifier(ident2)) => ident1 == ident2,
            (Self::Abstraction(_, box expr1), Self::Abstraction(_, box expr2)) => expr1 == expr2,
            (Self::Application(box expr1, box arg1), Self::Application(box expr2, box arg2)) => {
                expr1 == expr2 && arg1 == arg2
            }
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

    pub const fn identifier(&self) -> Option<&String> {
        match self {
            Self::Identifier(ident) => Some(ident),
            _ => None,
        }
    }

    pub const fn abstraction(&self) -> Option<(&String, &Expression)> {
        match self {
            Self::Abstraction(ident, box expr) => Some((ident, expr)),
            _ => None,
        }
    }

    pub const fn application(&self) -> Option<(&Expression, &Expression)> {
        match self {
            Self::Application(box expr, box arg) => Some((expr, arg)),
            _ => None,
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

    pub fn church_number(&self) -> Option<u64> {
        let (f, expr) = self.abstraction()?;
        let (x, expr) = expr.abstraction()?;

        let mut num = 0;
        let mut expr = expr;

        while let Some((func, next)) = expr.application() {
            if func.identifier() == Some(f) {
                expr = next;
                num += 1;
            } else {
                return None;
            }
        }

        if expr.identifier() == Some(x) {
            Some(num)
        } else {
            None
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

    // (λx.y)z -> y[x := z]
    pub fn beta(&self) -> Option<Self> {
        let (expr, z) = self.application()?;
        let (x, y) = expr.abstraction()?;
        Some(y.apply(x, z.clone()))
    }

    // λx.y x (if x isn't free in y) -> y
    pub fn eta(&self) -> Option<Self> {
        let (x, expr) = self.abstraction()?;
        let (y, expr) = expr.application()?;
        let y_arg = expr.identifier()?;

        if x == y_arg && !y.has_free_variable(x) {
            Some(y.clone())
        } else {
            None
        }
    }

    pub fn reductions(&self) -> HashSet<Self> {
        let mut reductions = HashSet::new();

        if let Some(expr) = self.beta() {
            reductions.insert(expr);
        }

        if let Some(expr) = self.eta() {
            reductions.insert(expr);
        }

        match self {
            Self::Abstraction(bound, expr) => {
                expr.reductions().into_iter().for_each(|expr| {
                    reductions.insert(Self::Abstraction(bound.clone(), Box::new(expr)));
                });
            }
            Self::Application(expr, arg) => {
                expr.reductions().into_iter().for_each(|expr| {
                    reductions.insert(Self::Application(Box::new(expr), arg.clone()));
                });
                arg.reductions().into_iter().for_each(|arg| {
                    reductions.insert(Self::Application(expr.clone(), Box::new(arg)));
                });
            }
            _ => {}
        }

        reductions
    }

    pub fn reductions_iter<'d>(
        &self,
        defines: Option<&'d [(String, Expression)]>,
    ) -> impl 'd + Iterator<Item = HashSet<Self>> {
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
        .map(move |candidates| {
            if let Some(defines) = defines {
                candidates
                    .into_iter()
                    .map(|expr| expr.make_readable(defines))
                    .collect()
            } else {
                candidates
            }
        })
    }

    fn replace_by_pattern(&self, pattern: &Self, to: &Self) -> Self {
        if self == pattern {
            to.clone()
        } else {
            match self {
                Self::Abstraction(bound, box expr) => {
                    let expr = expr.replace_by_pattern(pattern, to);
                    Expression::Abstraction(bound.clone(), Box::new(expr))
                }
                Self::Application(box expr, box arg) => {
                    let expr = expr.replace_by_pattern(pattern, to);
                    let arg = arg.replace_by_pattern(pattern, to);
                    Self::Application(Box::new(expr), Box::new(arg))
                }
                _ => self.clone(),
            }
        }
    }

    fn make_readable(self, defines: &[(String, Expression)]) -> Self {
        if let Some(num) = self.church_number() {
            return Self::Identifier(num.to_string());
        }

        let replaces = defines.iter().rev().flat_map(|(name, def)| {
            let reductions1 = def.reductions_iter(None).nth(1);
            let reductions2 = def.reductions_iter(None).nth(2);
            std::iter::once(def.clone())
                .chain(reductions1.into_iter().flatten())
                .chain(reductions2.into_iter().flatten())
                .map(move |e| (name.clone(), e))
        });

        replaces.fold(self, |expr, (name, def)| {
            expr.replace_by_pattern(&def, &Expression::Identifier(name.clone()))
        })
    }
}
