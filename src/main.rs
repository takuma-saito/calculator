
use std::fmt;
use std::ops::{Add, Sub, Mul, Div};

enum Expr {
    Number(Number),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

enum Number {
    I64(i64),
    I32(i32),
}

impl Number {
    fn get_i64(&self) -> Option<i64> {
        if let Self::I64(val) = &self { Some(*val) } else { None }
    }
}

macro_rules! impl_number_ops {
    ($trait_name:ident, $method_name:ident) => {
        impl $trait_name for Number {
            type Output = Number;
            fn $method_name(self, other: Number) -> Number {
                match (self, other) {
                    (Self::I64(x), Self::I64(y)) => Self::I64($trait_name::$method_name(x, y)),
                    (Self::I64(x), Self::I32(y)) => Self::I64($trait_name::$method_name(x, y as i64)),
                    (Self::I32(x), Self::I64(y)) => Self::I64($trait_name::$method_name(x as i64, y)),
                    (Self::I32(x), Self::I32(y)) => Self::I32($trait_name::$method_name(x, y)),
                }
            }
        }
    }
}

impl_number_ops!(Add, add);
impl_number_ops!(Sub, sub);
impl_number_ops!(Div, div);
impl_number_ops!(Mul, mul);

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::I64(val) => write!(f, "{}", val),
            Self::I32(val) => write!(f, "{}", val),
        }
    }
}

trait NumOps<T = Self, Output = Self>:
    Add<T, Output = Output>
    + Sub<T, Output = Output>
    + Mul<T, Output = Output>
    + Div<T, Output = Output>
    + fmt::Display {}

impl Expr {
    fn eval(self) -> Number {
        match self {
            Self::Number(number) => number,
            Self::Add(a, b) => Add::add((*a).eval(), (*b).eval()),
            Self::Sub(a, b) => Sub::sub((*a).eval(), (*b).eval()),
            Self::Mul(a, b) => Mul::mul((*a).eval(), (*b).eval()),
            Self::Div(a, b) => Div::div((*a).eval(), (*b).eval()),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Number(num) => write!(f, "{}", num),
            Self::Add(ref a, ref b) => write!(f, "({} + {})", *a, *b),
            Self::Sub(ref a, ref b) => write!(f, "({} - {})", *a, *b),
            Self::Mul(ref a, ref b) => write!(f, "({} * {})", *a, *b),
            Self::Div(ref a, ref b) => write!(f, "({} / {})", *a, *b),
        }
    }
}

impl Add for Expr {
    type Output = Expr;
    fn add(self, other: Expr) -> Expr {
        Self::Add(Box::new(self), Box::new(other))
    }
}
impl Sub for Expr {
    type Output = Expr;
    fn sub(self, other: Expr) -> Expr {
        Self::Sub(Box::new(self), Box::new(other))
    }
}
impl Mul for Expr {
    type Output = Expr;
    fn mul(self, other: Expr) -> Expr {
        Self::Mul(Box::new(self), Box::new(other))
    }
}
impl Div for Expr {
    type Output = Expr;
    fn div(self, other: Expr) -> Expr {
        Self::Div(Box::new(self), Box::new(other))
    }
}

impl NumOps for Expr {}
impl NumOps for Number {}
impl NumOps for i64 {}

enum RpnOp {
    Number(Number),
    Add,
    Sub,
    Mul,
    Div,
}
fn tokenize(text: &str) -> Vec<RpnOp> {
    let mut i = 0usize;
    let mut ops = vec![];
    for token in text.split_whitespace() {
        let rpn_op = match token {
            " " => continue,
            "+" => RpnOp::Add,
            "-" => RpnOp::Sub,
            "*" => RpnOp::Mul,
            "/" => RpnOp::Div,
            _ =>   RpnOp::Number(Number::I64(token.parse::<i64>().unwrap())),
        };
        ops.push(rpn_op);
    }
    ops
}
fn build_ast<F>(exprs: &mut Vec<Expr>, op: F)
    where F: FnOnce(Expr, Expr) -> Expr {
    let a = exprs.pop().unwrap();
    let b = exprs.pop().unwrap();
    exprs.push(op(a, b));
}
fn parse(text: &str) -> Expr {
    let mut exprs = vec![];
    for token in tokenize(text) {
        match token {
            RpnOp::Number(num) => exprs.push(Expr::Number(num)),
            RpnOp::Add => { build_ast(&mut exprs, |a, b| a + b) },
            RpnOp::Sub => { build_ast(&mut exprs, |a, b| a - b) },
            RpnOp::Div => { build_ast(&mut exprs, |a, b| a / b) },
            RpnOp::Mul => { build_ast(&mut exprs, |a, b| a * b) },
        }
    }
    exprs.pop().unwrap() // TODO: stack のチェック
}

fn eval_and_get_i64(arith: Expr) -> i64 {
    arith.eval().get_i64().unwrap()
}

#[test]
fn test() {
    let mut arith = parse("1 2 +");
    assert_eq!("(2 + 1)", format!("{}", arith));
    assert_eq!(3i64, eval_and_get_i64(arith));
    arith = parse("3 4 + 1 2 - *");
    assert_eq!("((2 - 1) * (4 + 3))", format!("{}", arith));
    assert_eq!(7i64, eval_and_get_i64(arith));
    arith = parse("3 6 / 1 4 - * 10 +");
    assert_eq!("(10 + ((4 - 1) * (6 / 3)))", format!("{}", arith));
    assert_eq!(16i64, eval_and_get_i64(arith));
}

fn main() {
}

