
use std::fmt;
use std::ops::{Add, Sub, Mul, Div};
use std::marker::PhantomData;

enum Expr<T: NumOp, U: NumOp> {
    Phantom(PhantomData<U>),
    NumI64(T),
    Add(Box<Expr<T, U>>, Box<Expr<T, U>>),
    Sub(Box<Expr<T, U>>, Box<Expr<T, U>>),
    Mul(Box<Expr<T, U>>, Box<Expr<T, U>>),
    Div(Box<Expr<T, U>>, Box<Expr<T, U>>),
}

struct Faction {
    num: i64,
    den: i64,
}

impl<T: NumOp, U: NumOp> Expr<T, U> {
    fn eval(self) -> U {
        match self {
            Expr::NumI64(val) => val as U,
            Expr::Add(a, b) => (*a).eval() + (*b).eval(),
            Expr::Sub(a, b) => (*a).eval() - (*b).eval(),
            Expr::Mul(a, b) => (*a).eval() * (*b).eval(),
            Expr::Div(a, b) => (*a).eval() / (*b).eval(),
            Expr::Phantom(u) => u,
        }
    }
}

impl<T: NumOp, U: NumOp> fmt::Display for Expr<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::NumI64(a) => write!(f, "{}", a),
            Expr::Add(ref a, ref b) => write!(f, "({} + {})", *a, *b),
            Expr::Sub(ref a, ref b) => write!(f, "({} - {})", *a, *b),
            Expr::Mul(ref a, ref b) => write!(f, "({} * {})", *a, *b),
            Expr::Div(ref a, ref b) => write!(f, "({} / {})", *a, *b),
        }
    }
}

trait NumOp<T = Self, Output = Self>:
    Add<T, Output = Output>
    + Sub<T, Output = Output>
    + Mul<T, Output = Output>
    + Div<T, Output = Output>
    + fmt::Display {}

impl<T: NumOp, U: NumOp> Add for Expr<T, U> {
    type Output = Expr<T, U>;
    fn add(self, other: Expr<T, U>) -> Expr<T, U> {
        Expr::Add(Box::new(self), Box::new(other))
    }
}
impl<T: NumOp, U: NumOp> Sub for Expr<T, U> {
    type Output = Expr<T, U>;
    fn sub(self, other: Expr<T, U>) -> Expr<T, U> {
        Expr::Sub(Box::new(self), Box::new(other))
    }
}
impl<T: NumOp, U: NumOp> Mul for Expr<T, U> {
    type Output = Expr<T, U>;
    fn mul(self, other: Expr<T, U>) -> Expr<T, U> {
        Expr::Mul(Box::new(self), Box::new(other))
    }
}
impl<T: NumOp, U: NumOp> Div for Expr<T, U> {
    type Output = Expr<T, U>;
    fn div(self, other: Expr<T, U>) -> Expr<T, U> {
        Expr::Div(Box::new(self), Box::new(other))
    }
}

impl<T: NumOp, U: NumOp> NumOp for Expr<T, U> {}
impl NumOp for i64 {}

fn num<U: NumOp>(val: i64) -> Expr<i64, U> { Expr::NumI64(val) }

enum RpnOp {
    NumI64(i64),
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
            _ =>   RpnOp::NumI64(token.parse::<i64>().unwrap()),
        };
        ops.push(rpn_op);
    }
    ops
}
fn build_ast<F, U>(exprs: &mut Vec<Expr<i64, U>>, op: F)
    where F: FnOnce(Expr<i64, U>, Expr<i64, U>) -> Expr<i64, U>, U: NumOp {
    let a = exprs.pop().unwrap();
    let b = exprs.pop().unwrap();
    exprs.push(op(a, b));
}
fn parse(text: &str) -> Expr<i64, i64> {
    let mut exprs = vec![];
    for token in tokenize(text) {
        match token {
            RpnOp::NumI64(i) => exprs.push(num::<64>(i)), // TODO
            RpnOp::Add => { build_ast(&mut exprs, |a, b| a + b) },
            RpnOp::Sub => { build_ast(&mut exprs, |a, b| a - b) },
            RpnOp::Div => { build_ast(&mut exprs, |a, b| a / b) },
            RpnOp::Mul => { build_ast(&mut exprs, |a, b| a * b) },
        }
    }
    exprs.pop().unwrap() // TODO: stack のチェック
}

#[test]
fn test() {
    let mut arith = parse("1 2 +");
    assert_eq!("(2 + 1)", format!("{}", arith));
    assert_eq!(3i64, arith.eval());
    arith = parse("3 4 + 1 2 - *");
    assert_eq!("((2 - 1) * (4 + 3))", format!("{}", arith));
    assert_eq!(7i64, arith.eval());
    arith = parse("3 6 / 1 4 - * 10 +");
    assert_eq!("(10 + ((4 - 1) * (6 / 3)))", format!("{}", arith));
    assert_eq!(16i64, arith.eval());
}

fn main() {
}

