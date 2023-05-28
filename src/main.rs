
use std::fmt;
use std::ops::{Add, Sub, Mul, Div};
use std::cmp::Ordering;

enum Expr {
    ExprPrimitive(ExprPrimitive),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

struct ExprPrimitive {
    primitive: Primitive,
    cast_type: CastType,
}

impl From<i64> for ExprPrimitive {
    fn from(value: i64) -> Self {
        Self {
            primitive: Primitive::I64(value),
            cast_type: CastType::I64,
        }
    }
}

impl From<ExprPrimitive> for Option<i64> {
    fn from(value: ExprPrimitive) -> Option<i64> {
        if let Primitive::I64(val) = value.primitive { Some(val) } else { None }
    }
}

impl From<f64> for ExprPrimitive {
    fn from(value: f64) -> Self {
        Self {
            primitive: Primitive::F64(value),
            cast_type: CastType::F64,
        }
    }
}

impl From<ExprPrimitive> for Option<f64> {
    fn from(value: ExprPrimitive) -> Option<f64> {
        if let Primitive::F64(val) = value.primitive { Some(val) } else { None }
    }
}

enum Primitive {
    I64(i64),
    F64(f64),
}

// F64 > I64
#[derive(Copy, Clone, PartialEq, Eq)]
enum CastType {
    I64,
    F64, 
}

impl PartialOrd for CastType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (CastType::F64, x) if *x != CastType::F64 => Some(Ordering::Greater),
            (x, CastType::F64) if *x != CastType::F64 => Some(Ordering::Less),
            (_, _) => Some(Ordering::Equal),
        }
    }
}

impl Ord for CastType {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

macro_rules! impl_number_ops {
    ($trait_name:ident, $method_name:ident) => {
        impl $trait_name for ExprPrimitive {
            type Output = ExprPrimitive;
            fn $method_name(self, other: ExprPrimitive) -> ExprPrimitive {
                let cast_type = self.cast_type.max(other.cast_type);
                let primitive = match (self.primitive, other.primitive, cast_type) {
                    (Primitive::I64(x), Primitive::I64(y), _) =>
                        Primitive::I64($trait_name::$method_name(x, y)),
                    (Primitive::F64(x), Primitive::F64(y), _) =>
                        Primitive::F64($trait_name::$method_name(x, y)),
                    (Primitive::I64(x), Primitive::F64(y), CastType::I64) =>
                        Primitive::I64($trait_name::$method_name(x, y as i64)),
                    (Primitive::I64(x), Primitive::F64(y), CastType::F64) =>
                        Primitive::F64($trait_name::$method_name(x as f64, y)),
                    (Primitive::F64(x), Primitive::I64(y), CastType::I64) =>
                        Primitive::I64($trait_name::$method_name(x as i64, y)),
                    (Primitive::F64(x), Primitive::I64(y), CastType::F64) =>
                        Primitive::F64($trait_name::$method_name(x, y as f64)),
                };
                ExprPrimitive { primitive: primitive, cast_type: cast_type }
            }
        }
    }
}

impl_number_ops!(Add, add);
impl_number_ops!(Sub, sub);
impl_number_ops!(Div, div);
impl_number_ops!(Mul, mul);

impl fmt::Display for ExprPrimitive {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.primitive {
            Primitive::I64(val) => write!(f, "{}", val),
            Primitive::F64(val) => write!(f, "{}", val),
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
    fn eval(self) -> ExprPrimitive {
        match self {
            Self::ExprPrimitive(number) => number,
            Self::Add(a, b) => (*a).eval() + (*b).eval(),
            Self::Sub(a, b) => (*a).eval() - (*b).eval(),
            Self::Mul(a, b) => (*a).eval() * (*b).eval(),
            Self::Div(a, b) => (*a).eval() / (*b).eval(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ExprPrimitive(num) => write!(f, "{}", num),
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
impl NumOps for ExprPrimitive {}
impl NumOps for i64 {}

enum RpnOp {
    ExprPrimitive(ExprPrimitive),
    Add,
    Sub,
    Mul,
    Div,
}

enum TokenParserState {
    Beginning,
    Sign(bool),
    NatNum(bool, u64),
    Decimal(bool, u64, u64, i32),
}

// @startuml
// 
// [*] --> Sign: {+|-}
// [*] --> Decimal: {0-9}
// Sign --> Decimal: {0-9}
// Decimal --> Decimal: {0-9}
// Float --> Float: {0-9}
// Decimal --> Float: {.}
// Float --> ParsedFloat: {Null}
// Decimal --> ParsedDecimal: {Null}
// ParsedFloat -> [*]
// ParsedDecimal -> [*]
// 
// @enduml
fn tokenize_primitive(token: &str) -> ExprPrimitive { // TODO: Result 型
    let mut state = TokenParserState::Beginning;
    for ch in token.chars() {
        match state {
            TokenParserState::Beginning => {
                state = match ch {
                    '-'   => TokenParserState::Sign(false),
                    '+'   => TokenParserState::Sign(true),
                    '0' ..= '9' => TokenParserState::NatNum(true, ch.to_digit(10).unwrap() as u64),
                    _ => panic!("Unexpected token {}", ch),
                };
            },
            TokenParserState::Sign(b) => {
                let d = ch.to_digit(10).unwrap() as u64;
                state = TokenParserState::NatNum(b, d);
            },
            TokenParserState::NatNum(sign, val) => {
                state = if ch != '.' {
                    let d = ch.to_digit(10).unwrap() as u64;
                    TokenParserState::NatNum(sign, val * 10 + d) // TODO u64 を超える場合を考慮
                } else {
                    TokenParserState::Decimal(sign, val, 0_u64, 0)
                };
            },
            TokenParserState::Decimal(sign, val, decimal_val, pos) => {
                let new_decimal_val = 10_u64 * decimal_val + (ch.to_digit(10).unwrap() as u64); // TODO: f64 を超える場合を考慮
                state = TokenParserState::Decimal(sign, val, new_decimal_val, pos - 1);
            },
        }
    }
    match state {
        TokenParserState::NatNum(sign, val)  => 
            (if sign { val as i64 } else { -(val as i64) }).into(),
        TokenParserState::Decimal(sign, val, decimal_val, pos) => {
            let v = (val as f64) + (decimal_val as f64) * (10.0_f64).powi(pos);
            let ret = if sign { v } else { -v };
            ret.into()
        },
        _ => panic!("Parse Faild"), // TODO: 適切なエラーを返却
    }
}
fn tokenize(text: &str) -> Vec<RpnOp> { // TODO: Result 型
    let mut ops = vec![];
    for token in text.split_whitespace() {
        let rpn_op = match token {
            " " => continue,
            "+" => RpnOp::Add,
            "-" => RpnOp::Sub,
            "*" => RpnOp::Mul,
            "/" => RpnOp::Div,
            _ => {
                RpnOp::ExprPrimitive(tokenize_primitive(token))
            }
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
            RpnOp::ExprPrimitive(num) => exprs.push(Expr::ExprPrimitive(num)),
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
    assert_eq!(Some(3_i64), arith.eval().into());
    arith = parse("3 4 + 1 2 - *");
    assert_eq!("((2 - 1) * (4 + 3))", format!("{}", arith));
    assert_eq!(Some(7_i64), arith.eval().into());
    arith = parse("3 6 / 1 4 - * 10 +");
    assert_eq!("(10 + ((4 - 1) * (6 / 3)))", format!("{}", arith));
    assert_eq!(Some(16_i64), arith.eval().into());

    arith = parse("3.1 2.4 +");
    assert_eq!(Some(3.1_f64 + 2.4_f64), arith.eval().into());

    arith = parse("-1");
    assert_eq!("-1", format!("{}", arith));
    assert_eq!(Some(-1), arith.eval().into());

    arith = parse("-1.234 1.534 *");
    assert_eq!("(1.534 * -1.234)", format!("{}", arith));
    assert_eq!(Some(-1.892956), arith.eval().into());
}

fn main() {
}

