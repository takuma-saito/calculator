
use std::io;
use std::fmt;
use std::ops::{Add, Sub, Mul, Div, Rem};

enum Expr {
    Primitive(Primitive),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Rem(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
    FracDiv(Box<Expr>, Box<Expr>),
    Exp(Box<Expr>),
    Ln(Box<Expr>),
}

#[derive(Debug, PartialEq)]
struct BigNum {
    val: Vec<u8>,
    sign: i8, // TODO
}

fn debug(vec: &Vec<u8>) {
    println!("0x[{}]", vec.iter().map(|x| format!("{}", x)).collect::<Vec<String>>().join(" "));
}

impl BigNum {

    fn trailing_zero(vec: &mut Vec<u8>) {
        while let Some(u) = vec.last() {
            if *u == 0 { vec.pop(); } else { break; }
        }
    }

    fn new<F: AsRef<str>>(text: F) -> Self {
        let source = text.as_ref();
        let len = source.len();
        let mut ret = vec![0_u8; ((10_f64.ln() / 256_f64.ln()) as usize + 2_usize) * len];
        for ch in source.chars() {
            assert!(ch.is_digit(10)); // TODO
            let mut carry = ch.to_digit(10).unwrap() as u32;
            for j in 0..ret.len() { // b256 = 10 * b256 + carry
                carry += (ret[j] as u32) * 10_u32;
                ret[j] = (carry & 0xff_u32) as u8;
                carry >>= 8;
            }
        }
        Self::trailing_zero(&mut ret);
        Self { val: ret, sign: 1_i8 }
    }

    fn new_from_u32(val: u32) -> Self {
        let mut ret = vec![];
        for (i, bitmask) in
            [0xff_u32, 0xff00_u32, 0xff0000_u32, 0xff000000_u32]
            .iter().enumerate() {
            ret.push(((val & bitmask) >> (i*8)) as u8);
        }
        Self::trailing_zero(&mut ret);
        Self { val: ret, sign: 1_i8 }
    }

    fn new_from_u64(val: u64) -> Self {
        let mut ret = vec![];
        for (i, bitmask) in
            [
                0xff_u64, 0xff00_u64, 0xff0000_u64, 0xff000000_u64,
                0xff00000000_u64, 0xff0000000000_u64, 0xff000000000000_u64, 0xff00000000000000_u64
            ]
            .iter().enumerate() {
            ret.push(((val & bitmask) >> (i*8)) as u8);
        }
        Self::trailing_zero(&mut ret);
        Self { val: ret, sign: 1_i8 }
    }
}

impl fmt::Display for BigNum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let len = self.val.len();
        let mut ret = vec![0; ((256_f64.ln() / 10_f64.ln()) as usize + 2_usize) * len];
        for i in 0..len {
            let mut carry = self.val[len - i - 1] as u32;
            for j in 0..ret.len() { // b10 = 256 * b10 + carry
                carry += (ret[j] as u32) << 8;
                ret[j] = (carry % 10) as u8;
                carry /= 10;
            }
        }
        Self::trailing_zero(&mut ret);
        write!(f, "{}", ret.iter().rev().map(|x| (x + '0' as u8) as char).collect::<String>())
    }
}

impl Add for BigNum {
    type Output = BigNum;
    fn add(self, other: BigNum) -> BigNum {
        let (x, y) = if self.val.len() >= other.val.len() { (self, other) } else { (other, self) };
        let mut carry = 0_u32;
        let mut ret = vec![0; x.val.len()];
        let len = x.val.len();
        for i in 0..len {
            carry += x.val[i] as u32;
            carry += *y.val.get(i).unwrap_or(&0) as u32; // TODO: Vec<T> から index にアクセスして Option<T> を取得することは可能？
            let mut j = i;
            while carry != 0 && j < len {
                carry += ret[j] as u32;
                ret[j] = (carry & 0xff_u32) as u8;
                carry >>= 8;
                j += 1;
            }
        }
        Self::trailing_zero(&mut ret);
        Self { val: ret, sign: 1_i8 }
    }
}

impl Mul for BigNum {
    type Output = BigNum;
    fn mul(self, other: BigNum) -> BigNum {
        let (x, y) = if self.val.len() >= other.val.len() { (self, other) } else { (other, self) };
        let mut ret = vec![0; x.val.len() * 2 + 1];
        for i in 0..y.val.len() {
            let mut carry = 0_u32;
            let u = y.val[i];
            for j in 0..x.val.len() {
                carry += (u as u32) * (x.val[j] as u32) + (ret[i+j] as u32);
                ret[i+j] = (carry & 0xff_u32) as u8;
                carry >>= 8;
            }
            assert!(carry < 256); // TODO
            ret[i+x.val.len()] = carry as u8;
        }
        Self::trailing_zero(&mut ret);
        Self { val: ret, sign: 1_i8 }
    }
}

impl Sub for BigNum {
    type Output = BigNum;
    fn sub(self, _other: BigNum) -> BigNum {
        unimplemented!();
    }
}

impl Div for BigNum {
    type Output = BigNum;
    fn div(self, _other: BigNum) -> BigNum {
        unimplemented!();
    }
}

impl Pow for BigNum {
    type Output = BigNum;
    fn pow(self, _other: BigNum) -> BigNum {
        unimplemented!();
    }
}

impl Rem for BigNum {
    type Output = BigNum;
    fn rem(self, _other: BigNum) -> BigNum {
        unimplemented!();
    }
}

#[test]
fn test_bignum() {
    assert_eq!("123456789",
        format!("{}", BigNum::new("123456789")));
    assert_eq!("123456789123456789123456789",
        format!("{}", BigNum::new("123456789123456789123456789")));
    assert_eq!("246913578",
        format!("{}", BigNum::new("123456789") + BigNum::new("123456789")));
    assert_eq!("246913578246913578246913578".to_string(),
        format!("{}", BigNum::new("123456789123456789123456789") + BigNum::new("123456789123456789123456789")));
    assert_eq!("15241578750190521".to_string(),
        format!("{}", BigNum::new("123456789") * BigNum::new("123456789")));
    assert_eq!("15241578780673678546105778281054720515622620750190521".to_string(),
        format!("{}", BigNum::new("123456789123456789123456789") * BigNum::new("123456789123456789123456789")));
}

#[test]
fn test_bignum_new() {
    assert_eq!("123456789",
        format!("{}", BigNum::new_from_u32(123456789_u32)));
    assert_eq!("123456789123456789",
        format!("{}", BigNum::new_from_u64(123456789123456789_u64)));
}

impl From<i64> for Primitive {
    fn from(value: i64) -> Self {
        Primitive::I64(value)
    }
}

impl From<i32> for Primitive {
    fn from(value: i32) -> Self {
        (value as i64).into()
    }
}

impl From<Primitive> for Option<i32> {
    fn from(value: Primitive) -> Option<i32> {
        Option::<i64>::from(value).map(|v| v as i32)
    }
}

impl From<Primitive> for Option<i64> {
    fn from(value: Primitive) -> Option<i64> {
        if let Primitive::I64(val) = value { Some(val) } else { None }
    }
}

impl From<Primitive> for Option<BigNum> {
    fn from(value: Primitive) -> Option<BigNum> {
        if let Primitive::BigNum(val) = value { Some(val) } else { None }
    }
}

impl From<f64> for Primitive {
    fn from(value: f64) -> Self {
        Primitive::F64(value)
    }
}

impl From<f32> for Primitive {
    fn from(value: f32) -> Self {
        (value as f64).into()
    }
}

impl From<Primitive> for Option<f64> {
    fn from(value: Primitive) -> Option<f64> {
        if let Primitive::F64(val) = value { Some(val) } else { None }
    }
}

impl From<Primitive> for Option<f32> {
    fn from(value: Primitive) -> Option<f32> {
        Option::<f64>::from(value).map(|v| v as f32)
    }
}

enum Primitive {
    I64(i64),
    F64(f64),
    Fraction(Fraction),
    BigNum(BigNum),
}

impl Primitive {
    fn as_f64(&self) -> f64 {
        match self {
            Primitive::F64(val) => *val,
            Primitive::I64(val) => (*val) as f64,
            Primitive::Fraction(frac) => (frac.top as f64) / (frac.bottom as f64),
            Primitive::BigNum(_val) => todo!(),
        }
    }
    fn as_i64(&self) -> i64 {
        match self {
            Primitive::F64(val) => (*val) as i64,
            Primitive::I64(val) => *val,
            Primitive::Fraction(frac) => frac.top / frac.bottom,
            Primitive::BigNum(_val) => todo!(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Fraction {
    top: i64,
    bottom: i64,
}

fn gcd(a: i64, b: i64) -> i64 {
    let (x, y) = if a.abs() > b.abs() { (a, b) } else { (b, a) }; // x > y
    if y == 0 { x } else { gcd(y, x % y) } // TODO: ループで実装
}

impl Fraction {
    // TODO: パフォーマンス課題
    fn new(top: i64, bottom: i64) -> Fraction {
        Fraction { top: top, bottom: bottom }
    }
    fn simplify(self) -> Fraction {
        let Fraction { top: a, bottom: b } = self;
        let g = gcd(a, b);
        Fraction {
            top: a/g,
            bottom: b/g,
        }
    }
}

impl From<Primitive> for Option<Fraction> {
    fn from(value: Primitive) -> Option<Fraction> {
        if let Primitive::Fraction(val) = value { Some(val) } else { None }
    }
}

impl Add for Fraction {
    type Output = Fraction;
    fn add(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: (self.top * other.bottom + self.bottom * other.top),
            bottom: self.bottom * other.bottom,
        };
        frac.simplify()
    }
}

impl Sub for Fraction {
    type Output = Fraction;
    fn sub(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: (self.top * other.bottom - self.bottom * other.top),
            bottom: self.bottom * other.bottom,
        };
        frac.simplify()
    }
}

impl Mul for Fraction {
    type Output = Fraction;
    fn mul(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: self.top * other.top,
            bottom: self.bottom * other.bottom,
        };
        frac.simplify()
    }
}

impl Div for Fraction {
    type Output = Fraction;
    fn div(self, other: Fraction) -> Fraction {
        let frac = Fraction {
            top: self.top * other.bottom,
            bottom: self.bottom * other.top,
        };
        frac.simplify()
    }
}

// TODO: 実装存在しない場合の処理検討
impl Rem for Fraction {
    type Output = Fraction;
    fn rem(self, _other: Fraction) -> Fraction {
        unimplemented!()
    }
}

// TODO: 実装存在しない場合の処理検討
impl Pow for Fraction {
    type Output = Fraction;
    fn pow(self, _other: Fraction) -> Fraction {
        unimplemented!()
    }
}

impl fmt::Display for Fraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}/{})", self.top, self.bottom)
    }
}

impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::I64(val) => write!(f, "{}", val),
            Self::F64(val) => write!(f, "{}", val),
            Self::Fraction(val) => write!(f, "{}", val),
            Self::BigNum(val) => write!(f, "{}", val),
        }
    }
}

trait ToFrac {
    fn to_frac(self) -> Fraction;
}

impl ToFrac for i64 {
    fn to_frac(self) -> Fraction {
        Fraction { top: self, bottom: 1 }
    }
}

// TODO: Fraction と F64 の変数変換
macro_rules! impl_number_ops {
    (@binary $trait_name:ident $method_name:ident) => {
        impl $trait_name for Primitive {
            type Output = Primitive;
            fn $method_name(self, other: Primitive) -> Primitive {
                match (self, other) {
                    (Primitive::BigNum(x), Primitive::BigNum(y)) =>
                        Primitive::BigNum($trait_name::$method_name(x, y)),
                    (Primitive::I64(x), Primitive::I64(y)) =>
                        Primitive::I64($trait_name::$method_name(x, y)),
                    (Primitive::F64(x), Primitive::F64(y)) =>
                        Primitive::F64($trait_name::$method_name(x, y)),
                    (Primitive::Fraction(x), Primitive::Fraction(y)) => 
                        Primitive::Fraction($trait_name::$method_name(x, y)),
                    (Primitive::I64(x), Primitive::Fraction(y)) =>
                        Primitive::Fraction($trait_name::$method_name(x.to_frac(), y)),
                    (Primitive::Fraction(x), Primitive::I64(y)) =>
                        Primitive::Fraction($trait_name::$method_name(x, y.to_frac())),
                    (Primitive::I64(x), Primitive::F64(y)) =>
                        Primitive::F64($trait_name::$method_name(x as f64, y)),
                    (Primitive::F64(x), Primitive::I64(y)) =>
                        Primitive::F64($trait_name::$method_name(x, y as f64)),
                    (a, b) => {
                        panic!("convert error: {} {}", a, b);
                    }
                }
            }
        }
    };
    (@unary $trait_name:ident $method_name:ident) => {
        impl $trait_name for Primitive {
            type Output = Primitive;
            fn $method_name(self) -> Primitive {
                Primitive::F64(self.as_f64().$method_name())
            }
        }
    };
}

trait FracDiv<Rhs = Self> {
    type Output;
    fn div(self, other: Rhs) -> Self::Output;
}

impl FracDiv for Primitive {
    type Output = Primitive;
    fn div(self, other: Primitive) -> Primitive {
        match (self, other) {
            (Primitive::I64(x), Primitive::I64(y)) => 
                Primitive::Fraction(Fraction { top: x, bottom: y}),
            (a, b) => {
                panic!("Fraction divion error: {} {}", a, b);
            }
        }
    }
}

impl_number_ops!(@binary Add add);
impl_number_ops!(@binary Sub sub);
impl_number_ops!(@binary Div div);
impl_number_ops!(@binary Mul mul);
impl_number_ops!(@binary Rem rem);
impl_number_ops!(@binary Pow pow);
impl_number_ops!(@unary Exp exp);
impl_number_ops!(@unary Ln ln);

trait Pow<Rhs = Self> {
    type Output;
    fn pow(self, rhs: Rhs) -> Self::Output;
}

impl Pow for i64 {
    type Output = i64;
    fn pow(self, other: i64) -> i64 {
        self.pow(other as u32)
    }
}

impl Pow for f64 {
    type Output = f64;
    fn pow(self, other: f64) -> f64 {
        self.powf(other)
    }
}

trait Exp {
    type Output;
    fn exp(self) -> Self::Output;
}

trait Ln {
    type Output;
    fn ln(self) -> Self::Output;
}

trait NumOps<T = Self, Output = Self>:
    Add<T, Output = Output>
    + Sub<T, Output = Output>
    + Mul<T, Output = Output>
    + Div<T, Output = Output>
    + Rem<T, Output = Output>
    + Pow<T, Output = Output>
    + Exp<Output = Output>
    + Ln<Output = Output>
    + FracDiv<T, Output = Output>
    + fmt::Display {}

impl Expr {
    fn eval(self) -> Primitive {
        match self {
            Self::Primitive(p) => p,
            Self::Add(a, b) => Add::add((*a).eval(), (*b).eval()),
            Self::Sub(a, b) => Sub::sub((*a).eval(), (*b).eval()),
            Self::Mul(a, b) => Mul::mul((*a).eval(), (*b).eval()),
            Self::Div(a, b) => Div::div((*a).eval(), (*b).eval()),
            Self::Rem(a, b) => Rem::rem((*a).eval(), (*b).eval()),
            Self::Pow(a, b) => Pow::pow((*a).eval(), (*b).eval()),
            Self::Exp(a) => Exp::exp((*a).eval()),
            Self::Ln(a) => Ln::ln((*a).eval()),
            Self::FracDiv(a, b) => FracDiv::div((*a).eval(), (*b).eval()),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Primitive(num) => write!(f, "{}", num),
            Self::Add(a, b)  => write!(f, "({} + {})", *a, *b),
            Self::Sub(a, b)  => write!(f, "({} - {})", *a, *b),
            Self::Mul(a, b)  => write!(f, "({} * {})", *a, *b),
            Self::Div(a, b)  => write!(f, "({} / {})", *a, *b),
            Self::Rem(a, b)  => write!(f, "({} % {})", *a, *b),
            Self::Pow(a, b)  => write!(f, "({} ** {})", *a, *b),
            Self::Exp(a) => write!(f, "exp({})", *a),
            Self::Ln(a) => write!(f, "ln({})", *a),
            Self::FracDiv(a, b) => write!(f, "({} / {})", *a, *b),
        }
    }
}

macro_rules! impl_for_expr {
    (@binary $trait_name:ident $method_name:ident) => {
        impl $trait_name for Expr {
            type Output = Expr;
            fn $method_name(self, other: Expr) -> Expr {
                Self::$trait_name(Box::new(self), Box::new(other))
            }
        }
    };
    (@unary $trait_name:ident $method_name:ident) => {
        impl $trait_name for Expr {
            type Output = Expr;
            fn $method_name(self) -> Expr {
                Self::$trait_name(Box::new(self))
            }
        }
    };
}

impl_for_expr!(@binary Add add);
impl_for_expr!(@binary Sub sub);
impl_for_expr!(@binary Div div);
impl_for_expr!(@binary Mul mul);
impl_for_expr!(@binary Rem rem);
impl_for_expr!(@binary Pow pow);
impl_for_expr!(@unary Exp exp);
impl_for_expr!(@unary Ln ln);
impl_for_expr!(@binary FracDiv div);

impl NumOps for Expr {}
impl NumOps for Primitive {}

enum RpnOp {
    Primitive(Primitive),
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Exp,
    Ln,
    FracDiv,
}

enum TokenParserState {
    Beginning,
    Sign(bool),
    NatNum(bool, u64),
    BigNum(bool, Vec<char>),
    Decimal(bool, u64, u64, i32),
}

// @startuml
// 
// [*] --> Sign: {+|-}
// [*] --> NatNum: {0-9}
// Sign --> NatNum: {0-9}
// NatNum --> NatNum: {0-9}
// Float --> Float: {0-9}
// NatNum --> Float: {.}
// Float --> ParsedFloat: {Null}
// NatNum --> ParsedNatNum: {Null}
// ParsedFloat -> [*]
// ParsedNatNum -> [*]
// 
// @enduml
fn tokenize_primitive(token: &str) -> Primitive { // TODO: Result 型
    let mut state = TokenParserState::Beginning;
    for ch in token.chars() {
        match state {
            TokenParserState::Beginning => {
                state = match ch {
                    '-'   => TokenParserState::Sign(false),
                    '+'   => TokenParserState::Sign(true),
                    'b'   => TokenParserState::BigNum(true, vec![]),
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
            TokenParserState::BigNum(sign, mut val) => {
                val.push(ch);
                state = TokenParserState::BigNum(sign, val);
            }
            TokenParserState::Decimal(sign, val, decimal_val, pos) => {
                let new_decimal_val = 10_u64 * decimal_val + (ch.to_digit(10).unwrap() as u64); // TODO: f64 を超える場合を考慮
                state = TokenParserState::Decimal(sign, val, new_decimal_val, pos - 1);
            },
        }
    }
    match state {
        TokenParserState::NatNum(sign, val)  => 
            (if sign { val as i64 } else { -(val as i64) }).into(),
        TokenParserState::BigNum(_sign, val)  => {
            let digits = val.into_iter().collect::<String>();
            Primitive::BigNum(BigNum::new(digits))
        }
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
            "%" => RpnOp::Rem,
            "**" => RpnOp::Pow,
            "exp" => RpnOp::Exp,
            "ln" => RpnOp::Ln,
            "//" => RpnOp::FracDiv,
            _ => {
                RpnOp::Primitive(tokenize_primitive(token))
            }
        };
        ops.push(rpn_op);
    }
    ops
}
fn build_ast_binary<F>(exprs: &mut Vec<Expr>, op: F)
    where F: FnOnce(Expr, Expr) -> Expr {
    let a = exprs.pop().unwrap();
    let b = exprs.pop().unwrap();
    exprs.push(op(a, b));
}
fn build_ast_unary<F>(exprs: &mut Vec<Expr>, op: F)
    where F: FnOnce(Expr) -> Expr {
    let a = exprs.pop().unwrap();
    exprs.push(op(a));
}
fn parse<N: AsRef<str>>(text: N) -> Expr {
    let mut exprs = vec![];
    for token in tokenize(text.as_ref()) {
        match token {
            RpnOp::Primitive(num) => exprs.push(Expr::Primitive(num)),
            RpnOp::Add => { build_ast_binary(&mut exprs, |a, b| Add::add(a, b)) },
            RpnOp::Sub => { build_ast_binary(&mut exprs, |a, b| Sub::sub(a, b)) },
            RpnOp::Div => { build_ast_binary(&mut exprs, |a, b| Div::div(a, b)) },
            RpnOp::Mul => { build_ast_binary(&mut exprs, |a, b| Mul::mul(a, b)) },
            RpnOp::Rem => { build_ast_binary(&mut exprs, |a, b| Rem::rem(a, b)) },
            RpnOp::Pow => { build_ast_binary(&mut exprs, |a, b| Pow::pow(a, b)) },
            RpnOp::Ln  => { build_ast_unary(&mut exprs, |a| Ln::ln(a)) },
            RpnOp::Exp => { build_ast_unary(&mut exprs, |a| Exp::exp(a)) },
            RpnOp::FracDiv => { build_ast_binary(&mut exprs, |a, b| FracDiv::div(a, b)) },
        }
    }
    exprs.pop().unwrap() // TODO: stack のチェック
}

macro_rules! parser_assert_eq {
    ($input:expr, $display_expected_value:expr, $eval_expected_value:expr) => {
        let arith = parse($input);
        assert_eq!($display_expected_value, format!("{}", arith));
        assert_eq!($eval_expected_value, arith.eval().into());
    }
}

#[test]
fn test_parse() {
    parser_assert_eq!("1 2 +", "(2 + 1)", Some(3));
    parser_assert_eq!("3 4 + 1 2 - *", "((2 - 1) * (4 + 3))", Some(7));
    parser_assert_eq!("3 6 / 1 4 - * 10 +", "(10 + ((4 - 1) * (6 / 3)))", Some(16));
    parser_assert_eq!("3.1 2.4 +", "(2.4 + 3.1)", Some(5.5));
    parser_assert_eq!("-1", "-1", Some(-1));
    parser_assert_eq!("-1.234 1.534 *", "(1.534 * -1.234)", Some(-1.892956));
    parser_assert_eq!("-1 -1.5 *", "(-1.5 * -1)", Some(1.5));
    parser_assert_eq!("-1 -1.5 *", "(-1.5 * -1)", Some(1.5));
    parser_assert_eq!("2 3.1 4.2 / 3 1.5 + * -", "(((1.5 + 3) * (4.2 / 3.1)) - 2)", Some(4.096774193548388));
    parser_assert_eq!("9 100 %", "(100 % 9)", Some(1));
    parser_assert_eq!("9 100 % 1 +", "(1 + (100 % 9))", Some(2));
    parser_assert_eq!("2.0 exp", "exp(2)", Some(7.38905609893065));
    parser_assert_eq!("2.0 ln", "ln(2)", Some(0.6931471805599453));
    parser_assert_eq!("5 3 **", "(3 ** 5)", Some(243));
    parser_assert_eq!("4 2.21234 **", "(2.21234 ** 4)", Some(23.955623922523824));
    parser_assert_eq!("2.5 3 **", "(3 ** 2.5)", Some(15.588457268119896));
    parser_assert_eq!("3 5 //", "(5 / 3)", Some(Fraction::new(5, 3)));
    parser_assert_eq!("-3 5 //", "(5 / -3)", Some(Fraction::new(5, -3)));
    parser_assert_eq!("5 3 // 12 11 // +", "((11 / 12) + (3 / 5))", Some(Fraction::new(91, 60)));
    parser_assert_eq!("3 5 // 7 8 // 3 4 // + *", "(((4 / 3) + (8 / 7)) * (5 / 3))", Some(Fraction::new(260, 63)));
    parser_assert_eq!("b1 b2 +", "(2 + 1)", Some(BigNum::new_from_u32(3_u32)));
    parser_assert_eq!("b123456789839823498723847 b1234987234987329873287394827394 +",
        "(1234987234987329873287394827394 + 123456789839823498723847)",
        Some(BigNum::new("1234987358444119713110893551241")));
    parser_assert_eq!("b123456789839823498723847 b1234987234987329873287394827394 * b1823429834 *",
        "(1823429834 * (1234987234987329873287394827394 * 123456789839823498723847))",
        Some(BigNum::new("278013896754500638853061628956443471427431794624042365856396812")));
}

fn main() -> io::Result<()> {
    for line in io::stdin().lines() {
        let arith = parse(line?);
        println!("{} = {}", arith.to_string(), arith.eval());
    }
    Ok(())
}
