
enum Expr {
    Num(i32),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

impl Expr {
    fn eval(self) -> i32 {
        match self {
            Expr::Num(val) => val,
            Expr::Add(a, b) => (*a).eval() + (*b).eval(),
            Expr::Sub(a, b) => (*a).eval() - (*b).eval(),
            Expr::Mul(a, b) => (*a).eval() * (*b).eval(),
            Expr::Div(a, b) => (*a).eval() / (*b).eval(),
        }
    }

    
    fn to_string(&self) -> String {
        match self {
            Expr::Num(ref a) => (*a).to_string(),
            Expr::Add(ref a, ref b) => format!("({} + {})", (*a).to_string(), (*b).to_string()),
            Expr::Sub(ref a, ref b) => format!("({} - {})", (*a).to_string(), (*b).to_string()),
            Expr::Mul(ref a, ref b) => format!("({} * {})", (*a).to_string(), (*b).to_string()),
            Expr::Div(ref a, ref b) => format!("({} / {})", (*a).to_string(), (*b).to_string()),
        }
    }
}

fn add(a: Expr, b: Expr) -> Expr { Expr::Add(Box::new(a), Box::new(b)) }
fn sub(a: Expr, b: Expr) -> Expr { Expr::Sub(Box::new(a), Box::new(b)) }
fn mul(a: Expr, b: Expr) -> Expr { Expr::Mul(Box::new(a), Box::new(b)) }
fn div(a: Expr, b: Expr) -> Expr { Expr::Div(Box::new(a), Box::new(b)) }
fn num(val: i32) -> Expr { Expr::Num(val) }

fn main() {
    let arith = add(num(1), mul(sub(num(10), num(4)), div(num(6), num(3))));
    println!("{} = {}", arith.to_string(), arith.eval());
}

