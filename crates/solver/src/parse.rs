//! 方程式のパーサ。
//!
//! `parse_strict` は About ページ (https://gghx0.github.io/fe-project/about) の文法に厳密に従う:
//!   f(A + B) = C + D
//! A, B, C, D はそれぞれ次の 17 個の式のどれか（表記はデータの display と同じ）:
//!   x, f(x), y, f(y), x^2, xf(x), f(x)^2, f(x^2), y^2, yf(y), f(y)^2, f(y^2),
//!   xf(y), yf(x), f(x)f(y), xy, f(xy)
//! 区切りは厳密に "f(" … " + " … ") = " … " + " … とする。
//!
//! `parse_general` は CLI 用の一般の式パーサ（+, -, *, ^, 括弧, f(...), x, y, 整数, 分数 a/b）。

use fe_kernel::Poly;

/// About ページの 17 個の式
pub const TERMS: [&str; 17] = [
    "x", "f(x)", "y", "f(y)", "x^2", "xf(x)", "f(x)^2", "f(x^2)", "y^2", "yf(y)", "f(y)^2", "f(y^2)", "xf(y)",
    "yf(x)", "f(x)f(y)", "xy", "f(xy)",
];

fn x() -> Poly {
    Poly::var(0)
}
fn y() -> Poly {
    Poly::var(1)
}
fn f(p: Poly) -> Poly {
    Poly::f(p)
}

/// 17 個の式のどれかを多項式に変換する
pub fn term_poly(t: &str) -> Option<Poly> {
    Some(match t {
        "x" => x(),
        "f(x)" => f(x()),
        "y" => y(),
        "f(y)" => f(y()),
        "x^2" => x().pow(2),
        "xf(x)" => x().mul(&f(x())),
        "f(x)^2" => f(x()).pow(2),
        "f(x^2)" => f(x().pow(2)),
        "y^2" => y().pow(2),
        "yf(y)" => y().mul(&f(y())),
        "f(y)^2" => f(y()).pow(2),
        "f(y^2)" => f(y().pow(2)),
        "xf(y)" => x().mul(&f(y())),
        "yf(x)" => y().mul(&f(x())),
        "f(x)f(y)" => f(x()).mul(&f(y())),
        "xy" => x().mul(&y()),
        "f(xy)" => f(x().mul(&y())),
        _ => return None,
    })
}

/// 厳密な文法での解析結果
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StrictEq {
    pub a: String,
    pub b: String,
    pub c: String,
    pub d: String,
}

impl StrictEq {
    /// (左辺, 右辺) = (f(A + B), C + D)
    pub fn sides(&self) -> (Poly, Poly) {
        let p = |t: &str| term_poly(t).expect("検査済みの項");
        (f(p(&self.a).add(&p(&self.b))), p(&self.c).add(&p(&self.d)))
    }
}

/// About ページの文法に厳密に従って解析する
pub fn parse_strict(s: &str) -> Result<StrictEq, String> {
    let (left, right) = s.split_once(" = ").ok_or("\" = \" がない")?;
    if right.contains(" = ") {
        return Err("\" = \" が複数ある".into());
    }
    let inner = left
        .strip_prefix("f(")
        .and_then(|t| t.strip_suffix(')'))
        .ok_or("左辺が f( … ) の形ではない")?;
    let two = |t: &str| -> Result<(String, String), String> {
        let parts: Vec<&str> = t.split(" + ").collect();
        if parts.len() != 2 {
            return Err(format!("\"{}\" が 2 項の和ではない", t));
        }
        for p in &parts {
            if !TERMS.contains(p) {
                return Err(format!("\"{}\" は許された 17 個の式ではない", p));
            }
        }
        Ok((parts[0].to_string(), parts[1].to_string()))
    };
    let (a, b) = two(inner)?;
    let (c, d) = two(right)?;
    Ok(StrictEq { a, b, c, d })
}

// ---------------------------------------------------------------------------
// 一般の式パーサ

struct P<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() {
            self.i += 1;
        }
    }
    fn peek(&mut self) -> Option<u8> {
        self.ws();
        self.s.get(self.i).copied()
    }
    fn eat(&mut self, c: u8) -> bool {
        if self.peek() == Some(c) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn expr(&mut self) -> Result<Poly, String> {
        let mut acc = if self.eat(b'-') { self.term()?.neg() } else { self.term()? };
        loop {
            if self.eat(b'+') {
                acc = acc.add(&self.term()?);
            } else if self.eat(b'-') {
                acc = acc.sub(&self.term()?);
            } else {
                return Ok(acc);
            }
        }
    }
    fn term(&mut self) -> Result<Poly, String> {
        let mut acc = self.power()?;
        loop {
            if self.eat(b'*') {
                acc = acc.mul(&self.power()?);
            } else if self.eat(b'/') {
                let d = self.power()?;
                let c = d.as_const().ok_or("定数以外での割り算はできない")?;
                if c == fe_kernel::poly::q(0) {
                    return Err("0 で割っている".into());
                }
                acc = acc.scale(&(fe_kernel::poly::q(1) / c));
            } else if matches!(self.peek(), Some(b'x') | Some(b'y') | Some(b'f') | Some(b'(')) || self.peek().map_or(false, |c| c.is_ascii_digit()) {
                // 暗黙の積 (xf(y), 2x など)
                acc = acc.mul(&self.power()?);
            } else {
                return Ok(acc);
            }
        }
    }
    fn power(&mut self) -> Result<Poly, String> {
        let base = self.atom()?;
        if self.eat(b'^') {
            self.ws();
            let st = self.i;
            while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
                self.i += 1;
            }
            let e: u32 = std::str::from_utf8(&self.s[st..self.i]).unwrap().parse().map_err(|_| "指数が不正")?;
            if e > 16 {
                return Err("指数が大きすぎる".into());
            }
            return Ok(base.pow(e));
        }
        Ok(base)
    }
    fn atom(&mut self) -> Result<Poly, String> {
        match self.peek() {
            Some(b'(') => {
                self.i += 1;
                let e = self.expr()?;
                if !self.eat(b')') {
                    return Err("')' がない".into());
                }
                Ok(e)
            }
            Some(b'x') => {
                self.i += 1;
                Ok(x())
            }
            Some(b'y') => {
                self.i += 1;
                Ok(y())
            }
            Some(b'f') => {
                self.i += 1;
                if !self.eat(b'(') {
                    return Err("f の後に '(' がない".into());
                }
                let e = self.expr()?;
                if !self.eat(b')') {
                    return Err("')' がない".into());
                }
                Ok(f(e))
            }
            Some(c) if c.is_ascii_digit() => {
                let st = self.i;
                while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
                    self.i += 1;
                }
                let n: i64 = std::str::from_utf8(&self.s[st..self.i]).unwrap().parse().map_err(|_| "数が大きすぎる")?;
                Ok(Poly::int(n))
            }
            other => Err(format!("予期しない文字 {:?}", other.map(|c| c as char))),
        }
    }
}

/// 一般の方程式 "L = R" を解析する
pub fn parse_general(s: &str) -> Result<(Poly, Poly), String> {
    let (l, r) = s.split_once('=').ok_or("'=' がない")?;
    let parse = |t: &str| -> Result<Poly, String> {
        let mut p = P { s: t.as_bytes(), i: 0 };
        let e = p.expr()?;
        p.ws();
        if p.i != p.s.len() {
            return Err(format!("解析できない残り: {}", &t[p.i..]));
        }
        Ok(e)
    };
    Ok((parse(l)?, parse(r)?))
}
