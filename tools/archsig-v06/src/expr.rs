//! 第3章「値と条件の書き方」の小さな式。

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// 定数。`None`、`0`、`"JPY"` など、書かれたとおりの字句。
    Const(String),
    /// `?`。解析器が形に直せなかった値。
    Unknown,
    /// `$引数` と、そこからたどるフィールドの名前の列。
    Path(String, Vec<String>),
    /// 操作の呼び出し。
    Call(String, Vec<Expr>),
    /// 引数のない名前。`?` で始まれば未解決。
    Name(String),
    Not(Box<Expr>),
    Neg(Box<Expr>),
    Bin(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
}

/// 式の字句の数の上限。読みは再帰で下るので、これを超える式は読まない(設計 §3.5)。
pub const TOKEN_LIMIT: usize = 1_000;

pub fn parse(text: &str) -> Result<Expr, String> {
    let tokens = lex(text)?;
    if tokens.len() > TOKEN_LIMIT {
        return Err(format!("式の字句の数が上限({TOKEN_LIMIT})を超える"));
    }
    let mut p = Parser { tokens, pos: 0 };
    let e = p.or()?;
    if p.pos != p.tokens.len() {
        return Err(format!("式の末尾が読めない: {text}"));
    }
    Ok(e)
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Num(String),
    Str(String),
    Ident(String),
    Dollar(String),
    Op(&'static str),
    LParen,
    RParen,
    Comma,
    Dot,
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn lex(text: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c.is_ascii_digit() {
            let s = i;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '.' && i + 1 < chars.len() && chars[i + 1].is_ascii_digit()) {
                i += 1;
            }
            out.push(Tok::Num(chars[s..i].iter().collect()));
        } else if c == '"' {
            let s = i;
            i += 1;
            while i < chars.len() && chars[i] != c {
                if chars[i] == '\\' {
                    i += 1;
                }
                i += 1;
            }
            if i >= chars.len() {
                return Err(format!("閉じていない文字列: {text}"));
            }
            i += 1;
            let body: String = chars[s + 1..i - 1].iter().collect();
            out.push(Tok::Str(format!("\"{body}\"")));
        } else if c == '$' {
            let s = i + 1;
            i += 1;
            while i < chars.len() && is_ident_char(chars[i]) {
                i += 1;
            }
            out.push(Tok::Dollar(chars[s..i].iter().collect()));
        } else if c == '?' {
            let s = i;
            i += 1;
            while i < chars.len() && (is_ident_char(chars[i]) || chars[i] == '.' && i + 1 < chars.len() && is_ident_char(chars[i + 1])) {
                i += 1;
            }
            out.push(Tok::Ident(chars[s..i].iter().collect()));
        } else if is_ident_char(c) {
            let s = i;
            while i < chars.len() && is_ident_char(chars[i]) {
                i += 1;
            }
            out.push(Tok::Ident(chars[s..i].iter().collect()));
        } else {
            let two: String = chars[i..(i + 2).min(chars.len())].iter().collect();
            let op = match two.as_str() {
                "==" => Some("=="),
                "!=" => Some("!="),
                "<=" => Some("<="),
                ">=" => Some(">="),
                _ => None,
            };
            if let Some(op) = op {
                out.push(Tok::Op(op));
                i += 2;
                continue;
            }
            let t = match c {
                '(' => Tok::LParen,
                ')' => Tok::RParen,
                ',' => Tok::Comma,
                '.' => Tok::Dot,
                '<' => Tok::Op("<"),
                '>' => Tok::Op(">"),
                '+' => Tok::Op("+"),
                '-' => Tok::Op("-"),
                '*' => Tok::Op("*"),
                '/' => Tok::Op("/"),
                _ => return Err(format!("読めない文字 `{c}`: {text}")),
            };
            out.push(t);
            i += 1;
        }
    }
    Ok(out)
}

struct Parser {
    tokens: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.tokens.get(self.pos)
    }

    fn eat_op(&mut self, ops: &[&str]) -> Option<&'static str> {
        match self.peek() {
            Some(Tok::Op(o)) if ops.contains(o) => {
                let o = *o;
                self.pos += 1;
                Some(o)
            }
            Some(Tok::Ident(w)) if (w == "and" || w == "or" || w == "not") && ops.contains(&w.as_str()) => {
                let o = match w.as_str() {
                    "and" => "and",
                    "or" => "or",
                    _ => "not",
                };
                self.pos += 1;
                Some(o)
            }
            _ => None,
        }
    }

    fn or(&mut self) -> Result<Expr, String> {
        let mut e = self.and()?;
        while self.eat_op(&["or"]).is_some() {
            e = Expr::Bin(BinOp::Or, Box::new(e), Box::new(self.and()?));
        }
        Ok(e)
    }

    fn and(&mut self) -> Result<Expr, String> {
        let mut e = self.not()?;
        while self.eat_op(&["and"]).is_some() {
            e = Expr::Bin(BinOp::And, Box::new(e), Box::new(self.not()?));
        }
        Ok(e)
    }

    fn not(&mut self) -> Result<Expr, String> {
        if self.eat_op(&["not"]).is_some() {
            return Ok(Expr::Not(Box::new(self.not()?)));
        }
        self.cmp()
    }

    fn cmp(&mut self) -> Result<Expr, String> {
        let a = self.add()?;
        if let Some(o) = self.eat_op(&["==", "!=", "<", "<=", ">", ">="]) {
            let op = match o {
                "==" => BinOp::Eq,
                "!=" => BinOp::Ne,
                "<" => BinOp::Lt,
                "<=" => BinOp::Le,
                ">" => BinOp::Gt,
                _ => BinOp::Ge,
            };
            return Ok(Expr::Bin(op, Box::new(a), Box::new(self.add()?)));
        }
        Ok(a)
    }

    fn add(&mut self) -> Result<Expr, String> {
        let mut e = self.mul()?;
        while let Some(o) = self.eat_op(&["+", "-"]) {
            let op = if o == "+" { BinOp::Add } else { BinOp::Sub };
            e = Expr::Bin(op, Box::new(e), Box::new(self.mul()?));
        }
        Ok(e)
    }

    fn mul(&mut self) -> Result<Expr, String> {
        let mut e = self.unary()?;
        while let Some(o) = self.eat_op(&["*", "/"]) {
            let op = if o == "*" { BinOp::Mul } else { BinOp::Div };
            e = Expr::Bin(op, Box::new(e), Box::new(self.unary()?));
        }
        Ok(e)
    }

    fn unary(&mut self) -> Result<Expr, String> {
        if self.eat_op(&["-"]).is_some() {
            return Ok(Expr::Neg(Box::new(self.unary()?)));
        }
        self.primary()
    }

    fn primary(&mut self) -> Result<Expr, String> {
        let t = self.peek().cloned().ok_or("式が途中で終わっている")?;
        self.pos += 1;
        match t {
            Tok::Num(n) => Ok(Expr::Const(n)),
            Tok::Str(s) => Ok(Expr::Const(s)),
            Tok::LParen => {
                let e = self.or()?;
                match self.peek() {
                    Some(Tok::RParen) => {
                        self.pos += 1;
                        Ok(e)
                    }
                    _ => Err("閉じていない括弧".to_string()),
                }
            }
            Tok::Dollar(p) => {
                let mut fields = Vec::new();
                while self.peek() == Some(&Tok::Dot) {
                    self.pos += 1;
                    match self.peek().cloned() {
                        Some(Tok::Ident(f)) => {
                            self.pos += 1;
                            fields.push(f);
                        }
                        _ => return Err("`.` の後に名前がない".to_string()),
                    }
                }
                Ok(Expr::Path(p, fields))
            }
            Tok::Ident(w) => {
                if w == "?" {
                    return Ok(Expr::Unknown);
                }
                let mut name = w;
                while self.peek() == Some(&Tok::Dot) {
                    self.pos += 1;
                    match self.peek().cloned() {
                        Some(Tok::Ident(f)) => {
                            self.pos += 1;
                            name.push('.');
                            name.push_str(&f);
                        }
                        _ => return Err("`.` の後に名前がない".to_string()),
                    }
                }
                if self.peek() == Some(&Tok::LParen) {
                    self.pos += 1;
                    let mut args = Vec::new();
                    if self.peek() == Some(&Tok::RParen) {
                        self.pos += 1;
                        return Ok(Expr::Call(name, args));
                    }
                    loop {
                        args.push(self.or()?);
                        match self.peek() {
                            Some(Tok::Comma) => self.pos += 1,
                            Some(Tok::RParen) => {
                                self.pos += 1;
                                break;
                            }
                            _ => return Err("呼び出しの引数が閉じていない".to_string()),
                        }
                    }
                    return Ok(Expr::Call(name, args));
                }
                Ok(Expr::Name(name))
            }
            other => Err(format!("読めない字句 {other:?}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_forms_of_chapter_3() {
        let path = |p: &str, f: &[&str]| Expr::Path(p.into(), f.iter().map(|x| x.to_string()).collect());
        assert_eq!(
            parse("$new.country != $order.shipping_address.country").unwrap(),
            Expr::Bin(BinOp::Ne, Box::new(path("new", &["country"])), Box::new(path("order", &["shipping_address", "country"])))
        );
        assert_eq!(parse("shop.a.f($new)").unwrap(), Expr::Call("shop.a.f".into(), vec![path("new", &[])]));
        assert_eq!(
            parse("$order.total * 100").unwrap(),
            Expr::Bin(BinOp::Mul, Box::new(path("order", &["total"])), Box::new(Expr::Const("100".into())))
        );
        assert_eq!(parse("not $order.paid").unwrap(), Expr::Not(Box::new(path("order", &["paid"]))));
        assert_eq!(parse("None").unwrap(), Expr::Name("None".into()));
        assert_eq!(parse("?").unwrap(), Expr::Unknown);
    }

    #[test]
    fn unresolved_names() {
        assert_eq!(parse("?mail.send($x)").unwrap(), Expr::Call("?mail.send".into(), vec![Expr::Path("x".into(), vec![])]));
        assert_eq!(parse("f(?)").unwrap(), Expr::Call("f".into(), vec![Expr::Unknown]));
    }
}
