//! 係数域、スカラー定数、および型付き affine / 多項式構文木（PolyExpr）。

use crate::ir::provenance::SourceRef;
use archsig_common::canonical::Json;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeSet;
use std::fmt;

/// SHIGURE IR が扱う基礎係数域（Z / Q / F_p）。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CoeffDomain {
    Z,
    Q,
    Fp(BigUint),
}

impl CoeffDomain {
    pub fn wire(&self) -> Json {
        match self {
            CoeffDomain::Z => Json::str("Z"),
            CoeffDomain::Q => Json::str("Q"),
            CoeffDomain::Fp(p) => Json::Arr(vec![Json::str("Fp"), Json::str(p.to_string())]),
        }
    }
}

impl fmt::Display for CoeffDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CoeffDomain::Z => write!(f, "Z"),
            CoeffDomain::Q => write!(f, "Q"),
            CoeffDomain::Fp(p) => write!(f, "Fp({p})"),
        }
    }
}

/// 係数域に属する正確なスカラー定数。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarLit {
    Z(BigInt),
    /// 既約分数（`den > 0`、`gcd(|num|, den) == 1`）。
    Q {
        num: BigInt,
        den: BigInt,
    },
    /// 有限体 `Fp(modulus)` の正規代表（`0 <= value < modulus`）。
    Fp {
        value: BigUint,
        modulus: BigUint,
    },
}

impl ScalarLit {
    pub fn int(n: impl Into<BigInt>) -> Self {
        ScalarLit::Z(n.into())
    }

    /// 既約有理数を構築する。分母が 0 なら `None`。
    pub fn rat(num: impl Into<BigInt>, den: impl Into<BigInt>) -> Option<Self> {
        let mut n = num.into();
        let mut d = den.into();
        if d.is_zero() {
            return None;
        }
        if d.is_negative() {
            n = -n;
            d = -d;
        }
        if n.is_zero() {
            return Some(ScalarLit::Q {
                num: BigInt::zero(),
                den: BigInt::one(),
            });
        }
        let g = n.gcd(&d);
        Some(ScalarLit::Q {
            num: n / &g,
            den: d / g,
        })
    }

    /// `Fp(modulus)` の元を構築する。法が 2 未満なら `None`。
    pub fn fp(value: BigInt, modulus: BigUint) -> Option<Self> {
        if modulus < BigUint::from(2u32) {
            return None;
        }
        let m_signed = BigInt::from(modulus.clone());
        let reduced = value.mod_floor(&m_signed);
        let (_, mag) = reduced.into_parts();
        Some(ScalarLit::Fp {
            value: mag,
            modulus,
        })
    }

    pub fn domain(&self) -> CoeffDomain {
        match self {
            ScalarLit::Z(_) => CoeffDomain::Z,
            ScalarLit::Q { .. } => CoeffDomain::Q,
            ScalarLit::Fp { modulus, .. } => CoeffDomain::Fp(modulus.clone()),
        }
    }

    pub fn matches_domain(&self, expected: &CoeffDomain) -> bool {
        match (self, expected) {
            (ScalarLit::Z(_), CoeffDomain::Z) => true,
            (ScalarLit::Q { .. }, CoeffDomain::Q) => true,
            (ScalarLit::Fp { modulus, .. }, CoeffDomain::Fp(p)) => modulus == p,
            _ => false,
        }
    }

    pub fn to_json(&self) -> Json {
        match self {
            ScalarLit::Z(n) => Json::str(n.to_string()),
            ScalarLit::Q { num, den } => {
                Json::Arr(vec![Json::str(num.to_string()), Json::str(den.to_string())])
            }
            ScalarLit::Fp { value, .. } => Json::str(value.to_string()),
        }
    }
}

impl fmt::Display for ScalarLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScalarLit::Z(n) => write!(f, "{n}"),
            ScalarLit::Q { num, den } if den.is_one() => write!(f, "{num}"),
            ScalarLit::Q { num, den } => write!(f, "{num}/{den}"),
            ScalarLit::Fp { value, modulus } => write!(f, "{value} mod {modulus}"),
        }
    }
}

/// 状態座標・操作引数・探索パラメータ上の型付き多項式 / affine 構文木（G-140 P0.1）。
///
/// 未観測値（`Unobserved`）を既知の零定数と型レベルで分離し、
/// 深い平坦和でもスタックを枯渇させないよう `Clone`・`PartialEq`・`Display`・`Drop` を反復実装する。
#[derive(Debug, Eq)]
pub enum PolyExpr {
    Const(ScalarLit),
    /// 現在の phase に属する状態座標変数。
    StateVar(String),
    /// 操作宣言の引数変数。
    ArgVar(String),
    /// 許容変換 H が導入する探索・記号パラメータ変数。
    ParamVar(String),
    /// 未観測の原始値への依存。零へ丸めず欠測位置を保持する。
    Unobserved {
        slot: String,
        origin: Option<SourceRef>,
    },
    Neg(Box<PolyExpr>),
    Add(Box<PolyExpr>, Box<PolyExpr>),
    Sub(Box<PolyExpr>, Box<PolyExpr>),
    Mul(Box<PolyExpr>, Box<PolyExpr>),
    Pow(Box<PolyExpr>, u32),
}

impl PolyExpr {
    pub fn constant(lit: ScalarLit) -> Self {
        PolyExpr::Const(lit)
    }

    pub fn int(n: impl Into<BigInt>) -> Self {
        PolyExpr::Const(ScalarLit::int(n))
    }

    pub fn rat(num: impl Into<BigInt>, den: impl Into<BigInt>) -> Option<Self> {
        ScalarLit::rat(num, den).map(PolyExpr::Const)
    }

    pub fn state(name: impl Into<String>) -> Self {
        PolyExpr::StateVar(name.into())
    }

    pub fn arg(name: impl Into<String>) -> Self {
        PolyExpr::ArgVar(name.into())
    }

    pub fn param(name: impl Into<String>) -> Self {
        PolyExpr::ParamVar(name.into())
    }

    pub fn unobserved(slot: impl Into<String>, origin: Option<SourceRef>) -> Self {
        PolyExpr::Unobserved {
            slot: slot.into(),
            origin,
        }
    }

    pub fn negate(expr: PolyExpr) -> Self {
        PolyExpr::Neg(Box::new(expr))
    }

    pub fn sum(lhs: PolyExpr, rhs: PolyExpr) -> Self {
        PolyExpr::Add(Box::new(lhs), Box::new(rhs))
    }

    pub fn diff(lhs: PolyExpr, rhs: PolyExpr) -> Self {
        PolyExpr::Sub(Box::new(lhs), Box::new(rhs))
    }

    pub fn prod(lhs: PolyExpr, rhs: PolyExpr) -> Self {
        PolyExpr::Mul(Box::new(lhs), Box::new(rhs))
    }

    pub fn pow(base: PolyExpr, exp: u32) -> Self {
        PolyExpr::Pow(Box::new(base), exp)
    }

    /// 式中に現れる未観測 slot 名をすべて収集する（深い木でもスタック安全な反復走査）。
    pub fn collect_unobserved(&self, out: &mut BTreeSet<String>) {
        let mut stack = vec![self];
        while let Some(node) = stack.pop() {
            match node {
                PolyExpr::Unobserved { slot, .. } => {
                    out.insert(slot.clone());
                }
                PolyExpr::Const(_)
                | PolyExpr::StateVar(_)
                | PolyExpr::ArgVar(_)
                | PolyExpr::ParamVar(_) => {}
                PolyExpr::Neg(e) | PolyExpr::Pow(e, _) => stack.push(e),
                PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
            }
        }
    }

    /// 式中の状態変数・引数変数・パラメータ変数の集合を収集する（反復走査）。
    pub fn collect_vars(
        &self,
        states: &mut BTreeSet<String>,
        args: &mut BTreeSet<String>,
        params: &mut BTreeSet<String>,
    ) {
        let mut stack = vec![self];
        while let Some(node) = stack.pop() {
            match node {
                PolyExpr::StateVar(v) => {
                    states.insert(v.clone());
                }
                PolyExpr::ArgVar(v) => {
                    args.insert(v.clone());
                }
                PolyExpr::ParamVar(v) => {
                    params.insert(v.clone());
                }
                PolyExpr::Const(_) | PolyExpr::Unobserved { .. } => {}
                PolyExpr::Neg(e) | PolyExpr::Pow(e, _) => stack.push(e),
                PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
            }
        }
    }

    /// 式中のパラメータ変数（`ParamVar`）のみを収集する（反復走査）。
    pub fn collect_params(&self, params: &mut BTreeSet<String>) {
        let mut stack = vec![self];
        while let Some(node) = stack.pop() {
            match node {
                PolyExpr::ParamVar(v) => {
                    params.insert(v.clone());
                }
                PolyExpr::Const(_)
                | PolyExpr::StateVar(_)
                | PolyExpr::ArgVar(_)
                | PolyExpr::Unobserved { .. } => {}
                PolyExpr::Neg(e) | PolyExpr::Pow(e, _) => stack.push(e),
                PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
            }
        }
    }

    /// 式が状態座標と操作引数について持つ最大次数を返す（パラメータ係数は次数 0、反復走査）。
    /// 未観測値（`Unobserved`）を含む式は次数未確定として `None` を返す。
    ///
    /// G-140 P0.1 の型付き affine term の適用条件検査に用いる。
    pub fn max_state_arg_degree(&self) -> Option<u32> {
        enum DegFrame<'a> {
            Visit(&'a PolyExpr),
            Max2,
            Add2,
            MulConst(u32),
        }
        let mut work = vec![DegFrame::Visit(self)];
        let mut vals: Vec<u32> = Vec::new();
        while let Some(frame) = work.pop() {
            match frame {
                DegFrame::Visit(node) => match node {
                    PolyExpr::Unobserved { .. } => return None,
                    PolyExpr::Const(_) | PolyExpr::ParamVar(_) => vals.push(0),
                    PolyExpr::StateVar(_) | PolyExpr::ArgVar(_) => vals.push(1),
                    PolyExpr::Neg(e) => work.push(DegFrame::Visit(e)),
                    PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) => {
                        work.push(DegFrame::Max2);
                        work.push(DegFrame::Visit(b));
                        work.push(DegFrame::Visit(a));
                    }
                    PolyExpr::Mul(a, b) => {
                        work.push(DegFrame::Add2);
                        work.push(DegFrame::Visit(b));
                        work.push(DegFrame::Visit(a));
                    }
                    PolyExpr::Pow(e, exp) => {
                        work.push(DegFrame::MulConst(*exp));
                        work.push(DegFrame::Visit(e));
                    }
                },
                DegFrame::Max2 => {
                    let b = vals.pop()?;
                    let a = vals.pop()?;
                    vals.push(a.max(b));
                }
                DegFrame::Add2 => {
                    let b = vals.pop()?;
                    let a = vals.pop()?;
                    vals.push(a.saturating_add(b));
                }
                DegFrame::MulConst(exp) => {
                    let a = vals.pop()?;
                    vals.push(a.saturating_mul(exp));
                }
            }
        }
        vals.pop()
    }

    /// 状態座標・操作引数について affine（次数 1 以下）かを返す。
    /// 未観測値を含む場合は `None`（未確定）を返し、affine と誤認定しない。
    pub fn is_affine_in_state_and_args(&self) -> Option<bool> {
        self.max_state_arg_degree().map(|deg| deg <= 1)
    }
}

impl std::ops::Neg for PolyExpr {
    type Output = PolyExpr;
    fn neg(self) -> PolyExpr {
        PolyExpr::negate(self)
    }
}

impl std::ops::Add for PolyExpr {
    type Output = PolyExpr;
    fn add(self, rhs: PolyExpr) -> PolyExpr {
        PolyExpr::sum(self, rhs)
    }
}

impl std::ops::Sub for PolyExpr {
    type Output = PolyExpr;
    fn sub(self, rhs: PolyExpr) -> PolyExpr {
        PolyExpr::diff(self, rhs)
    }
}

impl std::ops::Mul for PolyExpr {
    type Output = PolyExpr;
    fn mul(self, rhs: PolyExpr) -> PolyExpr {
        PolyExpr::prod(self, rhs)
    }
}

impl Drop for PolyExpr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_poly_expr_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_poly_expr_children(&mut node, &mut stack);
        }
    }
}

fn take_poly_expr_children(expr: &mut PolyExpr, stack: &mut Vec<PolyExpr>) {
    let zero = || PolyExpr::Const(ScalarLit::Z(BigInt::from(0)));
    match expr {
        PolyExpr::Neg(a) | PolyExpr::Pow(a, _) => {
            stack.push(std::mem::replace(&mut **a, zero()));
        }
        PolyExpr::Add(a, b) | PolyExpr::Sub(a, b) | PolyExpr::Mul(a, b) => {
            stack.push(std::mem::replace(&mut **a, zero()));
            stack.push(std::mem::replace(&mut **b, zero()));
        }
        PolyExpr::Const(_)
        | PolyExpr::StateVar(_)
        | PolyExpr::ArgVar(_)
        | PolyExpr::ParamVar(_)
        | PolyExpr::Unobserved { .. } => {}
    }
}

impl Clone for PolyExpr {
    fn clone(&self) -> Self {
        enum CloneFrame<'a> {
            Visit(&'a PolyExpr),
            Neg,
            Add,
            Sub,
            Mul,
            Pow(u32),
        }
        let mut work = vec![CloneFrame::Visit(self)];
        let mut out: Vec<PolyExpr> = Vec::new();
        while let Some(frame) = work.pop() {
            match frame {
                CloneFrame::Visit(node) => match node {
                    PolyExpr::Const(c) => out.push(PolyExpr::Const(c.clone())),
                    PolyExpr::StateVar(v) => out.push(PolyExpr::StateVar(v.clone())),
                    PolyExpr::ArgVar(v) => out.push(PolyExpr::ArgVar(v.clone())),
                    PolyExpr::ParamVar(v) => out.push(PolyExpr::ParamVar(v.clone())),
                    PolyExpr::Unobserved { slot, origin } => out.push(PolyExpr::Unobserved {
                        slot: slot.clone(),
                        origin: origin.clone(),
                    }),
                    PolyExpr::Neg(a) => {
                        work.push(CloneFrame::Neg);
                        work.push(CloneFrame::Visit(a));
                    }
                    PolyExpr::Add(a, b) => {
                        work.push(CloneFrame::Add);
                        work.push(CloneFrame::Visit(b));
                        work.push(CloneFrame::Visit(a));
                    }
                    PolyExpr::Sub(a, b) => {
                        work.push(CloneFrame::Sub);
                        work.push(CloneFrame::Visit(b));
                        work.push(CloneFrame::Visit(a));
                    }
                    PolyExpr::Mul(a, b) => {
                        work.push(CloneFrame::Mul);
                        work.push(CloneFrame::Visit(b));
                        work.push(CloneFrame::Visit(a));
                    }
                    PolyExpr::Pow(a, e) => {
                        work.push(CloneFrame::Pow(*e));
                        work.push(CloneFrame::Visit(a));
                    }
                },
                CloneFrame::Neg => {
                    let a = out.pop().expect("clone neg");
                    out.push(PolyExpr::Neg(Box::new(a)));
                }
                CloneFrame::Add => {
                    let b = out.pop().expect("clone add rhs");
                    let a = out.pop().expect("clone add lhs");
                    out.push(PolyExpr::Add(Box::new(a), Box::new(b)));
                }
                CloneFrame::Sub => {
                    let b = out.pop().expect("clone sub rhs");
                    let a = out.pop().expect("clone sub lhs");
                    out.push(PolyExpr::Sub(Box::new(a), Box::new(b)));
                }
                CloneFrame::Mul => {
                    let b = out.pop().expect("clone mul rhs");
                    let a = out.pop().expect("clone mul lhs");
                    out.push(PolyExpr::Mul(Box::new(a), Box::new(b)));
                }
                CloneFrame::Pow(e) => {
                    let a = out.pop().expect("clone pow");
                    out.push(PolyExpr::Pow(Box::new(a), e));
                }
            }
        }
        out.pop().expect("cloned PolyExpr root")
    }
}

impl PartialEq for PolyExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(self, other)];
        while let Some((lhs, rhs)) = stack.pop() {
            match (lhs, rhs) {
                (PolyExpr::Const(a), PolyExpr::Const(b)) => {
                    if a != b {
                        return false;
                    }
                }
                (PolyExpr::StateVar(a), PolyExpr::StateVar(b))
                | (PolyExpr::ArgVar(a), PolyExpr::ArgVar(b))
                | (PolyExpr::ParamVar(a), PolyExpr::ParamVar(b)) => {
                    if a != b {
                        return false;
                    }
                }
                (
                    PolyExpr::Unobserved {
                        slot: s1,
                        origin: o1,
                    },
                    PolyExpr::Unobserved {
                        slot: s2,
                        origin: o2,
                    },
                ) => {
                    if s1 != s2 || o1 != o2 {
                        return false;
                    }
                }
                (PolyExpr::Neg(a), PolyExpr::Neg(b)) => stack.push((a, b)),
                (PolyExpr::Add(a1, a2), PolyExpr::Add(b1, b2))
                | (PolyExpr::Sub(a1, a2), PolyExpr::Sub(b1, b2))
                | (PolyExpr::Mul(a1, a2), PolyExpr::Mul(b1, b2)) => {
                    stack.push((a2, b2));
                    stack.push((a1, b1));
                }
                (PolyExpr::Pow(a, e1), PolyExpr::Pow(b, e2)) => {
                    if e1 != e2 {
                        return false;
                    }
                    stack.push((a, b));
                }
                _ => return false,
            }
        }
        true
    }
}

impl fmt::Display for PolyExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum DispFrame<'a> {
            Expr(&'a PolyExpr),
            Text(&'static str),
            PowSuffix(u32),
        }
        let mut stack = vec![DispFrame::Expr(self)];
        while let Some(frame) = stack.pop() {
            match frame {
                DispFrame::Text(s) => f.write_str(s)?,
                DispFrame::PowSuffix(exp) => write!(f, "^{exp})")?,
                DispFrame::Expr(node) => match node {
                    PolyExpr::Const(c) => write!(f, "{c}")?,
                    PolyExpr::StateVar(v) | PolyExpr::ArgVar(v) | PolyExpr::ParamVar(v) => {
                        f.write_str(v)?;
                    }
                    PolyExpr::Unobserved { slot, .. } => write!(f, "?{slot}")?,
                    PolyExpr::Neg(e) => {
                        stack.push(DispFrame::Text(")"));
                        stack.push(DispFrame::Expr(e));
                        stack.push(DispFrame::Text("(-"));
                    }
                    PolyExpr::Add(a, b) => {
                        stack.push(DispFrame::Text(")"));
                        stack.push(DispFrame::Expr(b));
                        stack.push(DispFrame::Text(" + "));
                        stack.push(DispFrame::Expr(a));
                        stack.push(DispFrame::Text("("));
                    }
                    PolyExpr::Sub(a, b) => {
                        stack.push(DispFrame::Text(")"));
                        stack.push(DispFrame::Expr(b));
                        stack.push(DispFrame::Text(" - "));
                        stack.push(DispFrame::Expr(a));
                        stack.push(DispFrame::Text("("));
                    }
                    PolyExpr::Mul(a, b) => {
                        stack.push(DispFrame::Text(")"));
                        stack.push(DispFrame::Expr(b));
                        stack.push(DispFrame::Text(" * "));
                        stack.push(DispFrame::Expr(a));
                        stack.push(DispFrame::Text("("));
                    }
                    PolyExpr::Pow(e, exp) => {
                        stack.push(DispFrame::PowSuffix(*exp));
                        stack.push(DispFrame::Expr(e));
                        stack.push(DispFrame::Text("("));
                    }
                },
            }
        }
        Ok(())
    }
}
