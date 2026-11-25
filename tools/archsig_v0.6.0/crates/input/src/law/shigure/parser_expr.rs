//! SHIGURE 宣言内の多項式・等式構文解析（`parser.rs` からの責務分割）。

use super::parser::PResult;
use super::*;
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::Zero;

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

impl<E: InputError> Parser<E> {
    /// 等式 `lhs = rhs` を `lhs - rhs`（`rhs` が定数 0 なら `lhs`）として解析する。
    pub(super) fn parse_shigure_equation_poly(&mut self) -> PResult<ShigurePolyExpr, E> {
        let lhs = self.parse_shigure_poly_expr()?;
        self.expect_sym("=")?;
        let rhs = self.parse_shigure_poly_expr()?;
        if matches!(&rhs, ShigurePolyExpr::Int(n) if n.is_zero()) {
            Ok(lhs)
        } else {
            Ok(ShigurePolyExpr::Sub(Box::new(lhs), Box::new(rhs)))
        }
    }

    pub(super) fn parse_shigure_poly_expr(&mut self) -> PResult<ShigurePolyExpr, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let mut acc = self.parse_shigure_poly_term()?;
            loop {
                self.checkpoint_here()?;
                if self.eat_sym("+") {
                    let rhs = self.parse_shigure_poly_term()?;
                    acc = ShigurePolyExpr::Add(Box::new(acc), Box::new(rhs));
                } else if self.eat_sym("-") {
                    let rhs = self.parse_shigure_poly_term()?;
                    acc = ShigurePolyExpr::Sub(Box::new(acc), Box::new(rhs));
                } else {
                    break;
                }
            }
            Ok(acc)
        })
    }

    fn parse_shigure_poly_term(&mut self) -> PResult<ShigurePolyExpr, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            let mut acc = self.parse_shigure_poly_unary()?;
            while self.eat_sym("*") {
                self.checkpoint_here()?;
                let rhs = self.parse_shigure_poly_unary()?;
                acc = ShigurePolyExpr::Mul(Box::new(acc), Box::new(rhs));
            }
            Ok(acc)
        })
    }

    fn parse_shigure_poly_unary(&mut self) -> PResult<ShigurePolyExpr, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            self.checkpoint_here()?;
            if self.eat_sym("-") {
                let inner = self.parse_shigure_poly_unary()?;
                Ok(ShigurePolyExpr::Neg(Box::new(inner)))
            } else {
                self.parse_shigure_poly_primary()
            }
        })
    }

    fn parse_shigure_poly_primary(&mut self) -> PResult<ShigurePolyExpr, E> {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || {
            self.checkpoint_here()?;
            if self.eat_sym("(") {
                let inner = self.parse_shigure_poly_expr()?;
                self.expect_sym(")")?;
                return Ok(inner);
            }
            if let Some(tok) = self.peek().cloned()
                && tok.kind == TokenKind::Int
            {
                self.advance();
                let n = tok.text.parse::<BigInt>().map_err(|_| {
                    Box::new(Issue::law(
                        Code::Syntax,
                        tok.span,
                        "invalid integer literal",
                    ))
                })?;
                return Ok(ShigurePolyExpr::Int(n));
            }
            if self.is_kw("rat") && self.peek_at(1).is_some_and(|t| t.text == "(") {
                let start = self.here().0;
                self.advance();
                self.expect_sym("(")?;
                let neg = self.eat_sym("-");
                let num_raw = self.expect_int_token()?;
                self.expect_sym(",")?;
                let den_raw = self.expect_int_token()?;
                self.expect_sym(")")?;
                let span = (start, self.prev_end());
                let mut num = num_raw.parse::<BigInt>().map_err(|_| {
                    Box::new(Issue::law(Code::Syntax, span, "invalid rational numerator"))
                })?;
                if neg {
                    num = -num;
                }
                let den = den_raw.parse::<BigInt>().map_err(|_| {
                    Box::new(Issue::law(
                        Code::Syntax,
                        span,
                        "invalid rational denominator",
                    ))
                })?;
                if den <= BigInt::zero() {
                    return Err(Box::new(Issue::law(
                        Code::Syntax,
                        span,
                        "rational denominator must be positive",
                    ))
                    .into());
                }
                let g = num.gcd(&den);
                return Ok(ShigurePolyExpr::Rat {
                    num: num / &g,
                    den: den / g,
                });
            }
            if self.is_kw("fp") && self.peek_at(1).is_some_and(|t| t.text == "(") {
                let start = self.here().0;
                self.advance();
                self.expect_sym("(")?;
                let val_raw = self.expect_int_token()?;
                self.expect_sym(",")?;
                let mod_raw = self.expect_int_token()?;
                self.expect_sym(")")?;
                let span = (start, self.prev_end());
                let value = val_raw.parse::<BigUint>().map_err(|_| {
                    Box::new(Issue::law(Code::Syntax, span, "invalid Fp value literal"))
                })?;
                let modulus = mod_raw.parse::<BigUint>().map_err(|_| {
                    Box::new(Issue::law(Code::Syntax, span, "invalid Fp modulus literal"))
                })?;
                return Ok(ShigurePolyExpr::Fp { value, modulus });
            }
            if self.is_kw("pow") && self.peek_at(1).is_some_and(|t| t.text == "(") {
                let start = self.here().0;
                self.advance();
                self.expect_sym("(")?;
                let base = self.parse_shigure_poly_expr()?;
                self.expect_sym(",")?;
                let exp_raw = self.expect_int_token()?;
                self.expect_sym(")")?;
                let span = (start, self.prev_end());
                let exp = exp_raw.parse::<u32>().map_err(|_| {
                    Box::new(Issue::law(
                        Code::Syntax,
                        span,
                        "exponent in `pow` out of range",
                    ))
                })?;
                return Ok(ShigurePolyExpr::Pow(Box::new(base), exp));
            }
            let id = self.ident()?;
            Ok(ShigurePolyExpr::Var(id.name))
        })
    }
}
