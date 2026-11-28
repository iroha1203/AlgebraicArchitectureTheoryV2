//! Phase 4 以降の SHIGURE パーサ共通ヘルパ。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::RawMemberCoordValue;
use super::parser::PResult;
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    pub(super) fn p4_syntax_err<T>(&self, span: Span, msg: &str) -> PResult<T, E> {
        Err(Box::new(Issue::law(Code::Syntax, span, msg)).into())
    }

    pub(super) fn parse_u32_token(&mut self, context: &str) -> PResult<u32, E> {
        let raw = self.expect_int_token()?;
        raw.parse::<u32>().map_err(|_| {
            Box::new(Issue::law(
                Code::Syntax,
                self.prev_span(),
                format!("integer out of u32 range in {context}"),
            ))
            .into()
        })
    }

    pub(super) fn parse_i64_token(&mut self, context: &str) -> PResult<i64, E> {
        let neg = self.eat_sym("-");
        let raw = self.expect_int_token()?;
        let text = if neg { format!("-{raw}") } else { raw };
        text.parse::<i64>().map_err(|_| {
            Box::new(Issue::law(
                Code::Syntax,
                self.prev_span(),
                format!("integer out of i64 range in {context}"),
            ))
            .into()
        })
    }

    pub(super) fn parse_p4_ident_list(&mut self, context: &str) -> PResult<Vec<Ident>, E> {
        let items = self.parse_ident_bracket_list()?;
        for id in &items {
            self.reject_forbidden_ident(id, context)?;
        }
        Ok(items)
    }

    pub(super) fn parse_p4_coord_value(&mut self) -> PResult<RawMemberCoordValue, E> {
        if self.eat_kw("observed") {
            let f_start = self.here().0;
            let field = self.qname()?;
            Ok(RawMemberCoordValue::ObservedField {
                field,
                span: (f_start, self.prev_end()),
            })
        } else if self.eat_kw("missing") {
            Ok(RawMemberCoordValue::Missing(self.prev_span()))
        } else {
            Ok(RawMemberCoordValue::Literal(
                self.parse_shigure_scalar_lit()?,
            ))
        }
    }

    pub(super) fn parse_p4_coord_value_list(&mut self) -> PResult<Vec<RawMemberCoordValue>, E> {
        self.expect_sym("[")?;
        let mut items = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                items.push(self.parse_p4_coord_value()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(items)
    }

    pub(super) fn parse_p4_coord_vec_block(
        &mut self,
        context: &str,
    ) -> PResult<Vec<(Ident, Vec<RawMemberCoordValue>, Span)>, E> {
        self.expect_sym("{")?;
        let mut out = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let a_start = self.here().0;
            self.reject_peek_forbidden(context)?;
            let var = self.ident()?;
            self.reject_forbidden_ident(&var, context)?;
            self.expect_sym("=")?;
            let vals = self.parse_p4_coord_value_list()?;
            self.expect_sym(";")?;
            out.push((var, vals, (a_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(out)
    }

    pub(super) fn parse_p4_coord_scalar_block(
        &mut self,
        context: &str,
    ) -> PResult<Vec<(Ident, RawMemberCoordValue, Span)>, E> {
        self.expect_sym("{")?;
        let mut out = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let a_start = self.here().0;
            self.reject_peek_forbidden(context)?;
            let var = self.ident()?;
            self.reject_forbidden_ident(&var, context)?;
            self.expect_sym("=")?;
            let val = self.parse_p4_coord_value()?;
            self.expect_sym(";")?;
            out.push((var, val, (a_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(out)
    }

    pub(super) fn parse_p4_poly_assign_block(
        &mut self,
        context: &str,
    ) -> PResult<Vec<(Ident, ShigurePolyExpr, Span)>, E> {
        self.expect_sym("{")?;
        let mut out = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let a_start = self.here().0;
            self.reject_peek_forbidden(context)?;
            let var = self.ident()?;
            self.reject_forbidden_ident(&var, context)?;
            self.expect_sym("=")?;
            let expr = self.parse_shigure_poly_expr()?;
            self.expect_sym(";")?;
            out.push((var, expr, (a_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(out)
    }

    pub(super) fn parse_p4_ident_arrow_block(
        &mut self,
        context: &str,
    ) -> PResult<Vec<(Ident, Ident, Span)>, E> {
        self.expect_sym("{")?;
        let mut out = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let a_start = self.here().0;
            self.reject_peek_forbidden(context)?;
            let lhs = self.ident()?;
            self.reject_forbidden_ident(&lhs, context)?;
            self.expect_sym("->")?;
            let rhs = self.ident()?;
            self.reject_forbidden_ident(&rhs, context)?;
            self.expect_sym(";")?;
            out.push((lhs, rhs, (a_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(out)
    }

    pub(super) fn parse_p4_ident_opt_arrow_block(
        &mut self,
        context: &str,
    ) -> PResult<Vec<(Ident, Option<Ident>, Span)>, E> {
        self.expect_sym("{")?;
        let mut out = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let a_start = self.here().0;
            self.reject_peek_forbidden(context)?;
            let lhs = self.ident()?;
            self.reject_forbidden_ident(&lhs, context)?;
            self.expect_sym("->")?;
            let rhs = if self.eat_kw("none") {
                None
            } else {
                let id = self.ident()?;
                self.reject_forbidden_ident(&id, context)?;
                Some(id)
            };
            self.expect_sym(";")?;
            out.push((lhs, rhs, (a_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(out)
    }

    pub(super) fn reject_peek_forbidden(&self, context: &str) -> PResult<(), E> {
        if let Some(t) = self.peek()
            && t.kind == TokenKind::Name
            && is_forbidden_conclusion_field(&t.text)
        {
            self.reject_conclusion_or_unknown(context)?;
        }
        Ok(())
    }

    pub(super) fn parse_lit_matrix(&mut self) -> PResult<Vec<Vec<ShigureScalarLit>>, E> {
        self.expect_sym("[")?;
        let mut rows = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                rows.push(self.parse_shigure_lit_bracket_list()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(rows)
    }

    pub(super) fn parse_lit_tensor3(&mut self) -> PResult<Vec<Vec<Vec<ShigureScalarLit>>>, E> {
        self.expect_sym("[")?;
        let mut mats = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                mats.push(self.parse_lit_matrix()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(mats)
    }
}
