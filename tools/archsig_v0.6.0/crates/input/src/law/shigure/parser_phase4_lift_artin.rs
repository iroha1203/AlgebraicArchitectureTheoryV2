//! `shigure lift`・`shigure artin` 宣言の構文解析と Phase 4 共通パーサヘルパ（AC2）。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::RawMemberCoordValue;
use super::ast_phase4_lift_artin::*;
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

    fn parse_lit_matrix(&mut self) -> PResult<Vec<Vec<ShigureScalarLit>>, E> {
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

    fn parse_lit_tensor3(&mut self) -> PResult<Vec<Vec<Vec<ShigureScalarLit>>>, E> {
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

    // ---- `shigure lift` ----

    pub(super) fn parse_shigure_lift(&mut self, start: usize) -> PResult<RawLiftTask, E> {
        self.expect_kw("lift")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`shigure lift`")?;
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut origins = Vec::new();
        let mut variables: Option<Vec<Ident>> = None;
        let mut ring_params = Vec::new();
        let mut laws = Vec::new();
        let mut extension: Option<RawSquareZeroSpec> = None;
        let mut base_point: Option<Vec<(Ident, Vec<RawMemberCoordValue>, Span)>> = None;
        let mut ambient_lift: Option<Vec<(Ident, Vec<RawMemberCoordValue>, Span)>> = None;
        let mut relative_reading: Option<RawRelativeReading> = None;
        let mut declaration_cover: Option<RawDeclarationCover> = None;
        let mut affine_allowed: Option<RawAffineAllowed> = None;
        let mut redundant_comparison: Option<RawRedundantComparison> = None;
        let mut etale_descent: Option<RawFiniteEtaleDescent> = None;
        let mut max_syzygy_pairs: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure lift`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin("`shigure lift`")?);
            } else if self.eat_kw("vars") {
                if variables.is_some() {
                    return self.err("duplicate `vars` clause in `shigure lift`");
                }
                let list = self.parse_p4_ident_list("`shigure lift` vars")?;
                self.expect_sym(";")?;
                variables = Some(list);
            } else if self.eat_kw("ring_param") {
                let rp_start = self.prev_span().0;
                let rp_name = self.ident()?;
                self.reject_forbidden_ident(&rp_name, "`shigure lift` ring_param")?;
                self.expect_sym("=")?;
                let vals = self.parse_p4_coord_value_list()?;
                self.expect_sym(";")?;
                ring_params.push(RawRingParam {
                    name: rp_name,
                    value_in_r_prime: vals,
                    span: (rp_start, self.prev_end()),
                });
            } else if self.eat_kw("law") {
                laws.push(self.parse_shigure_named_eq("`shigure lift` law")?);
            } else if self.eat_kw("extension") {
                if extension.is_some() {
                    return self.err("duplicate `extension` clause in `shigure lift`");
                }
                extension = Some(self.parse_square_zero_spec(self.prev_span().0)?);
            } else if self.eat_kw("base_point") {
                if base_point.is_some() {
                    return self.err("duplicate `base_point` block in `shigure lift`");
                }
                base_point = Some(self.parse_p4_coord_vec_block("`shigure lift` base_point")?);
            } else if self.eat_kw("ambient_lift") {
                if ambient_lift.is_some() {
                    return self.err("duplicate `ambient_lift` block in `shigure lift`");
                }
                ambient_lift = Some(self.parse_p4_coord_vec_block("`shigure lift` ambient_lift")?);
            } else if self.eat_kw("relative_reading") {
                if relative_reading.is_some() {
                    return self.err("duplicate `relative_reading` block in `shigure lift`");
                }
                relative_reading = Some(self.parse_relative_reading(self.prev_span().0)?);
            } else if self.eat_kw("declaration_cover") {
                if declaration_cover.is_some() {
                    return self.err("duplicate `declaration_cover` block in `shigure lift`");
                }
                declaration_cover = Some(self.parse_declaration_cover(self.prev_span().0)?);
            } else if self.eat_kw("affine_allowed") {
                if affine_allowed.is_some() {
                    return self.err("duplicate `affine_allowed` block in `shigure lift`");
                }
                affine_allowed = Some(self.parse_affine_allowed(self.prev_span().0)?);
            } else if self.eat_kw("redundant_comparison") {
                if redundant_comparison.is_some() {
                    return self.err("duplicate `redundant_comparison` block in `shigure lift`");
                }
                redundant_comparison = Some(self.parse_redundant_comparison(self.prev_span().0)?);
            } else if self.eat_kw("etale_descent") {
                if etale_descent.is_some() {
                    return self.err("duplicate `etale_descent` block in `shigure lift`");
                }
                etale_descent = Some(self.parse_etale_descent(self.prev_span().0)?);
            } else if self.eat_kw("max_syzygy_pairs") {
                if max_syzygy_pairs.is_some() {
                    return self.err("duplicate `max_syzygy_pairs` clause in `shigure lift`");
                }
                let n = self.parse_usize_token("`max_syzygy_pairs`")?;
                self.expect_sym(";")?;
                max_syzygy_pairs = Some(n);
            } else {
                self.reject_conclusion_or_unknown("`shigure lift`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(domain) = domain else {
            return self.p4_syntax_err(span, "`shigure lift` requires a `domain` clause");
        };
        if origins.is_empty() {
            return self.p4_syntax_err(span, "`shigure lift` requires at least one `origin` clause");
        }
        let Some(variables) = variables else {
            return self.p4_syntax_err(span, "`shigure lift` requires a `vars` clause");
        };
        let Some(extension) = extension else {
            return self.p4_syntax_err(span, "`shigure lift` requires an `extension` clause");
        };
        let Some(base_point) = base_point else {
            return self.p4_syntax_err(span, "`shigure lift` requires a `base_point` block");
        };
        Ok(RawLiftTask {
            name,
            domain,
            origins,
            variables,
            ring_params,
            laws,
            extension,
            base_point,
            ambient_lift,
            relative_reading,
            declaration_cover,
            affine_allowed,
            redundant_comparison,
            etale_descent,
            max_syzygy_pairs,
            span,
        })
    }

    fn parse_square_zero_spec(&mut self, start: usize) -> PResult<RawSquareZeroSpec, E> {
        if self.eat_kw("truncated") {
            self.expect_sym("(")?;
            let var_name = self.ident()?;
            self.reject_forbidden_ident(&var_name, "`extension truncated`")?;
            self.expect_sym(",")?;
            let base_degree = self.parse_usize_token("`extension truncated`")?;
            self.expect_sym(")")?;
            self.expect_sym(";")?;
            return Ok(RawSquareZeroSpec::TruncatedPoly {
                var_name,
                base_degree,
                span: (start, self.prev_end()),
            });
        }
        if self.eat_kw("explicit_table") {
            self.expect_sym("{")?;
            let mut r_prime_basis = None;
            let mut r_prime_one = None;
            let mut r_prime_mul = None;
            let mut r_base_basis = None;
            let mut r_base_one = None;
            let mut r_base_mul = None;
            let mut projection = None;
            while !self.is_sym("}") {
                self.checkpoint_here()?;
                if self.eat_kw("r_prime_basis") {
                    if r_prime_basis.is_some() {
                        return self.err("duplicate `r_prime_basis` in `explicit_table`");
                    }
                    r_prime_basis = Some(self.parse_p4_ident_list("`explicit_table`")?);
                    self.expect_sym(";")?;
                } else if self.eat_kw("r_prime_one") {
                    if r_prime_one.is_some() {
                        return self.err("duplicate `r_prime_one` in `explicit_table`");
                    }
                    r_prime_one = Some(self.parse_shigure_lit_bracket_list()?);
                    self.expect_sym(";")?;
                } else if self.eat_kw("r_prime_mul") {
                    if r_prime_mul.is_some() {
                        return self.err("duplicate `r_prime_mul` in `explicit_table`");
                    }
                    r_prime_mul = Some(self.parse_lit_tensor3()?);
                    self.expect_sym(";")?;
                } else if self.eat_kw("r_base_basis") {
                    if r_base_basis.is_some() {
                        return self.err("duplicate `r_base_basis` in `explicit_table`");
                    }
                    r_base_basis = Some(self.parse_p4_ident_list("`explicit_table`")?);
                    self.expect_sym(";")?;
                } else if self.eat_kw("r_base_one") {
                    if r_base_one.is_some() {
                        return self.err("duplicate `r_base_one` in `explicit_table`");
                    }
                    r_base_one = Some(self.parse_shigure_lit_bracket_list()?);
                    self.expect_sym(";")?;
                } else if self.eat_kw("r_base_mul") {
                    if r_base_mul.is_some() {
                        return self.err("duplicate `r_base_mul` in `explicit_table`");
                    }
                    r_base_mul = Some(self.parse_lit_tensor3()?);
                    self.expect_sym(";")?;
                } else if self.eat_kw("projection") {
                    if projection.is_some() {
                        return self.err("duplicate `projection` in `explicit_table`");
                    }
                    projection = Some(self.parse_lit_matrix()?);
                    self.expect_sym(";")?;
                } else {
                    self.reject_conclusion_or_unknown("`extension explicit_table`")?;
                }
            }
            self.expect_sym("}")?;
            let span = (start, self.prev_end());
            let (Some(rpb), Some(rpo), Some(rpm), Some(rbb), Some(rbo), Some(rbm), Some(proj)) = (
                r_prime_basis,
                r_prime_one,
                r_prime_mul,
                r_base_basis,
                r_base_one,
                r_base_mul,
                projection,
            ) else {
                return self.p4_syntax_err(
                    span,
                    "`extension explicit_table` requires all of `r_prime_basis`, `r_prime_one`, `r_prime_mul`, `r_base_basis`, `r_base_one`, `r_base_mul`, and `projection`",
                );
            };
            return Ok(RawSquareZeroSpec::ExplicitTable {
                r_prime_basis: rpb,
                r_prime_one: rpo,
                r_prime_mul: rpm,
                r_base_basis: rbb,
                r_base_one: rbo,
                r_base_mul: rbm,
                projection: proj,
                span,
            });
        }
        self.err("expected `truncated(<var>, <base_degree>);` or `explicit_table { ... }` after `extension`")
    }

    fn parse_relative_reading(&mut self, start: usize) -> PResult<RawRelativeReading, E> {
        self.expect_sym("{")?;
        let mut obs_vars: Option<Vec<Ident>> = None;
        let mut obs_laws = Vec::new();
        let mut reading_map: Option<Vec<(Ident, ShigurePolyExpr, Span)>> = None;
        let mut designated_obs_lift: Option<Vec<(Ident, Vec<RawMemberCoordValue>, Span)>> = None;
        let mut raw_read_diff: Option<RawReadComparisonAst> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("obs_vars") {
                if obs_vars.is_some() {
                    return self.err("duplicate `obs_vars` in `relative_reading`");
                }
                let list = self.parse_p4_ident_list("`relative_reading` obs_vars")?;
                self.expect_sym(";")?;
                obs_vars = Some(list);
            } else if self.eat_kw("obs_law") {
                obs_laws.push(self.parse_shigure_named_eq("`relative_reading` obs_law")?);
            } else if self.eat_kw("reading_map") {
                if reading_map.is_some() {
                    return self.err("duplicate `reading_map` in `relative_reading`");
                }
                reading_map = Some(self.parse_p4_poly_assign_block("`relative_reading` reading_map")?);
            } else if self.eat_kw("designated_obs_lift") {
                if designated_obs_lift.is_some() {
                    return self.err("duplicate `designated_obs_lift` in `relative_reading`");
                }
                designated_obs_lift =
                    Some(self.parse_p4_coord_vec_block("`relative_reading` designated_obs_lift")?);
            } else if self.eat_kw("raw_read_diff") {
                if raw_read_diff.is_some() {
                    return self.err("duplicate `raw_read_diff` in `relative_reading`");
                }
                let rr_start = self.prev_span().0;
                let label = self.string()?;
                let negated = if self.eat_kw("negated") {
                    true
                } else if self.eat_kw("same_sign") {
                    false
                } else {
                    return self.err("expected `negated` or `same_sign` in `raw_read_diff`");
                };
                self.expect_sym(":")?;
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                raw_read_diff = Some(RawReadComparisonAst {
                    label,
                    expr,
                    negated,
                    span: (rr_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`relative_reading`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(obs_vars) = obs_vars else {
            return self.p4_syntax_err(span, "`relative_reading` requires `obs_vars`");
        };
        let Some(reading_map) = reading_map else {
            return self.p4_syntax_err(span, "`relative_reading` requires `reading_map`");
        };
        let Some(designated_obs_lift) = designated_obs_lift else {
            return self.p4_syntax_err(span, "`relative_reading` requires `designated_obs_lift`");
        };
        Ok(RawRelativeReading {
            obs_vars,
            obs_laws,
            reading_map,
            designated_obs_lift,
            raw_read_diff,
            span,
        })
    }

    fn parse_declaration_cover(&mut self, start: usize) -> PResult<RawDeclarationCover, E> {
        self.expect_sym("{")?;
        let mut contexts = Vec::new();
        let mut two_context_cech = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("context") {
                let c_start = self.prev_span().0;
                let c_name = self.ident()?;
                self.reject_forbidden_ident(&c_name, "`declaration_cover` context")?;
                self.expect_sym("{")?;
                let mut vars = Vec::new();
                let mut laws = Vec::new();
                let mut observations = Vec::new();
                let mut seen_vars = false;
                let mut seen_laws = false;
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if self.eat_kw("vars") {
                        if seen_vars {
                            return self.err("duplicate `vars` in `declaration_cover` context");
                        }
                        vars = self.parse_p4_ident_list("`declaration_cover` context vars")?;
                        self.expect_sym(";")?;
                        seen_vars = true;
                    } else if self.eat_kw("laws") {
                        if seen_laws {
                            return self.err("duplicate `laws` in `declaration_cover` context");
                        }
                        laws = self.parse_p4_ident_list("`declaration_cover` context laws")?;
                        self.expect_sym(";")?;
                        seen_laws = true;
                    } else if self.eat_kw("obs") {
                        observations.push(self.parse_shigure_named_poly("`declaration_cover` obs")?);
                    } else {
                        self.reject_conclusion_or_unknown("`declaration_cover` context")?;
                    }
                }
                self.expect_sym("}")?;
                contexts.push(RawDeclarationContext {
                    name: c_name,
                    vars,
                    laws,
                    observations,
                    span: (c_start, self.prev_end()),
                });
            } else if self.eat_kw("two_context_cech") {
                if two_context_cech.is_some() {
                    return self.err("duplicate `two_context_cech` in `declaration_cover`");
                }
                let tc_start = self.prev_span().0;
                self.expect_sym("{")?;
                let mut left_context = None;
                let mut right_context = None;
                let mut shared_vars = None;
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if self.eat_kw("left") {
                        if left_context.is_some() {
                            return self.err("duplicate `left` in `two_context_cech`");
                        }
                        left_context = Some(self.ident()?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("right") {
                        if right_context.is_some() {
                            return self.err("duplicate `right` in `two_context_cech`");
                        }
                        right_context = Some(self.ident()?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("shared_vars") {
                        if shared_vars.is_some() {
                            return self.err("duplicate `shared_vars` in `two_context_cech`");
                        }
                        shared_vars = Some(self.parse_p4_ident_list("`two_context_cech`")?);
                        self.expect_sym(";")?;
                    } else {
                        self.reject_conclusion_or_unknown("`two_context_cech`")?;
                    }
                }
                self.expect_sym("}")?;
                let tc_span = (tc_start, self.prev_end());
                let (Some(left_context), Some(right_context), Some(shared_vars)) =
                    (left_context, right_context, shared_vars)
                else {
                    return self.p4_syntax_err(
                        tc_span,
                        "`two_context_cech` requires `left`, `right`, and `shared_vars`",
                    );
                };
                two_context_cech = Some(RawTwoContextCech {
                    left_context,
                    right_context,
                    shared_vars,
                    span: tc_span,
                });
            } else {
                self.reject_conclusion_or_unknown("`declaration_cover`")?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawDeclarationCover {
            contexts,
            two_context_cech,
            span: (start, self.prev_end()),
        })
    }

    fn parse_affine_allowed(&mut self, start: usize) -> PResult<RawAffineAllowed, E> {
        self.expect_sym("{")?;
        let mut allowed_vars = None;
        let mut finite_displacement = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("allowed_vars") {
                if allowed_vars.is_some() {
                    return self.err("duplicate `allowed_vars` in `affine_allowed`");
                }
                allowed_vars = Some(self.parse_p4_ident_list("`affine_allowed`")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("finite_displacement") {
                if finite_displacement.is_some() {
                    return self.err("duplicate `finite_displacement` in `affine_allowed`");
                }
                finite_displacement = Some(self.parse_shigure_bool("`affine_allowed`")?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`affine_allowed`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(allowed_vars) = allowed_vars else {
            return self.p4_syntax_err(span, "`affine_allowed` requires `allowed_vars`");
        };
        Ok(RawAffineAllowed {
            allowed_vars,
            finite_displacement: finite_displacement.unwrap_or(false),
            span,
        })
    }

    fn parse_redundant_comparison(&mut self, start: usize) -> PResult<RawRedundantComparison, E> {
        self.expect_sym("{")?;
        let mut reference_laws = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("ref_law") {
                reference_laws.push(self.parse_shigure_named_eq("`redundant_comparison` ref_law")?);
            } else {
                self.reject_conclusion_or_unknown("`redundant_comparison`")?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawRedundantComparison {
            reference_laws,
            span: (start, self.prev_end()),
        })
    }

    fn parse_etale_descent(&mut self, start: usize) -> PResult<RawFiniteEtaleDescent, E> {
        self.expect_sym("{")?;
        let mut base_var = None;
        let mut cover_var = None;
        let mut degree = None;
        let mut base_invertible = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("base_var") {
                if base_var.is_some() {
                    return self.err("duplicate `base_var` in `etale_descent`");
                }
                let id = self.ident()?;
                self.reject_forbidden_ident(&id, "`etale_descent`")?;
                self.expect_sym(";")?;
                base_var = Some(id);
            } else if self.eat_kw("cover_var") {
                if cover_var.is_some() {
                    return self.err("duplicate `cover_var` in `etale_descent`");
                }
                let id = self.ident()?;
                self.reject_forbidden_ident(&id, "`etale_descent`")?;
                self.expect_sym(";")?;
                cover_var = Some(id);
            } else if self.eat_kw("degree") {
                if degree.is_some() {
                    return self.err("duplicate `degree` in `etale_descent`");
                }
                let d = self.parse_u32_token("`etale_descent` degree")?;
                self.expect_sym(";")?;
                degree = Some(d);
            } else if self.eat_kw("base_invertible") {
                if base_invertible.is_some() {
                    return self.err("duplicate `base_invertible` in `etale_descent`");
                }
                let flag = self.parse_shigure_bool("`etale_descent`")?;
                self.expect_sym(";")?;
                base_invertible = Some(flag);
            } else {
                self.reject_conclusion_or_unknown("`etale_descent`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(base_var), Some(cover_var), Some(degree)) = (base_var, cover_var, degree) else {
            return self.p4_syntax_err(
                span,
                "`etale_descent` requires `base_var`, `cover_var`, and `degree`",
            );
        };
        Ok(RawFiniteEtaleDescent {
            base_var,
            cover_var,
            degree,
            base_invertible: base_invertible.unwrap_or(true),
            span,
        })
    }

    // ---- `shigure artin` ----

    fn parse_aux_def(&mut self, context: &str) -> PResult<RawAuxiliaryDef, E> {
        let a_start = self.prev_span().0;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym("=")?;
        let expr = self.parse_shigure_poly_expr()?;
        self.expect_sym(";")?;
        Ok(RawAuxiliaryDef {
            name,
            expr,
            span: (a_start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_artin(&mut self, start: usize) -> PResult<RawArtinTask, E> {
        self.expect_kw("artin")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`shigure artin`")?;
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut origins = Vec::new();
        let mut obs_vars: Option<Vec<Ident>> = None;
        let mut obs_relations = Vec::new();
        let mut aux_defs = Vec::new();
        let mut extra_laws = Vec::new();
        let mut base_point: Option<Vec<(Ident, RawMemberCoordValue, Span)>> = None;
        let mut max_order: Option<usize> = None;
        let mut max_artin_dim: Option<usize> = None;
        let mut composite_stage: Option<RawCompositeStage> = None;
        let mut base_change: Option<RawArtinBaseChange> = None;
        let mut non_noetherian_infinite: Option<bool> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure artin`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin("`shigure artin`")?);
            } else if self.eat_kw("obs_vars") {
                if obs_vars.is_some() {
                    return self.err("duplicate `obs_vars` clause in `shigure artin`");
                }
                obs_vars = Some(self.parse_p4_ident_list("`shigure artin` obs_vars")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("obs_relation") {
                obs_relations.push(self.parse_shigure_named_eq("`shigure artin` obs_relation")?);
            } else if self.eat_kw("aux_def") {
                aux_defs.push(self.parse_aux_def("`shigure artin` aux_def")?);
            } else if self.eat_kw("extra_law") {
                extra_laws.push(self.parse_shigure_named_eq("`shigure artin` extra_law")?);
            } else if self.eat_kw("base_point") {
                if base_point.is_some() {
                    return self.err("duplicate `base_point` block in `shigure artin`");
                }
                base_point = Some(self.parse_p4_coord_scalar_block("`shigure artin` base_point")?);
            } else if self.eat_kw("max_order") {
                if max_order.is_some() {
                    return self.err("duplicate `max_order` clause in `shigure artin`");
                }
                let n = self.parse_usize_token("`max_order`")?;
                self.expect_sym(";")?;
                max_order = Some(n);
            } else if self.eat_kw("max_artin_dim") {
                if max_artin_dim.is_some() {
                    return self.err("duplicate `max_artin_dim` clause in `shigure artin`");
                }
                let n = self.parse_usize_token("`max_artin_dim`")?;
                self.expect_sym(";")?;
                max_artin_dim = Some(n);
            } else if self.eat_kw("composite_stage") {
                if composite_stage.is_some() {
                    return self.err("duplicate `composite_stage` block in `shigure artin`");
                }
                let cs_start = self.prev_span().0;
                self.expect_sym("{")?;
                let mut c_aux = Vec::new();
                let mut c_laws = Vec::new();
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if self.eat_kw("aux_def") {
                        c_aux.push(self.parse_aux_def("`composite_stage` aux_def")?);
                    } else if self.eat_kw("extra_law") {
                        c_laws.push(self.parse_shigure_named_eq("`composite_stage` extra_law")?);
                    } else {
                        self.reject_conclusion_or_unknown("`composite_stage`")?;
                    }
                }
                self.expect_sym("}")?;
                composite_stage = Some(RawCompositeStage {
                    aux_defs: c_aux,
                    extra_laws: c_laws,
                    span: (cs_start, self.prev_end()),
                });
            } else if self.eat_kw("base_change") {
                if base_change.is_some() {
                    return self.err("duplicate `base_change` block in `shigure artin`");
                }
                let bc_start = self.prev_span().0;
                self.expect_sym("{")?;
                let mut target_domain = None;
                let mut test_order = None;
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if self.eat_kw("target_domain") {
                        if target_domain.is_some() {
                            return self.err("duplicate `target_domain` in `base_change`");
                        }
                        target_domain = Some(self.parse_shigure_coeff_domain()?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("test_order") {
                        if test_order.is_some() {
                            return self.err("duplicate `test_order` in `base_change`");
                        }
                        let n = self.parse_usize_token("`test_order`")?;
                        self.expect_sym(";")?;
                        test_order = Some(n);
                    } else {
                        self.reject_conclusion_or_unknown("`base_change`")?;
                    }
                }
                self.expect_sym("}")?;
                let bc_span = (bc_start, self.prev_end());
                let Some(target_domain) = target_domain else {
                    return self.p4_syntax_err(bc_span, "`base_change` requires `target_domain`");
                };
                base_change = Some(RawArtinBaseChange {
                    target_domain,
                    test_order,
                    span: bc_span,
                });
            } else if self.eat_kw("non_noetherian_infinite") {
                if non_noetherian_infinite.is_some() {
                    return self.err("duplicate `non_noetherian_infinite` in `shigure artin`");
                }
                let flag = self.parse_shigure_bool("`shigure artin`")?;
                self.expect_sym(";")?;
                non_noetherian_infinite = Some(flag);
            } else {
                self.reject_conclusion_or_unknown("`shigure artin`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(domain) = domain else {
            return self.p4_syntax_err(span, "`shigure artin` requires a `domain` clause");
        };
        if origins.is_empty() {
            return self.p4_syntax_err(span, "`shigure artin` requires at least one `origin` clause");
        }
        let Some(obs_vars) = obs_vars else {
            return self.p4_syntax_err(span, "`shigure artin` requires an `obs_vars` clause");
        };
        let Some(base_point) = base_point else {
            return self.p4_syntax_err(span, "`shigure artin` requires a `base_point` block");
        };
        let Some(max_order) = max_order else {
            return self.p4_syntax_err(span, "`shigure artin` requires a `max_order` clause");
        };
        Ok(RawArtinTask {
            name,
            domain,
            origins,
            obs_vars,
            obs_relations,
            aux_defs,
            extra_laws,
            base_point,
            max_order,
            max_artin_dim,
            composite_stage,
            base_change,
            non_noetherian_infinite: non_noetherian_infinite.unwrap_or(false),
            span,
        })
    }
}
