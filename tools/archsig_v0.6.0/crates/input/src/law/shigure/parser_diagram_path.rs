//! `shigure diagram` および `shigure path` 宣言の構文解析。

use super::ast_ext::*;
use super::parser::PResult;
use super::*;
use crate::law::ast::{Ident, QName, Span};
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::Zero;

#[derive(Default)]
pub(super) struct MorphismBuilder {
    comparison: Option<QName>,
    identity: Option<Span>,
    state_comparisons: Vec<RawStateComparison>,
    word_translation: Vec<RawTranslatedWord>,
}

impl MorphismBuilder {
    pub(super) fn has_comparison(&self) -> bool {
        self.comparison.is_some()
    }

    pub(super) fn try_parse_clause<E: InputError>(
        &mut self,
        p: &mut Parser<E>,
        context: &str,
    ) -> PResult<bool, E> {
        if p.eat_kw("comparison") {
            if self.comparison.is_some() {
                return p.err(format!("duplicate `comparison` clause in {context}"));
            }
            self.comparison = Some(p.qname()?);
            p.expect_sym(";")?;
            return Ok(true);
        }
        if p.eat_kw("identity") {
            let sp = p.prev_span();
            if self.identity.is_some() {
                return p.err(format!("duplicate `identity` clause in {context}"));
            }
            p.expect_sym(";")?;
            self.identity = Some(sp);
            return Ok(true);
        }
        if p.eat_kw("state_map") {
            self.state_comparisons
                .push(p.parse_shigure_state_comparison_after_kw()?);
            return Ok(true);
        }
        if p.eat_kw("translate") {
            self.word_translation
                .push(p.parse_shigure_translated_word_after_kw()?);
            return Ok(true);
        }
        Ok(false)
    }

    pub(super) fn finish<E: InputError>(
        self,
        span: Span,
        context: &str,
    ) -> PResult<Option<RawMorphismBody>, E> {
        let has_inline = !self.state_comparisons.is_empty() || !self.word_translation.is_empty();
        let kinds = usize::from(self.comparison.is_some())
            + usize::from(self.identity.is_some())
            + usize::from(has_inline);
        if kinds > 1 {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                format!(
                    "cannot mix `comparison`, `identity`, and inline `state_map`/`translate` in {context}"
                ),
            ))
            .into());
        }
        if let Some(cmp) = self.comparison {
            return Ok(Some(RawMorphismBody::Comparison(cmp)));
        }
        if let Some(sp) = self.identity {
            return Ok(Some(RawMorphismBody::Identity(sp)));
        }
        if has_inline {
            return Ok(Some(RawMorphismBody::Inline {
                state_comparisons: self.state_comparisons,
                word_translation: self.word_translation,
            }));
        }
        Ok(None)
    }
}

impl<E: InputError> Parser<E> {
    pub(super) fn parse_shigure_direction(&mut self) -> PResult<ShigureDirection, E> {
        if self.eat_kw("state_map") {
            Ok(ShigureDirection::StateMap)
        } else if self.eat_kw("time_order") {
            Ok(ShigureDirection::TimeOrder)
        } else {
            self.err("expected `state_map` or `time_order` after `direction`")
        }
    }

    pub(super) fn parse_ident_bracket_list(&mut self) -> PResult<Vec<Ident>, E> {
        self.expect_sym("[")?;
        let mut items = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                items.push(self.ident()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(items)
    }

    pub(super) fn parse_usize_token(&mut self, context: &str) -> PResult<usize, E> {
        let raw = self.expect_int_token()?;
        raw.parse::<usize>().map_err(|_| {
            Box::new(Issue::law(
                Code::Syntax,
                self.prev_span(),
                format!("integer out of range in {context}"),
            ))
            .into()
        })
    }

    pub(super) fn parse_morphism_block(&mut self, context: &str) -> PResult<RawMorphismBody, E> {
        let b_start = self.here().0;
        self.expect_sym("{")?;
        let mut morph = MorphismBuilder::default();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if !morph.try_parse_clause(self, context)? {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (b_start, self.prev_end());
        morph.finish(span, context)?.ok_or_else(|| {
            Box::new(Issue::law(
                Code::Syntax,
                span,
                format!("{context} requires `comparison`, `identity`, or `state_map`/`translate`"),
            ))
            .into()
        })
    }

    pub(super) fn parse_shigure_scalar_lit(&mut self) -> PResult<ShigureScalarLit, E> {
        let start = self.here().0;
        if self.is_kw("rat") && self.peek_at(1).is_some_and(|t| t.text == "(") {
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
            return Ok(ShigureScalarLit::Rat {
                num: num / &g,
                den: den / g,
            });
        }
        if self.is_kw("fp") && self.peek_at(1).is_some_and(|t| t.text == "(") {
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
            return Ok(ShigureScalarLit::Fp { value, modulus });
        }
        let neg = self.eat_sym("-");
        let int_raw = self.expect_int_token()?;
        let span = (start, self.prev_end());
        let mut n = int_raw
            .parse::<BigInt>()
            .map_err(|_| Box::new(Issue::law(Code::Syntax, span, "invalid integer literal")))?;
        if neg {
            n = -n;
        }
        Ok(ShigureScalarLit::Int(n))
    }

    pub(super) fn parse_shigure_diagram(&mut self, start: usize) -> PResult<RawDiagramTask, E> {
        self.expect_kw("diagram")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut direction: Option<ShigureDirection> = None;
        let mut vertices = Vec::new();
        let mut edges = Vec::new();
        let mut relations = Vec::new();
        let mut change_spec: Option<QName> = None;
        let mut eval_condition: Option<QName> = None;
        let mut edge_eval_conditions = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("direction") {
                if direction.is_some() {
                    return self.err("duplicate `direction` clause in `shigure diagram`");
                }
                direction = Some(self.parse_shigure_direction()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("vertex") {
                let v_start = self.prev_span().0;
                let is_fixed = if self.is_kw("fixed")
                    && self.peek_at(1).is_some_and(|t| t.kind == TokenKind::Name)
                {
                    self.advance();
                    true
                } else {
                    false
                };
                let v_name = self.ident()?;
                self.expect_sym(":")?;
                let presentation = self.qname()?;
                self.expect_sym(";")?;
                vertices.push(RawDiagramVertex {
                    name: v_name,
                    presentation,
                    is_fixed,
                    span: (v_start, self.prev_end()),
                });
            } else if self.eat_kw("edge") {
                let e_start = self.prev_span().0;
                let is_fixed = if self.is_kw("fixed")
                    && self.peek_at(1).is_some_and(|t| t.kind == TokenKind::Name)
                {
                    self.advance();
                    true
                } else {
                    false
                };
                let e_name = self.ident()?;
                self.expect_sym(":")?;
                let source = self.ident()?;
                self.expect_sym("->")?;
                let target = self.ident()?;
                let morphism = self.parse_morphism_block("`shigure diagram` edge")?;
                edges.push(RawDiagramEdge {
                    name: e_name,
                    source,
                    target,
                    is_fixed,
                    morphism,
                    span: (e_start, self.prev_end()),
                });
            } else if self.eat_kw("relation") {
                let r_start = self.prev_span().0;
                let r_name = self.ident()?;
                self.expect_sym(":")?;
                let lhs = self.parse_ident_bracket_list()?;
                self.expect_sym("=")?;
                let rhs = self.parse_ident_bracket_list()?;
                self.expect_sym(";")?;
                relations.push(RawDiagramRelation {
                    name: r_name,
                    lhs,
                    rhs,
                    span: (r_start, self.prev_end()),
                });
            } else if self.eat_kw("change_spec") {
                if change_spec.is_some() {
                    return self.err("duplicate `change_spec` clause in `shigure diagram`");
                }
                change_spec = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("eval_condition") {
                if eval_condition.is_some() {
                    return self.err("duplicate `eval_condition` clause in `shigure diagram`");
                }
                eval_condition = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("edge_eval_condition") {
                let ec_start = self.prev_span().0;
                let edge = self.ident()?;
                self.expect_sym(":")?;
                let ec = self.qname()?;
                self.expect_sym(";")?;
                edge_eval_conditions.push(RawEdgeEvalCondition {
                    edge,
                    eval_condition: ec,
                    span: (ec_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`shigure diagram`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(direction) = direction else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure diagram` requires a `direction` clause",
            ))
            .into());
        };
        let Some(change_spec) = change_spec else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure diagram` requires a `change_spec` clause",
            ))
            .into());
        };
        Ok(RawDiagramTask {
            name,
            direction,
            vertices,
            edges,
            relations,
            change_spec,
            eval_condition,
            edge_eval_conditions,
            span,
        })
    }

    pub(super) fn parse_shigure_path(&mut self, start: usize) -> PResult<RawPathTask, E> {
        self.expect_kw("path")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut kind: Option<ShigurePathKind> = None;
        let mut direction: Option<ShigureDirection> = None;
        let mut query_mode: Option<RawPathQueryMode> = None;
        let mut length: Option<usize> = None;
        let mut vertices = Vec::new();
        let mut rules = Vec::new();
        let mut ep_start: Option<RawModelEndpoint> = None;
        let mut ep_end: Option<RawModelEndpoint> = None;
        let mut protocol: Option<RawProtocolExecution> = None;
        let mut change_spec: Option<QName> = None;
        let mut eval_condition: Option<QName> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("kind") {
                if kind.is_some() {
                    return self.err("duplicate `kind` clause in `shigure path`");
                }
                let k = if self.eat_kw("fixed_protocol_change_path") {
                    ShigurePathKind::FixedProtocolChangePath
                } else if self.eat_kw("enlarged_protocol_execution_path") {
                    ShigurePathKind::EnlargedProtocolExecutionPath
                } else {
                    return self.err(
                        "expected `fixed_protocol_change_path` or `enlarged_protocol_execution_path` after `kind`",
                    );
                };
                kind = Some(k);
                self.expect_sym(";")?;
            } else if self.eat_kw("direction") {
                if direction.is_some() {
                    return self.err("duplicate `direction` clause in `shigure path`");
                }
                direction = Some(self.parse_shigure_direction()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("mode") {
                if query_mode.is_some() {
                    return self.err("duplicate `mode` clause in `shigure path`");
                }
                query_mode = Some(self.parse_path_mode()?);
            } else if self.eat_kw("length") {
                if length.is_some() {
                    return self.err("duplicate `length` clause in `shigure path`");
                }
                length = Some(self.parse_usize_token("`shigure path` length")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("vertex") {
                let v_start = self.prev_span().0;
                let vertex = self.ident()?;
                self.expect_sym(":")?;
                let presentation = self.qname()?;
                self.expect_sym(";")?;
                vertices.push(RawPathVertexBinding {
                    vertex,
                    presentation,
                    span: (v_start, self.prev_end()),
                });
            } else if self.eat_kw("start") {
                if ep_start.is_some() {
                    return self.err("duplicate `start` clause in `shigure path`");
                }
                ep_start = Some(self.parse_model_endpoint(self.prev_span().0)?);
            } else if self.eat_kw("end") {
                if ep_end.is_some() {
                    return self.err("duplicate `end` clause in `shigure path`");
                }
                ep_end = Some(self.parse_model_endpoint(self.prev_span().0)?);
            } else if self.eat_kw("rule") {
                rules.push(self.parse_one_step_rule(self.prev_span().0)?);
            } else if self.eat_kw("protocol") {
                if protocol.is_some() {
                    return self.err("duplicate `protocol` clause in `shigure path`");
                }
                protocol = Some(self.parse_protocol_execution(self.prev_span().0)?);
            } else if self.eat_kw("change_spec") {
                if change_spec.is_some() {
                    return self.err("duplicate `change_spec` clause in `shigure path`");
                }
                change_spec = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("eval_condition") {
                if eval_condition.is_some() {
                    return self.err("duplicate `eval_condition` clause in `shigure path`");
                }
                eval_condition = Some(self.qname()?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`shigure path`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(kind) = kind else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure path` requires a `kind` clause",
            ))
            .into());
        };
        let Some(direction) = direction else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure path` requires a `direction` clause",
            ))
            .into());
        };
        let Some(change_spec) = change_spec else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure path` requires a `change_spec` clause",
            ))
            .into());
        };
        Ok(RawPathTask {
            name,
            kind,
            direction,
            query_mode: query_mode.unwrap_or(RawPathQueryMode::Find),
            length,
            vertices,
            rules,
            start: ep_start,
            end: ep_end,
            protocol,
            change_spec,
            eval_condition,
            span,
        })
    }

    fn parse_path_mode(&mut self) -> PResult<RawPathQueryMode, E> {
        if self.eat_kw("find") {
            self.expect_sym(";")?;
            return Ok(RawPathQueryMode::Find);
        }
        if self.eat_kw("concatenate") {
            self.expect_sym("{")?;
            let mut first: Option<Vec<Ident>> = None;
            let mut second: Option<Vec<Ident>> = None;
            while !self.is_sym("}") {
                self.checkpoint_here()?;
                if self.eat_kw("first") {
                    if first.is_some() {
                        return self.err("duplicate `first` in `mode concatenate`");
                    }
                    first = Some(self.parse_ident_bracket_list()?);
                    self.expect_sym(";")?;
                } else if self.eat_kw("second") {
                    if second.is_some() {
                        return self.err("duplicate `second` in `mode concatenate`");
                    }
                    second = Some(self.parse_ident_bracket_list()?);
                    self.expect_sym(";")?;
                } else {
                    self.reject_conclusion_or_unknown("`mode concatenate`")?;
                }
            }
            self.expect_sym("}")?;
            let Some(first) = first else {
                return self.err("`mode concatenate` requires a `first` list");
            };
            let Some(second) = second else {
                return self.err("`mode concatenate` requires a `second` list");
            };
            return Ok(RawPathQueryMode::Concatenate { first, second });
        }
        if self.eat_kw("subdivide") {
            let target_edge = self.parse_morphism_block("`mode subdivide`")?;
            return Ok(RawPathQueryMode::Subdivide { target_edge });
        }
        self.err("expected `find`, `concatenate`, or `subdivide` after `mode`")
    }

    fn parse_model_endpoint(&mut self, start: usize) -> PResult<RawModelEndpoint, E> {
        let vertex = self.ident()?;
        let mut param_values = Vec::new();
        if self.eat_sym("{") {
            while !self.is_sym("}") {
                self.checkpoint_here()?;
                if let Some(t) = self.peek()
                    && t.kind == TokenKind::Name
                    && is_forbidden_conclusion_field(&t.text)
                {
                    self.reject_conclusion_or_unknown("path endpoint")?;
                }
                let p_start = self.here().0;
                let p_name = self.ident()?;
                self.expect_sym("=")?;
                let lit = self.parse_shigure_scalar_lit()?;
                self.expect_sym(";")?;
                param_values.push((p_name, lit, (p_start, self.prev_end())));
            }
            self.expect_sym("}")?;
        } else {
            self.expect_sym(";")?;
        }
        Ok(RawModelEndpoint {
            vertex,
            param_values,
            span: (start, self.prev_end()),
        })
    }

    fn parse_one_step_rule(&mut self, start: usize) -> PResult<RawOneStepRule, E> {
        let name = self.ident()?;
        self.expect_sym(":")?;
        let from_vertex = self.ident()?;
        self.expect_sym("->")?;
        let to_vertex = self.ident()?;
        self.expect_sym("{")?;
        let mut param_guards = Vec::new();
        let mut param_updates = Vec::new();
        let mut eval_condition: Option<QName> = None;
        let mut morph = MorphismBuilder::default();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("guard") {
                let g_start = self.prev_span().0;
                let g_name = self.ident()?;
                self.expect_sym(":")?;
                let expr = self.parse_shigure_equation_poly()?;
                self.expect_sym(";")?;
                param_guards.push((g_name, expr, (g_start, self.prev_end())));
            } else if self.eat_kw("update") {
                let u_start = self.prev_span().0;
                let p_name = self.ident()?;
                self.expect_sym("=")?;
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                param_updates.push((p_name, expr, (u_start, self.prev_end())));
            } else if self.eat_kw("eval_condition") {
                if eval_condition.is_some() {
                    return self.err("duplicate `eval_condition` clause in `rule`");
                }
                eval_condition = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if !morph.try_parse_clause(self, "`rule`")? {
                self.reject_conclusion_or_unknown("`rule`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(morphism) = morph.finish(span, "`rule`")? else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`rule` requires `comparison`, `identity`, or `state_map`/`translate`",
            ))
            .into());
        };
        Ok(RawOneStepRule {
            name,
            from_vertex,
            to_vertex,
            param_guards,
            param_updates,
            morphism,
            eval_condition,
            span,
        })
    }

    fn parse_protocol_execution(&mut self, start: usize) -> PResult<RawProtocolExecution, E> {
        self.expect_sym("{")?;
        let mut comparison: Option<QName> = None;
        let mut start_phase: Option<Ident> = None;
        let mut start_laws = Vec::new();
        let mut end_phase: Option<Ident> = None;
        let mut end_laws = Vec::new();
        let mut allowed_ops: Option<Vec<Ident>> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("comparison") {
                if comparison.is_some() {
                    return self.err("duplicate `comparison` in `protocol`");
                }
                comparison = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("start_phase") {
                if start_phase.is_some() {
                    return self.err("duplicate `start_phase` in `protocol`");
                }
                start_phase = Some(self.ident()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("start_law") {
                start_laws.push(self.parse_shigure_law_decl_after_kw("`start_law`")?);
            } else if self.eat_kw("end_phase") {
                if end_phase.is_some() {
                    return self.err("duplicate `end_phase` in `protocol`");
                }
                end_phase = Some(self.ident()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("end_law") {
                end_laws.push(self.parse_shigure_law_decl_after_kw("`end_law`")?);
            } else if self.eat_kw("allowed_ops") {
                if allowed_ops.is_some() {
                    return self.err("duplicate `allowed_ops` in `protocol`");
                }
                allowed_ops = Some(self.parse_ident_bracket_list()?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`protocol`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(comparison) = comparison else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`protocol` requires a `comparison` clause",
            ))
            .into());
        };
        let Some(start_phase) = start_phase else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`protocol` requires a `start_phase` clause",
            ))
            .into());
        };
        let Some(end_phase) = end_phase else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`protocol` requires an `end_phase` clause",
            ))
            .into());
        };
        let Some(allowed_ops) = allowed_ops else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`protocol` requires an `allowed_ops` clause",
            ))
            .into());
        };
        Ok(RawProtocolExecution {
            comparison,
            start_phase,
            start_laws,
            end_phase,
            end_laws,
            allowed_ops,
            span,
        })
    }
}
