//! `shigure change_spec`・`shigure eval_condition`・`shigure task` 宣言の構文解析
//! （`parser.rs` からの責務分割）。

use super::parser::PResult;
use super::*;
use crate::law::ast::QName;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    pub(super) fn parse_shigure_change_spec(&mut self, start: usize) -> PResult<RawChangeSpec, E> {
        self.expect_kw("change_spec")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut parameters = Vec::new();
        let mut fixed = Vec::new();
        let mut editable = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure change_spec`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("param") {
                let p_start = self.prev_span().0;
                let p_name = self.ident()?;
                self.expect_sym(":")?;
                let p_domain = self.parse_shigure_coeff_domain()?;
                self.expect_sym(";")?;
                parameters.push(RawParamDecl {
                    name: p_name,
                    domain: p_domain,
                    span: (p_start, self.prev_end()),
                });
            } else if self.eat_kw("fixed") {
                let f_start = self.prev_span().0;
                let target = if self.eat_kw("semantic_law") {
                    RawFixedTarget::SemanticLaw(self.qname()?)
                } else if self.eat_kw("representation_law") {
                    RawFixedTarget::RepresentationLaw(self.qname()?)
                } else if self.eat_kw("operation") || self.eat_kw("op") {
                    RawFixedTarget::OperationExpr(self.qname()?)
                } else if self.eat_kw("observation") || self.eat_kw("obs") {
                    RawFixedTarget::ObservationExpr(self.qname()?)
                } else if self.eat_kw("state_comparison") {
                    RawFixedTarget::StateComparisonExpr(self.ident()?)
                } else if self.eat_kw("word_translation") {
                    RawFixedTarget::WordTranslationOp(self.ident()?)
                } else {
                    return self.err(
                        "expected `semantic_law`, `representation_law`, `operation`, `observation`, `state_comparison`, or `word_translation` after `fixed`",
                    );
                };
                self.expect_sym(";")?;
                fixed.push((target, (f_start, self.prev_end())));
            } else if self.eat_kw("editable") {
                let e_start = self.prev_span().0;
                if self.eat_kw("semantic_law") {
                    return Err(Box::new(Issue::law(
                        Code::Type,
                        (e_start, self.prev_end()),
                        "semantic_law cannot be marked editable (semantic laws are protected)",
                    ))
                    .into());
                }
                let target = if self.eat_kw("representation_law") {
                    RawEditableTarget::RepresentationLaw(self.qname()?)
                } else if self.eat_kw("operation") || self.eat_kw("op") {
                    RawEditableTarget::OperationExpr(self.qname()?)
                } else if self.eat_kw("state_comparison") {
                    RawEditableTarget::StateComparisonExpr(self.ident()?)
                } else {
                    return self.err(
                        "expected `representation_law`, `operation`, or `state_comparison` after `editable`",
                    );
                };
                self.expect_sym(";")?;
                editable.push((target, (e_start, self.prev_end())));
            } else {
                self.reject_conclusion_or_unknown("`shigure change_spec`")?;
            }
        }
        self.expect_sym("}")?;
        let Some(domain) = domain else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                (start, self.prev_end()),
                "`shigure change_spec` requires a `domain` clause",
            ))
            .into());
        };
        Ok(RawChangeSpec {
            name,
            domain,
            parameters,
            fixed,
            editable,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_eval_condition(
        &mut self,
        start: usize,
    ) -> PResult<RawEvalCondition, E> {
        self.expect_kw("eval_condition")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut point_domain: Option<RawPointDomain> = None;
        let mut evaluations = Vec::new();
        let mut equations = Vec::new();
        let mut invertibles = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("point_domain") {
                if point_domain.is_some() {
                    return self.err("duplicate `point_domain` clause in `shigure eval_condition`");
                }
                point_domain = Some(self.parse_shigure_point_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("eval") {
                let e_start = self.prev_span().0;
                let e_name = self.ident()?;
                self.expect_sym("=")?;
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                evaluations.push(RawNamedPoly {
                    name: e_name,
                    expr,
                    span: (e_start, self.prev_end()),
                });
            } else if self.eat_kw("equation") {
                let e_start = self.prev_span().0;
                let e_name = self.ident()?;
                self.expect_sym(":")?;
                let expr = self.parse_shigure_equation_poly()?;
                self.expect_sym(";")?;
                equations.push(RawNamedPoly {
                    name: e_name,
                    expr,
                    span: (e_start, self.prev_end()),
                });
            } else if self.eat_kw("invertible") {
                let e_start = self.prev_span().0;
                let e_name = self.ident()?;
                self.expect_sym(":")?;
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                invertibles.push(RawNamedPoly {
                    name: e_name,
                    expr,
                    span: (e_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`shigure eval_condition`")?;
            }
        }
        self.expect_sym("}")?;
        let Some(point_domain) = point_domain else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                (start, self.prev_end()),
                "`shigure eval_condition` requires a `point_domain` clause",
            ))
            .into());
        };
        Ok(RawEvalCondition {
            name,
            point_domain,
            evaluations,
            equations,
            invertibles,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_task(&mut self, start: usize) -> PResult<RawTask, E> {
        self.expect_kw("task")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut comparison: Option<QName> = None;
        let mut change_spec: Option<QName> = None;
        let mut eval_condition: Option<QName> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("comparison") {
                if comparison.is_some() {
                    return self.err("duplicate `comparison` clause in `shigure task`");
                }
                comparison = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("change_spec") {
                if change_spec.is_some() {
                    return self.err("duplicate `change_spec` clause in `shigure task`");
                }
                change_spec = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("eval_condition") {
                if eval_condition.is_some() {
                    return self.err("duplicate `eval_condition` clause in `shigure task`");
                }
                eval_condition = Some(self.qname()?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`shigure task`")?;
            }
        }
        self.expect_sym("}")?;
        let Some(comparison) = comparison else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                (start, self.prev_end()),
                "`shigure task` requires a `comparison` clause",
            ))
            .into());
        };
        let Some(change_spec) = change_spec else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                (start, self.prev_end()),
                "`shigure task` requires a `change_spec` clause",
            ))
            .into());
        };
        Ok(RawTask {
            name,
            comparison,
            change_spec,
            eval_condition,
            span: (start, self.prev_end()),
        })
    }
}
