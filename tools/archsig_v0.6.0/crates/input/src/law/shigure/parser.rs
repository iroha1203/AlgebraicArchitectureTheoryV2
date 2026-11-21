//! `archsig.law/2` 内の `shigure` 宣言群の構文解析。
//!
//! 既存の `law/parser.rs` を肥大化させず、文脈キーワード `shigure` に続く
//! `presentation` / `comparison` / `change_spec` / `eval_condition` / `task` だけを解析する。

use super::*;
use crate::law::ast::QName;
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::Zero;

const RED_ZONE: usize = 128 * 1024;
const STACK_STEP: usize = 4 * 1024 * 1024;

type PResult<T, E> = Result<T, E>;

impl<E: InputError> Parser<E> {
    /// `shigure <kind> <Name> { ... }` を解析する（`shigure` は未消費）。
    pub(crate) fn parse_shigure_decl(&mut self) -> PResult<ShigureDeclAst, E> {
        let start = self.here().0;
        self.expect_kw("shigure")?;
        let Some(tok) = self.peek().cloned() else {
            return self.err(
                "expected `presentation`, `comparison`, `change_spec`, `eval_condition`, or `task` after `shigure`",
            );
        };
        if tok.kind != TokenKind::Name {
            return self.err("expected SHIGURE declaration kind after `shigure`");
        }
        if is_forbidden_conclusion_field(&tok.text) {
            return self.err(format!(
                "conclusion injection is forbidden: `{}` cannot be declared in Law input",
                tok.text
            ));
        }
        match tok.text.as_str() {
            "presentation" => self
                .parse_shigure_presentation(start)
                .map(ShigureDeclAst::Presentation),
            "comparison" => self
                .parse_shigure_comparison(start)
                .map(ShigureDeclAst::Comparison),
            "change_spec" => self
                .parse_shigure_change_spec(start)
                .map(ShigureDeclAst::ChangeSpec),
            "eval_condition" => self
                .parse_shigure_eval_condition(start)
                .map(ShigureDeclAst::EvalCondition),
            "task" => self.parse_shigure_task(start).map(ShigureDeclAst::Task),
            other => self.err(format!(
                "unknown SHIGURE declaration kind `{other}`; expected `presentation`, `comparison`, `change_spec`, `eval_condition`, or `task`"
            )),
        }
    }

    fn reject_conclusion_or_unknown(&self, context: &str) -> PResult<(), E> {
        if let Some(t) = self.peek()
            && t.kind == TokenKind::Name
            && is_forbidden_conclusion_field(&t.text)
        {
            return self.err(format!(
                "conclusion injection is forbidden: `{}` cannot be supplied in {context}",
                t.text
            ));
        }
        self.err(format!("unexpected clause in {context}"))
    }

    fn parse_shigure_coeff_domain(&mut self) -> PResult<RawCoeffDomain, E> {
        let start = self.here().0;
        if self.eat_kw("Z") {
            return Ok(RawCoeffDomain::Z((start, self.prev_end())));
        }
        if self.eat_kw("Q") {
            return Ok(RawCoeffDomain::Q((start, self.prev_end())));
        }
        if self.eat_kw("Fp") {
            self.expect_sym("(")?;
            let modulus = self.expect_int_token()?;
            self.expect_sym(")")?;
            return Ok(RawCoeffDomain::Fp {
                modulus,
                span: (start, self.prev_end()),
            });
        }
        self.err("expected coefficient domain `Z`, `Q`, or `Fp(<prime>)`")
    }

    fn parse_shigure_point_domain(&mut self) -> PResult<RawPointDomain, E> {
        let start = self.here().0;
        if self.eat_kw("algebraic_closure") {
            return Ok(RawPointDomain::AlgebraicClosure((start, self.prev_end())));
        }
        if self.eat_kw("rational_points") || self.eat_kw("Q_points") {
            return Ok(RawPointDomain::RationalPoints((start, self.prev_end())));
        }
        if self.eat_kw("integer_points") || self.eat_kw("Z_points") {
            return Ok(RawPointDomain::IntegerPoints((start, self.prev_end())));
        }
        if self.eat_kw("universal_ring") {
            return Ok(RawPointDomain::UniversalRing((start, self.prev_end())));
        }
        if self.eat_kw("finite_field_points") || self.eat_kw("Fp_points") {
            self.expect_sym("(")?;
            let modulus = self.expect_int_token()?;
            self.expect_sym(")")?;
            return Ok(RawPointDomain::FiniteFieldPoints {
                modulus,
                span: (start, self.prev_end()),
            });
        }
        self.err("expected point domain `algebraic_closure`, `rational_points`, `integer_points`, `finite_field_points(<prime>)`, or `universal_ring`")
    }

    fn expect_int_token(&mut self) -> PResult<String, E> {
        match self.peek().cloned() {
            Some(t) if t.kind == TokenKind::Int => {
                self.advance();
                Ok(t.text)
            }
            _ => self.err("expected a nonnegative integer literal"),
        }
    }

    fn parse_shigure_presentation(&mut self, start: usize) -> PResult<RawPresentation, E> {
        self.expect_kw("presentation")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut sorts = Vec::new();
        let mut phases = Vec::new();
        let mut operations = Vec::new();
        let mut observations = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure presentation`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("sort") {
                let s_start = self.prev_span().0;
                let s_name = self.ident()?;
                let rank = if self.eat_kw("rank") {
                    let raw = self.expect_int_token()?;
                    raw.parse::<usize>().map_err(|_| {
                        Box::new(Issue::law(
                            Code::Syntax,
                            self.prev_span(),
                            "sort rank out of range",
                        ))
                    })?
                } else {
                    1
                };
                self.expect_sym(";")?;
                sorts.push(RawSortDecl {
                    name: s_name,
                    rank,
                    span: (s_start, self.prev_end()),
                });
            } else if self.eat_kw("phase") {
                phases.push(self.parse_shigure_phase()?);
            } else if self.eat_kw("op") || self.eat_kw("operation") {
                operations.push(self.parse_shigure_operation()?);
            } else if self.eat_kw("obs") || self.eat_kw("observation") {
                observations.push(self.parse_shigure_observation()?);
            } else {
                self.reject_conclusion_or_unknown("`shigure presentation`")?;
            }
        }
        self.expect_sym("}")?;
        let Some(domain) = domain else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                (start, self.prev_end()),
                "`shigure presentation` requires a `domain` clause",
            ))
            .into());
        };
        Ok(RawPresentation {
            name,
            domain,
            sorts,
            phases,
            operations,
            observations,
            span: (start, self.prev_end()),
        })
    }

    fn parse_shigure_phase(&mut self) -> PResult<RawPhaseDecl, E> {
        let start = self.prev_span().0;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut coords = Vec::new();
        let mut state_laws = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("coord") {
                let c_start = self.prev_span().0;
                let c_name = self.ident()?;
                self.expect_sym(":")?;
                let sort = self.ident()?;
                let binding = if self.eat_kw("observed") {
                    let f_start = self.here().0;
                    let field = self.qname()?;
                    RawCoordBinding::ObservedField {
                        field,
                        span: (f_start, self.prev_end()),
                    }
                } else {
                    RawCoordBinding::Symbolic
                };
                self.expect_sym(";")?;
                coords.push(RawCoordDecl {
                    name: c_name,
                    sort,
                    binding,
                    span: (c_start, self.prev_end()),
                });
            } else if self.eat_kw("law") {
                let l_start = self.prev_span().0;
                let kind = if self.eat_kw("semantic") || self.eat_kw("required") {
                    ShigureLawKind::Semantic
                } else if self.eat_kw("representation") {
                    ShigureLawKind::Representation
                } else {
                    return self.err(
                        "expected `semantic` (or `required`) or `representation` after `law` in `phase`",
                    );
                };
                let l_name = self.ident()?;
                self.expect_sym(":")?;
                let expr = self.parse_shigure_equation_poly()?;
                self.expect_sym(";")?;
                state_laws.push(RawStateLawDecl {
                    name: l_name,
                    kind,
                    expr,
                    span: (l_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`phase`")?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawPhaseDecl {
            name,
            coords,
            state_laws,
            span: (start, self.prev_end()),
        })
    }

    fn parse_shigure_operation(&mut self) -> PResult<RawOperationDecl, E> {
        let start = self.prev_span().0;
        let name = self.ident()?;
        self.expect_sym("(")?;
        let mut args = Vec::new();
        if !self.is_sym(")") {
            loop {
                self.checkpoint_here()?;
                let arg_name = self.ident()?;
                self.expect_sym(":")?;
                let arg_sort = self.ident()?;
                args.push((arg_name, arg_sort));
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(")")?;
        self.expect_sym(":")?;
        let source_phase = self.ident()?;
        self.expect_sym("->")?;
        let target_phase = self.ident()?;
        self.expect_sym("{")?;
        let mut updates = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let coord = self.ident()?;
            self.expect_sym("=")?;
            let expr = self.parse_shigure_poly_expr()?;
            self.expect_sym(";")?;
            updates.push((coord, expr));
        }
        self.expect_sym("}")?;
        Ok(RawOperationDecl {
            name,
            source_phase,
            target_phase,
            args,
            updates,
            span: (start, self.prev_end()),
        })
    }

    fn parse_shigure_observation(&mut self) -> PResult<RawObservationDecl, E> {
        let start = self.prev_span().0;
        let name = self.ident()?;
        self.expect_kw("on")?;
        let phase = self.ident()?;
        self.expect_sym("=")?;
        self.expect_sym("(")?;
        let mut components = Vec::new();
        if !self.is_sym(")") {
            loop {
                self.checkpoint_here()?;
                components.push(self.parse_shigure_poly_expr()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(")")?;
        self.expect_sym(";")?;
        Ok(RawObservationDecl {
            name,
            phase,
            components,
            span: (start, self.prev_end()),
        })
    }

    fn parse_shigure_comparison(&mut self, start: usize) -> PResult<RawComparison, E> {
        self.expect_kw("comparison")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut before: Option<QName> = None;
        let mut after: Option<QName> = None;
        let mut state_comparisons = Vec::new();
        let mut word_translation = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("before") {
                if before.is_some() {
                    return self.err("duplicate `before` clause in `shigure comparison`");
                }
                before = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("after") {
                if after.is_some() {
                    return self.err("duplicate `after` clause in `shigure comparison`");
                }
                after = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("state_map") {
                let s_start = self.prev_span().0;
                let after_phase = self.ident()?;
                self.expect_sym("->")?;
                let before_phase = self.ident()?;
                self.expect_sym("{")?;
                let mut map = Vec::new();
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    let target_coord = self.ident()?;
                    self.expect_sym("=")?;
                    let expr = self.parse_shigure_poly_expr()?;
                    self.expect_sym(";")?;
                    map.push((target_coord, expr));
                }
                self.expect_sym("}")?;
                state_comparisons.push(RawStateComparison {
                    after_phase,
                    before_phase,
                    map,
                    span: (s_start, self.prev_end()),
                });
            } else if self.eat_kw("translate") {
                let t_start = self.prev_span().0;
                let after_operation = self.ident()?;
                self.expect_sym("->")?;
                self.expect_sym("[")?;
                let mut steps = Vec::new();
                if !self.is_sym("]") {
                    loop {
                        self.checkpoint_here()?;
                        let st_start = self.here().0;
                        let before_operation = self.ident()?;
                        self.expect_sym("(")?;
                        let mut arg_exprs = Vec::new();
                        if !self.is_sym(")") {
                            loop {
                                self.checkpoint_here()?;
                                arg_exprs.push(self.parse_shigure_poly_expr()?);
                                if !self.eat_sym(",") {
                                    break;
                                }
                            }
                        }
                        self.expect_sym(")")?;
                        steps.push(RawTranslatedStep {
                            before_operation,
                            arg_exprs,
                            span: (st_start, self.prev_end()),
                        });
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                }
                self.expect_sym("]")?;
                self.expect_sym(";")?;
                word_translation.push(RawTranslatedWord {
                    after_operation,
                    steps,
                    span: (t_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`shigure comparison`")?;
            }
        }
        self.expect_sym("}")?;
        let Some(before) = before else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                (start, self.prev_end()),
                "`shigure comparison` requires a `before` clause",
            ))
            .into());
        };
        let Some(after) = after else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                (start, self.prev_end()),
                "`shigure comparison` requires an `after` clause",
            ))
            .into());
        };
        Ok(RawComparison {
            name,
            before,
            after,
            state_comparisons,
            word_translation,
            span: (start, self.prev_end()),
        })
    }

    fn parse_shigure_change_spec(&mut self, start: usize) -> PResult<RawChangeSpec, E> {
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

    fn parse_shigure_eval_condition(&mut self, start: usize) -> PResult<RawEvalCondition, E> {
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

    fn parse_shigure_task(&mut self, start: usize) -> PResult<RawTask, E> {
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

    /// 等式 `lhs = rhs` を `lhs - rhs`（`rhs` が定数 0 なら `lhs`）として解析する。
    fn parse_shigure_equation_poly(&mut self) -> PResult<ShigurePolyExpr, E> {
        let lhs = self.parse_shigure_poly_expr()?;
        self.expect_sym("=")?;
        let rhs = self.parse_shigure_poly_expr()?;
        if matches!(&rhs, ShigurePolyExpr::Int(n) if n.is_zero()) {
            Ok(lhs)
        } else {
            Ok(ShigurePolyExpr::Sub(Box::new(lhs), Box::new(rhs)))
        }
    }

    fn parse_shigure_poly_expr(&mut self) -> PResult<ShigurePolyExpr, E> {
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
