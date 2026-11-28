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

pub(super) type PResult<T, E> = Result<T, E>;

impl<E: InputError> Parser<E> {
    /// `shigure <kind> <Name> { ... }` を解析する（`shigure` は未消費）。
    pub(crate) fn parse_shigure_decl(&mut self) -> PResult<ShigureDeclAst, E> {
        let start = self.here().0;
        self.expect_kw("shigure")?;
        let Some(tok) = self.peek().cloned() else {
            return self.err(
                "expected SHIGURE declaration kind (`presentation`, `comparison`, `change_spec`, `eval_condition`, `task`, `diagram`, `path`, `transfer`, `family`, `robustness`, `chevalley`, `observations`, `lift`, `artin`, `diagnostics`, `atlas`, `occurrence`, `partial`, `revision`, or `multisource`) after `shigure`",
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
            "diagram" => self
                .parse_shigure_diagram(start)
                .map(ShigureDeclAst::Diagram),
            "path" => self
                .parse_shigure_path(start)
                .map(|p| ShigureDeclAst::Path(Box::new(p))),
            "transfer" => self
                .parse_shigure_transfer(start)
                .map(ShigureDeclAst::Transfer),
            "family" => self
                .parse_shigure_family(start)
                .map(|f| ShigureDeclAst::Family(Box::new(f))),
            "robustness" => self
                .parse_shigure_robustness(start)
                .map(ShigureDeclAst::Robustness),
            "chevalley" => self
                .parse_shigure_chevalley(start)
                .map(ShigureDeclAst::Chevalley),
            "observations" => self
                .parse_shigure_observations(start)
                .map(ShigureDeclAst::Observations),
            "lift" => self
                .parse_shigure_lift(start)
                .map(|l| ShigureDeclAst::Lift(Box::new(l))),
            "artin" => self
                .parse_shigure_artin(start)
                .map(|a| ShigureDeclAst::Artin(Box::new(a))),
            "diagnostics" => self
                .parse_shigure_diagnostics(start)
                .map(|d| ShigureDeclAst::Diagnostics(Box::new(d))),
            "atlas" => self
                .parse_shigure_atlas(start)
                .map(|a| ShigureDeclAst::Atlas(Box::new(a))),
            "occurrence" => self
                .parse_shigure_occurrence(start)
                .map(|o| ShigureDeclAst::Occurrence(Box::new(o))),
            "partial" => self
                .parse_shigure_partial(start)
                .map(|p| ShigureDeclAst::Partial(Box::new(p))),
            "revision" => self
                .parse_shigure_revision(start)
                .map(|r| ShigureDeclAst::Revision(Box::new(r))),
            "multisource" => self
                .parse_shigure_multisource(start)
                .map(|m| ShigureDeclAst::Multisource(Box::new(m))),
            other => self.err(format!(
                "unknown SHIGURE declaration kind `{other}`; expected `presentation`, `comparison`, `change_spec`, `eval_condition`, `task`, `diagram`, `path`, `transfer`, `family`, `robustness`, `chevalley`, `observations`, `lift`, `artin`, `diagnostics`, `atlas`, `occurrence`, `partial`, `revision`, or `multisource`"
            )),
        }
    }

    pub(super) fn reject_conclusion_or_unknown(&self, context: &str) -> PResult<(), E> {
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

    pub(super) fn parse_shigure_coeff_domain(&mut self) -> PResult<RawCoeffDomain, E> {
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

    pub(super) fn parse_shigure_point_domain(&mut self) -> PResult<RawPointDomain, E> {
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

    pub(super) fn expect_int_token(&mut self) -> PResult<String, E> {
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
                state_laws.push(self.parse_shigure_law_decl_after_kw("`phase`")?);
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

    pub(super) fn parse_shigure_law_decl_after_kw(
        &mut self,
        context: &str,
    ) -> PResult<RawStateLawDecl, E> {
        let l_start = self.prev_span().0;
        let kind = if self.eat_kw("semantic") || self.eat_kw("required") {
            ShigureLawKind::Semantic
        } else if self.eat_kw("representation") {
            ShigureLawKind::Representation
        } else {
            return self.err(format!(
                "expected `semantic` (or `required`) or `representation` in {context} law declaration"
            ));
        };
        let l_name = self.ident()?;
        self.expect_sym(":")?;
        let expr = self.parse_shigure_equation_poly()?;
        self.expect_sym(";")?;
        Ok(RawStateLawDecl {
            name: l_name,
            kind,
            expr,
            span: (l_start, self.prev_end()),
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
        let mut domain_laws = Vec::new();
        let mut updates = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("law") {
                domain_laws.push(self.parse_shigure_law_decl_after_kw("`op`")?);
            } else {
                if let Some(t) = self.peek()
                    && t.kind == TokenKind::Name
                    && is_forbidden_conclusion_field(&t.text)
                {
                    self.reject_conclusion_or_unknown("`op`")?;
                }
                let coord = self.ident()?;
                self.expect_sym("=")?;
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                updates.push((coord, expr));
            }
        }
        self.expect_sym("}")?;
        Ok(RawOperationDecl {
            name,
            source_phase,
            target_phase,
            args,
            domain_laws,
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
                state_comparisons.push(self.parse_shigure_state_comparison_after_kw()?);
            } else if self.eat_kw("translate") {
                word_translation.push(self.parse_shigure_translated_word_after_kw()?);
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

    pub(super) fn parse_shigure_state_comparison_after_kw(
        &mut self,
    ) -> PResult<RawStateComparison, E> {
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
        Ok(RawStateComparison {
            after_phase,
            before_phase,
            map,
            span: (s_start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_word_step_list(&mut self) -> PResult<Vec<RawTranslatedStep>, E> {
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
        Ok(steps)
    }

    pub(super) fn parse_shigure_translated_word_after_kw(
        &mut self,
    ) -> PResult<RawTranslatedWord, E> {
        let t_start = self.prev_span().0;
        let after_operation = self.ident()?;
        self.expect_sym("->")?;
        let steps = self.parse_shigure_word_step_list()?;
        self.expect_sym(";")?;
        Ok(RawTranslatedWord {
            after_operation,
            steps,
            span: (t_start, self.prev_end()),
        })
    }
}
