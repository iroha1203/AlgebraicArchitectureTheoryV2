//! `shigure transfer` 宣言の構文解析。

use super::ast_ext::*;
use super::parser::PResult;
use super::parser_diagram_path::MorphismBuilder;
use super::*;
use crate::law::ast::{Ident, QName};
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    pub(super) fn parse_shigure_transfer(&mut self, start: usize) -> PResult<RawTransferTask, E> {
        self.expect_kw("transfer")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut steps = Vec::new();
        let mut word_checks = Vec::new();
        let mut old_word_lifts = Vec::new();
        let mut change_spec: Option<QName> = None;
        let mut eval_condition: Option<QName> = None;
        let mut require_full_domain: Option<bool> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("step") {
                steps.push(self.parse_transfer_step(self.prev_span().0)?);
            } else if self.eat_kw("word_check") {
                word_checks.push(self.parse_word_check(self.prev_span().0)?);
            } else if self.eat_kw("old_word_lift") {
                old_word_lifts.push(self.parse_old_word_lift(self.prev_span().0)?);
            } else if self.eat_kw("change_spec") {
                if change_spec.is_some() {
                    return self.err("duplicate `change_spec` clause in `shigure transfer`");
                }
                change_spec = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("eval_condition") {
                if eval_condition.is_some() {
                    return self.err("duplicate `eval_condition` clause in `shigure transfer`");
                }
                eval_condition = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("require_full_domain") {
                if require_full_domain.is_some() {
                    return self
                        .err("duplicate `require_full_domain` clause in `shigure transfer`");
                }
                let flag = if self.eat_kw("true") {
                    true
                } else if self.eat_kw("false") {
                    false
                } else {
                    return self.err("expected `true` or `false` after `require_full_domain`");
                };
                self.expect_sym(";")?;
                require_full_domain = Some(flag);
            } else {
                self.reject_conclusion_or_unknown("`shigure transfer`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(change_spec) = change_spec else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure transfer` requires a `change_spec` clause",
            ))
            .into());
        };
        Ok(RawTransferTask {
            name,
            steps,
            word_checks,
            old_word_lifts,
            change_spec,
            eval_condition,
            require_full_domain: require_full_domain.unwrap_or(false),
            span,
        })
    }

    fn parse_transfer_step(&mut self, start: usize) -> PResult<RawTransferStep, E> {
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut before: Option<QName> = None;
        let mut after: Option<QName> = None;
        let mut source_phase: Option<Ident> = None;
        let mut target_phase: Option<Ident> = None;
        let mut domain_laws = Vec::new();
        let mut lift_map: Option<Vec<(Ident, ShigurePolyExpr, Span)>> = None;
        let mut morph = MorphismBuilder::default();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("before") {
                if before.is_some() {
                    return self.err("duplicate `before` clause in transfer `step`");
                }
                before = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("after") {
                if after.is_some() {
                    return self.err("duplicate `after` clause in transfer `step`");
                }
                after = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("source_phase") {
                if source_phase.is_some() {
                    return self.err("duplicate `source_phase` clause in transfer `step`");
                }
                source_phase = Some(self.ident()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("target_phase") {
                if target_phase.is_some() {
                    return self.err("duplicate `target_phase` clause in transfer `step`");
                }
                target_phase = Some(self.ident()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("domain_law") {
                domain_laws.push(self.parse_shigure_law_decl_after_kw("`domain_law`")?);
            } else if self.eat_kw("lift") {
                if lift_map.is_some() {
                    return self.err("duplicate `lift` block in transfer `step`");
                }
                self.expect_sym("{")?;
                let mut map = Vec::new();
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if let Some(t) = self.peek()
                        && t.kind == TokenKind::Name
                        && is_forbidden_conclusion_field(&t.text)
                    {
                        self.reject_conclusion_or_unknown("transfer `lift`")?;
                    }
                    let l_start = self.here().0;
                    let coord = self.ident()?;
                    self.expect_sym("=")?;
                    let expr = self.parse_shigure_poly_expr()?;
                    self.expect_sym(";")?;
                    map.push((coord, expr, (l_start, self.prev_end())));
                }
                self.expect_sym("}")?;
                lift_map = Some(map);
            } else if !morph.try_parse_clause(self, "transfer `step`")? {
                self.reject_conclusion_or_unknown("transfer `step`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());

        if morph.has_comparison() && (before.is_some() || after.is_some()) {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "cannot mix `comparison` with `before`/`after` in transfer `step`",
            ))
            .into());
        }
        let body = morph.finish(span, "transfer `step`")?;
        let source = match body {
            Some(RawMorphismBody::Comparison(cmp)) => RawTransferStepSource::Comparison(cmp),
            Some(morphism) => {
                let Some(before) = before else {
                    return Err(Box::new(Issue::law(
                        Code::Syntax,
                        span,
                        "inline transfer `step` requires a `before` presentation",
                    ))
                    .into());
                };
                let Some(after) = after else {
                    return Err(Box::new(Issue::law(
                        Code::Syntax,
                        span,
                        "inline transfer `step` requires an `after` presentation",
                    ))
                    .into());
                };
                RawTransferStepSource::Inline {
                    before,
                    after,
                    morphism,
                }
            }
            None => {
                return Err(Box::new(Issue::law(
                    Code::Syntax,
                    span,
                    "transfer `step` requires `comparison` or `before`/`after` with morphism",
                ))
                .into());
            }
        };

        let Some(source_phase) = source_phase else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "transfer `step` requires a `source_phase` clause",
            ))
            .into());
        };
        let Some(target_phase) = target_phase else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "transfer `step` requires a `target_phase` clause",
            ))
            .into());
        };
        let Some(lift_map) = lift_map else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "transfer `step` requires a `lift` block",
            ))
            .into());
        };

        Ok(RawTransferStep {
            name,
            source,
            source_phase,
            target_phase,
            domain_laws,
            lift_map,
            span,
        })
    }

    fn parse_optional_word_args(&mut self) -> PResult<Vec<Ident>, E> {
        let mut args = Vec::new();
        if self.eat_sym("(") {
            if !self.is_sym(")") {
                loop {
                    self.checkpoint_here()?;
                    args.push(self.ident()?);
                    if !self.eat_sym(",") {
                        break;
                    }
                }
            }
            self.expect_sym(")")?;
        }
        Ok(args)
    }

    fn parse_word_steps(&mut self) -> PResult<Vec<RawWordStep>, E> {
        let raw_steps = self.parse_shigure_word_step_list()?;
        Ok(raw_steps
            .into_iter()
            .map(|st| RawWordStep {
                operation: st.before_operation,
                arg_exprs: st.arg_exprs,
                span: st.span,
            })
            .collect())
    }

    fn parse_word_check(&mut self, start: usize) -> PResult<RawWordCheck, E> {
        let name = self.ident()?;
        let args = self.parse_optional_word_args()?;
        self.expect_sym("=")?;
        let steps = self.parse_word_steps()?;
        self.expect_sym(";")?;
        Ok(RawWordCheck {
            name,
            args,
            steps,
            span: (start, self.prev_end()),
        })
    }

    fn parse_old_word_lift(&mut self, start: usize) -> PResult<RawOldWordLift, E> {
        let name = self.ident()?;
        let args = self.parse_optional_word_args()?;
        self.expect_sym("{")?;
        let mut target_steps: Option<Vec<RawWordStep>> = None;
        let mut max_length: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("target") {
                if target_steps.is_some() {
                    return self.err("duplicate `target` clause in `old_word_lift`");
                }
                target_steps = Some(self.parse_word_steps()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("max_length") {
                if max_length.is_some() {
                    return self.err("duplicate `max_length` clause in `old_word_lift`");
                }
                max_length = Some(self.parse_usize_token("`old_word_lift` max_length")?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`old_word_lift`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(target_steps) = target_steps else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`old_word_lift` requires a `target` clause",
            ))
            .into());
        };
        Ok(RawOldWordLift {
            name,
            args,
            target_steps,
            max_length,
            span,
        })
    }
}
