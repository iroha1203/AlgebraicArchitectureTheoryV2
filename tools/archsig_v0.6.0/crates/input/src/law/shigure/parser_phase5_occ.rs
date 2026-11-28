//! `shigure occurrence` 宣言の構文解析および Phase 5 共通記号パーサ（AC2）。

use super::ast_phase3::RawMemberCoordValue;
use super::ast_phase5_obs::*;
use super::parser::PResult;
use crate::law::ast::Span;
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    /// 記号名（禁止結論名でない識別子・文字列リテラル・符号付き含む整数）を解析する。
    pub(super) fn parse_p5_symbol(&mut self, context: &str) -> PResult<(String, Span), E> {
        self.reject_peek_forbidden(context)?;
        if let Some(tok) = self.peek().cloned() {
            match tok.kind {
                TokenKind::Str => {
                    let s = self.string()?;
                    return Ok((s, tok.span));
                }
                TokenKind::Int => {
                    let n = self.expect_int_token()?;
                    return Ok((n, tok.span));
                }
                TokenKind::Name => {
                    let id = self.ident()?;
                    self.reject_forbidden_ident(&id, context)?;
                    return Ok((id.name, id.span));
                }
                TokenKind::Sym if tok.text == "-" => {
                    let start = tok.span.0;
                    self.advance();
                    let n = self.expect_int_token()?;
                    return Ok((format!("-{n}"), (start, self.prev_end())));
                }
                TokenKind::Sym => {}
            }
        }
        self.err(format!(
            "expected symbol literal or identifier in {context}"
        ))
    }

    pub(super) fn parse_p5_symbol_list(
        &mut self,
        context: &str,
    ) -> PResult<Vec<(String, Span)>, E> {
        self.expect_sym("[")?;
        let mut items = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                items.push(self.parse_p5_symbol(context)?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(items)
    }

    pub(super) fn parse_p5_symbolic_value(
        &mut self,
        context: &str,
    ) -> PResult<RawSymbolicValue, E> {
        if self.eat_kw("observed") {
            let f_start = self.here().0;
            let field = self.qname()?;
            Ok(RawSymbolicValue::ObservedField {
                field,
                span: (f_start, self.prev_end()),
            })
        } else if self.eat_kw("missing") {
            Ok(RawSymbolicValue::Missing(self.prev_span()))
        } else {
            let (s, span) = self.parse_p5_symbol(context)?;
            Ok(RawSymbolicValue::Literal(s, span))
        }
    }

    pub(super) fn parse_p5_coord_matrix(&mut self) -> PResult<Vec<Vec<RawMemberCoordValue>>, E> {
        self.expect_sym("[")?;
        let mut rows = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                rows.push(self.parse_p4_coord_value_list()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(rows)
    }

    pub(super) fn parse_p5_op_sig(
        &mut self,
        start: usize,
        is_total: bool,
        context: &str,
    ) -> PResult<RawOccurrenceOp, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym("(")?;
        let arg_sorts = self.parse_p4_ident_list(context)?;
        self.expect_sym(")")?;
        self.expect_sym("->")?;
        let out_sort = self.ident()?;
        self.reject_forbidden_ident(&out_sort, context)?;
        self.expect_sym(";")?;
        Ok(RawOccurrenceOp {
            name,
            arg_sorts,
            out_sort,
            is_total,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_p5_rel_sig(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawOccurrenceRel, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym("(")?;
        let arg_sorts = self.parse_p4_ident_list(context)?;
        self.expect_sym(")")?;
        self.expect_sym(";")?;
        Ok(RawOccurrenceRel {
            name,
            arg_sorts,
            span: (start, self.prev_end()),
        })
    }

    fn parse_occurrence_reading(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawOccurrenceReading, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym(":")?;
        let sort = self.ident()?;
        self.reject_forbidden_ident(&sort, context)?;
        self.expect_sym("{")?;
        let mut values = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let e_start = self.here().0;
            let elem = self.parse_p5_symbol(context)?;
            self.expect_sym("->")?;
            let val = if self.eat_kw("none") {
                None
            } else {
                Some(self.parse_p5_symbolic_value(context)?)
            };
            self.expect_sym(";")?;
            values.push((elem, val, (e_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(RawOccurrenceReading {
            name,
            sort,
            values,
            span: (start, self.prev_end()),
        })
    }

    fn parse_occurrence_initial_readout(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawOccurrenceInitialReadout, E> {
        let sort = self.ident()?;
        self.reject_forbidden_ident(&sort, context)?;
        self.expect_sym("{")?;
        let mut values = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let e_start = self.here().0;
            let elem = self.parse_p5_symbol(context)?;
            self.expect_sym("->")?;
            let val = self.parse_p5_symbolic_value(context)?;
            self.expect_sym(";")?;
            values.push((elem, val, (e_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(RawOccurrenceInitialReadout {
            sort,
            values,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_occurrence(
        &mut self,
        start: usize,
    ) -> PResult<RawOccurrenceTask, E> {
        self.expect_kw("occurrence")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`shigure occurrence`")?;
        self.expect_sym("{")?;

        let mut origins = Vec::new();
        let mut sorts = Vec::new();
        let mut operations = Vec::new();
        let mut relations = Vec::new();
        let mut identity_requests = Vec::new();
        let mut op_records = Vec::new();
        let mut pred_records = Vec::new();
        let mut base_readings = Vec::new();
        let mut context_closed_17_5: Option<bool> = None;
        let mut explicit_contexts = Vec::new();
        let mut preserve_full_domains = Vec::new();
        let mut initial_readouts = Vec::new();
        let mut max_congruence_steps: Option<usize> = None;
        let mut max_partitions: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin("`shigure occurrence`")?);
            } else if self.eat_kw("fixed_value") {
                let s_start = self.prev_span().0;
                self.expect_kw("sort")?;
                let s_name = self.ident()?;
                self.reject_forbidden_ident(&s_name, "`shigure occurrence` sort")?;
                self.expect_sym("=")?;
                let elements = self.parse_p5_symbol_list("`shigure occurrence` sort elements")?;
                self.expect_sym(";")?;
                sorts.push(RawOccurrenceSort {
                    name: s_name,
                    elements,
                    is_fixed_value: true,
                    span: (s_start, self.prev_end()),
                });
            } else if self.eat_kw("sort") {
                let s_start = self.prev_span().0;
                let s_name = self.ident()?;
                self.reject_forbidden_ident(&s_name, "`shigure occurrence` sort")?;
                self.expect_sym("=")?;
                let elements = self.parse_p5_symbol_list("`shigure occurrence` sort elements")?;
                self.expect_sym(";")?;
                sorts.push(RawOccurrenceSort {
                    name: s_name,
                    elements,
                    is_fixed_value: false,
                    span: (s_start, self.prev_end()),
                });
            } else if self.eat_kw("operation") {
                operations.push(self.parse_p5_op_sig(
                    self.prev_span().0,
                    true,
                    "`shigure occurrence` operation",
                )?);
            } else if self.eat_kw("partial_operation") {
                operations.push(self.parse_p5_op_sig(
                    self.prev_span().0,
                    false,
                    "`shigure occurrence` partial_operation",
                )?);
            } else if self.eat_kw("relation") {
                relations.push(
                    self.parse_p5_rel_sig(self.prev_span().0, "`shigure occurrence` relation")?,
                );
            } else if self.eat_kw("identify") {
                let id_start = self.prev_span().0;
                let sort = self.ident()?;
                self.reject_forbidden_ident(&sort, "`shigure occurrence` identify")?;
                let lhs = self.parse_p5_symbol("`shigure occurrence` identify")?;
                self.expect_sym("=")?;
                let rhs = self.parse_p5_symbol("`shigure occurrence` identify")?;
                self.expect_sym(";")?;
                identity_requests.push((sort, lhs, rhs, (id_start, self.prev_end())));
            } else if self.eat_kw("op_record") {
                let r_start = self.prev_span().0;
                let op_name = self.ident()?;
                self.reject_forbidden_ident(&op_name, "`shigure occurrence` op_record")?;
                self.expect_sym("(")?;
                let args = self.parse_p5_symbol_list("`shigure occurrence` op_record args")?;
                self.expect_sym(")")?;
                self.expect_sym("->")?;
                let output =
                    self.parse_p5_symbolic_value("`shigure occurrence` op_record output")?;
                self.expect_sym(";")?;
                op_records.push(RawOccurrenceOpRecord {
                    op_name,
                    args,
                    output,
                    span: (r_start, self.prev_end()),
                });
            } else if self.eat_kw("domain_record") {
                let r_start = self.prev_span().0;
                let pred_name = self.ident()?;
                self.reject_forbidden_ident(&pred_name, "`shigure occurrence` domain_record")?;
                self.expect_sym("(")?;
                let args = self.parse_p5_symbol_list("`shigure occurrence` domain_record args")?;
                self.expect_sym(")")?;
                self.expect_sym("=")?;
                let holds = self.parse_shigure_bool("`shigure occurrence` domain_record")?;
                self.expect_sym(";")?;
                pred_records.push(RawOccurrencePredRecord {
                    kind: OccurrencePredKind::Domain,
                    name: pred_name,
                    args,
                    holds,
                    span: (r_start, self.prev_end()),
                });
            } else if self.eat_kw("rel_record") {
                let r_start = self.prev_span().0;
                let pred_name = self.ident()?;
                self.reject_forbidden_ident(&pred_name, "`shigure occurrence` rel_record")?;
                self.expect_sym("(")?;
                let args = self.parse_p5_symbol_list("`shigure occurrence` rel_record args")?;
                self.expect_sym(")")?;
                self.expect_sym("=")?;
                let holds = self.parse_shigure_bool("`shigure occurrence` rel_record")?;
                self.expect_sym(";")?;
                pred_records.push(RawOccurrencePredRecord {
                    kind: OccurrencePredKind::Relation,
                    name: pred_name,
                    args,
                    holds,
                    span: (r_start, self.prev_end()),
                });
            } else if self.eat_kw("base_reading") {
                base_readings.push(self.parse_occurrence_reading(
                    self.prev_span().0,
                    "`shigure occurrence` base_reading",
                )?);
            } else if self.eat_kw("explicit_context") {
                explicit_contexts.push(self.parse_occurrence_reading(
                    self.prev_span().0,
                    "`shigure occurrence` explicit_context",
                )?);
            } else if self.eat_kw("context_closed") {
                if context_closed_17_5.is_some() {
                    return self.err("duplicate `context_closed` clause in `shigure occurrence`");
                }
                self.expect_sym("=")?;
                let flag = self.parse_shigure_bool("`shigure occurrence` context_closed")?;
                self.expect_sym(";")?;
                context_closed_17_5 = Some(flag);
            } else if self.eat_kw("preserve_full_domain") {
                let list = self.parse_p4_ident_list("`shigure occurrence` preserve_full_domain")?;
                self.expect_sym(";")?;
                preserve_full_domains.extend(list);
            } else if self.eat_kw("initial_readout") {
                initial_readouts.push(self.parse_occurrence_initial_readout(
                    self.prev_span().0,
                    "`shigure occurrence` initial_readout",
                )?);
            } else if self.eat_kw("max_congruence_steps") {
                if max_congruence_steps.is_some() {
                    return self
                        .err("duplicate `max_congruence_steps` clause in `shigure occurrence`");
                }
                self.expect_sym("=")?;
                let n = self.parse_usize_token("`max_congruence_steps`")?;
                self.expect_sym(";")?;
                max_congruence_steps = Some(n);
            } else if self.eat_kw("max_partitions") {
                if max_partitions.is_some() {
                    return self.err("duplicate `max_partitions` clause in `shigure occurrence`");
                }
                self.expect_sym("=")?;
                let n = self.parse_usize_token("`max_partitions`")?;
                self.expect_sym(";")?;
                max_partitions = Some(n);
            } else {
                self.reject_conclusion_or_unknown("`shigure occurrence`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        if origins.is_empty() {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure occurrence` requires at least one `origin` clause",
            ))
            .into());
        }
        Ok(RawOccurrenceTask {
            name,
            origins,
            sorts,
            operations,
            relations,
            identity_requests,
            op_records,
            pred_records,
            base_readings,
            context_closed_17_5,
            explicit_contexts,
            preserve_full_domains,
            initial_readouts,
            max_congruence_steps,
            max_partitions,
            span,
        })
    }
}
