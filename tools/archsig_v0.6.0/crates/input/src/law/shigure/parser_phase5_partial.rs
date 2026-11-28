//! `shigure partial` 宣言の構文解析（表示クラス・エントリ / AC2）。

use super::ast_phase3::RawMemberCoordValue;
use super::ast_phase5_obs::*;
use super::parser::PResult;
use super::*;
use crate::law::ast::Ident;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    fn parse_partial_value(&mut self, context: &str) -> PResult<RawPartialValue, E> {
        if self.eat_kw("known") {
            Ok(RawPartialValue::Known(
                self.parse_p5_symbolic_value(context)?,
            ))
        } else if self.eat_kw("absent") {
            Ok(RawPartialValue::ExplicitAbsent)
        } else if self.eat_kw("unobserved") {
            let slot = self.ident()?;
            self.reject_forbidden_ident(&slot, context)?;
            Ok(RawPartialValue::UnobservedSlot(slot))
        } else {
            self.err(format!(
                "expected `known <value>`, `absent`, or `unobserved <slot>` in {context}"
            ))
        }
    }

    fn parse_partial_truth(&mut self, context: &str) -> PResult<RawPartialTruth, E> {
        if self.eat_kw("true") {
            Ok(RawPartialTruth::True)
        } else if self.eat_kw("absent") {
            Ok(RawPartialTruth::ExplicitAbsent)
        } else if self.eat_kw("unobserved") {
            let slot = self.ident()?;
            self.reject_forbidden_ident(&slot, context)?;
            Ok(RawPartialTruth::UnobservedSlot(slot))
        } else {
            self.err(format!(
                "expected `true`, `absent`, or `unobserved <slot>` in {context}"
            ))
        }
    }

    fn parse_partial_background(
        &mut self,
        context: &str,
    ) -> PResult<Vec<RawBackgroundConstraint>, E> {
        self.expect_sym("{")?;
        let mut out = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let c_start = self.here().0;
            if self.is_kw("eval_law") || self.is_kw("eval_eq") {
                return self.p4_syntax_err(
                    self.here(),
                    "evaluation laws cannot be placed inside `background` constraints",
                );
            } else if self.eat_kw("slot_eq") {
                self.expect_sym("(")?;
                let a = self.ident()?;
                self.reject_forbidden_ident(&a, context)?;
                self.expect_sym(",")?;
                let b = self.ident()?;
                self.reject_forbidden_ident(&b, context)?;
                self.expect_sym(")")?;
                self.expect_sym(";")?;
                out.push(RawBackgroundConstraint::SlotEquality(
                    a,
                    b,
                    (c_start, self.prev_end()),
                ));
            } else if self.eat_kw("slot_neq") {
                self.expect_sym("(")?;
                let a = self.ident()?;
                self.reject_forbidden_ident(&a, context)?;
                self.expect_sym(",")?;
                let b = self.ident()?;
                self.reject_forbidden_ident(&b, context)?;
                self.expect_sym(")")?;
                self.expect_sym(";")?;
                out.push(RawBackgroundConstraint::SlotNotEqual(
                    a,
                    b,
                    (c_start, self.prev_end()),
                ));
            } else if self.eat_kw("injective") {
                self.expect_sym("(")?;
                let op = self.ident()?;
                self.reject_forbidden_ident(&op, context)?;
                self.expect_sym(")")?;
                self.expect_sym(";")?;
                out.push(RawBackgroundConstraint::OperationInjective(
                    op,
                    (c_start, self.prev_end()),
                ));
            } else if self.eat_kw("surjective") {
                self.expect_sym("(")?;
                let op = self.ident()?;
                self.reject_forbidden_ident(&op, context)?;
                self.expect_sym(")")?;
                self.expect_sym(";")?;
                out.push(RawBackgroundConstraint::OperationSurjective(
                    op,
                    (c_start, self.prev_end()),
                ));
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        Ok(out)
    }

    fn parse_partial_record(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawPartialRecord, E> {
        let id = self.ident()?;
        self.reject_forbidden_ident(&id, context)?;
        self.expect_sym(":")?;
        let kind = if self.eat_kw("op_value") {
            let op_name = self.ident()?;
            self.reject_forbidden_ident(&op_name, context)?;
            self.expect_sym("(")?;
            let args = self.parse_p5_symbol_list(context)?;
            self.expect_sym(")")?;
            self.expect_sym("=")?;
            let value = self.parse_partial_value(context)?;
            RawPartialRecordKind::OpValue {
                op_name,
                args,
                value,
            }
        } else if self.eat_kw("op_domain") {
            let op_name = self.ident()?;
            self.reject_forbidden_ident(&op_name, context)?;
            self.expect_sym("(")?;
            let args = self.parse_p5_symbol_list(context)?;
            self.expect_sym(")")?;
            self.expect_sym("=")?;
            let defined = self.parse_partial_truth(context)?;
            RawPartialRecordKind::OpDomain {
                op_name,
                args,
                defined,
            }
        } else if self.eat_kw("op_graph") {
            let op_name = self.ident()?;
            self.reject_forbidden_ident(&op_name, context)?;
            self.expect_sym("(")?;
            let args = self.parse_p5_symbol_list(context)?;
            self.expect_sym(",")?;
            let output = self.parse_p5_symbol(context)?;
            self.expect_sym(")")?;
            self.expect_sym("=")?;
            let present = self.parse_partial_truth(context)?;
            RawPartialRecordKind::OpGraph {
                op_name,
                args,
                output,
                present,
            }
        } else if self.eat_kw("rel") {
            let rel_name = self.ident()?;
            self.reject_forbidden_ident(&rel_name, context)?;
            self.expect_sym("(")?;
            let args = self.parse_p5_symbol_list(context)?;
            self.expect_sym(")")?;
            self.expect_sym("=")?;
            let holds = self.parse_partial_truth(context)?;
            RawPartialRecordKind::Relation {
                rel_name,
                args,
                holds,
            }
        } else if self.eat_kw("slot_assign") {
            let slot = self.ident()?;
            self.reject_forbidden_ident(&slot, context)?;
            self.expect_sym("=")?;
            let value = self.parse_p5_symbol(context)?;
            RawPartialRecordKind::SlotAssignment { slot, value }
        } else {
            self.reject_conclusion_or_unknown(context)?;
            unreachable!()
        };
        self.expect_sym(";")?;
        Ok(RawPartialRecord {
            id,
            kind,
            span: (start, self.prev_end()),
        })
    }

    fn parse_finite_partial(&mut self, start: usize) -> PResult<RawFinitePartial, E> {
        let context = "`shigure partial` finite_table";
        self.expect_sym("{")?;
        let mut sorts = Vec::new();
        let mut operations = Vec::new();
        let mut relations = Vec::new();
        let mut slots = Vec::new();
        let mut background_constraints = Vec::new();
        let mut records = Vec::new();
        let mut max_completions: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("sort") {
                let s_start = self.prev_span().0;
                let s_name = self.ident()?;
                self.reject_forbidden_ident(&s_name, context)?;
                self.expect_sym("=")?;
                let elems = self.parse_p5_symbol_list(context)?;
                self.expect_sym(";")?;
                sorts.push((s_name, elems, (s_start, self.prev_end())));
            } else if self.eat_kw("operation") {
                operations.push(self.parse_p5_op_sig(self.prev_span().0, true, context)?);
            } else if self.eat_kw("partial_operation") {
                operations.push(self.parse_p5_op_sig(self.prev_span().0, false, context)?);
            } else if self.eat_kw("relation") {
                relations.push(self.parse_p5_rel_sig(self.prev_span().0, context)?);
            } else if self.eat_kw("slot") {
                let sl_start = self.prev_span().0;
                let sl_name = self.ident()?;
                self.reject_forbidden_ident(&sl_name, context)?;
                self.expect_sym(":")?;
                let sort = self.ident()?;
                self.reject_forbidden_ident(&sort, context)?;
                self.expect_kw("in")?;
                let domain_values = self.parse_p5_symbol_list(context)?;
                self.expect_sym(";")?;
                slots.push(RawPartialSlotDecl {
                    name: sl_name,
                    sort,
                    domain_values,
                    span: (sl_start, self.prev_end()),
                });
            } else if self.eat_kw("background") {
                background_constraints.extend(self.parse_partial_background(context)?);
            } else if self.eat_kw("record") {
                records.push(self.parse_partial_record(self.prev_span().0, context)?);
            } else if self.eat_kw("max_completions") {
                if max_completions.is_some() {
                    return self.err("duplicate `max_completions` clause in `finite_table`");
                }
                self.expect_sym("=")?;
                let n = self.parse_usize_token("`max_completions`")?;
                self.expect_sym(";")?;
                max_completions = Some(n);
            } else if self.is_kw("eval_law") {
                return self.p4_syntax_err(
                    self.here(),
                    "`eval_law` must be declared at top level of `shigure partial`, separated from `finite_table`",
                );
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawFinitePartial {
            sorts,
            operations,
            relations,
            slots,
            background_constraints,
            records,
            max_completions,
            span: (start, self.prev_end()),
        })
    }

    fn parse_affine_row(&mut self, start: usize, context: &str) -> PResult<RawAffineRow, E> {
        let id = self.ident()?;
        self.reject_forbidden_ident(&id, context)?;
        self.expect_sym(":")?;
        let coeffs = self.parse_p4_coord_value_list()?;
        self.expect_sym("=")?;
        let rhs = self.parse_p4_coord_value()?;
        self.expect_sym(";")?;
        Ok(RawAffineRow {
            id,
            coeffs,
            rhs,
            span: (start, self.prev_end()),
        })
    }

    fn parse_affine_partial(&mut self, start: usize) -> PResult<RawAffinePartial, E> {
        let context = "`shigure partial` affine";
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut coord_names: Option<Vec<Ident>> = None;
        let mut x0: Option<Vec<RawMemberCoordValue>> = None;
        let mut direction_t: Option<Vec<Vec<RawMemberCoordValue>>> = None;
        let mut background_rows = Vec::new();
        let mut record_rows = Vec::new();
        let mut eval_equations = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `affine`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("coords") {
                if coord_names.is_some() {
                    return self.err("duplicate `coords` clause in `affine`");
                }
                coord_names = Some(self.parse_p4_ident_list(context)?);
                self.expect_sym(";")?;
            } else if self.eat_kw("x0") {
                if x0.is_some() {
                    return self.err("duplicate `x0` clause in `affine`");
                }
                self.expect_sym("=")?;
                x0 = Some(self.parse_p4_coord_value_list()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("direction_t") {
                if direction_t.is_some() {
                    return self.err("duplicate `direction_t` clause in `affine`");
                }
                self.expect_sym("=")?;
                direction_t = Some(self.parse_p5_coord_matrix()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("background_row") {
                background_rows.push(self.parse_affine_row(self.prev_span().0, context)?);
            } else if self.eat_kw("record_row") {
                record_rows.push(self.parse_affine_row(self.prev_span().0, context)?);
            } else if self.eat_kw("eval_eq") {
                eval_equations.push(self.parse_affine_row(self.prev_span().0, context)?);
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(domain) = domain else {
            return self.p4_syntax_err(span, "`affine` block requires `domain`");
        };
        Ok(RawAffinePartial {
            domain,
            coord_names: coord_names.unwrap_or_default(),
            x0: x0.unwrap_or_default(),
            direction_t: direction_t.unwrap_or_default(),
            background_rows,
            record_rows,
            eval_equations,
            span,
        })
    }

    pub(super) fn parse_shigure_partial(&mut self, start: usize) -> PResult<RawPartialTask, E> {
        self.expect_kw("partial")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`shigure partial`")?;
        self.expect_sym("{")?;

        let mut origins = Vec::new();
        let mut representation: Option<RawPartialRepresentation> = None;
        let mut eval_laws = Vec::new();
        let mut quantifier_spec = None;
        let mut open_domain = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin("`shigure partial`")?);
            } else if self.eat_kw("finite_table") {
                if representation.is_some() {
                    return self.err("duplicate representation block in `shigure partial`");
                }
                representation = Some(RawPartialRepresentation::FiniteTable(
                    self.parse_finite_partial(self.prev_span().0)?,
                ));
            } else if self.eat_kw("affine") {
                if representation.is_some() {
                    return self.err("duplicate representation block in `shigure partial`");
                }
                representation = Some(RawPartialRepresentation::Affine(
                    self.parse_affine_partial(self.prev_span().0)?,
                ));
            } else if self.eat_kw("unsupported") {
                if representation.is_some() {
                    return self.err("duplicate representation block in `shigure partial`");
                }
                let u_start = self.prev_span().0;
                let description = self.string()?;
                self.expect_sym(";")?;
                representation = Some(RawPartialRepresentation::UnsupportedClass {
                    description,
                    span: (u_start, self.prev_end()),
                });
            } else if self.eat_kw("eval_law") {
                eval_laws.push(
                    self.parse_partial_eval_law(self.prev_span().0, "`shigure partial` eval_law")?,
                );
            } else if self.eat_kw("quantifier") {
                if quantifier_spec.is_some() {
                    return self.err("duplicate `quantifier` block in `shigure partial`");
                }
                quantifier_spec = Some(self.parse_quantifier_spec(self.prev_span().0)?);
            } else if self.eat_kw("open_domain") {
                if open_domain.is_some() {
                    return self.err("duplicate `open_domain` block in `shigure partial`");
                }
                open_domain = Some(self.parse_open_domain(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`shigure partial`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        if origins.is_empty() {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure partial` requires at least one `origin` clause",
            ))
            .into());
        }
        let Some(representation) = representation else {
            return self.p4_syntax_err(
                span,
                "`shigure partial` requires a representation block (`finite_table`, `affine`, or `unsupported`)",
            );
        };
        Ok(RawPartialTask {
            name,
            origins,
            representation,
            eval_laws,
            quantifier_spec,
            open_domain,
            span,
        })
    }
}
