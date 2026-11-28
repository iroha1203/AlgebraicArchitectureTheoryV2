//! `shigure revision`・`shigure multisource` 宣言の構文解析（AC2）。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::RawMemberCoordValue;
use super::ast_phase5_rev::*;
use super::parser::PResult;
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    fn parse_p5_coord_decl(&mut self, start: usize, context: &str) -> PResult<RawRevisionCoord, E> {
        let id = self.ident()?;
        self.reject_forbidden_ident(&id, context)?;
        self.expect_kw("in")?;
        let domain_values = self.parse_shigure_lit_bracket_list()?;
        self.expect_sym(";")?;
        Ok(RawRevisionCoord {
            id,
            domain_values,
            span: (start, self.prev_end()),
        })
    }

    fn parse_p5_linear_terms(
        &mut self,
        context: &str,
    ) -> PResult<Vec<(ShigureScalarLit, Ident)>, E> {
        self.expect_sym("[")?;
        let mut terms = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                self.expect_sym("(")?;
                let coeff = self.parse_shigure_scalar_lit()?;
                self.expect_sym(",")?;
                let coord = self.ident()?;
                self.reject_forbidden_ident(&coord, context)?;
                self.expect_sym(")")?;
                terms.push((coeff, coord));
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(terms)
    }

    fn parse_p5_constraint(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawRevisionConstraint, E> {
        let id = self.ident()?;
        self.reject_forbidden_ident(&id, context)?;
        self.expect_kw("support")?;
        let support = self.parse_p4_ident_list(context)?;
        self.expect_sym(":")?;
        let predicate = if self.eat_kw("eq") {
            self.expect_sym("(")?;
            let a = self.ident()?;
            self.reject_forbidden_ident(&a, context)?;
            self.expect_sym(",")?;
            let b = self.ident()?;
            self.reject_forbidden_ident(&b, context)?;
            self.expect_sym(")")?;
            RawRevisionPredicate::Equality(a, b)
        } else if self.eat_kw("linear_zero") {
            RawRevisionPredicate::LinearZero {
                terms: self.parse_p5_linear_terms(context)?,
            }
        } else if self.eat_kw("allowed_tuples") {
            self.expect_sym("(")?;
            let coords = self.parse_p4_ident_list(context)?;
            self.expect_sym(",")?;
            let tuples = self.parse_lit_matrix()?;
            self.expect_sym(")")?;
            RawRevisionPredicate::AllowedTuples { coords, tuples }
        } else {
            return self.err(format!(
                "expected `eq(...)`, `linear_zero [...]`, or `allowed_tuples(...)` in {context}"
            ));
        };
        self.expect_sym(";")?;
        Ok(RawRevisionConstraint {
            id,
            support,
            predicate,
            span: (start, self.prev_end()),
        })
    }

    fn parse_revision_side(&mut self, start: usize, context: &str) -> PResult<RawRevisionSide, E> {
        self.expect_sym("{")?;
        let mut assignments = Vec::new();
        let mut extra_constraints = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("assign") {
                let a_start = self.prev_span().0;
                let coord = self.ident()?;
                self.reject_forbidden_ident(&coord, context)?;
                self.expect_sym("=")?;
                let val = self.parse_p4_coord_value()?;
                self.expect_sym(";")?;
                assignments.push((coord, val, (a_start, self.prev_end())));
            } else if self.eat_kw("constraint") {
                extra_constraints.push(self.parse_p5_constraint(self.prev_span().0, context)?);
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawRevisionSide {
            assignments,
            extra_constraints,
            span: (start, self.prev_end()),
        })
    }

    fn parse_revision_probe(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawRevisionEvalProbe, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_kw("support")?;
        let support = self.parse_p4_ident_list(context)?;
        self.expect_sym(":")?;
        let (antecedent_coord, antecedent_value) = if self.eat_kw("if") {
            let ac = self.ident()?;
            self.reject_forbidden_ident(&ac, context)?;
            self.expect_sym("=")?;
            let av = self.parse_shigure_scalar_lit()?;
            self.expect_sym("=>")?;
            (Some(ac), Some(av))
        } else {
            (None, None)
        };
        let target_coord = self.ident()?;
        self.reject_forbidden_ident(&target_coord, context)?;
        self.expect_sym("=")?;
        let expected_value = self.parse_shigure_scalar_lit()?;
        self.expect_sym(";")?;
        Ok(RawRevisionEvalProbe {
            name,
            support,
            target_coord,
            expected_value,
            antecedent_coord,
            antecedent_value,
            span: (start, self.prev_end()),
        })
    }

    fn parse_snf_revision(&mut self, start: usize) -> PResult<RawSnfRevision, E> {
        let context = "`shigure revision` snf";
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut num_cols: Option<usize> = None;
        let mut common_operator: Option<Vec<Vec<RawMemberCoordValue>>> = None;
        let mut operator_before: Option<Vec<Vec<RawMemberCoordValue>>> = None;
        let mut operator_after: Option<Vec<Vec<RawMemberCoordValue>>> = None;
        let mut rhs_before: Option<Vec<RawMemberCoordValue>> = None;
        let mut rhs_after: Option<Vec<RawMemberCoordValue>> = None;
        let mut operator_unobserved = Vec::new();
        let mut force_reuse_existing_snf = None;
        let mut origin_label_only = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `snf`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("num_cols") {
                if num_cols.is_some() {
                    return self.err("duplicate `num_cols` clause in `snf`");
                }
                self.expect_sym("=")?;
                num_cols = Some(self.parse_usize_token("`num_cols`")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("common_operator") {
                if common_operator.is_some() {
                    return self.err("duplicate `common_operator` clause in `snf`");
                }
                self.expect_sym("=")?;
                common_operator = Some(self.parse_p5_coord_matrix()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("operator_before") {
                if operator_before.is_some() {
                    return self.err("duplicate `operator_before` clause in `snf`");
                }
                self.expect_sym("=")?;
                operator_before = Some(self.parse_p5_coord_matrix()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("operator_after") {
                if operator_after.is_some() {
                    return self.err("duplicate `operator_after` clause in `snf`");
                }
                self.expect_sym("=")?;
                operator_after = Some(self.parse_p5_coord_matrix()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("rhs_before") {
                if rhs_before.is_some() {
                    return self.err("duplicate `rhs_before` clause in `snf`");
                }
                self.expect_sym("=")?;
                rhs_before = Some(self.parse_p4_coord_value_list()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("rhs_after") {
                if rhs_after.is_some() {
                    return self.err("duplicate `rhs_after` clause in `snf`");
                }
                self.expect_sym("=")?;
                rhs_after = Some(self.parse_p4_coord_value_list()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("operator_unobserved") {
                let slots = self.parse_p4_ident_list(context)?;
                self.expect_sym(";")?;
                operator_unobserved.extend(slots);
            } else if self.eat_kw("force_reuse") {
                if force_reuse_existing_snf.is_some() {
                    return self.err("duplicate `force_reuse` clause in `snf`");
                }
                self.expect_sym("=")?;
                force_reuse_existing_snf = Some(self.parse_shigure_bool("`snf` force_reuse")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("origin_label_only") {
                if origin_label_only.is_some() {
                    return self.err("duplicate `origin_label_only` clause in `snf`");
                }
                self.expect_sym("=")?;
                origin_label_only = Some(self.parse_shigure_bool("`snf` origin_label_only")?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let operator = match (common_operator, operator_before, operator_after) {
            (Some(common), None, None) => RawSnfOperatorMode::Common(common),
            (None, Some(before), Some(after)) => RawSnfOperatorMode::Split { before, after },
            (Some(_), _, _) => {
                return self.p4_syntax_err(
                    span,
                    "`snf` cannot combine `common_operator` with `operator_before`/`operator_after`",
                );
            }
            _ => {
                return self.p4_syntax_err(
                    span,
                    "`snf` requires either `common_operator` or both `operator_before` and `operator_after`",
                );
            }
        };
        let (Some(domain), Some(num_cols), Some(rhs_before), Some(rhs_after)) =
            (domain, num_cols, rhs_before, rhs_after)
        else {
            return self.p4_syntax_err(
                span,
                "`snf` requires `domain`, `num_cols`, `rhs_before`, and `rhs_after`",
            );
        };
        Ok(RawSnfRevision {
            domain,
            num_cols,
            operator,
            rhs_before,
            rhs_after,
            operator_unobserved,
            force_reuse_existing_snf: force_reuse_existing_snf.unwrap_or(false),
            origin_label_only: origin_label_only.unwrap_or(false),
            span,
        })
    }

    pub(super) fn parse_shigure_revision(&mut self, start: usize) -> PResult<RawRevisionTask, E> {
        let context = "`shigure revision`";
        self.expect_kw("revision")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym("{")?;

        let mut kind: Option<ShigureRevisionKind> = None;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut origins = Vec::new();
        let mut coords = Vec::new();
        let mut shared_constraints = Vec::new();
        let mut before: Option<RawRevisionSide> = None;
        let mut after: Option<RawRevisionSide> = None;
        let mut explicit_delta_coords = Vec::new();
        let mut probes = Vec::new();
        let mut snf: Option<RawSnfRevision> = None;
        let mut max_completions: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("kind") {
                if kind.is_some() {
                    return self.err("duplicate `kind` clause in `shigure revision`");
                }
                self.expect_sym("=")?;
                if self.eat_kw("extension") {
                    kind = Some(ShigureRevisionKind::Extension);
                } else if self.eat_kw("span") {
                    kind = Some(ShigureRevisionKind::Span);
                } else {
                    return self.err("expected `extension` or `span` after `kind =`");
                }
                self.expect_sym(";")?;
            } else if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure revision`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin(context)?);
            } else if self.eat_kw("coord") {
                coords.push(self.parse_p5_coord_decl(self.prev_span().0, context)?);
            } else if self.eat_kw("shared_constraint") {
                shared_constraints.push(self.parse_p5_constraint(self.prev_span().0, context)?);
            } else if self.eat_kw("before") {
                if before.is_some() {
                    return self.err("duplicate `before` block in `shigure revision`");
                }
                before = Some(self.parse_revision_side(self.prev_span().0, "`revision` before")?);
            } else if self.eat_kw("after") {
                if after.is_some() {
                    return self.err("duplicate `after` block in `shigure revision`");
                }
                after = Some(self.parse_revision_side(self.prev_span().0, "`revision` after")?);
            } else if self.eat_kw("explicit_delta") {
                let list = self.parse_p4_ident_list(context)?;
                self.expect_sym(";")?;
                explicit_delta_coords.extend(list);
            } else if self.eat_kw("probe") {
                probes.push(self.parse_revision_probe(self.prev_span().0, context)?);
            } else if self.eat_kw("snf") {
                if snf.is_some() {
                    return self.err("duplicate `snf` block in `shigure revision`");
                }
                snf = Some(self.parse_snf_revision(self.prev_span().0)?);
            } else if self.eat_kw("max_completions") {
                if max_completions.is_some() {
                    return self.err("duplicate `max_completions` clause in `shigure revision`");
                }
                self.expect_sym("=")?;
                let n = self.parse_usize_token("`max_completions`")?;
                self.expect_sym(";")?;
                max_completions = Some(n);
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        if origins.is_empty() {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure revision` requires at least one `origin` clause",
            ))
            .into());
        }
        let Some(kind) = kind else {
            return self
                .p4_syntax_err(span, "`shigure revision` requires `kind = extension|span;`");
        };
        let Some(domain) = domain else {
            return self.p4_syntax_err(span, "`shigure revision` requires a `domain` clause");
        };
        Ok(RawRevisionTask {
            name,
            kind,
            domain,
            origins,
            coords,
            shared_constraints,
            before: before.unwrap_or_default(),
            after: after.unwrap_or_default(),
            explicit_delta_coords,
            probes,
            snf,
            max_completions,
            span,
        })
    }

    fn parse_multisource_source(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawSourcePresentation, E> {
        let source_id = self.ident()?;
        self.reject_forbidden_ident(&source_id, context)?;
        self.expect_sym("{")?;
        let mut origin: Option<RawOriginRef> = None;
        let mut assignments = Vec::new();
        let mut forbidden_values = Vec::new();
        let mut extra_constraints = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                if origin.is_some() {
                    return self.err("duplicate `origin` in `multisource` source");
                }
                origin = Some(self.parse_shigure_origin(context)?);
            } else if self.eat_kw("assign") {
                let a_start = self.prev_span().0;
                let coord = self.ident()?;
                self.reject_forbidden_ident(&coord, context)?;
                self.expect_sym("=")?;
                let val = self.parse_p4_coord_value()?;
                self.expect_sym(";")?;
                assignments.push((coord, val, (a_start, self.prev_end())));
            } else if self.eat_kw("forbidden") {
                let f_start = self.prev_span().0;
                let coord = self.ident()?;
                self.reject_forbidden_ident(&coord, context)?;
                self.expect_sym("=")?;
                let val = self.parse_p4_coord_value()?;
                self.expect_sym(";")?;
                forbidden_values.push((coord, val, (f_start, self.prev_end())));
            } else if self.eat_kw("constraint") {
                extra_constraints.push(self.parse_p5_constraint(self.prev_span().0, context)?);
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(origin) = origin else {
            return self.p4_syntax_err(span, "`source` requires an explicit `origin` clause");
        };
        Ok(RawSourcePresentation {
            source_id,
            origin,
            assignments,
            forbidden_values,
            extra_constraints,
            span,
        })
    }

    fn parse_multisource_candidate(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawCandidateRecord, E> {
        let id = self.ident()?;
        self.reject_forbidden_ident(&id, context)?;
        self.expect_sym("{")?;
        let mut origin: Option<RawOriginRef> = None;
        let mut coord: Option<Ident> = None;
        let mut value: Option<RawMemberCoordValue> = None;
        let mut cost: Option<(ShigureScalarLit, Span)> = None;
        let mut verified_actual_value: Option<(RawMemberCoordValue, Span)> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                if origin.is_some() {
                    return self.err("duplicate `origin` in `candidate`");
                }
                origin = Some(self.parse_shigure_origin(context)?);
            } else if self.eat_kw("coord") {
                if coord.is_some() {
                    return self.err("duplicate `coord` in `candidate`");
                }
                self.expect_sym("=")?;
                let c = self.ident()?;
                self.reject_forbidden_ident(&c, context)?;
                self.expect_sym(";")?;
                coord = Some(c);
            } else if self.eat_kw("value") {
                if value.is_some() {
                    return self.err("duplicate `value` in `candidate`");
                }
                self.expect_sym("=")?;
                value = Some(self.parse_p4_coord_value()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("cost") {
                if cost.is_some() {
                    return self.err("duplicate `cost` in `candidate`");
                }
                let c_start = self.prev_span().0;
                self.expect_sym("=")?;
                let lit = self.parse_shigure_scalar_lit()?;
                self.expect_sym(";")?;
                cost = Some((lit, (c_start, self.prev_end())));
            } else if self.eat_kw("verified_actual") {
                if verified_actual_value.is_some() {
                    return self.err("duplicate `verified_actual` in `candidate`");
                }
                let v_start = self.prev_span().0;
                self.expect_sym("=")?;
                let v = self.parse_p4_coord_value()?;
                self.expect_sym(";")?;
                verified_actual_value = Some((v, (v_start, self.prev_end())));
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(origin), Some(coord), Some(value)) = (origin, coord, value) else {
            return self.p4_syntax_err(span, "`candidate` requires `origin`, `coord`, and `value`");
        };
        Ok(RawCandidateRecord {
            id,
            coord,
            value,
            cost,
            origin,
            verified_actual_value,
            span,
        })
    }

    fn parse_multisource_support_goal(
        &mut self,
        start: usize,
        context: &str,
    ) -> PResult<RawSupportGoalSpec, E> {
        self.expect_sym("{")?;
        let mut trusted_assignments = Vec::new();
        let mut candidates = Vec::new();
        let mut goal: Option<RawSupportGoalFormula> = None;
        let mut expected_truth: Option<bool> = None;
        let mut check_post_adoption_stability = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("trusted") {
                trusted_assignments.extend(self.parse_p4_coord_scalar_block(context)?);
            } else if self.eat_kw("candidate") {
                candidates.push(self.parse_multisource_candidate(self.prev_span().0, context)?);
            } else if self.eat_kw("goal") {
                if goal.is_some() {
                    return self.err("duplicate `goal` in `support_goal`");
                }
                self.expect_sym("=")?;
                let g_start = self.here().0;
                if self.eat_kw("eq") {
                    self.expect_sym("(")?;
                    let a = self.ident()?;
                    self.reject_forbidden_ident(&a, context)?;
                    self.expect_sym(",")?;
                    let b = self.ident()?;
                    self.reject_forbidden_ident(&b, context)?;
                    self.expect_sym(")")?;
                    self.expect_sym(";")?;
                    goal = Some(RawSupportGoalFormula::CoordEquality(
                        a,
                        b,
                        (g_start, self.prev_end()),
                    ));
                } else if self.eat_kw("eq_const") {
                    self.expect_sym("(")?;
                    let c = self.ident()?;
                    self.reject_forbidden_ident(&c, context)?;
                    self.expect_sym(",")?;
                    let v = self.parse_shigure_scalar_lit()?;
                    self.expect_sym(")")?;
                    self.expect_sym(";")?;
                    goal = Some(RawSupportGoalFormula::CoordEqualsConst(
                        c,
                        v,
                        (g_start, self.prev_end()),
                    ));
                } else {
                    return self.err("expected `eq(a, b)` or `eq_const(c, v)` after `goal =`");
                }
            } else if self.eat_kw("expected_truth") {
                if expected_truth.is_some() {
                    return self.err("duplicate `expected_truth` in `support_goal`");
                }
                self.expect_sym("=")?;
                expected_truth = Some(self.parse_shigure_bool("`support_goal` expected_truth")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("check_stability") {
                if check_post_adoption_stability.is_some() {
                    return self.err("duplicate `check_stability` in `support_goal`");
                }
                self.expect_sym("=")?;
                check_post_adoption_stability =
                    Some(self.parse_shigure_bool("`support_goal` check_stability")?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(goal), Some(expected_truth)) = (goal, expected_truth) else {
            return self.p4_syntax_err(span, "`support_goal` requires `goal` and `expected_truth`");
        };
        Ok(RawSupportGoalSpec {
            trusted_assignments,
            candidates,
            goal,
            expected_truth,
            check_post_adoption_stability: check_post_adoption_stability.unwrap_or(false),
            span,
        })
    }

    pub(super) fn parse_shigure_multisource(
        &mut self,
        start: usize,
    ) -> PResult<RawMultisourceTask, E> {
        let context = "`shigure multisource`";
        self.expect_kw("multisource")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym("{")?;

        let mut domain: Option<RawCoeffDomain> = None;
        let mut origins = Vec::new();
        let mut coords = Vec::new();
        let mut background_constraints = Vec::new();
        let mut sources = Vec::new();
        let mut support_goal = None;
        let mut max_sources_subset_steps: Option<usize> = None;
        let mut max_results: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure multisource`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin(context)?);
            } else if self.eat_kw("coord") {
                coords.push(self.parse_p5_coord_decl(self.prev_span().0, context)?);
            } else if self.eat_kw("background_constraint") {
                background_constraints.push(self.parse_p5_constraint(self.prev_span().0, context)?);
            } else if self.eat_kw("source") {
                sources.push(self.parse_multisource_source(self.prev_span().0, context)?);
            } else if self.eat_kw("support_goal") {
                if support_goal.is_some() {
                    return self.err("duplicate `support_goal` block in `shigure multisource`");
                }
                support_goal =
                    Some(self.parse_multisource_support_goal(self.prev_span().0, context)?);
            } else if self.eat_kw("max_steps") {
                if max_sources_subset_steps.is_some() {
                    return self.err("duplicate `max_steps` clause in `shigure multisource`");
                }
                self.expect_sym("=")?;
                max_sources_subset_steps = Some(self.parse_usize_token("`max_steps`")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("max_results") {
                if max_results.is_some() {
                    return self.err("duplicate `max_results` clause in `shigure multisource`");
                }
                self.expect_sym("=")?;
                max_results = Some(self.parse_usize_token("`max_results`")?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown(context)?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        if origins.is_empty() {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure multisource` requires at least one `origin` clause",
            ))
            .into());
        }
        let Some(domain) = domain else {
            return self.p4_syntax_err(span, "`shigure multisource` requires a `domain` clause");
        };
        Ok(RawMultisourceTask {
            name,
            domain,
            origins,
            coords,
            background_constraints,
            sources,
            support_goal,
            max_sources_subset_steps,
            max_results,
            span,
        })
    }
}
