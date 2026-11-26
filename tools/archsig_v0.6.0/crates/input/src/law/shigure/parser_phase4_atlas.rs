//! `shigure atlas` 宣言の構文解析（Phase 4 / AC2）。

use super::ast_phase3::RawMemberCoordValue;
use super::ast_phase4_diag_atlas::*;
use super::parser::PResult;
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::parser::Parser;
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    fn parse_graph_edge(&mut self, start: usize, context: &str) -> PResult<RawGraphEdge, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym("(")?;
        let from = self.ident()?;
        self.expect_sym("->")?;
        let to = self.ident()?;
        self.expect_sym(")")?;
        self.expect_kw("offset")?;
        let offset = self.parse_p4_coord_value()?;
        self.expect_sym(";")?;
        Ok(RawGraphEdge {
            name,
            from,
            to,
            offset,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_atlas(&mut self, start: usize) -> PResult<RawAtlasTask, E> {
        self.expect_kw("atlas")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`shigure atlas`")?;
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut origins = Vec::new();
        let mut vertices: Option<Vec<Ident>> = None;
        let mut edges = Vec::new();
        let mut mu: Option<(RawMemberCoordValue, Span)> = None;
        let mut base_lambdas: Option<Vec<(Ident, RawMemberCoordValue, Span)>> = None;
        let mut allowed_vertices: Option<Vec<Ident>> = None;
        let mut allowed_edges: Option<Vec<Ident>> = None;
        let mut compare_to_q: Option<bool> = None;
        let mut refinement: Option<Box<RawAtlasRefinement>> = None;
        let mut extended_language_check: Option<RawExtendedLanguageCheck> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure atlas`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin("`shigure atlas`")?);
            } else if self.eat_kw("vertices") {
                if vertices.is_some() {
                    return self.err("duplicate `vertices` clause in `shigure atlas`");
                }
                vertices = Some(self.parse_p4_ident_list("`shigure atlas` vertices")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("edge") {
                edges.push(self.parse_graph_edge(self.prev_span().0, "`shigure atlas` edge")?);
            } else if self.eat_kw("mu") {
                if mu.is_some() {
                    return self.err("duplicate `mu` clause in `shigure atlas`");
                }
                let m_start = self.prev_span().0;
                let val = self.parse_p4_coord_value()?;
                self.expect_sym(";")?;
                mu = Some((val, (m_start, self.prev_end())));
            } else if self.eat_kw("base_lambdas") {
                if base_lambdas.is_some() {
                    return self.err("duplicate `base_lambdas` block in `shigure atlas`");
                }
                base_lambdas =
                    Some(self.parse_p4_coord_scalar_block("`shigure atlas` base_lambdas")?);
            } else if self.eat_kw("allowed_vertices") {
                if allowed_vertices.is_some() {
                    return self.err("duplicate `allowed_vertices` clause in `shigure atlas`");
                }
                allowed_vertices =
                    Some(self.parse_p4_ident_list("`shigure atlas` allowed_vertices")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("allowed_edges") {
                if allowed_edges.is_some() {
                    return self.err("duplicate `allowed_edges` clause in `shigure atlas`");
                }
                allowed_edges = Some(self.parse_p4_ident_list("`shigure atlas` allowed_edges")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("compare_to_q") {
                if compare_to_q.is_some() {
                    return self.err("duplicate `compare_to_q` clause in `shigure atlas`");
                }
                let flag = self.parse_shigure_bool("`shigure atlas`")?;
                self.expect_sym(";")?;
                compare_to_q = Some(flag);
            } else if self.eat_kw("refinement") {
                if refinement.is_some() {
                    return self.err("duplicate `refinement` block in `shigure atlas`");
                }
                refinement = Some(Box::new(self.parse_atlas_refinement(self.prev_span().0)?));
            } else if self.eat_kw("extended_language_check") {
                if extended_language_check.is_some() {
                    return self
                        .err("duplicate `extended_language_check` block in `shigure atlas`");
                }
                extended_language_check =
                    Some(self.parse_extended_language_check(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`shigure atlas`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(domain) = domain else {
            return self.p4_syntax_err(span, "`shigure atlas` requires a `domain` clause");
        };
        if origins.is_empty() {
            return self.p4_syntax_err(
                span,
                "`shigure atlas` requires at least one `origin` clause",
            );
        }
        let Some(vertices) = vertices else {
            return self.p4_syntax_err(span, "`shigure atlas` requires a `vertices` clause");
        };
        let Some(mu) = mu else {
            return self.p4_syntax_err(span, "`shigure atlas` requires a `mu` clause");
        };
        let Some(base_lambdas) = base_lambdas else {
            return self.p4_syntax_err(span, "`shigure atlas` requires a `base_lambdas` block");
        };
        Ok(RawAtlasTask {
            name,
            domain,
            origins,
            vertices,
            edges,
            mu,
            base_lambdas,
            allowed_vertices: allowed_vertices.unwrap_or_default(),
            allowed_edges: allowed_edges.unwrap_or_default(),
            compare_to_q: compare_to_q.unwrap_or(false),
            refinement,
            extended_language_check,
            span,
        })
    }

    fn parse_atlas_refinement(&mut self, start: usize) -> PResult<RawAtlasRefinement, E> {
        self.expect_sym("{")?;
        let mut fine_vertices = None;
        let mut fine_edges = Vec::new();
        let mut vertex_map = None;
        let mut edge_map = None;
        let mut common_sources = None;
        let mut coarse_reading = None;
        let mut fine_reading = None;
        let mut coarse_nerve = None;
        let mut fine_nerve = None;
        let mut nerve_chart_map = None;
        let mut nerve_edge_map = None;
        let mut nerve_face_map = None;
        let mut eval_condition = None;
        let mut forgetful_reading = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("fine_vertices") {
                if fine_vertices.is_some() {
                    return self.err("duplicate `fine_vertices` in `refinement`");
                }
                fine_vertices = Some(self.parse_p4_ident_list("`refinement` fine_vertices")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("fine_edge") {
                fine_edges
                    .push(self.parse_graph_edge(self.prev_span().0, "`refinement` fine_edge")?);
            } else if self.eat_kw("vertex_map") {
                if vertex_map.is_some() {
                    return self.err("duplicate `vertex_map` in `refinement`");
                }
                vertex_map = Some(self.parse_p4_ident_arrow_block("`refinement` vertex_map")?);
            } else if self.eat_kw("edge_map") {
                if edge_map.is_some() {
                    return self.err("duplicate `edge_map` in `refinement`");
                }
                edge_map = Some(self.parse_p4_ident_opt_arrow_block("`refinement` edge_map")?);
            } else if self.eat_kw("common_sources") {
                if common_sources.is_some() {
                    return self.err("duplicate `common_sources` in `refinement`");
                }
                common_sources = Some(self.parse_p4_ident_list("`refinement` common_sources")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("coarse_reading") {
                if coarse_reading.is_some() {
                    return self.err("duplicate `coarse_reading` in `refinement`");
                }
                coarse_reading =
                    Some(self.parse_p4_ident_arrow_block("`refinement` coarse_reading")?);
            } else if self.eat_kw("fine_reading") {
                if fine_reading.is_some() {
                    return self.err("duplicate `fine_reading` in `refinement`");
                }
                fine_reading = Some(self.parse_p4_ident_arrow_block("`refinement` fine_reading")?);
            } else if self.eat_kw("coarse_nerve") {
                if coarse_nerve.is_some() {
                    return self.err("duplicate `coarse_nerve` in `refinement`");
                }
                coarse_nerve = Some(self.parse_supported_nerve(self.prev_span().0)?);
            } else if self.eat_kw("fine_nerve") {
                if fine_nerve.is_some() {
                    return self.err("duplicate `fine_nerve` in `refinement`");
                }
                fine_nerve = Some(self.parse_supported_nerve(self.prev_span().0)?);
            } else if self.eat_kw("nerve_chart_map") {
                if nerve_chart_map.is_some() {
                    return self.err("duplicate `nerve_chart_map` in `refinement`");
                }
                nerve_chart_map =
                    Some(self.parse_p4_ident_arrow_block("`refinement` nerve_chart_map")?);
            } else if self.eat_kw("nerve_edge_map") {
                if nerve_edge_map.is_some() {
                    return self.err("duplicate `nerve_edge_map` in `refinement`");
                }
                nerve_edge_map =
                    Some(self.parse_p4_ident_opt_arrow_block("`refinement` nerve_edge_map")?);
            } else if self.eat_kw("nerve_face_map") {
                if nerve_face_map.is_some() {
                    return self.err("duplicate `nerve_face_map` in `refinement`");
                }
                nerve_face_map =
                    Some(self.parse_p4_ident_opt_arrow_block("`refinement` nerve_face_map")?);
            } else if self.eat_kw("eval_condition") {
                if eval_condition.is_some() {
                    return self.err("duplicate `eval_condition` in `refinement`");
                }
                eval_condition = Some(self.parse_atlas_eval_condition(self.prev_span().0)?);
            } else if self.eat_kw("forgetful_reading") {
                if forgetful_reading.is_some() {
                    return self.err("duplicate `forgetful_reading` in `refinement`");
                }
                forgetful_reading = Some(self.parse_forgetful_reading(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`refinement`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (
            Some(fine_vertices),
            Some(vertex_map),
            Some(edge_map),
            Some(common_sources),
            Some(coarse_reading),
            Some(fine_reading),
            Some(coarse_nerve),
            Some(fine_nerve),
            Some(nerve_chart_map),
            Some(nerve_edge_map),
        ) = (
            fine_vertices,
            vertex_map,
            edge_map,
            common_sources,
            coarse_reading,
            fine_reading,
            coarse_nerve,
            fine_nerve,
            nerve_chart_map,
            nerve_edge_map,
        )
        else {
            return self.p4_syntax_err(
                span,
                "`refinement` requires `fine_vertices`, `vertex_map`, `edge_map`, `common_sources`, `coarse_reading`, `fine_reading`, `coarse_nerve`, `fine_nerve`, `nerve_chart_map`, and `nerve_edge_map`",
            );
        };
        Ok(RawAtlasRefinement {
            fine_vertices,
            fine_edges,
            vertex_map,
            edge_map,
            common_sources,
            coarse_reading,
            fine_reading,
            coarse_nerve,
            fine_nerve,
            nerve_chart_map,
            nerve_edge_map,
            nerve_face_map: nerve_face_map.unwrap_or_default(),
            eval_condition,
            forgetful_reading,
            span,
        })
    }

    fn parse_atlas_eval_condition(&mut self, start: usize) -> PResult<RawAtlasEvalCondition, E> {
        self.expect_sym("{")?;
        let mut evaluations = Vec::new();
        let mut equations = Vec::new();
        let mut invertibles = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("eval") {
                let e_start = self.prev_span().0;
                let name = self.ident()?;
                self.reject_forbidden_ident(&name, "`eval_condition` eval")?;
                self.expect_sym("=")?;
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                evaluations.push(RawNamedPoly {
                    name,
                    expr,
                    span: (e_start, self.prev_end()),
                });
            } else if self.eat_kw("equation") {
                equations.push(self.parse_shigure_named_eq("`eval_condition` equation")?);
            } else if self.eat_kw("invertible") {
                invertibles.push(self.parse_shigure_named_poly("`eval_condition` invertible")?);
            } else {
                self.reject_conclusion_or_unknown("`refinement` eval_condition")?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawAtlasEvalCondition {
            evaluations,
            equations,
            invertibles,
            span: (start, self.prev_end()),
        })
    }

    fn parse_forgetful_reading(&mut self, start: usize) -> PResult<RawForgetfulReading, E> {
        self.expect_sym("{")?;
        let mut forgotten_var = None;
        let mut eval_expr = None;
        let mut condition_eq = None;
        let mut sample_values = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("forgotten_var") {
                if forgotten_var.is_some() {
                    return self.err("duplicate `forgotten_var` in `forgetful_reading`");
                }
                let id = self.ident()?;
                self.reject_forbidden_ident(&id, "`forgetful_reading`")?;
                self.expect_sym(";")?;
                forgotten_var = Some(id);
            } else if self.eat_kw("eval_expr") {
                if eval_expr.is_some() {
                    return self.err("duplicate `eval_expr` in `forgetful_reading`");
                }
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                eval_expr = Some(expr);
            } else if self.eat_kw("condition_eq") {
                if condition_eq.is_some() {
                    return self.err("duplicate `condition_eq` in `forgetful_reading`");
                }
                self.expect_sym(":")?;
                let expr = self.parse_shigure_equation_poly()?;
                self.expect_sym(";")?;
                condition_eq = Some(expr);
            } else if self.eat_kw("sample_values") {
                if sample_values.is_some() {
                    return self.err("duplicate `sample_values` in `forgetful_reading`");
                }
                sample_values = Some(self.parse_p4_coord_value_list()?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`forgetful_reading`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(forgotten_var), Some(eval_expr), Some(condition_eq), Some(sample_values)) =
            (forgotten_var, eval_expr, condition_eq, sample_values)
        else {
            return self.p4_syntax_err(
                span,
                "`forgetful_reading` requires `forgotten_var`, `eval_expr`, `condition_eq`, and `sample_values`",
            );
        };
        Ok(RawForgetfulReading {
            forgotten_var,
            eval_expr,
            condition_eq,
            sample_values,
            span,
        })
    }

    fn parse_extended_language_check(
        &mut self,
        start: usize,
    ) -> PResult<RawExtendedLanguageCheck, E> {
        self.expect_sym("{")?;
        let mut state_vars = None;
        let mut adapter_map = None;
        let mut atomic_ops = Vec::new();
        let mut extended_checks = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("state_vars") {
                if state_vars.is_some() {
                    return self.err("duplicate `state_vars` in `extended_language_check`");
                }
                state_vars = Some(self.parse_p4_ident_list("`extended_language_check`")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("adapter_map") {
                if adapter_map.is_some() {
                    return self.err("duplicate `adapter_map` in `extended_language_check`");
                }
                adapter_map =
                    Some(self.parse_p4_poly_assign_block("`extended_language_check` adapter_map")?);
            } else if self.eat_kw("atomic_op") {
                atomic_ops.push(self.parse_atomic_op_compare(self.prev_span().0)?);
            } else if self.eat_kw("protocol_sequence") {
                extended_checks.push(self.parse_protocol_sequence(self.prev_span().0)?);
            } else if self.eat_kw("runtime_arg_op") {
                extended_checks.push(self.parse_runtime_arg_op(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`extended_language_check`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(state_vars), Some(adapter_map)) = (state_vars, adapter_map) else {
            return self.p4_syntax_err(
                span,
                "`extended_language_check` requires `state_vars` and `adapter_map`",
            );
        };
        Ok(RawExtendedLanguageCheck {
            state_vars,
            adapter_map,
            atomic_ops,
            extended_checks,
            span,
        })
    }

    fn parse_atomic_op_compare(&mut self, start: usize) -> PResult<RawAtomicOpCompare, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`atomic_op`")?;
        self.expect_sym("(")?;
        let mut arg_vars = Vec::new();
        if !self.is_sym(")") {
            loop {
                self.checkpoint_here()?;
                let a = self.ident()?;
                self.reject_forbidden_ident(&a, "`atomic_op` arg")?;
                arg_vars.push(a);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(")")?;
        self.expect_sym("{")?;
        let mut before_updates = None;
        let mut after_updates = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("before") {
                if before_updates.is_some() {
                    return self.err("duplicate `before` in `atomic_op`");
                }
                before_updates = Some(self.parse_p4_poly_assign_block("`atomic_op` before")?);
            } else if self.eat_kw("after") {
                if after_updates.is_some() {
                    return self.err("duplicate `after` in `atomic_op`");
                }
                after_updates = Some(self.parse_p4_poly_assign_block("`atomic_op` after")?);
            } else {
                self.reject_conclusion_or_unknown("`atomic_op`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(before_updates), Some(after_updates)) = (before_updates, after_updates) else {
            return self.p4_syntax_err(span, "`atomic_op` requires `before` and `after`");
        };
        Ok(RawAtomicOpCompare {
            name,
            arg_vars,
            before_updates,
            after_updates,
            span,
        })
    }

    fn parse_protocol_sequence(&mut self, start: usize) -> PResult<RawExtendedOperationCheck, E> {
        let name = self.string()?;
        self.expect_sym("{")?;
        let mut extended_state_vars = None;
        let mut initial_state = None;
        let mut before_steps = Vec::new();
        let mut after_steps = Vec::new();
        let mut before_read = None;
        let mut after_read = None;
        let mut intermediate_laws = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("extended_state_vars") {
                if extended_state_vars.is_some() {
                    return self.err("duplicate `extended_state_vars` in `protocol_sequence`");
                }
                extended_state_vars =
                    Some(self.parse_p4_ident_list("`protocol_sequence` extended_state_vars")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("initial_state") {
                if initial_state.is_some() {
                    return self.err("duplicate `initial_state` in `protocol_sequence`");
                }
                initial_state =
                    Some(self.parse_p4_coord_scalar_block("`protocol_sequence` initial_state")?);
            } else if self.eat_kw("before_step") {
                before_steps
                    .push(self.parse_p4_poly_assign_block("`protocol_sequence` before_step")?);
            } else if self.eat_kw("after_step") {
                after_steps
                    .push(self.parse_p4_poly_assign_block("`protocol_sequence` after_step")?);
            } else if self.eat_kw("before_read") {
                if before_read.is_some() {
                    return self.err("duplicate `before_read` in `protocol_sequence`");
                }
                before_read = Some(Box::new(self.parse_shigure_poly_expr()?));
                self.expect_sym(";")?;
            } else if self.eat_kw("after_read") {
                if after_read.is_some() {
                    return self.err("duplicate `after_read` in `protocol_sequence`");
                }
                after_read = Some(Box::new(self.parse_shigure_poly_expr()?));
                self.expect_sym(";")?;
            } else if self.eat_kw("intermediate_law") {
                intermediate_laws
                    .push(self.parse_shigure_named_eq("`protocol_sequence` intermediate_law")?);
            } else {
                self.reject_conclusion_or_unknown("`protocol_sequence`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(extended_state_vars), Some(initial_state), Some(before_read), Some(after_read)) =
            (extended_state_vars, initial_state, before_read, after_read)
        else {
            return self.p4_syntax_err(
                span,
                "`protocol_sequence` requires `extended_state_vars`, `initial_state`, `before_read`, and `after_read`",
            );
        };
        Ok(RawExtendedOperationCheck::ProtocolSequence {
            name,
            extended_state_vars,
            initial_state,
            before_steps,
            after_steps,
            before_read,
            after_read,
            intermediate_laws,
            span,
        })
    }

    fn parse_runtime_arg_op(&mut self, start: usize) -> PResult<RawExtendedOperationCheck, E> {
        let name = self.string()?;
        self.expect_sym("{")?;
        let mut before_updates = None;
        let mut after_updates = None;
        let mut sample_state = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("before") {
                if before_updates.is_some() {
                    return self.err("duplicate `before` in `runtime_arg_op`");
                }
                before_updates = Some(self.parse_p4_poly_assign_block("`runtime_arg_op` before")?);
            } else if self.eat_kw("after") {
                if after_updates.is_some() {
                    return self.err("duplicate `after` in `runtime_arg_op`");
                }
                after_updates = Some(self.parse_p4_poly_assign_block("`runtime_arg_op` after")?);
            } else if self.eat_kw("sample_state") {
                if sample_state.is_some() {
                    return self.err("duplicate `sample_state` in `runtime_arg_op`");
                }
                sample_state =
                    Some(self.parse_p4_coord_scalar_block("`runtime_arg_op` sample_state")?);
            } else {
                self.reject_conclusion_or_unknown("`runtime_arg_op`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(before_updates), Some(after_updates), Some(sample_state)) =
            (before_updates, after_updates, sample_state)
        else {
            return self.p4_syntax_err(
                span,
                "`runtime_arg_op` requires `before`, `after`, and `sample_state`",
            );
        };
        Ok(RawExtendedOperationCheck::RuntimeArgOp {
            name,
            before_updates,
            after_updates,
            sample_state,
            span,
        })
    }
}
