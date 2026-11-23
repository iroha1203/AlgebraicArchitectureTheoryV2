//! `shigure family` 宣言と共通 Phase 3 構文ヘルパの解析。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::*;
use super::parser::PResult;
use super::*;
use crate::law::ast::{Ident, Span};
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    pub(super) fn parse_shigure_bool(&mut self, context: &str) -> PResult<bool, E> {
        if self.eat_kw("true") {
            Ok(true)
        } else if self.eat_kw("false") {
            Ok(false)
        } else {
            self.err(format!("expected `true` or `false` in {context}"))
        }
    }

    pub(super) fn parse_shigure_origin(&mut self, context: &str) -> PResult<RawOriginRef, E> {
        let start = self.prev_span().0;
        let out = if self.eat_kw("static_analysis") {
            let id = self.string()?;
            RawOriginRef::Explicit {
                kind: ShigureOriginKind::StaticAnalysis,
                id,
                span: (start, self.prev_end()),
            }
        } else if self.eat_kw("runtime_observation") {
            let id = self.string()?;
            RawOriginRef::Explicit {
                kind: ShigureOriginKind::RuntimeObservation,
                id,
                span: (start, self.prev_end()),
            }
        } else if self.eat_kw("llm_candidate") {
            let id = self.string()?;
            RawOriginRef::Explicit {
                kind: ShigureOriginKind::LlmCandidate,
                id,
                span: (start, self.prev_end()),
            }
        } else if self.eat_kw("human_adopted") {
            let id = self.string()?;
            RawOriginRef::Explicit {
                kind: ShigureOriginKind::HumanAdopted,
                id,
                span: (start, self.prev_end()),
            }
        } else if self.eat_kw("archmap") {
            let id = self.string()?;
            RawOriginRef::ArchMap {
                id,
                span: (start, self.prev_end()),
            }
        } else {
            return self.err(format!(
                "expected `static_analysis`, `runtime_observation`, `llm_candidate`, `human_adopted`, or `archmap` after `origin` in {context}"
            ));
        };
        self.expect_sym(";")?;
        Ok(out)
    }

    pub(super) fn parse_shigure_poly_bracket_list(&mut self) -> PResult<Vec<ShigurePolyExpr>, E> {
        self.expect_sym("[")?;
        let mut items = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                items.push(self.parse_shigure_poly_expr()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(items)
    }

    pub(super) fn parse_shigure_lit_bracket_list(&mut self) -> PResult<Vec<ShigureScalarLit>, E> {
        self.expect_sym("[")?;
        let mut items = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                items.push(self.parse_shigure_scalar_lit()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(items)
    }

    pub(super) fn reject_forbidden_ident(&self, id: &Ident, context: &str) -> PResult<(), E> {
        if is_forbidden_conclusion_field(&id.name) {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                id.span,
                format!(
                    "conclusion injection is forbidden: `{}` cannot appear in {context}",
                    id.name
                ),
            ))
            .into());
        }
        Ok(())
    }

    pub(super) fn parse_shigure_named_eq(&mut self, context: &str) -> PResult<RawNamedPoly, E> {
        let start = self.prev_span().0;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym(":")?;
        let expr = self.parse_shigure_equation_poly()?;
        self.expect_sym(";")?;
        Ok(RawNamedPoly {
            name,
            expr,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_named_poly(&mut self, context: &str) -> PResult<RawNamedPoly, E> {
        let start = self.prev_span().0;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, context)?;
        self.expect_sym(":")?;
        let expr = self.parse_shigure_poly_expr()?;
        self.expect_sym(";")?;
        Ok(RawNamedPoly {
            name,
            expr,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_family(&mut self, start: usize) -> PResult<RawFamilySpec, E> {
        self.expect_kw("family")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut domain: Option<RawCoeffDomain> = None;
        let mut realizations: Option<RawRealizationFamily> = None;
        let mut candidates: Option<RawCandidateFamily> = None;
        let mut goodness: Option<RawGoodnessSpec> = None;
        let mut reading_comparison: Option<RawReadingComparison> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("domain") {
                if domain.is_some() {
                    return self.err("duplicate `domain` clause in `shigure family`");
                }
                domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("realizations") {
                if realizations.is_some() {
                    return self.err("duplicate `realizations` block in `shigure family`");
                }
                realizations = Some(self.parse_realization_family(self.prev_span().0)?);
            } else if self.eat_kw("candidates") {
                if candidates.is_some() {
                    return self.err("duplicate `candidates` block in `shigure family`");
                }
                candidates = Some(self.parse_candidate_family(self.prev_span().0)?);
            } else if self.eat_kw("goodness") {
                if goodness.is_some() {
                    return self.err("duplicate `goodness` block in `shigure family`");
                }
                goodness = Some(self.parse_goodness_spec(self.prev_span().0)?);
            } else if self.eat_kw("reading_comparison") {
                if reading_comparison.is_some() {
                    return self.err("duplicate `reading_comparison` block in `shigure family`");
                }
                reading_comparison = Some(self.parse_reading_comparison(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`shigure family`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(domain) = domain else {
            return self.syntax_err(span, "`shigure family` requires a `domain` clause");
        };
        let Some(realizations) = realizations else {
            return self.syntax_err(span, "`shigure family` requires a `realizations` block");
        };
        let Some(candidates) = candidates else {
            return self.syntax_err(span, "`shigure family` requires a `candidates` block");
        };
        let Some(goodness) = goodness else {
            return self.syntax_err(span, "`shigure family` requires a `goodness` block");
        };
        Ok(RawFamilySpec {
            name,
            domain,
            realizations,
            candidates,
            goodness,
            reading_comparison,
            span,
        })
    }

    fn syntax_err<T>(&self, span: Span, msg: &str) -> PResult<T, E> {
        Err(Box::new(Issue::law(Code::Syntax, span, msg)).into())
    }

    fn parse_ident_var_list(&mut self, context: &str) -> PResult<Vec<Ident>, E> {
        let vars = self.parse_ident_bracket_list()?;
        for v in &vars {
            self.reject_forbidden_ident(v, context)?;
        }
        self.expect_sym(";")?;
        Ok(vars)
    }

    fn parse_realization_family(&mut self, start: usize) -> PResult<RawRealizationFamily, E> {
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut u_vars: Option<Vec<Ident>> = None;
        let mut b_vars: Option<Vec<Ident>> = None;
        let mut reading_q: Option<Vec<ShigurePolyExpr>> = None;
        let mut members = Vec::new();
        let mut explicit_empty = false;
        let mut scheme: Option<RawRealizationSpace> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("u_vars") {
                if u_vars.is_some() {
                    return self.err("duplicate `u_vars` in `realizations`");
                }
                u_vars = Some(self.parse_ident_var_list("`realizations` u_vars")?);
            } else if self.eat_kw("b_vars") {
                if b_vars.is_some() {
                    return self.err("duplicate `b_vars` in `realizations`");
                }
                b_vars = Some(self.parse_ident_var_list("`realizations` b_vars")?);
            } else if self.eat_kw("reading_q") {
                if reading_q.is_some() {
                    return self.err("duplicate `reading_q` in `realizations`");
                }
                let exprs = self.parse_shigure_poly_bracket_list()?;
                self.expect_sym(";")?;
                reading_q = Some(exprs);
            } else if self.eat_kw("members") {
                if explicit_empty || !members.is_empty() || scheme.is_some() {
                    return self.err("conflicting `members` clause in `realizations`");
                }
                self.expect_sym("[")?;
                self.expect_sym("]")?;
                self.expect_sym(";")?;
                explicit_empty = true;
            } else if self.eat_kw("member") {
                if explicit_empty || scheme.is_some() {
                    return self.err("cannot mix `member` with `members []` or `scheme`");
                }
                members.push(self.parse_realization_member(self.prev_span().0)?);
            } else if self.eat_kw("scheme") {
                if explicit_empty || !members.is_empty() || scheme.is_some() {
                    return self.err("conflicting `scheme` block in `realizations`");
                }
                scheme = Some(self.parse_realization_scheme(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`realizations`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(u_vars) = u_vars else {
            return self.syntax_err(span, "`realizations` requires a `u_vars` clause");
        };
        let space = if let Some(s) = scheme {
            s
        } else if explicit_empty || !members.is_empty() {
            RawRealizationSpace::FiniteMembers {
                members,
                explicit_empty,
            }
        } else {
            return self.syntax_err(
                span,
                "`realizations` requires `members []`, `member` blocks, or a `scheme` block",
            );
        };
        Ok(RawRealizationFamily {
            name,
            u_vars,
            b_vars: b_vars.unwrap_or_default(),
            reading_q: reading_q.unwrap_or_default(),
            space,
            span,
        })
    }

    fn parse_member_set_coord(
        &mut self,
        context: &str,
    ) -> PResult<(Ident, RawMemberCoordValue, Span), E> {
        let start = self.prev_span().0;
        let var = self.ident()?;
        self.reject_forbidden_ident(&var, context)?;
        self.expect_sym("=")?;
        let val = if self.eat_kw("observed") {
            let f_start = self.here().0;
            let field = self.qname()?;
            RawMemberCoordValue::ObservedField {
                field,
                span: (f_start, self.prev_end()),
            }
        } else if self.eat_kw("missing") {
            RawMemberCoordValue::Missing(self.prev_span())
        } else {
            RawMemberCoordValue::Literal(self.parse_shigure_scalar_lit()?)
        };
        self.expect_sym(";")?;
        Ok((var, val, (start, self.prev_end())))
    }

    fn parse_realization_member(&mut self, start: usize) -> PResult<RawRealizationMember, E> {
        let id = self.ident()?;
        self.expect_sym("{")?;
        let mut assignments = Vec::new();
        let mut is_raw_candidate = None;
        let mut presentation = None;
        let mut origin = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                if origin.is_some() {
                    return self.err("duplicate `origin` clause in realization `member`");
                }
                origin = Some(self.parse_shigure_origin("realization `member`")?);
            } else if self.eat_kw("is_raw_candidate") {
                if is_raw_candidate.is_some() {
                    return self.err("duplicate `is_raw_candidate` in realization `member`");
                }
                let flag = self.parse_shigure_bool("realization `member`")?;
                self.expect_sym(";")?;
                is_raw_candidate = Some(flag);
            } else if self.eat_kw("presentation") {
                if presentation.is_some() {
                    return self.err("duplicate `presentation` in realization `member`");
                }
                presentation = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("set") {
                assignments.push(self.parse_member_set_coord("realization `member`")?);
            } else {
                self.reject_conclusion_or_unknown("realization `member`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(origin) = origin else {
            return self.syntax_err(span, "realization `member` requires an `origin` clause");
        };
        Ok(RawRealizationMember {
            id,
            assignments,
            is_raw_candidate: is_raw_candidate.unwrap_or(false),
            presentation,
            origin,
            span,
        })
    }

    fn parse_realization_scheme(&mut self, start: usize) -> PResult<RawRealizationSpace, E> {
        self.expect_sym("{")?;
        let mut equations = Vec::new();
        let mut invertibles = Vec::new();
        let mut is_raw_candidate = None;
        let mut origin = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                if origin.is_some() {
                    return self.err("duplicate `origin` clause in realization `scheme`");
                }
                origin = Some(self.parse_shigure_origin("realization `scheme`")?);
            } else if self.eat_kw("is_raw_candidate") {
                if is_raw_candidate.is_some() {
                    return self.err("duplicate `is_raw_candidate` in realization `scheme`");
                }
                let flag = self.parse_shigure_bool("realization `scheme`")?;
                self.expect_sym(";")?;
                is_raw_candidate = Some(flag);
            } else if self.eat_kw("equation") {
                equations.push(self.parse_shigure_named_eq("realization `scheme`")?);
            } else if self.eat_kw("invertible") {
                invertibles.push(self.parse_shigure_named_poly("realization `scheme`")?);
            } else {
                self.reject_conclusion_or_unknown("realization `scheme`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(origin) = origin else {
            return self.syntax_err(span, "realization `scheme` requires an `origin` clause");
        };
        Ok(RawRealizationSpace::PolynomialScheme {
            equations,
            invertibles,
            is_raw_candidate: is_raw_candidate.unwrap_or(false),
            origin,
            span,
        })
    }

    fn parse_candidate_family(&mut self, start: usize) -> PResult<RawCandidateFamily, E> {
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut c_vars: Option<Vec<Ident>> = None;
        let mut pi: Option<Vec<ShigurePolyExpr>> = None;
        let mut members = Vec::new();
        let mut explicit_empty = false;
        let mut scheme: Option<RawCandidateSpace> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("c_vars") {
                if c_vars.is_some() {
                    return self.err("duplicate `c_vars` in `candidates`");
                }
                c_vars = Some(self.parse_ident_var_list("`candidates` c_vars")?);
            } else if self.eat_kw("pi") {
                if pi.is_some() {
                    return self.err("duplicate `pi` in `candidates`");
                }
                let exprs = self.parse_shigure_poly_bracket_list()?;
                self.expect_sym(";")?;
                pi = Some(exprs);
            } else if self.eat_kw("members") {
                if explicit_empty || !members.is_empty() || scheme.is_some() {
                    return self.err("conflicting `members` clause in `candidates`");
                }
                self.expect_sym("[")?;
                self.expect_sym("]")?;
                self.expect_sym(";")?;
                explicit_empty = true;
            } else if self.eat_kw("member") {
                if explicit_empty || scheme.is_some() {
                    return self.err("cannot mix `member` with `members []` or `scheme`");
                }
                members.push(self.parse_candidate_member(self.prev_span().0)?);
            } else if self.eat_kw("scheme") {
                if explicit_empty || !members.is_empty() || scheme.is_some() {
                    return self.err("conflicting `scheme` block in `candidates`");
                }
                scheme = Some(self.parse_candidate_scheme(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`candidates`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let space = if let Some(s) = scheme {
            s
        } else if explicit_empty || !members.is_empty() {
            RawCandidateSpace::FiniteMembers {
                members,
                explicit_empty,
            }
        } else {
            return self.syntax_err(
                span,
                "`candidates` requires `members []`, `member` blocks, or a `scheme` block",
            );
        };
        Ok(RawCandidateFamily {
            name,
            c_vars: c_vars.unwrap_or_default(),
            pi: pi.unwrap_or_default(),
            space,
            span,
        })
    }

    fn parse_candidate_member(&mut self, start: usize) -> PResult<RawCandidateMember, E> {
        let id = self.ident()?;
        self.expect_sym("{")?;
        let mut assignments = Vec::new();
        let mut origin = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                if origin.is_some() {
                    return self.err("duplicate `origin` clause in candidate `member`");
                }
                origin = Some(self.parse_shigure_origin("candidate `member`")?);
            } else if self.eat_kw("set") {
                assignments.push(self.parse_member_set_coord("candidate `member`")?);
            } else {
                self.reject_conclusion_or_unknown("candidate `member`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(origin) = origin else {
            return self.syntax_err(span, "candidate `member` requires an `origin` clause");
        };
        Ok(RawCandidateMember {
            id,
            assignments,
            origin,
            span,
        })
    }

    fn parse_candidate_scheme(&mut self, start: usize) -> PResult<RawCandidateSpace, E> {
        self.expect_sym("{")?;
        let mut equations = Vec::new();
        let mut invertibles = Vec::new();
        let mut origin = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                if origin.is_some() {
                    return self.err("duplicate `origin` clause in candidate `scheme`");
                }
                origin = Some(self.parse_shigure_origin("candidate `scheme`")?);
            } else if self.eat_kw("equation") {
                equations.push(self.parse_shigure_named_eq("candidate `scheme`")?);
            } else if self.eat_kw("invertible") {
                invertibles.push(self.parse_shigure_named_poly("candidate `scheme`")?);
            } else {
                self.reject_conclusion_or_unknown("candidate `scheme`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(origin) = origin else {
            return self.syntax_err(span, "candidate `scheme` requires an `origin` clause");
        };
        Ok(RawCandidateSpace::PolynomialScheme {
            equations,
            invertibles,
            origin,
            span,
        })
    }

    fn parse_goodness_spec(&mut self, start: usize) -> PResult<RawGoodnessSpec, E> {
        if self.eat_kw("direct") {
            self.expect_sym("{")?;
            let mut equations = Vec::new();
            let mut invertibles = Vec::new();
            let mut preservation = None;
            let mut raw_sequence = None;
            while !self.is_sym("}") {
                self.checkpoint_here()?;
                if self.eat_kw("equation") {
                    equations.push(self.parse_shigure_named_eq("`goodness direct`")?);
                } else if self.eat_kw("invertible") {
                    invertibles.push(self.parse_shigure_named_poly("`goodness direct`")?);
                } else if self.eat_kw("preservation") {
                    if preservation.is_some() {
                        return self.err("duplicate `preservation` in `goodness direct`");
                    }
                    preservation = Some(self.parse_preservation_source(self.prev_span().0)?);
                } else if self.eat_kw("raw_sequence") {
                    if raw_sequence.is_some() {
                        return self.err("duplicate `raw_sequence` in `goodness direct`");
                    }
                    raw_sequence = Some(self.parse_raw_sequence(self.prev_span().0)?);
                } else {
                    self.reject_conclusion_or_unknown("`goodness direct`")?;
                }
            }
            self.expect_sym("}")?;
            Ok(RawGoodnessSpec::Direct {
                equations,
                invertibles,
                preservation,
                raw_sequence,
                span: (start, self.prev_end()),
            })
        } else if self.eat_kw("existential") {
            self.expect_sym("{")?;
            let mut witness_vars: Option<Vec<Ident>> = None;
            let mut equations = Vec::new();
            let mut invertibles = Vec::new();
            let mut preservation = None;
            while !self.is_sym("}") {
                self.checkpoint_here()?;
                if self.eat_kw("witness_vars") {
                    if witness_vars.is_some() {
                        return self.err("duplicate `witness_vars` in `goodness existential`");
                    }
                    witness_vars = Some(self.parse_ident_var_list("`goodness existential`")?);
                } else if self.eat_kw("equation") {
                    equations.push(self.parse_shigure_named_eq("`goodness existential`")?);
                } else if self.eat_kw("invertible") {
                    invertibles.push(self.parse_shigure_named_poly("`goodness existential`")?);
                } else if self.eat_kw("preservation") {
                    if preservation.is_some() {
                        return self.err("duplicate `preservation` in `goodness existential`");
                    }
                    preservation = Some(self.parse_preservation_source(self.prev_span().0)?);
                } else {
                    self.reject_conclusion_or_unknown("`goodness existential`")?;
                }
            }
            self.expect_sym("}")?;
            let span = (start, self.prev_end());
            let Some(witness_vars) = witness_vars else {
                return self.syntax_err(
                    span,
                    "`goodness existential` requires a `witness_vars` clause",
                );
            };
            Ok(RawGoodnessSpec::Existential {
                witness_vars,
                equations,
                invertibles,
                preservation,
                span,
            })
        } else {
            self.err("expected `direct` or `existential` after `goodness`")
        }
    }

    fn parse_preservation_source(&mut self, start: usize) -> PResult<RawPreservationSource, E> {
        self.expect_sym("{")?;
        let mut comparison = None;
        let mut change_spec = None;
        let mut param_bindings = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("comparison") {
                if comparison.is_some() {
                    return self.err("duplicate `comparison` in `preservation`");
                }
                comparison = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("change_spec") {
                if change_spec.is_some() {
                    return self.err("duplicate `change_spec` in `preservation`");
                }
                change_spec = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("bind") {
                let b_start = self.prev_span().0;
                let param = self.ident()?;
                self.reject_forbidden_ident(&param, "`preservation` bind")?;
                self.expect_sym("=")?;
                let expr = self.parse_shigure_poly_expr()?;
                self.expect_sym(";")?;
                param_bindings.push((param, expr, (b_start, self.prev_end())));
            } else {
                self.reject_conclusion_or_unknown("`preservation`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(comparison) = comparison else {
            return self.syntax_err(span, "`preservation` requires a `comparison` clause");
        };
        let Some(change_spec) = change_spec else {
            return self.syntax_err(span, "`preservation` requires a `change_spec` clause");
        };
        Ok(RawPreservationSource {
            comparison,
            change_spec,
            param_bindings,
            span,
        })
    }

    fn parse_raw_sequence(&mut self, start: usize) -> PResult<RawSequenceSpec, E> {
        self.expect_sym("{")?;
        let mut start_phase = None;
        let mut start_state = Vec::new();
        let mut steps = Vec::new();
        let mut observation_name = None;
        let mut baseline_step_index = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("start_phase") {
                if start_phase.is_some() {
                    return self.err("duplicate `start_phase` in `raw_sequence`");
                }
                start_phase = Some(self.ident()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("start_state") {
                let s_start = self.prev_span().0;
                let coord = self.ident()?;
                self.reject_forbidden_ident(&coord, "`raw_sequence` start_state")?;
                self.expect_sym("=")?;
                let lit = self.parse_shigure_scalar_lit()?;
                self.expect_sym(";")?;
                start_state.push((coord, lit, (s_start, self.prev_end())));
            } else if self.eat_kw("step") {
                let st_start = self.prev_span().0;
                let operation = self.ident()?;
                let mut args = Vec::new();
                if self.eat_sym("(") {
                    if !self.is_sym(")") {
                        loop {
                            self.checkpoint_here()?;
                            args.push(self.parse_shigure_scalar_lit()?);
                            if !self.eat_sym(",") {
                                break;
                            }
                        }
                    }
                    self.expect_sym(")")?;
                }
                self.expect_sym(";")?;
                steps.push(RawSequenceStep {
                    operation,
                    args,
                    span: (st_start, self.prev_end()),
                });
            } else if self.eat_kw("observation") {
                if observation_name.is_some() {
                    return self.err("duplicate `observation` in `raw_sequence`");
                }
                observation_name = Some(self.ident()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("baseline_step_index") {
                if baseline_step_index.is_some() {
                    return self.err("duplicate `baseline_step_index` in `raw_sequence`");
                }
                baseline_step_index =
                    Some(self.parse_usize_token("`raw_sequence` baseline_step_index")?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`raw_sequence`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(start_phase) = start_phase else {
            return self.syntax_err(span, "`raw_sequence` requires a `start_phase` clause");
        };
        let Some(observation_name) = observation_name else {
            return self.syntax_err(span, "`raw_sequence` requires an `observation` clause");
        };
        Ok(RawSequenceSpec {
            start_phase,
            start_state,
            steps,
            observation_name,
            baseline_step_index,
            span,
        })
    }

    fn parse_reading_comparison(&mut self, start: usize) -> PResult<RawReadingComparison, E> {
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut fine_b_vars: Option<Vec<Ident>> = None;
        let mut fine_q: Option<Vec<ShigurePolyExpr>> = None;
        let mut coarsen_r: Option<Vec<ShigurePolyExpr>> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("fine_b_vars") {
                if fine_b_vars.is_some() {
                    return self.err("duplicate `fine_b_vars` in `reading_comparison`");
                }
                fine_b_vars = Some(self.parse_ident_var_list("`reading_comparison`")?);
            } else if self.eat_kw("fine_q") {
                if fine_q.is_some() {
                    return self.err("duplicate `fine_q` in `reading_comparison`");
                }
                let list = self.parse_shigure_poly_bracket_list()?;
                self.expect_sym(";")?;
                fine_q = Some(list);
            } else if self.eat_kw("coarsen_r") {
                if coarsen_r.is_some() {
                    return self.err("duplicate `coarsen_r` in `reading_comparison`");
                }
                let list = self.parse_shigure_poly_bracket_list()?;
                self.expect_sym(";")?;
                coarsen_r = Some(list);
            } else {
                self.reject_conclusion_or_unknown("`reading_comparison`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(fine_b_vars) = fine_b_vars else {
            return self.syntax_err(span, "`reading_comparison` requires `fine_b_vars`");
        };
        let Some(fine_q) = fine_q else {
            return self.syntax_err(span, "`reading_comparison` requires `fine_q`");
        };
        let Some(coarsen_r) = coarsen_r else {
            return self.syntax_err(span, "`reading_comparison` requires `coarsen_r`");
        };
        Ok(RawReadingComparison {
            name,
            fine_b_vars,
            fine_q,
            coarsen_r,
            span,
        })
    }
}
