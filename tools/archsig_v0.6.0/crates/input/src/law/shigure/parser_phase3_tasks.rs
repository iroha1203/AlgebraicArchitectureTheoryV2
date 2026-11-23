//! `shigure robustness`・`shigure chevalley`・`shigure observations` 宣言の構文解析。

use super::ast_ext::ShigureScalarLit;
use super::ast_phase3::*;
use super::parser::PResult;
use super::*;
use crate::law::ast::{QName, Span};
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::issue::{Code, Issue};
use archsig_common::json::InputError;
use num_bigint::BigInt;

impl<E: InputError> Parser<E> {
    fn parse_candidate_selector(&mut self, context: &str) -> PResult<RawCandidateSelector, E> {
        if self.eat_kw("id") {
            let id = self.ident()?;
            self.reject_forbidden_ident(&id, context)?;
            self.expect_sym(";")?;
            Ok(RawCandidateSelector::ById(id))
        } else if self.eat_kw("values") {
            self.expect_sym("{")?;
            let mut pairs = Vec::new();
            while !self.is_sym("}") {
                self.checkpoint_here()?;
                let p_start = self.here().0;
                if let Some(t) = self.peek()
                    && t.kind == TokenKind::Name
                    && is_forbidden_conclusion_field(&t.text)
                {
                    self.reject_conclusion_or_unknown(context)?;
                }
                let var = self.ident()?;
                self.reject_forbidden_ident(&var, context)?;
                self.expect_sym("=")?;
                let lit = self.parse_shigure_scalar_lit()?;
                self.expect_sym(";")?;
                pairs.push((var, lit, (p_start, self.prev_end())));
            }
            self.expect_sym("}")?;
            Ok(RawCandidateSelector::ByValues(pairs))
        } else {
            self.err(format!(
                "expected `id` or `values` after `designated_candidate` in {context}"
            ))
        }
    }

    pub(super) fn parse_shigure_robustness(
        &mut self,
        start: usize,
    ) -> PResult<RawRobustnessTask, E> {
        self.expect_kw("robustness")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut family: Option<QName> = None;
        let mut point_domain: Option<RawPointDomain> = None;
        let mut base_value: Option<Vec<ShigureScalarLit>> = None;
        let mut designated_candidate: Option<RawCandidateSelector> = None;
        let mut check_universal_ring: Option<bool> = None;
        let mut fine_base_value: Option<Vec<ShigureScalarLit>> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("family") {
                if family.is_some() {
                    return self.err("duplicate `family` clause in `shigure robustness`");
                }
                family = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("point_domain") {
                if point_domain.is_some() {
                    return self.err("duplicate `point_domain` clause in `shigure robustness`");
                }
                point_domain = Some(self.parse_shigure_point_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("base_value") {
                if base_value.is_some() {
                    return self.err("duplicate `base_value` clause in `shigure robustness`");
                }
                let list = self.parse_shigure_lit_bracket_list()?;
                self.expect_sym(";")?;
                base_value = Some(list);
            } else if self.eat_kw("designated_candidate") {
                if designated_candidate.is_some() {
                    return self
                        .err("duplicate `designated_candidate` clause in `shigure robustness`");
                }
                designated_candidate = Some(self.parse_candidate_selector("`shigure robustness`")?);
            } else if self.eat_kw("check_universal_ring") {
                if check_universal_ring.is_some() {
                    return self
                        .err("duplicate `check_universal_ring` clause in `shigure robustness`");
                }
                let flag = self.parse_shigure_bool("`shigure robustness`")?;
                self.expect_sym(";")?;
                check_universal_ring = Some(flag);
            } else if self.eat_kw("fine_base_value") {
                if fine_base_value.is_some() {
                    return self.err("duplicate `fine_base_value` clause in `shigure robustness`");
                }
                let list = self.parse_shigure_lit_bracket_list()?;
                self.expect_sym(";")?;
                fine_base_value = Some(list);
            } else {
                self.reject_conclusion_or_unknown("`shigure robustness`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(family) = family else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure robustness` requires a `family` clause",
            ))
            .into());
        };
        let Some(point_domain) = point_domain else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure robustness` requires a `point_domain` clause",
            ))
            .into());
        };
        Ok(RawRobustnessTask {
            name,
            family,
            point_domain,
            base_value: base_value.unwrap_or_default(),
            designated_candidate,
            check_universal_ring: check_universal_ring.unwrap_or(false),
            fine_base_value,
            span,
        })
    }

    pub(super) fn parse_shigure_chevalley(&mut self, start: usize) -> PResult<RawChevalleyTask, E> {
        self.expect_kw("chevalley")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut family: Option<QName> = None;
        let mut point_domain: Option<RawPointDomain> = None;
        let mut base_value: Option<Vec<ShigureScalarLit>> = None;
        let mut designated_candidate: Option<RawCandidateSelector> = None;
        let mut probes = Vec::new();
        let mut check_global_regular_section: Option<bool> = None;
        let mut check_universal_ring: Option<bool> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("family") {
                if family.is_some() {
                    return self.err("duplicate `family` clause in `shigure chevalley`");
                }
                family = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("point_domain") {
                if point_domain.is_some() {
                    return self.err("duplicate `point_domain` clause in `shigure chevalley`");
                }
                point_domain = Some(self.parse_shigure_point_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("base_value") {
                if base_value.is_some() {
                    return self.err("duplicate `base_value` clause in `shigure chevalley`");
                }
                let list = self.parse_shigure_lit_bracket_list()?;
                self.expect_sym(";")?;
                base_value = Some(list);
            } else if self.eat_kw("designated_candidate") {
                if designated_candidate.is_some() {
                    return self
                        .err("duplicate `designated_candidate` clause in `shigure chevalley`");
                }
                designated_candidate = Some(self.parse_candidate_selector("`shigure chevalley`")?);
            } else if self.eat_kw("probe") {
                probes.push(self.parse_rational_probe(self.prev_span().0)?);
            } else if self.eat_kw("check_global_regular_section") {
                if check_global_regular_section.is_some() {
                    return self.err(
                        "duplicate `check_global_regular_section` clause in `shigure chevalley`",
                    );
                }
                let flag = self.parse_shigure_bool("`shigure chevalley`")?;
                self.expect_sym(";")?;
                check_global_regular_section = Some(flag);
            } else if self.eat_kw("check_universal_ring") {
                if check_universal_ring.is_some() {
                    return self
                        .err("duplicate `check_universal_ring` clause in `shigure chevalley`");
                }
                let flag = self.parse_shigure_bool("`shigure chevalley`")?;
                self.expect_sym(";")?;
                check_universal_ring = Some(flag);
            } else {
                self.reject_conclusion_or_unknown("`shigure chevalley`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(family) = family else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure chevalley` requires a `family` clause",
            ))
            .into());
        };
        let Some(point_domain) = point_domain else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure chevalley` requires a `point_domain` clause",
            ))
            .into());
        };
        Ok(RawChevalleyTask {
            name,
            family,
            point_domain,
            base_value,
            designated_candidate,
            probes,
            check_global_regular_section: check_global_regular_section.unwrap_or(false),
            check_universal_ring: check_universal_ring.unwrap_or(false),
            span,
        })
    }

    fn parse_rational_probe(&mut self, start: usize) -> PResult<RawRationalProbe, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`chevalley` probe")?;
        self.expect_sym("{")?;
        let mut assignments = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            let a_start = self.here().0;
            if let Some(t) = self.peek()
                && t.kind == TokenKind::Name
                && is_forbidden_conclusion_field(&t.text)
            {
                self.reject_conclusion_or_unknown("`chevalley` probe")?;
            }
            let var = self.ident()?;
            self.reject_forbidden_ident(&var, "`chevalley` probe")?;
            self.expect_sym("=")?;
            let lit = self.parse_shigure_scalar_lit()?;
            self.expect_sym(";")?;
            assignments.push((var, lit, (a_start, self.prev_end())));
        }
        self.expect_sym("}")?;
        Ok(RawRationalProbe {
            name,
            assignments,
            span: (start, self.prev_end()),
        })
    }

    pub(super) fn parse_shigure_observations(
        &mut self,
        start: usize,
    ) -> PResult<RawObservationTask, E> {
        self.expect_kw("observations")?;
        let name = self.ident()?;
        self.expect_sym("{")?;
        let mut family: Option<QName> = None;
        let mut point_domain: Option<RawPointDomain> = None;
        let mut base_value: Option<Vec<ShigureScalarLit>> = None;
        let mut observations = Vec::new();
        let mut law_readout: Option<RawLawReadoutDecl> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("family") {
                if family.is_some() {
                    return self.err("duplicate `family` clause in `shigure observations`");
                }
                family = Some(self.qname()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("point_domain") {
                if point_domain.is_some() {
                    return self.err("duplicate `point_domain` clause in `shigure observations`");
                }
                point_domain = Some(self.parse_shigure_point_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("base_value") {
                if base_value.is_some() {
                    return self.err("duplicate `base_value` clause in `shigure observations`");
                }
                let list = self.parse_shigure_lit_bracket_list()?;
                self.expect_sym(";")?;
                base_value = Some(list);
            } else if self.eat_kw("observe") {
                observations.push(self.parse_candidate_observation(self.prev_span().0)?);
            } else if self.eat_kw("law_readout") {
                if law_readout.is_some() {
                    return self.err("duplicate `law_readout` clause in `shigure observations`");
                }
                law_readout = Some(self.parse_law_readout(self.prev_span().0)?);
            } else {
                self.reject_conclusion_or_unknown("`shigure observations`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(family) = family else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure observations` requires a `family` clause",
            ))
            .into());
        };
        let Some(point_domain) = point_domain else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`shigure observations` requires a `point_domain` clause",
            ))
            .into());
        };
        Ok(RawObservationTask {
            name,
            family,
            point_domain,
            base_value: base_value.unwrap_or_default(),
            observations,
            law_readout,
            span,
        })
    }

    fn parse_candidate_observation(
        &mut self,
        start: usize,
    ) -> PResult<RawCandidateObservationDecl, E> {
        let id = self.ident()?;
        self.reject_forbidden_ident(&id, "`observe`")?;
        self.expect_sym("{")?;
        let mut origin = None;
        let mut cost: Option<(BigInt, Span)> = None;
        let mut components = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("origin") {
                if origin.is_some() {
                    return self.err("duplicate `origin` clause in `observe`");
                }
                origin = Some(self.parse_shigure_origin("`observe`")?);
            } else if self.eat_kw("cost") {
                if cost.is_some() {
                    return self.err("duplicate `cost` clause in `observe`");
                }
                let c_start = self.prev_span().0;
                let raw = self.expect_int_token()?;
                let val = raw.parse::<BigInt>().map_err(|_| {
                    Box::new(Issue::law(
                        Code::Syntax,
                        self.prev_span(),
                        "invalid cost integer",
                    ))
                })?;
                self.expect_sym(";")?;
                cost = Some((val, (c_start, self.prev_end())));
            } else if self.eat_kw("component") {
                components.push(self.parse_shigure_named_poly("`observe`")?);
            } else {
                self.reject_conclusion_or_unknown("`observe`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(origin) = origin else {
            return Err(Box::new(Issue::law(
                Code::Syntax,
                span,
                "`observe` requires an `origin` clause",
            ))
            .into());
        };
        Ok(RawCandidateObservationDecl {
            id,
            components,
            cost,
            origin,
            span,
        })
    }

    fn parse_law_readout(&mut self, start: usize) -> PResult<RawLawReadoutDecl, E> {
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`law_readout`")?;
        self.expect_sym("{")?;
        let mut components = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("component") {
                components.push(self.parse_shigure_named_poly("`law_readout`")?);
            } else {
                self.reject_conclusion_or_unknown("`law_readout`")?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawLawReadoutDecl {
            name,
            components,
            span: (start, self.prev_end()),
        })
    }
}
