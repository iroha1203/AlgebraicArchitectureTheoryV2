//! `shigure diagnostics` 宣言および共通 `nerve` ブロックの構文解析（Phase 4 / AC2）。

use super::ast_phase4_diag_atlas::*;
use super::parser::PResult;
use super::*;
use crate::law::ast::Ident;
use crate::law::lexer::TokenKind;
use crate::law::parser::Parser;
use archsig_common::json::InputError;

impl<E: InputError> Parser<E> {
    pub(super) fn parse_supported_nerve(&mut self, start: usize) -> PResult<RawSupportedNerve, E> {
        self.expect_sym("{")?;
        let mut charts = Vec::new();
        let mut edges = Vec::new();
        let mut faces = Vec::new();

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("chart") {
                let c_start = self.prev_span().0;
                let name = self.ident()?;
                self.reject_forbidden_ident(&name, "`nerve` chart")?;
                let support = self.parse_p4_ident_list("`nerve` chart support")?;
                self.expect_sym(";")?;
                charts.push(RawChartSupport {
                    name,
                    support,
                    span: (c_start, self.prev_end()),
                });
            } else if self.eat_kw("edge") {
                let e_start = self.prev_span().0;
                let name = self.ident()?;
                self.reject_forbidden_ident(&name, "`nerve` edge")?;
                self.expect_sym("(")?;
                let left = self.ident()?;
                self.expect_sym(",")?;
                let right = self.ident()?;
                self.expect_sym(")")?;
                self.expect_sym(";")?;
                edges.push(RawNerveEdge {
                    name,
                    left,
                    right,
                    span: (e_start, self.prev_end()),
                });
            } else if self.eat_kw("face") {
                let f_start = self.prev_span().0;
                let name = self.ident()?;
                self.reject_forbidden_ident(&name, "`nerve` face")?;
                self.expect_sym("(")?;
                let e0 = self.ident()?;
                self.expect_sym(",")?;
                let e1 = self.ident()?;
                self.expect_sym(",")?;
                let e2 = self.ident()?;
                self.expect_sym(")")?;
                self.expect_sym(";")?;
                faces.push(RawNerveFace {
                    name,
                    e0,
                    e1,
                    e2,
                    span: (f_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`nerve`")?;
            }
        }
        self.expect_sym("}")?;
        Ok(RawSupportedNerve {
            charts,
            edges,
            faces,
            span: (start, self.prev_end()),
        })
    }

    fn parse_i64_list(&mut self, context: &str) -> PResult<Vec<i64>, E> {
        self.expect_sym("[")?;
        let mut items = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                items.push(self.parse_i64_token(context)?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(items)
    }

    fn parse_i64_matrix(&mut self, context: &str) -> PResult<Vec<Vec<i64>>, E> {
        self.expect_sym("[")?;
        let mut rows = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                rows.push(self.parse_i64_list(context)?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(rows)
    }

    fn parse_partition_blocks(&mut self, context: &str) -> PResult<Vec<Vec<Ident>>, E> {
        self.expect_sym("[")?;
        let mut blocks = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                blocks.push(self.parse_p4_ident_list(context)?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(blocks)
    }

    fn parse_partition_path(&mut self, context: &str) -> PResult<Vec<Vec<Vec<Ident>>>, E> {
        self.expect_sym("[")?;
        let mut steps = Vec::new();
        if !self.is_sym("]") {
            loop {
                self.checkpoint_here()?;
                steps.push(self.parse_partition_blocks(context)?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym("]")?;
        Ok(steps)
    }

    fn parse_poly_or_observed(&mut self) -> PResult<RawPolyOrObserved, E> {
        if self.is_kw("observed") && self.peek_at(1).is_some_and(|t| t.kind == TokenKind::Name) {
            self.advance();
            let f_start = self.here().0;
            let field = self.qname()?;
            Ok(RawPolyOrObserved::ObservedField {
                field,
                span: (f_start, self.prev_end()),
            })
        } else if self.is_kw("missing") && self.peek_at(1).is_some_and(|t| t.text == ";") {
            self.advance();
            Ok(RawPolyOrObserved::Missing(self.prev_span()))
        } else {
            Ok(RawPolyOrObserved::Poly(self.parse_shigure_poly_expr()?))
        }
    }

    pub(super) fn parse_shigure_diagnostics(
        &mut self,
        start: usize,
    ) -> PResult<RawDiagnosticsTask, E> {
        self.expect_kw("diagnostics")?;
        let name = self.ident()?;
        self.reject_forbidden_ident(&name, "`shigure diagnostics`")?;
        self.expect_sym("{")?;
        let mut diagnostic_coeff: Option<RawCoeffDomain> = None;
        let mut origins = Vec::new();
        let mut nerve: Option<RawSupportedNerve> = None;
        let mut readout: Option<RawDiagnosticsReadout> = None;
        let mut coeff_change: Option<RawCoeffChangeComparison> = None;
        let mut collisions = Vec::new();
        let mut r_point_probe: Option<RawRPointProbe> = None;
        let mut dimension_realization: Option<RawDimensionRealization> = None;
        let mut max_partitions: Option<usize> = None;

        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("diagnostic_coeff") {
                if diagnostic_coeff.is_some() {
                    return self.err("duplicate `diagnostic_coeff` in `shigure diagnostics`");
                }
                diagnostic_coeff = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("origin") {
                origins.push(self.parse_shigure_origin("`shigure diagnostics`")?);
            } else if self.eat_kw("nerve") {
                if nerve.is_some() {
                    return self.err("duplicate `nerve` block in `shigure diagnostics`");
                }
                nerve = Some(self.parse_supported_nerve(self.prev_span().0)?);
            } else if self.eat_kw("static_readout") {
                if readout.is_some() {
                    return self.err("duplicate readout block in `shigure diagnostics`");
                }
                readout = Some(self.parse_static_readout(self.prev_span().0)?);
            } else if self.eat_kw("poly_readout") {
                if readout.is_some() {
                    return self.err("duplicate readout block in `shigure diagnostics`");
                }
                readout = Some(self.parse_poly_readout(self.prev_span().0)?);
            } else if self.eat_kw("coeff_change") {
                if coeff_change.is_some() {
                    return self.err("duplicate `coeff_change` block in `shigure diagnostics`");
                }
                coeff_change = Some(self.parse_coeff_change(self.prev_span().0)?);
            } else if self.eat_kw("collision") {
                collisions.push(self.parse_collision(self.prev_span().0)?);
            } else if self.eat_kw("r_point_probe") {
                if r_point_probe.is_some() {
                    return self.err("duplicate `r_point_probe` block in `shigure diagnostics`");
                }
                r_point_probe = Some(self.parse_r_point_probe(self.prev_span().0)?);
            } else if self.eat_kw("dimension_realization") {
                if dimension_realization.is_some() {
                    return self
                        .err("duplicate `dimension_realization` block in `shigure diagnostics`");
                }
                dimension_realization = Some(self.parse_dimension_realization(self.prev_span().0)?);
            } else if self.eat_kw("max_partitions") {
                if max_partitions.is_some() {
                    return self.err("duplicate `max_partitions` clause in `shigure diagnostics`");
                }
                let n = self.parse_usize_token("`max_partitions`")?;
                self.expect_sym(";")?;
                max_partitions = Some(n);
            } else {
                self.reject_conclusion_or_unknown("`shigure diagnostics`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(diagnostic_coeff) = diagnostic_coeff else {
            return self.p4_syntax_err(
                span,
                "`shigure diagnostics` requires a `diagnostic_coeff` clause",
            );
        };
        if origins.is_empty() {
            return self.p4_syntax_err(
                span,
                "`shigure diagnostics` requires at least one `origin` clause",
            );
        }
        let Some(nerve) = nerve else {
            return self.p4_syntax_err(span, "`shigure diagnostics` requires a `nerve` block");
        };
        let Some(readout) = readout else {
            return self.p4_syntax_err(
                span,
                "`shigure diagnostics` requires a `static_readout` or `poly_readout` block",
            );
        };
        Ok(RawDiagnosticsTask {
            name,
            diagnostic_coeff,
            origins,
            nerve,
            readout,
            coeff_change,
            collisions,
            r_point_probe,
            dimension_realization,
            max_partitions,
            span,
        })
    }

    fn parse_static_readout(&mut self, start: usize) -> PResult<RawDiagnosticsReadout, E> {
        self.expect_sym("{")?;
        let mut sources = None;
        let mut targets = None;
        let mut reading = None;
        let mut laws = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("sources") {
                if sources.is_some() {
                    return self.err("duplicate `sources` in `static_readout`");
                }
                sources = Some(self.parse_p4_ident_list("`static_readout` sources")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("targets") {
                if targets.is_some() {
                    return self.err("duplicate `targets` in `static_readout`");
                }
                targets = Some(self.parse_p4_ident_list("`static_readout` targets")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("reading") {
                if reading.is_some() {
                    return self.err("duplicate `reading` in `static_readout`");
                }
                reading = Some(self.parse_p4_ident_arrow_block("`static_readout` reading")?);
            } else if self.eat_kw("law") {
                let l_start = self.prev_span().0;
                let law_name = self.ident()?;
                self.reject_forbidden_ident(&law_name, "`static_readout` law")?;
                self.expect_sym("{")?;
                let mut values = Vec::new();
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    let v_start = self.here().0;
                    self.reject_peek_forbidden("`static_readout` law")?;
                    let src = self.ident()?;
                    self.reject_forbidden_ident(&src, "`static_readout` law")?;
                    self.expect_sym("=")?;
                    let lit = self.parse_shigure_scalar_lit()?;
                    self.expect_sym(";")?;
                    values.push((src, lit, (v_start, self.prev_end())));
                }
                self.expect_sym("}")?;
                laws.push(RawStaticLawReadout {
                    law_name,
                    values,
                    span: (l_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`static_readout`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(sources), Some(targets), Some(reading)) = (sources, targets, reading) else {
            return self.p4_syntax_err(
                span,
                "`static_readout` requires `sources`, `targets`, and `reading`",
            );
        };
        Ok(RawDiagnosticsReadout::Static {
            sources,
            targets,
            reading,
            laws,
            span,
        })
    }

    fn parse_poly_readout(&mut self, start: usize) -> PResult<RawDiagnosticsReadout, E> {
        self.expect_sym("{")?;
        let mut base_domain = None;
        let mut base_vars = None;
        let mut base_relations = Vec::new();
        let mut sources = None;
        let mut laws = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("base_domain") {
                if base_domain.is_some() {
                    return self.err("duplicate `base_domain` in `poly_readout`");
                }
                base_domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("base_vars") {
                if base_vars.is_some() {
                    return self.err("duplicate `base_vars` in `poly_readout`");
                }
                base_vars = Some(self.parse_p4_ident_list("`poly_readout` base_vars")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("base_relation") {
                base_relations.push(self.parse_shigure_named_eq("`poly_readout` base_relation")?);
            } else if self.eat_kw("sources") {
                if sources.is_some() {
                    return self.err("duplicate `sources` in `poly_readout`");
                }
                sources = Some(self.parse_p4_ident_list("`poly_readout` sources")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("law") {
                let l_start = self.prev_span().0;
                let law_name = self.ident()?;
                self.reject_forbidden_ident(&law_name, "`poly_readout` law")?;
                self.expect_sym("{")?;
                let mut values = Vec::new();
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    let v_start = self.here().0;
                    self.reject_peek_forbidden("`poly_readout` law")?;
                    let src = self.ident()?;
                    self.reject_forbidden_ident(&src, "`poly_readout` law")?;
                    self.expect_sym("=")?;
                    let val = self.parse_poly_or_observed()?;
                    self.expect_sym(";")?;
                    values.push((src, val, (v_start, self.prev_end())));
                }
                self.expect_sym("}")?;
                laws.push(RawPolyLawReadout {
                    law_name,
                    values,
                    span: (l_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`poly_readout`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(base_domain), Some(base_vars), Some(sources)) = (base_domain, base_vars, sources)
        else {
            return self.p4_syntax_err(
                span,
                "`poly_readout` requires `base_domain`, `base_vars`, and `sources`",
            );
        };
        Ok(RawDiagnosticsReadout::Polynomial {
            base_domain,
            base_vars,
            base_relations,
            sources,
            laws,
            span,
        })
    }

    fn parse_coeff_change(&mut self, start: usize) -> PResult<RawCoeffChangeComparison, E> {
        self.expect_sym("{")?;
        let mut target_domain = None;
        let mut compare_codomain_regeneration = None;
        let mut explicit_z_complex = None;
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("target_domain") {
                if target_domain.is_some() {
                    return self.err("duplicate `target_domain` in `coeff_change`");
                }
                target_domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("compare_codomain_regeneration") {
                if compare_codomain_regeneration.is_some() {
                    return self.err("duplicate `compare_codomain_regeneration` in `coeff_change`");
                }
                let flag = self.parse_shigure_bool("`coeff_change`")?;
                self.expect_sym(";")?;
                compare_codomain_regeneration = Some(flag);
            } else if self.eat_kw("explicit_z_complex") {
                if explicit_z_complex.is_some() {
                    return self.err("duplicate `explicit_z_complex` in `coeff_change`");
                }
                let ez_start = self.prev_span().0;
                self.expect_sym("{")?;
                let mut dim0 = None;
                let mut dim1 = None;
                let mut d0 = None;
                let mut designated_cocycle = None;
                while !self.is_sym("}") {
                    self.checkpoint_here()?;
                    if self.eat_kw("dim0") {
                        if dim0.is_some() {
                            return self.err("duplicate `dim0` in `explicit_z_complex`");
                        }
                        dim0 = Some(self.parse_usize_token("`explicit_z_complex` dim0")?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("dim1") {
                        if dim1.is_some() {
                            return self.err("duplicate `dim1` in `explicit_z_complex`");
                        }
                        dim1 = Some(self.parse_usize_token("`explicit_z_complex` dim1")?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("d0") {
                        if d0.is_some() {
                            return self.err("duplicate `d0` in `explicit_z_complex`");
                        }
                        d0 = Some(self.parse_i64_matrix("`explicit_z_complex` d0")?);
                        self.expect_sym(";")?;
                    } else if self.eat_kw("designated_cocycle") {
                        if designated_cocycle.is_some() {
                            return self
                                .err("duplicate `designated_cocycle` in `explicit_z_complex`");
                        }
                        designated_cocycle =
                            Some(self.parse_i64_list("`explicit_z_complex` designated_cocycle")?);
                        self.expect_sym(";")?;
                    } else {
                        self.reject_conclusion_or_unknown("`explicit_z_complex`")?;
                    }
                }
                self.expect_sym("}")?;
                let ez_span = (ez_start, self.prev_end());
                let (Some(dim0), Some(dim1), Some(d0)) = (dim0, dim1, d0) else {
                    return self.p4_syntax_err(
                        ez_span,
                        "`explicit_z_complex` requires `dim0`, `dim1`, and `d0`",
                    );
                };
                explicit_z_complex = Some(RawExplicitZComplex {
                    dim0,
                    dim1,
                    d0,
                    designated_cocycle,
                    span: ez_span,
                });
            } else {
                self.reject_conclusion_or_unknown("`coeff_change`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let Some(target_domain) = target_domain else {
            return self.p4_syntax_err(span, "`coeff_change` requires `target_domain`");
        };
        Ok(RawCoeffChangeComparison {
            target_domain,
            compare_codomain_regeneration: compare_codomain_regeneration.unwrap_or(false),
            explicit_z_complex,
            span,
        })
    }

    fn parse_collision(&mut self, start: usize) -> PResult<RawCollisionComparison, E> {
        let label = self.string()?;
        self.expect_kw("on")?;
        let law_name = self.ident()?;
        self.reject_forbidden_ident(&law_name, "`collision`")?;
        self.expect_sym("{")?;
        let mut fine_partition = None;
        let mut coarse_partition = None;
        let mut alternative_merge_paths = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("fine") {
                if fine_partition.is_some() {
                    return self.err("duplicate `fine` in `collision`");
                }
                fine_partition = Some(self.parse_partition_blocks("`collision` fine")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("coarse") {
                if coarse_partition.is_some() {
                    return self.err("duplicate `coarse` in `collision`");
                }
                coarse_partition = Some(self.parse_partition_blocks("`collision` coarse")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("alt_path") {
                alternative_merge_paths.push(self.parse_partition_path("`collision` alt_path")?);
                self.expect_sym(";")?;
            } else {
                self.reject_conclusion_or_unknown("`collision`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(fine_partition), Some(coarse_partition)) = (fine_partition, coarse_partition)
        else {
            return self.p4_syntax_err(span, "`collision` requires `fine` and `coarse`");
        };
        Ok(RawCollisionComparison {
            label,
            law_name,
            fine_partition,
            coarse_partition,
            alternative_merge_paths,
            span,
        })
    }

    fn parse_r_point_probe(&mut self, start: usize) -> PResult<RawRPointProbe, E> {
        self.expect_sym("{")?;
        let mut ring_var = None;
        let mut ring_max_deg = None;
        let mut points = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("ring_var") {
                if ring_var.is_some() {
                    return self.err("duplicate `ring_var` in `r_point_probe`");
                }
                let id = self.ident()?;
                self.reject_forbidden_ident(&id, "`r_point_probe`")?;
                self.expect_sym(";")?;
                ring_var = Some(id);
            } else if self.eat_kw("ring_max_deg") {
                if ring_max_deg.is_some() {
                    return self.err("duplicate `ring_max_deg` in `r_point_probe`");
                }
                ring_max_deg = Some(self.parse_usize_token("`r_point_probe` ring_max_deg")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("point") {
                let p_start = self.prev_span().0;
                let label = self.string()?;
                let coords = self.parse_p4_coord_vec_block("`r_point_probe` point")?;
                points.push(RawNamedRPoint {
                    label,
                    coords,
                    span: (p_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`r_point_probe`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(ring_var), Some(ring_max_deg)) = (ring_var, ring_max_deg) else {
            return self.p4_syntax_err(
                span,
                "`r_point_probe` requires `ring_var` and `ring_max_deg`",
            );
        };
        Ok(RawRPointProbe {
            ring_var,
            ring_max_deg,
            points,
            span,
        })
    }

    fn parse_dimension_realization(&mut self, start: usize) -> PResult<RawDimensionRealization, E> {
        self.expect_sym("{")?;
        let mut base_domain = None;
        let mut base_vars = None;
        let mut vanishing_polys = Vec::new();
        let mut invertible_poly = None;
        let mut probe_points = Vec::new();
        while !self.is_sym("}") {
            self.checkpoint_here()?;
            if self.eat_kw("base_domain") {
                if base_domain.is_some() {
                    return self.err("duplicate `base_domain` in `dimension_realization`");
                }
                base_domain = Some(self.parse_shigure_coeff_domain()?);
                self.expect_sym(";")?;
            } else if self.eat_kw("base_vars") {
                if base_vars.is_some() {
                    return self.err("duplicate `base_vars` in `dimension_realization`");
                }
                base_vars = Some(self.parse_p4_ident_list("`dimension_realization` base_vars")?);
                self.expect_sym(";")?;
            } else if self.eat_kw("vanishing") {
                vanishing_polys
                    .push(self.parse_shigure_named_eq("`dimension_realization` vanishing")?);
            } else if self.eat_kw("invertible") {
                if invertible_poly.is_some() {
                    return self.err("duplicate `invertible` in `dimension_realization`");
                }
                invertible_poly =
                    Some(self.parse_shigure_named_poly("`dimension_realization` invertible")?);
            } else if self.eat_kw("probe") {
                let p_start = self.prev_span().0;
                let label = self.string()?;
                let coords = self.parse_p4_coord_scalar_block("`dimension_realization` probe")?;
                probe_points.push(RawNamedBasePoint {
                    label,
                    coords,
                    span: (p_start, self.prev_end()),
                });
            } else {
                self.reject_conclusion_or_unknown("`dimension_realization`")?;
            }
        }
        self.expect_sym("}")?;
        let span = (start, self.prev_end());
        let (Some(base_domain), Some(base_vars), Some(invertible_poly)) =
            (base_domain, base_vars, invertible_poly)
        else {
            return self.p4_syntax_err(
                span,
                "`dimension_realization` requires `base_domain`, `base_vars`, and `invertible`",
            );
        };
        Ok(RawDimensionRealization {
            base_domain,
            base_vars,
            vanishing_polys,
            invertible_poly,
            probe_points,
            span,
        })
    }
}
