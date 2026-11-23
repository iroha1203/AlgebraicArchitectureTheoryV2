//! `CheckedShigureDecls` および SHIGURE 検査済み宣言群の `ControlledEq` 実装。
//!
//! `comparison.rs` の肥大化を避け、全フィールド比較を `Checkpoint::TableComparison` と
//! `stacker::maybe_grow`（`Comparison::eq` 経由）で中断可能かつスタック安全に照合する。

use super::BundleError;
use super::comparison::{Comparison, ControlledEq};
use crate::law::shigure::{
    CheckedShigureDecls, ShigureChangeSpec, ShigureCoeffDomain, ShigureComparison,
    ShigureCoordBinding, ShigureCoordDecl, ShigureEditableTarget, ShigureEvalCondition,
    ShigureFixedTarget, ShigureLawKind, ShigureNamedPoly, ShigureObservationDecl,
    ShigureOperationDecl, ShigureParamDecl, ShigurePhaseDecl, ShigurePointDomain, ShigurePolyExpr,
    ShigurePresentation, ShigureSortDecl, ShigureStateComparison, ShigureStateLawDecl, ShigureTask,
    ShigureTranslatedStep, ShigureTranslatedWord,
};

impl ControlledEq for u32 {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        if self == other { Ok(()) } else { c.mismatch() }
    }
}

impl ControlledEq for ShigureLawKind {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        if self == other { Ok(()) } else { c.mismatch() }
    }
}

impl ControlledEq for ShigureCoeffDomain {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Z, Self::Z) | (Self::Q, Self::Q) => Ok(()),
            (Self::Fp(a), Self::Fp(b)) => c.eq(a, b),
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigurePointDomain {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::AlgebraicClosure, Self::AlgebraicClosure)
            | (Self::RationalPoints, Self::RationalPoints)
            | (Self::IntegerPoints, Self::IntegerPoints)
            | (Self::UniversalRing, Self::UniversalRing) => Ok(()),
            (Self::FiniteFieldPoints(a), Self::FiniteFieldPoints(b)) => c.eq(a, b),
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigurePolyExpr {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => c.eq(a, b),
            (Self::Rat { num: n1, den: d1 }, Self::Rat { num: n2, den: d2 }) => {
                c.eq(n1, n2)?;
                c.eq(d1, d2)
            }
            (
                Self::Fp {
                    value: v1,
                    modulus: m1,
                },
                Self::Fp {
                    value: v2,
                    modulus: m2,
                },
            ) => {
                c.eq(v1, v2)?;
                c.eq(m1, m2)
            }
            (Self::Var(a), Self::Var(b)) => c.eq(a, b),
            (Self::Neg(a), Self::Neg(b)) => c.eq(a, b),
            (Self::Add(a1, a2), Self::Add(b1, b2))
            | (Self::Sub(a1, a2), Self::Sub(b1, b2))
            | (Self::Mul(a1, a2), Self::Mul(b1, b2)) => {
                c.eq(a1, b1)?;
                c.eq(a2, b2)
            }
            (Self::Pow(a, e1), Self::Pow(b, e2)) => {
                c.eq(e1, e2)?;
                c.eq(a, b)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureCoordBinding {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Symbolic, Self::Symbolic) => Ok(()),
            (
                Self::ObservedField {
                    entity: e1,
                    field: f1,
                    span: s1,
                },
                Self::ObservedField {
                    entity: e2,
                    field: f2,
                    span: s2,
                },
            ) => {
                c.eq(e1, e2)?;
                c.eq(f1, f2)?;
                c.eq(s1, s2)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureCoordDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.sort, &other.sort)?;
        c.eq(&self.binding, &other.binding)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureStateLawDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.kind, &other.kind)?;
        c.eq(&self.expr, &other.expr)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigurePhaseDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.coords, &other.coords)?;
        c.eq(&self.state_laws, &other.state_laws)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureSortDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.rank, &other.rank)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureOperationDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.source_phase, &other.source_phase)?;
        c.eq(&self.target_phase, &other.target_phase)?;
        c.eq(&self.args, &other.args)?;
        c.eq(&self.domain_laws, &other.domain_laws)?;
        c.eq(&self.updates, &other.updates)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureObservationDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.phase, &other.phase)?;
        c.eq(&self.components, &other.components)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigurePresentation {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.coeff_domain, &other.coeff_domain)?;
        c.eq(&self.sorts, &other.sorts)?;
        c.eq(&self.phases, &other.phases)?;
        c.eq(&self.operations, &other.operations)?;
        c.eq(&self.observations, &other.observations)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureStateComparison {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.after_phase, &other.after_phase)?;
        c.eq(&self.before_phase, &other.before_phase)?;
        c.eq(&self.map, &other.map)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureTranslatedStep {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.before_operation, &other.before_operation)?;
        c.eq(&self.arg_exprs, &other.arg_exprs)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureTranslatedWord {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.after_operation, &other.after_operation)?;
        c.eq(&self.steps, &other.steps)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureComparison {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.before, &other.before)?;
        c.eq(&self.after, &other.after)?;
        c.eq(&self.state_comparisons, &other.state_comparisons)?;
        c.eq(&self.word_translation, &other.word_translation)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureParamDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.coeff_domain, &other.coeff_domain)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureFixedTarget {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::SemanticLaw {
                    presentation: p1,
                    phase: ph1,
                    law: l1,
                },
                Self::SemanticLaw {
                    presentation: p2,
                    phase: ph2,
                    law: l2,
                },
            )
            | (
                Self::RepresentationLaw {
                    presentation: p1,
                    phase: ph1,
                    law: l1,
                },
                Self::RepresentationLaw {
                    presentation: p2,
                    phase: ph2,
                    law: l2,
                },
            ) => {
                c.eq(p1, p2)?;
                c.eq(ph1, ph2)?;
                c.eq(l1, l2)
            }
            (
                Self::OperationExpr {
                    presentation: p1,
                    operation: o1,
                },
                Self::OperationExpr {
                    presentation: p2,
                    operation: o2,
                },
            ) => {
                c.eq(p1, p2)?;
                c.eq(o1, o2)
            }
            (
                Self::ObservationExpr {
                    presentation: p1,
                    phase: ph1,
                    observation: o1,
                },
                Self::ObservationExpr {
                    presentation: p2,
                    phase: ph2,
                    observation: o2,
                },
            ) => {
                c.eq(p1, p2)?;
                c.eq(ph1, ph2)?;
                c.eq(o1, o2)
            }
            (
                Self::StateComparisonExpr { after_phase: a1 },
                Self::StateComparisonExpr { after_phase: a2 },
            ) => c.eq(a1, a2),
            (
                Self::WordTranslationOp { operation: o1 },
                Self::WordTranslationOp { operation: o2 },
            ) => c.eq(o1, o2),
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureEditableTarget {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::OperationExpr {
                    presentation: p1,
                    operation: o1,
                },
                Self::OperationExpr {
                    presentation: p2,
                    operation: o2,
                },
            ) => {
                c.eq(p1, p2)?;
                c.eq(o1, o2)
            }
            (
                Self::RepresentationLaw {
                    presentation: p1,
                    phase: ph1,
                    law: l1,
                },
                Self::RepresentationLaw {
                    presentation: p2,
                    phase: ph2,
                    law: l2,
                },
            ) => {
                c.eq(p1, p2)?;
                c.eq(ph1, ph2)?;
                c.eq(l1, l2)
            }
            (
                Self::StateComparisonExpr { after_phase: a1 },
                Self::StateComparisonExpr { after_phase: a2 },
            ) => c.eq(a1, a2),
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureChangeSpec {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.coeff_domain, &other.coeff_domain)?;
        c.eq(&self.parameters, &other.parameters)?;
        c.eq(&self.fixed, &other.fixed)?;
        c.eq(&self.editable, &other.editable)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureNamedPoly {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.expr, &other.expr)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureEvalCondition {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.point_domain, &other.point_domain)?;
        c.eq(&self.evaluations, &other.evaluations)?;
        c.eq(&self.equations, &other.equations)?;
        c.eq(&self.invertibles, &other.invertibles)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureTask {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.comparison, &other.comparison)?;
        c.eq(&self.change_spec, &other.change_spec)?;
        c.eq(&self.eval_condition, &other.eval_condition)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for CheckedShigureDecls {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.presentations, &other.presentations)?;
        c.eq(&self.comparisons, &other.comparisons)?;
        c.eq(&self.change_specs, &other.change_specs)?;
        c.eq(&self.eval_conditions, &other.eval_conditions)?;
        c.eq(&self.tasks, &other.tasks)?;
        c.eq(&self.diagrams, &other.diagrams)?;
        c.eq(&self.paths, &other.paths)?;
        c.eq(&self.transfers, &other.transfers)?;
        c.eq(&self.families, &other.families)?;
        c.eq(&self.robustness_tasks, &other.robustness_tasks)?;
        c.eq(&self.chevalley_tasks, &other.chevalley_tasks)?;
        c.eq(&self.observation_tasks, &other.observation_tasks)
    }
}

#[cfg(test)]
mod tests {
    use crate::archmap::{OriginKind, check_archmap};
    use crate::definition::check_definitions;
    use crate::input::{CheckedInputs, InputSources, InputStatus, check_inputs};
    use crate::law::check_law;
    use archsig_common::control::Control;

    #[test]
    fn from_checked_rejects_mutated_shigure_decls_and_origin_kind() {
        let def = include_bytes!("../../../../tests/fixtures/counter.atoms.json");
        let defs = check_definitions(&[("definition0", def.as_slice())]).unwrap();
        let digest = defs.vocabularies()["Counter"].digest.clone();
        let law_src = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading MutCheck {{
  use vocabulary Counter version "1" digest "{digest}";
  shigure presentation P {{
    domain Z; sort D;
    phase S {{ coord x: D; }}
    op id(): S -> S {{ x = x; }}
    obs r on S = (x);
  }}
}}
"#
        );
        let map_src = format!(
            r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace":"Counter","version":"1","digest":"{digest}"}}],
  "sources": [],
  "origins": [{{"id":"o1","mode":"specification","method":"spec","kind":"human_adopted","locations":[],"note":"n"}}],
  "snapshots": [{{"id":"s1","origin":"o1","subjects":[],"atoms":[]}}]
}}"#
        );
        let sources = InputSources::from_bytes(
            vec![def.to_vec()],
            law_src.into_bytes(),
            map_src.into_bytes(),
        );
        assert!(check_inputs(sources.clone(), &Control::unlimited()).is_ok());

        // 1. Mutated CheckedLaw.shigure must be rejected even with unchanged digests.
        let mut law_mut = check_law(sources.law().bytes(), &defs).unwrap();
        law_mut.shigure.presentations.clear();
        let map_ok = check_archmap(sources.archmap().bytes(), &defs).unwrap();
        let err_law = CheckedInputs::from_checked(
            sources.clone(),
            defs.clone(),
            law_mut,
            map_ok,
            &Control::unlimited(),
        )
        .unwrap_err();
        assert_eq!(err_law.status(), InputStatus::Invalid);

        // 2. Mutated Origin.kind must be rejected even with unchanged digests.
        let law_ok = check_law(sources.law().bytes(), &defs).unwrap();
        let mut map_mut = check_archmap(sources.archmap().bytes(), &defs).unwrap();
        map_mut.origins[0].kind = Some(OriginKind::LlmCandidate);
        let err_map = CheckedInputs::from_checked(
            sources.clone(),
            defs.clone(),
            law_ok,
            map_mut,
            &Control::unlimited(),
        )
        .unwrap_err();
        assert_eq!(err_map.status(), InputStatus::Invalid);

        // 3. TableComparison 中断チェックポイントが CheckedShigureDecls 内部でも発火して中断できる。
        let sum_50 = std::iter::repeat_n("x", 50).collect::<Vec<_>>().join(" + ");
        let deep_law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading DeepCheck {{
  use vocabulary Counter version "1" digest "{digest}";
  shigure presentation P {{
    domain Z; sort D;
    phase S {{ coord x: D; }}
    op id(): S -> S {{ x = {sum_50}; }}
    obs r on S = (x);
  }}
}}
"#
        );
        let deep_sources = InputSources::from_bytes(
            vec![def.to_vec()],
            deep_law.into_bytes(),
            sources.archmap().bytes().to_vec(),
        );
        let law_d = check_law(deep_sources.law().bytes(), &defs).unwrap();
        let map_d = check_archmap(deep_sources.archmap().bytes(), &defs).unwrap();
        let hits = std::rc::Rc::new(std::cell::Cell::new(0usize));
        let seen = hits.clone();
        let count_ctrl = Control::new(move |pt| {
            if pt == archsig_common::control::Checkpoint::TableComparison {
                seen.set(seen.get() + 1);
            }
            None
        });
        assert!(
            CheckedInputs::from_checked(
                deep_sources.clone(),
                defs.clone(),
                law_d,
                map_d,
                &count_ctrl
            )
            .is_ok()
        );
        assert!(hits.get() > 100);

        let law_d2 = check_law(deep_sources.law().bytes(), &defs).unwrap();
        let map_d2 = check_archmap(deep_sources.archmap().bytes(), &defs).unwrap();
        let stop_at = hits.get() - 5;
        let cur = std::rc::Rc::new(std::cell::Cell::new(0usize));
        let stop_ctrl = Control::new(move |pt| {
            if pt == archsig_common::control::Checkpoint::TableComparison {
                let next = cur.get() + 1;
                cur.set(next);
                if next == stop_at {
                    return Some(crate::result::Signal::Term);
                }
            }
            None
        });
        let stopped = CheckedInputs::from_checked(deep_sources, defs, law_d2, map_d2, &stop_ctrl)
            .unwrap_err();
        assert_eq!(stopped.status(), InputStatus::Interrupted);
    }
}
