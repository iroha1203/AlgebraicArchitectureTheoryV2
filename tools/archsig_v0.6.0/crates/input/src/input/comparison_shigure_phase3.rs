//! `shigure family`・`robustness`・`chevalley`・`observations` 検査済みモデルの `ControlledEq` 実装。

use super::BundleError;
use super::comparison::{Comparison, ControlledEq};
use crate::law::shigure::{
    ShigureCandidateFamily, ShigureCandidateMember, ShigureCandidateObservationDecl,
    ShigureCandidateSelector, ShigureCandidateSpace, ShigureChevalleyTask, ShigureFamilySpec,
    ShigureGoodnessSpec, ShigureLawReadoutDecl, ShigureMemberCoordValue, ShigureObservationTask,
    ShigureOriginKind, ShigureOriginRef, ShigurePreservationSource, ShigureRationalProbe,
    ShigureRawSequenceSpec, ShigureReadingComparison, ShigureRealizationFamily,
    ShigureRealizationMember, ShigureRealizationSpace, ShigureRobustnessTask,
};

impl ControlledEq for ShigureOriginKind {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        if self == other { Ok(()) } else { c.mismatch() }
    }
}

impl ControlledEq for ShigureOriginRef {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Explicit {
                    kind: k1,
                    id: id1,
                    span: s1,
                },
                Self::Explicit {
                    kind: k2,
                    id: id2,
                    span: s2,
                },
            ) => {
                c.eq(k1, k2)?;
                c.eq(id1, id2)?;
                c.eq(s1, s2)
            }
            (Self::ArchMap { id: id1, span: s1 }, Self::ArchMap { id: id2, span: s2 }) => {
                c.eq(id1, id2)?;
                c.eq(s1, s2)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureMemberCoordValue {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Literal(a), Self::Literal(b)) => c.eq(a, b),
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
            (Self::Missing, Self::Missing) => Ok(()),
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureRealizationMember {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.id, &other.id)?;
        c.eq(&self.assignments, &other.assignments)?;
        c.eq(&self.is_raw_candidate, &other.is_raw_candidate)?;
        c.eq(&self.presentation, &other.presentation)?;
        c.eq(&self.origin, &other.origin)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureRealizationSpace {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::FiniteMembers(a), Self::FiniteMembers(b)) => c.eq(a, b),
            (
                Self::PolynomialScheme {
                    equations: e1,
                    invertibles: i1,
                    is_raw_candidate: r1,
                    origin: o1,
                },
                Self::PolynomialScheme {
                    equations: e2,
                    invertibles: i2,
                    is_raw_candidate: r2,
                    origin: o2,
                },
            ) => {
                c.eq(e1, e2)?;
                c.eq(i1, i2)?;
                c.eq(r1, r2)?;
                c.eq(o1, o2)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureRealizationFamily {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.u_vars, &other.u_vars)?;
        c.eq(&self.b_vars, &other.b_vars)?;
        c.eq(&self.reading_q, &other.reading_q)?;
        c.eq(&self.space, &other.space)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureCandidateMember {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.id, &other.id)?;
        c.eq(&self.assignments, &other.assignments)?;
        c.eq(&self.origin, &other.origin)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureCandidateSpace {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::FiniteMembers(a), Self::FiniteMembers(b)) => c.eq(a, b),
            (
                Self::PolynomialScheme {
                    equations: e1,
                    invertibles: i1,
                    origin: o1,
                },
                Self::PolynomialScheme {
                    equations: e2,
                    invertibles: i2,
                    origin: o2,
                },
            ) => {
                c.eq(e1, e2)?;
                c.eq(i1, i2)?;
                c.eq(o1, o2)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureCandidateFamily {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.c_vars, &other.c_vars)?;
        c.eq(&self.pi, &other.pi)?;
        c.eq(&self.space, &other.space)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigurePreservationSource {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.comparison, &other.comparison)?;
        c.eq(&self.change_spec, &other.change_spec)?;
        c.eq(&self.param_bindings, &other.param_bindings)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureRawSequenceSpec {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.start_phase, &other.start_phase)?;
        c.eq(&self.start_state, &other.start_state)?;
        c.eq(&self.steps, &other.steps)?;
        c.eq(&self.observation_name, &other.observation_name)?;
        c.eq(&self.baseline_step_index, &other.baseline_step_index)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureGoodnessSpec {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Direct {
                    equations: e1,
                    invertibles: i1,
                    preservation: p1,
                    raw_sequence: r1,
                },
                Self::Direct {
                    equations: e2,
                    invertibles: i2,
                    preservation: p2,
                    raw_sequence: r2,
                },
            ) => {
                c.eq(e1, e2)?;
                c.eq(i1, i2)?;
                c.eq(p1, p2)?;
                c.eq(r1, r2)
            }
            (
                Self::Existential {
                    witness_vars: w1,
                    equations: e1,
                    invertibles: i1,
                    preservation: p1,
                },
                Self::Existential {
                    witness_vars: w2,
                    equations: e2,
                    invertibles: i2,
                    preservation: p2,
                },
            ) => {
                c.eq(w1, w2)?;
                c.eq(e1, e2)?;
                c.eq(i1, i2)?;
                c.eq(p1, p2)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureReadingComparison {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.fine_b_vars, &other.fine_b_vars)?;
        c.eq(&self.fine_q, &other.fine_q)?;
        c.eq(&self.coarsen_r, &other.coarsen_r)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureFamilySpec {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.coeff_domain, &other.coeff_domain)?;
        c.eq(&self.realizations, &other.realizations)?;
        c.eq(&self.candidates, &other.candidates)?;
        c.eq(&self.goodness, &other.goodness)?;
        c.eq(&self.reading_comparison, &other.reading_comparison)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureCandidateSelector {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::ById(a), Self::ById(b)) => c.eq(a, b),
            (Self::ByValues(a), Self::ByValues(b)) => c.eq(a, b),
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureRobustnessTask {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.family, &other.family)?;
        c.eq(&self.point_domain, &other.point_domain)?;
        c.eq(&self.base_value, &other.base_value)?;
        c.eq(&self.designated_candidate, &other.designated_candidate)?;
        c.eq(&self.check_universal_ring, &other.check_universal_ring)?;
        c.eq(&self.fine_base_value, &other.fine_base_value)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureRationalProbe {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.u_assignments, &other.u_assignments)?;
        c.eq(&self.c_assignments, &other.c_assignments)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureChevalleyTask {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.family, &other.family)?;
        c.eq(&self.point_domain, &other.point_domain)?;
        c.eq(&self.base_value, &other.base_value)?;
        c.eq(&self.designated_candidate, &other.designated_candidate)?;
        c.eq(&self.probes, &other.probes)?;
        c.eq(
            &self.check_global_regular_section,
            &other.check_global_regular_section,
        )?;
        c.eq(&self.check_universal_ring, &other.check_universal_ring)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureCandidateObservationDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.id, &other.id)?;
        c.eq(&self.components, &other.components)?;
        c.eq(&self.cost, &other.cost)?;
        c.eq(&self.origin, &other.origin)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureLawReadoutDecl {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.components, &other.components)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureObservationTask {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.family, &other.family)?;
        c.eq(&self.point_domain, &other.point_domain)?;
        c.eq(&self.base_value, &other.base_value)?;
        c.eq(&self.observations, &other.observations)?;
        c.eq(&self.law_readout, &other.law_readout)?;
        c.eq(&self.span, &other.span)
    }
}

#[cfg(test)]
mod tests {
    use crate::archmap::check_archmap;
    use crate::definition::check_definitions;
    use crate::input::{CheckedInputs, InputSources, InputStatus, check_inputs};
    use crate::law::check_law;
    use archsig_common::control::Control;

    #[test]
    fn from_checked_rejects_mutated_phase3_shigure_decls() {
        let def = include_bytes!("../../../../tests/fixtures/counter.atoms.json");
        let defs = check_definitions(&[("definition0", def.as_slice())]).unwrap();
        let digest = defs.vocabularies()["Counter"].digest.clone();
        let law_src = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading P3MutCheck {{
  use vocabulary Counter version "1" digest "{digest}";
  shigure family F {{
    domain Z;
    realizations U {{
      u_vars [u];
      b_vars [b];
      reading_q [0];
      member u0 {{ origin static_analysis "o-u"; set u = 0; }}
    }}
    candidates C {{
      c_vars [c];
      pi [0];
      member c0 {{ origin human_adopted "o-c"; set c = 0; }}
    }}
    goodness direct {{ equation eq: u - c = 0; }}
  }}
  shigure robustness R {{
    family F;
    point_domain integer_points;
    base_value [0];
  }}
  shigure chevalley Ch {{
    family F;
    point_domain algebraic_closure;
  }}
  shigure observations Ob {{
    family F;
    point_domain integer_points;
    base_value [0];
    observe e0 {{ origin static_analysis "o-e"; component v: u; }}
  }}
}}
"#
        );
        let archmap_src = format!(
            r#"{{
  "format": "archsig.archmap/2",
  "semantics": "archsig/0.6.0",
  "vocabularies": [{{"namespace": "Counter", "version": "1", "digest": "{digest}"}}],
  "sources": [{{"id": "s1", "uri": "file://counter.rs", "revision": "r1", "digest": "sha256:0000000000000000000000000000000000000000000000000000000000000001"}}],
  "origins": [{{"id": "o1", "mode": "specification", "method": "spec", "kind": "human_adopted", "locations": [], "note": "n"}}],
  "snapshots": [{{"id": "snap1", "origin": "o1", "subjects": [], "atoms": []}}]
}}"#
        );
        let sources = InputSources::from_bytes(
            vec![def.to_vec()],
            law_src.as_bytes().to_vec(),
            archmap_src.as_bytes().to_vec(),
        );
        let checked = check_inputs(sources.clone(), &Control::unlimited()).unwrap();
        assert_eq!(checked.law().shigure().families.len(), 1);

        for mutate in [
            |law: &mut crate::law::CheckedLaw| {
                law.shigure.families.clear();
            },
            |law: &mut crate::law::CheckedLaw| {
                law.shigure.robustness_tasks.clear();
            },
            |law: &mut crate::law::CheckedLaw| {
                law.shigure.chevalley_tasks.clear();
            },
            |law: &mut crate::law::CheckedLaw| {
                law.shigure.observation_tasks.clear();
            },
        ] {
            let mut law_mut = check_law(sources.law().bytes(), &defs).unwrap();
            mutate(&mut law_mut);
            let map_ok = check_archmap(sources.archmap().bytes(), &defs).unwrap();
            let err = CheckedInputs::from_checked(
                sources.clone(),
                defs.clone(),
                law_mut,
                map_ok,
                &Control::unlimited(),
            )
            .unwrap_err();
            assert_eq!(err.status(), InputStatus::Invalid);
        }
    }
}
