//! `shigure diagram`・`shigure path`・`shigure transfer` 検査済みモデルの `ControlledEq` 実装。

use super::BundleError;
use super::comparison::{Comparison, ControlledEq};
use crate::law::shigure::{
    ShigureDiagramEdge, ShigureDiagramRelation, ShigureDiagramTask, ShigureDiagramVertex,
    ShigureDirection, ShigureModelEndpoint, ShigureMorphismBody, ShigureOldWordLift,
    ShigureOneStepRule, ShigurePathKind, ShigurePathQueryMode, ShigurePathTask,
    ShigureProtocolExecution, ShigureScalarLit, ShigureTransferStep, ShigureTransferStepSource,
    ShigureTransferTask, ShigureWordCheck, ShigureWordStep,
};

impl ControlledEq for ShigureDirection {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        if self == other { Ok(()) } else { c.mismatch() }
    }
}

impl ControlledEq for ShigurePathKind {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        if self == other { Ok(()) } else { c.mismatch() }
    }
}

impl ControlledEq for ShigureScalarLit {
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
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureMorphismBody {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Comparison(a), Self::Comparison(b)) => c.eq(a, b),
            (Self::Identity, Self::Identity) => Ok(()),
            (
                Self::Inline {
                    state_comparisons: s1,
                    word_translation: w1,
                },
                Self::Inline {
                    state_comparisons: s2,
                    word_translation: w2,
                },
            ) => {
                c.eq(s1, s2)?;
                c.eq(w1, w2)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureDiagramVertex {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.presentation, &other.presentation)?;
        c.eq(&self.is_fixed, &other.is_fixed)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureDiagramEdge {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.source, &other.source)?;
        c.eq(&self.target, &other.target)?;
        c.eq(&self.is_fixed, &other.is_fixed)?;
        c.eq(&self.morphism, &other.morphism)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureDiagramRelation {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.lhs, &other.lhs)?;
        c.eq(&self.rhs, &other.rhs)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureDiagramTask {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.direction, &other.direction)?;
        c.eq(&self.vertices, &other.vertices)?;
        c.eq(&self.edges, &other.edges)?;
        c.eq(&self.relations, &other.relations)?;
        c.eq(&self.change_spec, &other.change_spec)?;
        c.eq(&self.eval_condition, &other.eval_condition)?;
        c.eq(&self.edge_eval_conditions, &other.edge_eval_conditions)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigurePathQueryMode {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Find, Self::Find) => Ok(()),
            (
                Self::Concatenate {
                    first: f1,
                    second: s1,
                },
                Self::Concatenate {
                    first: f2,
                    second: s2,
                },
            ) => {
                c.eq(f1, f2)?;
                c.eq(s1, s2)
            }
            (Self::Subdivide { target_edge: a }, Self::Subdivide { target_edge: b }) => c.eq(a, b),
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureModelEndpoint {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.vertex, &other.vertex)?;
        c.eq(&self.param_values, &other.param_values)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureOneStepRule {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.from_vertex, &other.from_vertex)?;
        c.eq(&self.to_vertex, &other.to_vertex)?;
        c.eq(&self.param_guards, &other.param_guards)?;
        c.eq(&self.param_updates, &other.param_updates)?;
        c.eq(&self.morphism, &other.morphism)?;
        c.eq(&self.eval_condition, &other.eval_condition)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureProtocolExecution {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.comparison, &other.comparison)?;
        c.eq(&self.start_phase, &other.start_phase)?;
        c.eq(&self.start_laws, &other.start_laws)?;
        c.eq(&self.end_phase, &other.end_phase)?;
        c.eq(&self.end_laws, &other.end_laws)?;
        c.eq(&self.allowed_ops, &other.allowed_ops)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigurePathTask {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.kind, &other.kind)?;
        c.eq(&self.direction, &other.direction)?;
        c.eq(&self.query_mode, &other.query_mode)?;
        c.eq(&self.length, &other.length)?;
        c.eq(&self.vertices, &other.vertices)?;
        c.eq(&self.rules, &other.rules)?;
        c.eq(&self.start, &other.start)?;
        c.eq(&self.end, &other.end)?;
        c.eq(&self.protocol, &other.protocol)?;
        c.eq(&self.change_spec, &other.change_spec)?;
        c.eq(&self.eval_condition, &other.eval_condition)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureWordStep {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.operation, &other.operation)?;
        c.eq(&self.arg_exprs, &other.arg_exprs)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureWordCheck {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.args, &other.args)?;
        c.eq(&self.steps, &other.steps)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureOldWordLift {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.args, &other.args)?;
        c.eq(&self.target_steps, &other.target_steps)?;
        c.eq(&self.max_length, &other.max_length)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureTransferStepSource {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Comparison(a), Self::Comparison(b)) => c.eq(a, b),
            (
                Self::Inline {
                    before: b1,
                    after: a1,
                    morphism: m1,
                },
                Self::Inline {
                    before: b2,
                    after: a2,
                    morphism: m2,
                },
            ) => {
                c.eq(b1, b2)?;
                c.eq(a1, a2)?;
                c.eq(m1, m2)
            }
            _ => c.mismatch(),
        }
    }
}

impl ControlledEq for ShigureTransferStep {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.source, &other.source)?;
        c.eq(&self.source_phase, &other.source_phase)?;
        c.eq(&self.target_phase, &other.target_phase)?;
        c.eq(&self.domain_laws, &other.domain_laws)?;
        c.eq(&self.lift_map, &other.lift_map)?;
        c.eq(&self.span, &other.span)
    }
}

impl ControlledEq for ShigureTransferTask {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.steps, &other.steps)?;
        c.eq(&self.word_checks, &other.word_checks)?;
        c.eq(&self.old_word_lifts, &other.old_word_lifts)?;
        c.eq(&self.change_spec, &other.change_spec)?;
        c.eq(&self.eval_condition, &other.eval_condition)?;
        c.eq(&self.require_full_domain, &other.require_full_domain)?;
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
    fn from_checked_rejects_mutated_phase2_shigure_decls() {
        let def = include_bytes!("../../../../tests/fixtures/counter.atoms.json");
        let defs = check_definitions(&[("definition0", def.as_slice())]).unwrap();
        let digest = defs.vocabularies()["Counter"].digest.clone();
        let law_src = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading ExtMutCheck {{
  use vocabulary Counter version "1" digest "{digest}";
  shigure presentation P {{
    domain Z; sort D;
    phase S {{ coord x: D; }}
    op id(): S -> S {{ law representation pre: x = 0; x = x; }}
    obs r on S = (x);
  }}
  shigure change_spec H {{ domain Z; param k: Z; }}
  shigure diagram D {{
    direction state_map;
    vertex fixed v0: P;
    edge fixed e0: v0 -> v0 {{ identity; }}
    relation r0: [e0] = [e0];
    change_spec H;
  }}
  shigure path Pa {{
    kind fixed_protocol_change_path;
    direction state_map;
    length 0;
    vertex v0: P;
    start v0 {{ k = 0; }}
    end v0 {{ k = 0; }}
    change_spec H;
  }}
  shigure transfer Tr {{
    step s1 {{
      before P; after P; identity;
      source_phase S; target_phase S;
      lift {{ x = x; }}
    }}
    change_spec H;
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

        for mutate in [
            |law: &mut crate::law::CheckedLaw| {
                law.shigure
                    .presentations
                    .get_mut("ExtMutCheck.P")
                    .unwrap()
                    .operations[0]
                    .domain_laws
                    .clear();
            },
            |law: &mut crate::law::CheckedLaw| {
                law.shigure.diagrams.clear();
            },
            |law: &mut crate::law::CheckedLaw| {
                law.shigure.paths.clear();
            },
            |law: &mut crate::law::CheckedLaw| {
                law.shigure.transfers.clear();
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

        // 2. CheckedInputs::from_checked の TableComparison 中断点が新設宣言でも発火する。
        let hits = std::rc::Rc::new(std::cell::Cell::new(0usize));
        let seen = hits.clone();
        let count_ctrl = Control::new(move |pt| {
            if pt == archsig_common::control::Checkpoint::TableComparison {
                seen.set(seen.get() + 1);
            }
            None
        });
        let law_c = check_law(sources.law().bytes(), &defs).unwrap();
        let map_c = check_archmap(sources.archmap().bytes(), &defs).unwrap();
        assert!(
            CheckedInputs::from_checked(sources.clone(), defs.clone(), law_c, map_c, &count_ctrl)
                .is_ok()
        );
        let stop_at = hits.get() - 3;
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
        let law_s = check_law(sources.law().bytes(), &defs).unwrap();
        let map_s = check_archmap(sources.archmap().bytes(), &defs).unwrap();
        let stopped =
            CheckedInputs::from_checked(sources, defs, law_s, map_s, &stop_ctrl).unwrap_err();
        assert_eq!(stopped.status(), InputStatus::Interrupted);
    }
}
