//! 完全query patternと元残差から、成分別の有限detectorを生成する。
use super::{
    numeric,
    object_law_compatibility::LawCompatibilityOutcome,
    object_law_residuals::{
        LawNumericShape, LawResidualOutcome, LawResidualRow, ObjectLawResiduals,
        ObjectLawResidualsFailure, object_law_residuals,
    },
    result::ValidationFailure,
    value_transport::FiniteTransportValue,
};
use crate::{
    construction::{ConstructionFailure, profiles::CircuitPattern},
    observed::object_evaluation_table::ObjectEvaluationPosition,
};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::types::Type;
use archsig_input::input::CheckedInputs;
use std::sync::Arc;
#[track_caller]
fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(internal!(s))
}
fn tick(c: &Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectLawCircuits)
        .map_err(Into::into)
}
fn invalid(f: ValidationFailure) -> ConstructionFailure {
    match f {
        ValidationFailure::Stop(s) => s.into(),
        f => ConstructionFailure::Inconsistent(
            f.internal_context(format!("circuitの数値成分: {f:?}")),
        ),
    }
}
/// 既存detectorの有限code。Exactは実引数tupleの有限選言。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawCircuitDetector {
    Reject,
    Any,
    Exact(Vec<Vec<FiniteTransportValue>>),
}
/// 元残差結果のevaluation/row/caseを指す。row=Noneは適用外の一様読取り。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawCircuitWitness {
    pub evaluation: usize,
    pub row: Option<usize>,
    pub case: usize,
    pub original_evaluation: Option<usize>,
    pub epsilon_producer: Option<usize>,
    pub when: Option<bool>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawCircuitPoint {
    pub arguments: Vec<FiniteTransportValue>,
    pub witnesses: Vec<LawCircuitWitness>,
    pub when: Option<bool>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawCircuit {
    pub position: ObjectEvaluationPosition,
    pub pattern: Option<CircuitPattern>,
    pub shape: LawNumericShape,
    pub component: Vec<usize>,
    pub ty: Type,
    /// 適用外の一様読取り以外は全実引数を元順序で保持する。
    pub points: Vec<LawCircuitPoint>,
    pub uniform: Option<LawCircuitPoint>,
    /// Noneは構成未決/非対応/構成条件不成立であり、Rejectへ補わない。
    pub detector: Option<LawCircuitDetector>,
    pub complete: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawCircuitsCondition {
    Ready,
    ConditionFailed,
    Undetermined,
    Unsupported,
}
#[derive(Debug)]
pub struct ObjectLawCircuits {
    base: ObjectLawResiduals,
    circuits: Vec<LawCircuit>,
    condition: LawCircuitsCondition,
    complete: bool,
}
impl ObjectLawCircuits {
    pub fn base(&self) -> &ObjectLawResiduals {
        &self.base
    }
    pub fn circuits(&self) -> &[LawCircuit] {
        &self.circuits
    }
    pub fn condition(&self) -> &LawCircuitsCondition {
        &self.condition
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &Control,
    ) -> Result<(), ObjectLawCircuitsFailure> {
        self.base
            .recheck(Arc::clone(&inputs), c)
            .map_err(ObjectLawCircuitsFailure::Original)?;
        let reading = self.base.base().readings().construction();
        let expected = object_law_circuits(
            inputs,
            reading.reading(),
            &reading.root().snapshot,
            &reading.root().subject,
            c,
        )?;
        let checked = same(self, &expected, c);
        match checked {
            Ok(true) => Ok(()),
            result => Err(ObjectLawCircuitsFailure::Reading {
                cause: result.err().unwrap_or_else(|| {
                    bad("circuitが現在入力のpattern・全case・成分・detectorと違う")
                }),
                partial: Box::new(expected),
            }),
        }
    }
}
#[derive(Debug)]
pub enum ObjectLawCircuitsFailure {
    Original(ObjectLawResidualsFailure),
    Reading {
        cause: ConstructionFailure,
        partial: Box<ObjectLawCircuits>,
    },
}
impl ObjectLawCircuitsFailure {
    pub fn partial(&self) -> Option<&ObjectLawCircuits> {
        match self {
            Self::Reading { partial, .. } => Some(partial),
            _ => None,
        }
    }
}
fn condition(base: &ObjectLawResiduals) -> LawCircuitsCondition {
    let original = base.base().outcome();
    if matches!(original, Some(LawCompatibilityOutcome::Refuted(_)))
        || matches!(
            base.outcome(),
            Some(LawResidualOutcome::Refuted { .. } | LawResidualOutcome::ArgumentsDiffer)
        )
    {
        LawCircuitsCondition::ConditionFailed
    } else if !base.is_complete()
        || !base.base().profiles().is_complete()
        || !matches!(original, Some(LawCompatibilityOutcome::Compatible))
        || matches!(
            base.outcome(),
            None | Some(LawResidualOutcome::Undetermined)
        )
    {
        LawCircuitsCondition::Undetermined
    } else if matches!(base.outcome(), Some(LawResidualOutcome::Unsupported)) {
        LawCircuitsCondition::Unsupported
    } else {
        LawCircuitsCondition::Ready
    }
}
fn leaves(
    ty: &Type,
    path: &mut Vec<usize>,
    out: &mut Vec<(Vec<usize>, Type)>,
    c: &Control,
) -> Result<(), ConstructionFailure> {
    stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || {
        tick(c)?;
        match ty {
            Type::Tuple(items) => {
                for (i, ty) in items.iter().enumerate() {
                    path.push(i);
                    leaves(ty, path, out, c)?;
                    path.pop();
                }
            }
            Type::Z | Type::Q | Type::Fp(_) => out.push((path.clone(), ty.clone())),
            _ => return Err(bad("circuitの成分が数値型でない")),
        }
        Ok(())
    })
}
fn point(
    base: &ObjectLawResiduals,
    evaluation: usize,
    row: Option<usize>,
    r: &LawResidualRow,
    component: usize,
    arguments: Vec<FiniteTransportValue>,
    c: &Control,
) -> Result<LawCircuitPoint, ConstructionFailure> {
    let mut out = LawCircuitPoint {
        arguments,
        witnesses: vec![],
        when: None,
    };
    let mut consensus = None;
    let mut known = r.complete && !r.cases.is_empty();
    for (case, source) in r.cases.iter().enumerate() {
        tick(c)?;
        let value = if !source.complete {
            None
        } else {
            match source.reading.application().value() {
                Some(false) => Some(false),
                Some(true) => match source
                    .components
                    .get(component)
                    .and_then(|v| v.epsilon.as_ref())
                {
                    Some(epsilon) => {
                        let zero = numeric::zero(&epsilon.ty(), c).map_err(invalid)?;
                        Some(epsilon.scalar() != &zero)
                    }
                    None => None,
                },
                None => None,
            }
        };
        if value.is_none() || consensus.is_some_and(|previous| Some(previous) != value) {
            known = false;
        }
        if consensus.is_none() {
            consensus = value;
        }
        out.witnesses.push(LawCircuitWitness {
            evaluation,
            row,
            case,
            original_evaluation: source.evaluation,
            epsilon_producer: source.epsilon_producer,
            when: value,
        });
    }
    if known {
        out.when = consensus;
    }
    // 元結果を持つため参照先のDAG/支持/Scopeはこのbaseから辿る。
    if base.evaluations().get(evaluation).is_none() {
        return Err(bad("circuitの元評価がない"));
    }
    Ok(out)
}
fn build(out: &mut ObjectLawCircuits, c: &Control) -> Result<(), ConstructionFailure> {
    let mut plan = vec![];
    for e in 0..out.base.evaluations().len() {
        tick(c)?;
        let source = &out.base.evaluations()[e];
        let (LawNumericShape::Equality { ty, .. } | LawNumericShape::Conjunction { ty, .. }) =
            &source.shape
        else {
            continue;
        };
        let mut components = vec![];
        leaves(ty, &mut vec![], &mut components, c)?;
        for (component, (path, ty)) in components.into_iter().enumerate() {
            plan.push((e, component, path, ty));
        }
    }
    let count = plan.len();
    for (ordinal, (e, component, path, ty)) in plan.into_iter().enumerate() {
        tick(c)?;
        let source = &out.base.evaluations()[e];
        let profile = out
            .base
            .base()
            .profiles()
            .profiles()
            .get(source.position.object)
            .ok_or_else(|| bad("circuitのprofileがない"))?;
        // 複製前にquery全体を協調走査する。UとF内R/Eは元profileが構成済み。
        if let Some(pattern) = profile.pattern() {
            for _ in pattern.queries() {
                tick(c)?;
            }
        }
        out.circuits.push(LawCircuit {
            position: source.position,
            pattern: profile.pattern().cloned(),
            shape: source.shape.clone(),
            component: path,
            ty,
            points: vec![],
            uniform: None,
            detector: None,
            complete: false,
        });
        let n = out.circuits.len() - 1;
        let family = out.base.base().evaluations()[e].family();
        if source.rows.len() != family.rows().len() {
            return Err(bad("circuitの元引数行数が違う"));
        }
        for (row, r) in source.rows.iter().enumerate() {
            let arguments = family.rows()[row]
                .bindings()
                .iter()
                .map(|(_, v)| v.clone())
                .collect();
            let p = point(&out.base, e, Some(row), r, component, arguments, c)?;
            out.circuits[n].points.push(p);
            c.checkpoint(Checkpoint::Work)?;
        }
        if let Some(row) = &source.uniform {
            out.circuits[n].uniform = Some(point(&out.base, e, None, row, component, vec![], c)?);
        }
        let circuit = &mut out.circuits[n];
        let known = source.complete
            && family.is_complete()
            && family.missing().is_empty()
            && circuit
                .points
                .iter()
                .chain(circuit.uniform.iter())
                .all(|p| p.when.is_some());
        if out.condition == LawCircuitsCondition::Ready && known && circuit.pattern.is_some() {
            let mut exact = vec![];
            for p in &circuit.points {
                tick(c)?;
                if p.when == Some(true) {
                    exact.push(p.arguments.clone());
                }
            }
            // 一様の適用外は常にfalse。引数を捏造してanyへ変えない。
            circuit.detector = Some(if exact.is_empty() {
                LawCircuitDetector::Reject
            } else if family.domains().is_empty() {
                LawCircuitDetector::Any
            } else {
                LawCircuitDetector::Exact(exact)
            });
        }
        circuit.complete = source.complete;
        if ordinal + 1 == count {
            out.complete = true;
        }
        c.checkpoint(Checkpoint::ObjectLawCircuit)?;
    }
    out.complete = true;
    tick(c)
}
fn same(
    a: &ObjectLawCircuits,
    b: &ObjectLawCircuits,
    c: &Control,
) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    if a.condition != b.condition
        || a.complete != b.complete
        || a.circuits.len() != b.circuits.len()
    {
        return Ok(false);
    }
    for (a, b) in a.circuits.iter().zip(&b.circuits) {
        tick(c)?;
        if a != b {
            return Ok(false);
        }
    }
    tick(c)?;
    Ok(true)
}
pub fn object_law_circuits(
    inputs: Arc<CheckedInputs>,
    reading: &str,
    snapshot: &str,
    root: &str,
    c: &Control,
) -> Result<ObjectLawCircuits, ObjectLawCircuitsFailure> {
    let base = object_law_residuals(inputs, reading, snapshot, root, c)
        .map_err(ObjectLawCircuitsFailure::Original)?;
    let condition = condition(&base);
    let mut out = ObjectLawCircuits {
        base,
        circuits: vec![],
        condition,
        complete: false,
    };
    match build(&mut out, c) {
        Ok(()) => Ok(out),
        Err(cause) => Err(ObjectLawCircuitsFailure::Reading {
            cause,
            partial: Box::new(out),
        }),
    }
}

#[cfg(test)]
mod internal_error_tests {
    use super::*;

    #[test]
    fn contextual_circuit_failure_keeps_origin_and_existing_message() {
        let original = internal!("元の数値エラー");
        let location = original.location();
        let converted = invalid(ValidationFailure::Internal(original));
        let ConstructionFailure::Inconsistent(ref error) = converted else {
            panic!("内部エラー以外へ変換された")
        };
        assert_eq!(error.location(), location);
        assert_eq!(
            error.message(),
            "circuitの数値成分: Internal(\"元の数値エラー\")"
        );
        let wrapped =
            crate::observed::object_law_transport::ObjectLawTransportFailure::Construction(
                converted,
            );
        let context = wrapped.internal_context("law context".into());
        assert_eq!(context.location(), location);
        assert_eq!(context.message(), "law context");
    }
}
