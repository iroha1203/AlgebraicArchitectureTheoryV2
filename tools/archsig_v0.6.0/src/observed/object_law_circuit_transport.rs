//! 実Operationに沿って数値成分の零性と有限detectorの受理を検査する。
use super::{
    control::{Checkpoint, Control},
    input::CheckedInputs,
    object_law_circuits::{
        LawCircuit, LawCircuitDetector, LawCircuitPoint, LawCircuitsCondition, ObjectLawCircuits,
        ObjectLawCircuitsFailure, object_law_circuits,
    },
    object_law_transport::{
        LawTransportOutcome, ObjectLawTransport, ObjectLawTransportFailure, object_law_transport,
    },
    value_transport::FiniteTransportValue,
};
use crate::{
    construction::{
        ConstructionFailure, maps::DeclarationCorrespondence, readings::ObjectEvaluationPosition,
    },
    types::Type,
};
use std::sync::Arc;
fn tick(c: &mut Control) -> Result<(), ConstructionFailure> {
    c.checkpoint(Checkpoint::ObjectLawCircuitTransport)
        .map_err(Into::into)
}
fn bad(s: &str) -> ConstructionFailure {
    ConstructionFailure::Inconsistent(s.into())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawCircuitTransportRefutation {
    Components {
        source: Vec<(Vec<usize>, Type)>,
        target: Vec<(Vec<usize>, Type)>,
    },
    ZeroEquivalence {
        component: Vec<usize>,
        source: bool,
        target: bool,
    },
    Detector {
        component: Vec<usize>,
        source: bool,
        target: bool,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LawCircuitTransportOutcome {
    Preserved,
    Original(LawTransportOutcome),
    Construction {
        source: LawCircuitsCondition,
        target: LawCircuitsCondition,
    },
    Refuted(LawCircuitTransportRefutation),
    Undetermined,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawCircuitTransportPoint {
    pub source_circuit: usize,
    pub target_circuit: usize,
    pub source_point: Option<usize>,
    pub target_point: Option<usize>,
    pub source_bindings: Vec<(String, FiniteTransportValue)>,
    pub target_bindings: Vec<(String, FiniteTransportValue)>,
    pub source_when: Option<bool>,
    pub target_when: Option<bool>,
    pub source_accepts: Option<bool>,
    pub target_accepts: Option<bool>,
    pub outcome: LawCircuitTransportOutcome,
}
#[derive(Debug)]
pub struct ObjectLawCircuitTransport {
    declarations: DeclarationCorrespondence,
    position: ObjectEvaluationPosition,
    base: ObjectLawTransport,
    source: Option<ObjectLawCircuits>,
    target: Option<ObjectLawCircuits>,
    points: Vec<LawCircuitTransportPoint>,
    outcome: LawCircuitTransportOutcome,
    complete: bool,
}
impl ObjectLawCircuitTransport {
    pub fn base(&self) -> &ObjectLawTransport {
        &self.base
    }
    pub fn source(&self) -> Option<&ObjectLawCircuits> {
        self.source.as_ref()
    }
    pub fn target(&self) -> Option<&ObjectLawCircuits> {
        self.target.as_ref()
    }
    pub fn points(&self) -> &[LawCircuitTransportPoint] {
        &self.points
    }
    pub fn outcome(&self) -> &LawCircuitTransportOutcome {
        &self.outcome
    }
    pub fn is_complete(&self) -> bool {
        self.complete
    }
    pub fn recheck(
        &self,
        inputs: Arc<CheckedInputs>,
        c: &mut Control,
    ) -> Result<(), ObjectLawCircuitTransportFailure> {
        self.base
            .recheck(inputs.clone(), c)
            .map_err(ObjectLawCircuitTransportFailure::Original)?;
        for (source, side) in [(&self.source, true), (&self.target, false)] {
            if let Some(value) = source {
                if let Err(cause) = value.recheck(inputs.clone(), c) {
                    return Err(ObjectLawCircuitTransportFailure::Validation {
                        source: side,
                        cause,
                    });
                }
            }
        }
        let expected = object_law_circuit_transport(
            inputs,
            &self.declarations,
            self.position.object,
            self.position.instance,
            c,
        )?;
        let checked = same(self, &expected, c);
        match checked {
            Ok(true) => Ok(()),
            other => Err(ObjectLawCircuitTransportFailure::Reading {
                cause: LawCircuitTransportFailureCause::Construction(other.err().unwrap_or_else(
                    || bad("成分/circuit保存が現在入力・対象像・全引数・受理と違う"),
                )),
                partial: Box::new(expected),
            }),
        }
    }
}
#[derive(Debug)]
pub enum LawCircuitTransportFailureCause {
    Construction(ConstructionFailure),
    Source(ObjectLawCircuitsFailure),
    Target(ObjectLawCircuitsFailure),
}
impl From<ConstructionFailure> for LawCircuitTransportFailureCause {
    fn from(f: ConstructionFailure) -> Self {
        Self::Construction(f)
    }
}
#[derive(Debug)]
pub enum ObjectLawCircuitTransportFailure {
    Original(ObjectLawTransportFailure),
    Validation {
        source: bool,
        cause: ObjectLawCircuitsFailure,
    },
    Reading {
        cause: LawCircuitTransportFailureCause,
        partial: Box<ObjectLawCircuitTransport>,
    },
}
impl ObjectLawCircuitTransportFailure {
    pub fn partial(&self) -> Option<&ObjectLawCircuitTransport> {
        match self {
            Self::Reading { partial, .. } => Some(partial),
            _ => None,
        }
    }
}
fn indices(
    all: &ObjectLawCircuits,
    object: &crate::construction::maps::ObjectIdentity,
    instance: &crate::construction::readings::ObjectInstance,
    c: &mut Control,
) -> Result<Vec<usize>, ConstructionFailure> {
    let readings = all.base().base().readings();
    let o = readings
        .objects()
        .iter()
        .position(|o| o.identity() == object)
        .ok_or_else(|| bad("circuitの実対象像がない"))?;
    let i = readings
        .instances()
        .iter()
        .position(|i| i == instance)
        .ok_or_else(|| bad("circuitの対応Law instanceがない"))?;
    let mut result = vec![];
    for (index, circuit) in all.circuits().iter().enumerate() {
        tick(c)?;
        if circuit.position
            == (ObjectEvaluationPosition {
                object: o,
                instance: i,
            })
        {
            result.push(index);
        }
    }
    Ok(result)
}
fn pick<'a>(
    circuit: &'a LawCircuit,
    bindings: &[(String, FiniteTransportValue)],
    c: &mut Control,
) -> Result<(Option<usize>, &'a LawCircuitPoint), ConstructionFailure> {
    if let Some(p) = &circuit.uniform {
        return Ok((None, p));
    }
    for (i, p) in circuit.points.iter().enumerate() {
        tick(c)?;
        if p.arguments.len() == bindings.len()
            && p.arguments.iter().zip(bindings).all(|(v, (_, b))| v == b)
        {
            return Ok((Some(i), p));
        }
    }
    Err(bad("circuitに対応する実引数点がない"))
}
fn accepts(
    code: Option<&LawCircuitDetector>,
    bindings: &[(String, FiniteTransportValue)],
    c: &mut Control,
) -> Result<Option<bool>, ConstructionFailure> {
    match code {
        None => Ok(None),
        Some(LawCircuitDetector::Reject) => Ok(Some(false)),
        Some(LawCircuitDetector::Any) => Ok(Some(bindings.is_empty())),
        Some(LawCircuitDetector::Exact(rows)) => {
            for row in rows {
                tick(c)?;
                if row.len() == bindings.len() && row.iter().zip(bindings).all(|(a, (_, b))| a == b)
                {
                    return Ok(Some(true));
                }
            }
            Ok(Some(false))
        }
    }
}
fn point(
    out: &mut ObjectLawCircuitTransport,
    si: usize,
    ti: usize,
    sb: Vec<(String, FiniteTransportValue)>,
    tb: Vec<(String, FiniteTransportValue)>,
    c: &mut Control,
) -> Result<(), ConstructionFailure> {
    tick(c)?;
    let source = &out
        .source
        .as_ref()
        .ok_or_else(|| bad("source circuitがない"))?
        .circuits()[si];
    let target = &out
        .target
        .as_ref()
        .ok_or_else(|| bad("target circuitがない"))?
        .circuits()[ti];
    let (sp, s) = pick(source, &sb, c)?;
    let (tp, t) = pick(target, &tb, c)?;
    let sa = accepts(source.detector.as_ref(), &sb, c)?;
    let ta = accepts(target.detector.as_ref(), &tb, c)?;
    let outcome = match (s.when, t.when, sa, ta) {
        (Some(a), Some(b), _, _) if a != b => {
            LawCircuitTransportOutcome::Refuted(LawCircuitTransportRefutation::ZeroEquivalence {
                component: source.component.clone(),
                source: a,
                target: b,
            })
        }
        (_, _, Some(a), Some(b)) if a != b => {
            LawCircuitTransportOutcome::Refuted(LawCircuitTransportRefutation::Detector {
                component: source.component.clone(),
                source: a,
                target: b,
            })
        }
        (Some(_), Some(_), Some(_), Some(_)) => LawCircuitTransportOutcome::Preserved,
        _ => LawCircuitTransportOutcome::Undetermined,
    };
    out.points.push(LawCircuitTransportPoint {
        source_circuit: si,
        target_circuit: ti,
        source_point: sp,
        target_point: tp,
        source_bindings: sb,
        target_bindings: tb,
        source_when: s.when,
        target_when: t.when,
        source_accepts: sa,
        target_accepts: ta,
        outcome: outcome.clone(),
    });
    if matches!(outcome, LawCircuitTransportOutcome::Refuted(_))
        && !matches!(out.outcome, LawCircuitTransportOutcome::Refuted(_))
    {
        out.outcome = outcome;
    }
    Ok(())
}
fn populate(
    out: &mut ObjectLawCircuitTransport,
    inputs: Arc<CheckedInputs>,
    c: &mut Control,
) -> Result<(), LawCircuitTransportFailureCause> {
    tick(c)?;
    let s = out.base.source_readings().construction();
    out.source = Some(
        object_law_circuits(
            inputs.clone(),
            s.reading(),
            &s.root().snapshot,
            &s.root().subject,
            c,
        )
        .map_err(LawCircuitTransportFailureCause::Source)?,
    );
    let t = out.base.target_readings().construction();
    out.target = Some(
        object_law_circuits(
            inputs,
            t.reading(),
            &t.root().snapshot,
            &t.root().subject,
            c,
        )
        .map_err(LawCircuitTransportFailureCause::Target)?,
    );
    if out.base.outcome() != &LawTransportOutcome::Preserved {
        out.complete = true;
        tick(c)?;
        return Ok(());
    }
    let source = out
        .source
        .as_ref()
        .ok_or_else(|| bad("source circuitがない"))?;
    let target = out
        .target
        .as_ref()
        .ok_or_else(|| bad("target circuitがない"))?;
    if source.condition() != &LawCircuitsCondition::Ready
        || target.condition() != &LawCircuitsCondition::Ready
    {
        out.outcome = LawCircuitTransportOutcome::Construction {
            source: source.condition().clone(),
            target: target.condition().clone(),
        };
        out.complete = true;
        tick(c)?;
        return Ok(());
    }
    let ss = indices(source, out.base.object(), out.base.instance(), c)?;
    let ts = indices(
        target,
        out.base
            .target_object()
            .ok_or_else(|| bad("Lawの対象像がない"))?,
        out.base
            .target_instance()
            .ok_or_else(|| bad("Lawのinstance像がない"))?,
        c,
    )?;
    let mut source_shape = vec![];
    let mut target_shape = vec![];
    for (all, indices, shape) in [
        (source, &ss, &mut source_shape),
        (target, &ts, &mut target_shape),
    ] {
        for &i in indices {
            tick(c)?;
            shape.push((
                all.circuits()[i].component.clone(),
                all.circuits()[i].ty.clone(),
            ));
        }
    }
    if source_shape != target_shape {
        out.outcome =
            LawCircuitTransportOutcome::Refuted(LawCircuitTransportRefutation::Components {
                source: source_shape,
                target: target_shape,
            });
        out.complete = true;
        tick(c)?;
        return Ok(());
    }
    let mut bindings = vec![];
    if let Some(family) = out.base.family() {
        for row in family.rows() {
            tick(c)?;
            bindings.push((
                row.source_bindings().to_vec(),
                row.target_bindings().to_vec(),
            ));
        }
    } else {
        bindings.push((vec![], vec![]));
    }
    let count = ss
        .len()
        .checked_mul(bindings.len())
        .ok_or_else(|| bad("circuit比較点が大きすぎる"))?;
    let mut seen = 0;
    for (s, t) in ss.into_iter().zip(ts) {
        for (sb, tb) in &bindings {
            point(out, s, t, sb.clone(), tb.clone(), c)?;
            seen += 1;
            if seen == count {
                finish(out, c)?;
            }
            c.checkpoint(Checkpoint::ObjectLawCircuitTransportPoint)
                .map_err(ConstructionFailure::from)?;
        }
    }
    if count == 0 {
        finish(out, c)?;
    }
    tick(c)?;
    Ok(())
}
fn finish(out: &mut ObjectLawCircuitTransport, c: &mut Control) -> Result<(), ConstructionFailure> {
    if !matches!(out.outcome, LawCircuitTransportOutcome::Refuted(_)) {
        let mut known = true;
        for point in &out.points {
            tick(c)?;
            if point.outcome != LawCircuitTransportOutcome::Preserved {
                known = false;
            }
        }
        out.outcome = if known {
            LawCircuitTransportOutcome::Preserved
        } else {
            LawCircuitTransportOutcome::Undetermined
        };
    }
    out.complete = true;
    Ok(())
}
fn same(
    a: &ObjectLawCircuitTransport,
    b: &ObjectLawCircuitTransport,
    c: &mut Control,
) -> Result<bool, ConstructionFailure> {
    tick(c)?;
    if a.position != b.position
        || a.declarations != b.declarations
        || a.base.operation() != b.base.operation()
        || a.base.object() != b.base.object()
        || a.base.instance() != b.base.instance()
        || a.base.target_object() != b.base.target_object()
        || a.base.target_instance() != b.base.target_instance()
        || a.base.outcome() != b.base.outcome()
        || a.source.is_some() != b.source.is_some()
        || a.target.is_some() != b.target.is_some()
        || a.outcome != b.outcome
        || a.complete != b.complete
        || a.points.len() != b.points.len()
    {
        return Ok(false);
    }
    for (a, b) in [(&a.source, &b.source), (&a.target, &b.target)] {
        if let (Some(a), Some(b)) = (a, b) {
            tick(c)?;
            if a.base().base().readings() != b.base().base().readings()
                || a.condition() != b.condition()
                || a.is_complete() != b.is_complete()
                || a.circuits().len() != b.circuits().len()
            {
                return Ok(false);
            }
            for (a, b) in a.circuits().iter().zip(b.circuits()) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
        }
    }
    for (a, b) in a.points.iter().zip(&b.points) {
        tick(c)?;
        if a != b {
            return Ok(false);
        }
    }
    tick(c)?;
    Ok(true)
}
pub fn object_law_circuit_transport(
    inputs: Arc<CheckedInputs>,
    declarations: &DeclarationCorrespondence,
    object: usize,
    instance: usize,
    c: &mut Control,
) -> Result<ObjectLawCircuitTransport, ObjectLawCircuitTransportFailure> {
    let base = object_law_transport(inputs.clone(), declarations, object, instance, c)
        .map_err(ObjectLawCircuitTransportFailure::Original)?;
    // 最初の構成checkpointより前に、確定済みの元条件を保持する。
    let outcome = if base.outcome() == &LawTransportOutcome::Preserved {
        LawCircuitTransportOutcome::Undetermined
    } else {
        LawCircuitTransportOutcome::Original(base.outcome().clone())
    };
    let mut out = ObjectLawCircuitTransport {
        declarations: declarations.clone(),
        position: ObjectEvaluationPosition { object, instance },
        base,
        source: None,
        target: None,
        points: vec![],
        outcome,
        complete: false,
    };
    match populate(&mut out, inputs, c) {
        Ok(()) => Ok(out),
        Err(cause) => Err(ObjectLawCircuitTransportFailure::Reading {
            cause,
            partial: Box::new(out),
        }),
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        construction::{
            construct,
            maps::{correspondence, declaration_correspondence},
            readings::object_reading_instances,
        },
        observed::input::{InputSources, check_inputs},
    };
    fn example() -> (Arc<CheckedInputs>, DeclarationCorrespondence, usize, usize) {
        let left = include_bytes!("../../tests/fixtures/object-law-family.atoms.json");
        let right = include_bytes!("../../tests/fixtures/object-law-transport-right.atoms.json");
        let defs =
            crate::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &defs.vocabularies["Left"].digest;
        let rd = &defs.vocabularies["Right"].digest;
        let bridge = include_str!("../../tests/fixtures/object-law-transport-bridge.atoms.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd);
        let defs = crate::definition::check_definitions(&[
            ("left", left),
            ("right", right),
            ("bridge", bridge.as_bytes()),
        ])
        .unwrap();
        let expand = |s: &str| {
            s.replace("@LEFT_DIGEST@", ld)
                .replace("@RIGHT_DIGEST@", rd)
                .replace("@BRIDGE_DIGEST@", &defs.vocabularies["Bridge"].digest)
                .into_bytes()
        };
        let uses = "use vocabulary Left version \"1\" digest \"@LEFT_DIGEST@\";use vocabulary Right version \"1\" digest \"@RIGHT_DIGEST@\";use vocabulary Bridge version \"1\" digest \"@BRIDGE_DIGEST@\";";
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Before {{{uses}law required measure(c:Left.Child,b:Bool):2=0;}}reading After {{{uses}law required measure(d:Right.Child,q:Bool):3=0;}}"
        );
        let i = Arc::new(
            check_inputs(
                InputSources::from_bytes(
                    vec![left.to_vec(), right.to_vec(), bridge.as_bytes().to_vec()],
                    expand(&law),
                    expand(include_str!(
                        "../../tests/fixtures/object-view-transport.archmap.json"
                    )),
                ),
                &mut Control::unlimited(),
            )
            .unwrap(),
        );
        let mapping = correspondence(
            &i,
            "v",
            "m",
            "Before",
            Some("After"),
            &mut Control::unlimited(),
        )
        .unwrap();
        let d = declaration_correspondence(&i, mapping.map().unwrap(), &mut Control::unlimited())
            .unwrap();
        let r = object_reading_instances(
            &i,
            &construct(&i, "Before", "v", "a", &mut Control::unlimited()).unwrap(),
            &mut Control::unlimited(),
        )
        .unwrap();
        let o = r
            .objects()
            .iter()
            .position(|o| o.identity().subject().subject == "p")
            .unwrap();
        let n = r
            .instances()
            .iter()
            .position(|r| {
                r.declaration().name == "Before.measure" && r.bindings()[0].subject().subject == "p"
            })
            .unwrap();
        (i, d, o, n)
    }
    #[test]
    fn recheck_rejects_forged_images_arguments_when_acceptance_references_order_and_aggregation() {
        let (i, d, o, n) = example();
        for mode in 0..18 {
            let mut r =
                object_law_circuit_transport(i.clone(), &d, o, n, &mut Control::unlimited())
                    .unwrap();
            match mode {
                0 => r.points[0].source_circuit += 1,
                1 => r.points[0].target_circuit += 1,
                2 => r.points[0].source_point = None,
                3 => r.points[0].target_point = None,
                4 => r.points[0].source_bindings.clear(),
                5 => r.points[0].target_bindings[0].0 = "changed".into(),
                6 => r.points[0].source_when = Some(false),
                7 => r.points[0].target_when = None,
                8 => r.points[0].source_accepts = Some(false),
                9 => r.points[0].target_accepts = None,
                10 => r.points[0].outcome = LawCircuitTransportOutcome::Undetermined,
                11 => r.points.reverse(),
                12 => r.source = None,
                13 => std::mem::swap(&mut r.source, &mut r.target),
                14 => r.complete = false,
                15 => r.outcome = LawCircuitTransportOutcome::Undetermined,
                16 => r.position.object = 0,
                _ => {
                    r.base = object_law_transport(i.clone(), &d, 0, n, &mut Control::unlimited())
                        .unwrap()
                }
            }
            assert!(
                r.recheck(i.clone(), &mut Control::unlimited()).is_err(),
                "mode {mode}"
            );
        }
    }
}
