//! 元の Q パラメータ上で半空間と証拠を表示する。
use super::*;
use crate::observed::{
    environment::field_change::{Linear, Polyhedron},
    field_polyhedron::{self, Outcome},
};
use field_linear_result::{map, vector};
use linear_result::{Parts, module};

#[allow(clippy::too_many_arguments)]
pub(super) fn build(
    b: &mut Builder<'_>,
    linear: &Linear,
    polyhedron: &Polyhedron,
    ring: NodeRef,
    parameter_module: NodeRef,
    parameters: NodeRef,
    states: NodeRef,
    action: NodeRef,
    equations: NodeRef,
    rhs: NodeRef,
    requirements: &[NodeRef],
    c: &Control,
) -> Result<Parts, ValidationFailure> {
    let original =
        field_polyhedron::halfspaces(&linear.equations, &linear.rhs, &polyhedron.inequalities, c)?;
    field_polyhedron::verify(&original, linear.parameter_count, &polyhedron.outcome, c)?;
    let mut a = Vec::new();
    let mut upper = Vec::new();
    for halfspace in &polyhedron.inequalities {
        c.checkpoint(Checkpoint::PrimitiveValuation)?;
        a.push(halfspace.coefficients.clone());
        upper.push(halfspace.rhs.clone());
    }
    let inequality_module = module(b, ring, a.len(), "free", vec![])?;
    let inequalities = map(
        b,
        parameter_module,
        inequality_module,
        &a,
        linear.parameter_count,
        c,
    )?;
    let upper_bounds = vector(b, inequality_module, &upper, c)?;
    let mut args = vec![equations, rhs, inequalities, upper_bounds];
    args.extend(requirements);
    let mut certificate_fields = BTreeMap::<String, Json>::from([
        ("equalities".into(), equations.wire()),
        ("rhs".into(), rhs.wire()),
        ("inequalities".into(), inequalities.wire()),
        ("upper_bounds".into(), upper_bounds.wire()),
    ]);
    let outcome = match &polyhedron.outcome {
        Outcome::Empty(row) => {
            let weight_module = module(b, ring, original.len(), "free", vec![])?;
            let weights = vector(b, weight_module, &row.combination, c)?;
            args.push(weights);
            certificate_fields.insert("contradiction".into(), weights.wire());
            "empty"
        }
        Outcome::Unique { point, bounds } => {
            let point = vector(b, parameter_module, point, c)?;
            args.push(point);
            certificate_fields.insert("point".into(), point.wire());
            let weight_module = module(b, ring, original.len(), "free", vec![])?;
            let mut entries = Vec::new();
            for (lower, upper) in bounds {
                c.checkpoint(Checkpoint::PrimitiveValuation)?;
                let lower = vector(b, weight_module, &lower.combination, c)?;
                let upper = vector(b, weight_module, &upper.combination, c)?;
                args.extend([lower, upper]);
                entries.push(Json::obj([
                    ("lower", lower.wire()),
                    ("upper", upper.wire()),
                ]));
            }
            certificate_fields.insert("coordinate_bounds".into(), Json::Arr(entries));
            "unique"
        }
        Outcome::Multiple { first, second } => {
            let first = vector(b, parameter_module, first, c)?;
            let second = vector(b, parameter_module, second, c)?;
            args.extend([first, second]);
            certificate_fields.insert("point".into(), first.wire());
            certificate_fields.insert("second".into(), second.wire());
            "multiple"
        }
    };
    certificate_fields.insert("outcome".into(), Json::str(outcome));
    let certificate = b.push(
        NodeType::Evidence,
        "evidence",
        Json::obj([
            ("kind", Json::str(EvidenceKind::RationalPolyhedron.name())),
            ("data", Json::Obj(certificate_fields.into())),
        ]),
        args,
        None,
    )?;
    Ok(Parts {
        parameters,
        states,
        action,
        certificate,
        representation: Json::obj([
            ("kind", Json::str("rational_polyhedron")),
            ("equalities", equations.wire()),
            ("rhs", rhs.wire()),
            ("inequalities", inequalities.wire()),
            ("upper_bounds", upper_bounds.wire()),
            ("certificate", certificate.wire()),
        ]),
        representation_args: vec![equations, rhs, inequalities, upper_bounds, certificate],
    })
}
