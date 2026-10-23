//! 元の共有K[X]と原式の評価を、型付きnative DAGへ保持する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::Environment,
    equation_polynomial::EquationPolynomial,
    input::CheckedInputs,
    object_equation_presentation::{
        EquationGuard, EquationPresentation, EquationPresentationFailure,
        EquationPresentationStatus, object_equation_presentation,
    },
    result::*,
};
use crate::{
    canonical::Json,
    issue::Location,
    law::{ast::Role, model::Signature},
    result::location_wire,
    types::Type,
};
use std::sync::Arc;

#[path = "polynomial_law_family.rs"]
mod family;
#[path = "polynomial_law_reading.rs"]
mod reading;
#[path = "polynomial_law_sources.rs"]
mod sources;

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::EquationPresentation)?;
    Ok(())
}
fn refs(values: &[NodeRef]) -> Json {
    Json::Arr(values.iter().map(|r| r.wire()).collect())
}
fn binding_values(bindings: &[Binding]) -> Json {
    Json::Arr(
        bindings
            .iter()
            .map(|b| Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())]))
            .collect(),
    )
}
fn indices(values: &[usize]) -> Json {
    Json::Arr(values.iter().map(|n| Json::Nat(*n as u64)).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Variable {
    field: Fact,
    component: Vec<usize>,
    ty: Type,
}
impl Variable {
    fn wire(&self) -> Json {
        Json::obj([
            (
                "position",
                Json::obj([
                    ("kind", Json::str("observation")),
                    ("field", self.field.wire()),
                    ("component", indices(&self.component)),
                ]),
            ),
            ("type", self.ty.wire()),
        ])
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Transform {
    Substitute,
    Project,
    Equal,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ParameterDomain {
    pub name: String,
    pub ty: Type,
    pub occurrence: (usize, usize),
    pub reference: NodeRef,
    pub values: Vec<NodeRef>,
}
#[derive(Clone)]
pub(super) struct FamilyInputs {
    pub architecture: Arc<ArchitectureWitness>,
    pub object: usize,
    pub template: Original,
    pub base: Original,
    pub parameters: Vec<ParameterDomain>,
    pub base_rows: Vec<NodeRef>,
    pub target_rows: Vec<NodeRef>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Original {
    pub instance: usize,
    pub row: Option<usize>,
    pub bindings: Vec<Binding>,
    pub parameters: Vec<(String, Type)>,
    pub parameter_domains: Option<Vec<ParameterDomain>>,
    pub body: NodeRef,
    pub guard: Option<NodeRef>,
    pub reference: NodeRef,
    pub operands: Option<((NodeRef, Type), (NodeRef, Type))>,
    pub quantifiers: Vec<Quantifier>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Part {
    Equation(super::equation_presentation_node::Part),
    Scalar(Scalar),
    ReadingValue {
        value: Scalar,
        arguments: Vec<NodeRef>,
        wire: Json,
    },
    ReadingDomain {
        ty: Type,
        elements: Option<Vec<NodeRef>>,
    },
    ObservedBoolean {
        origin: NodeRef,
        body: bool,
        value: Scalar,
        support: Vec<Fact>,
        scope: Scope,
    },
    Source {
        quantifiers: Vec<Quantifier>,
        instance: usize,
        row: Option<usize>,
        expression: usize,
        location: Location,
        ty: Type,
        parameters: Vec<(String, Type)>,
        bindings: Vec<Binding>,
    },
    Transform {
        quantifiers: Vec<Quantifier>,
        operation: Transform,
        parameters: Vec<(String, Type)>,
        ty: Type,
        operands: Vec<NodeRef>,
        bindings: Vec<Binding>,
        position: Option<usize>,
    },
    LawInstance {
        quantifiers: Vec<Quantifier>,
        instance: usize,
        row: Option<usize>,
        name: String,
        role: Role,
        occurrence: Location,
        bindings: Vec<Binding>,
        guard: Option<NodeRef>,
        body: NodeRef,
    },
    Domain {
        ring: NodeRef,
        ty: Type,
    },
    Base(Type),
    Ring {
        base: NodeRef,
        variables: Vec<Variable>,
    },
    Polynomial {
        ring: NodeRef,
        terms: Vec<(NodeRef, Vec<usize>)>,
    },
    Ideal {
        ring: NodeRef,
        generators: Vec<NodeRef>,
        required: bool,
    },
    Evaluation {
        source: NodeRef,
        target: NodeRef,
        images: Vec<NodeRef>,
    },
}
impl Part {
    fn quantifiers(&self) -> &[Quantifier] {
        match self {
            Self::Source { quantifiers, .. }
            | Self::Transform { quantifiers, .. }
            | Self::LawInstance { quantifiers, .. } => quantifiers,
            Self::Equation(v) => v.quantifiers(),
            _ => &[],
        }
    }
    fn ty(&self) -> NodeType {
        NodeType::Construction(match self {
            Self::Equation(v) => return v.ty(),
            Self::Scalar(s)
            | Self::ReadingValue { value: s, .. }
            | Self::ObservedBoolean { value: s, .. } => {
                return NodeType::Value(s.ty());
            }
            Self::Source { ty, .. } | Self::Transform { ty, .. } => {
                return NodeType::Expression(ty.clone());
            }
            Self::LawInstance { .. } => return NodeType::LawInstance,
            Self::Domain { .. } | Self::ReadingDomain { .. } => return NodeType::Domain,
            Self::Base(_) | Self::Ring { .. } => T::Ring,
            Self::Polynomial { .. } => T::Polynomial,
            Self::Ideal { .. } => T::Ideal,
            Self::Evaluation { .. } => T::RingMap,
        })
    }
    fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Equation(v) => v.arguments(),
            Self::Scalar(_) | Self::Base(_) => vec![],
            Self::ReadingValue { arguments, .. } => arguments.clone(),
            Self::ObservedBoolean { origin, .. } => vec![*origin],
            Self::ReadingDomain { elements, .. } => elements.iter().flatten().copied().collect(),
            Self::Source { bindings, .. } => bindings.iter().map(|b| b.value).collect(),
            Self::Transform {
                operands, bindings, ..
            } => operands
                .iter()
                .copied()
                .chain(bindings.iter().map(|b| b.value))
                .collect(),
            Self::LawInstance {
                bindings,
                guard,
                body,
                ..
            } => bindings
                .iter()
                .map(|b| b.value)
                .chain(guard.iter().copied())
                .chain(std::iter::once(*body))
                .collect(),

            Self::Domain { ring, .. } => vec![*ring],
            Self::Ring { base, .. } => vec![*base],
            Self::Polynomial { ring, terms } => std::iter::once(*ring)
                .chain(terms.iter().map(|t| t.0))
                .collect(),
            Self::Ideal {
                ring, generators, ..
            } => std::iter::once(*ring)
                .chain(generators.iter().copied())
                .collect(),
            Self::Evaluation {
                source,
                target,
                images,
            } => [*source, *target]
                .into_iter()
                .chain(images.iter().copied())
                .collect(),
        }
    }
    fn construction(&self) -> &'static str {
        match self {
            Self::Equation(v) => v.construction(),
            Self::Scalar(_) | Self::ReadingValue { .. } | Self::ObservedBoolean { .. } => "binding",
            Self::Source { .. } | Self::Transform { .. } => "expression",
            Self::LawInstance { .. } => "law_instance",
            Self::Domain { .. } | Self::ReadingDomain { .. } => "domain",
            Self::Base(_) | Self::Ring { .. } => "ring",
            Self::Polynomial { .. } => "polynomial",
            Self::Ideal { .. } => "ideal",
            Self::Evaluation { .. } => "ring_map",
        }
    }
    fn wire(&self) -> Json {
        match self {
            Self::Equation(v) => v.wire(),
            Self::Scalar(v) | Self::ObservedBoolean { value: v, .. } => v.wire(),
            Self::ReadingValue { wire, .. } => wire.clone(),
            Self::Source {
                location,
                bindings,
                parameters,
                ..
            } => Json::obj([
                ("kind", Json::str("source")),
                ("location", location_wire(location)),
                (
                    "parameters",
                    Json::Arr(
                        parameters
                            .iter()
                            .map(|(name, ty)| {
                                Json::obj([("name", Json::str(name)), ("type", ty.wire())])
                            })
                            .collect(),
                    ),
                ),
                ("bindings", binding_values(bindings)),
            ]),
            Self::Transform {
                operation,
                parameters,
                operands,
                bindings,
                position,
                ..
            } => {
                let mut value = Json::obj([
                    ("kind", Json::str("transform")),
                    (
                        "operation",
                        Json::str(match operation {
                            Transform::Substitute => "substitute",
                            Transform::Project => "project",
                            Transform::Equal => "equal",
                        }),
                    ),
                    ("operands", refs(operands)),
                    (
                        "parameters",
                        Json::Arr(
                            parameters
                                .iter()
                                .map(|(name, ty)| {
                                    Json::obj([("name", Json::str(name)), ("type", ty.wire())])
                                })
                                .collect(),
                        ),
                    ),
                    ("bindings", binding_values(bindings)),
                ]);
                if let (Some(position), Json::Obj(fields)) = (position, &mut value) {
                    fields.insert("position".into(), Json::Nat(*position as u64));
                }
                value
            }
            Self::LawInstance {
                name,
                role,
                occurrence,
                bindings,
                guard,
                body,
                ..
            } => {
                let mut value = Json::obj([
                    ("name", Json::str(name)),
                    (
                        "role",
                        Json::str(match role {
                            Role::Required => "required",
                            Role::Optional => "optional",
                        }),
                    ),
                    ("occurrence", location_wire(occurrence)),
                    ("bindings", binding_values(bindings)),
                    ("body", body.wire()),
                ]);
                if let (Some(guard), Json::Obj(fields)) = (guard, &mut value) {
                    fields.insert("guard".into(), guard.wire());
                }
                value
            }

            Self::ReadingDomain { ty, elements } => match elements {
                Some(elements) => Json::obj([
                    ("kind", Json::str("finite")),
                    ("type", ty.wire()),
                    ("elements", refs(elements)),
                ]),
                None => Json::obj([("kind", Json::str("type")), ("type", ty.wire())]),
            },
            Self::Domain { ty, .. } => {
                Json::obj([("kind", Json::str("type")), ("type", ty.wire())])
            }
            Self::Base(ty) => Json::obj([("kind", Json::str("scalar")), ("scalar", ty.wire())]),
            Self::Ring { base, variables } => Json::obj([
                ("kind", Json::str("polynomial")),
                ("base", base.wire()),
                (
                    "variables",
                    Json::Arr(variables.iter().map(Variable::wire).collect()),
                ),
            ]),
            Self::Polynomial { ring, terms } => Json::obj([
                ("ring", ring.wire()),
                (
                    "terms",
                    Json::Arr(
                        terms
                            .iter()
                            .map(|(coefficient, powers)| {
                                Json::obj([
                                    ("coefficient", coefficient.wire()),
                                    ("powers", indices(powers)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            Self::Ideal {
                ring,
                generators,
                required,
            } => Json::obj([
                ("ring", ring.wire()),
                ("generators", refs(generators)),
                (
                    "kind",
                    Json::str(if *required { "obstruction" } else { "witness" }),
                ),
            ]),
            Self::Evaluation {
                source,
                target,
                images,
            } => Json::obj([
                ("kind", Json::str("polynomial")),
                ("source", source.wire()),
                ("target", target.wire()),
                ("images", refs(images)),
            ]),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Coordinate {
    pub occurrence: usize,
    pub instance: NodeRef,
    pub lhs: NodeRef,
    pub rhs: NodeRef,
    pub position: crate::construction::readings::ObjectEvaluationPosition,
    pub row: Option<usize>,
    pub case: usize,
    pub component: Vec<usize>,
    pub ty: Type,
    pub required: bool,
    pub ring: Option<NodeRef>,
    pub left: Option<NodeRef>,
    pub right: Option<NodeRef>,
    pub nu: Option<NodeRef>,
    pub epsilon: Option<NodeRef>,
    pub residual: Option<NodeRef>,
    pub witness: Option<NodeRef>,
    pub guard: EquationGuard,
    pub status: EquationPresentationStatus,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Unavailable {
    pub declaration: String,
    pub feature: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Diagram {
    pub unavailable: Option<Unavailable>,
    pub context: Option<NodeRef>,
    pub presentations: Vec<Option<NodeRef>>,
    pub originals: Vec<Original>,
    pub rings: Vec<NodeRef>,
    pub domains: Vec<NodeRef>,
    pub bases: Vec<NodeRef>,
    pub required: Vec<NodeRef>,
    pub evaluations: Vec<Option<NodeRef>>,
    pub coordinates: Vec<Coordinate>,
    pub readings: Vec<reading::Reading>,
    pub status: EquationPresentationStatus,
}
#[derive(Clone)]
pub(super) struct Source {
    inputs: Arc<CheckedInputs>,
    architecture: Arc<ArchitectureWitness>,
    reference: NodeRef,
    object: usize,
    core: Option<Arc<EquationPresentation>>,
    base: usize,
    parts: Vec<Part>,
    outputs: Diagram,
    owned_outputs: Option<Vec<Diagram>>,
    support: Vec<Fact>,
    scope: Scope,
}
impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PolynomialLawSource")
            .field("reference", &self.reference)
            .field("object", &self.object)
            .field("base", &self.base)
            .finish()
    }
}
#[derive(Clone, Debug)]
pub(crate) struct Data {
    source: Arc<Source>,
    index: usize,
}
impl PartialEq for Data {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.source, &other.source) && self.index == other.index
    }
}
impl Eq for Data {}
impl Data {
    pub(super) fn family_inputs(
        &self,
        reference: NodeRef,
    ) -> Result<Option<FamilyInputs>, ValidationFailure> {
        self.position(reference.0)?;
        if self.source.object != 0 {
            return Ok(None);
        }
        let outputs = std::iter::once((0, &self.source.outputs)).chain(
            self.source
                .owned_outputs
                .iter()
                .flatten()
                .enumerate()
                .map(|(i, d)| (i + 1, d)),
        );
        let Some((object, output, original)) = outputs
            .filter_map(|(i, d)| {
                d.originals
                    .iter()
                    .find(|o| o.reference == reference && o.row.is_none())
                    .map(|o| (i, d, o))
            })
            .next()
        else {
            return Ok(None);
        };
        let Some(base) = self
            .source
            .outputs
            .originals
            .iter()
            .find(|o| o.instance == original.instance && o.row.is_none())
        else {
            return Err("元Law族のbase templateがない".into());
        };
        let Some(parameters) = &base.parameter_domains else {
            return Ok(None);
        };
        if parameters.is_empty() || base.parameters.len() != parameters.len() {
            return Ok(None);
        }
        let Some(core) = &self.source.core else {
            return Ok(None);
        };
        let target = core
            .base()
            .base()
            .evaluations()
            .iter()
            .find(|e| e.position().object == object && e.position().instance == original.instance)
            .ok_or("元Law族の対象読取りがない")?;
        if !target.family().is_complete() || !target.family().missing().is_empty() {
            return Ok(None);
        }
        Ok(Some(FamilyInputs {
            architecture: self.source.architecture.clone(),
            object,
            template: original.clone(),
            base: base.clone(),
            parameters: parameters.clone(),
            base_rows: self
                .source
                .outputs
                .originals
                .iter()
                .filter(|o| o.instance == original.instance && o.row.is_some())
                .map(|o| o.reference)
                .collect(),
            target_rows: output
                .originals
                .iter()
                .filter(|o| o.instance == original.instance && o.row.is_some())
                .map(|o| o.reference)
                .collect(),
        }))
    }
    pub(super) fn evaluation_origin(
        &self,
        reference: NodeRef,
    ) -> Result<Option<super::law_evaluation::Origin>, ValidationFailure> {
        self.position(reference.0)?;
        let Some(Part::LawInstance {
            name,
            bindings,
            body,
            guard,
            ..
        }) = self.source.parts.get(self.index)
        else {
            return Ok(None);
        };
        let outputs: Vec<_> = std::iter::once((self.source.object, &self.source.outputs))
            .chain(
                self.source
                    .owned_outputs
                    .iter()
                    .flatten()
                    .enumerate()
                    .map(|(i, d)| (i + 1, d)),
            )
            .collect();
        let (object, diagram) = outputs
            .into_iter()
            .find(|(_, d)| d.originals.iter().any(|o| o.reference == reference))
            .ok_or("元多項式Law行が出力表にない")?;
        let reading = diagram.readings.iter().find(|r| r.instance == reference);
        let expr = |r: NodeRef| -> Result<usize, ValidationFailure> {
            match self
                .source
                .parts
                .get(r.0.checked_sub(self.source.base).ok_or("元式が計画外")?)
            {
                Some(Part::Source { expression, .. }) => Ok(*expression),
                _ => Err("元Law式がSourceでない".into()),
            }
        };
        Ok(Some(super::law_evaluation::Origin {
            architecture: self.source.architecture.clone(),
            object,
            declaration: name.clone(),
            bindings: bindings.clone(),
            body: expr(*body)?,
            body_reference: *body,
            guard: guard.map(expr).transpose()?,
            ready: reading.is_some_and(|r| {
                matches!(
                    r.application,
                    Some(super::object_law_transport::LawApplication::Guard(_))
                )
            }),
            outside: reading.is_some_and(|r| matches!(r.application, Some(super::object_law_transport::LawApplication::OutsideObject))),
            body_allowed: reading
                .is_some_and(|r| r.application.as_ref().and_then(|a| a.value()) != Some(false)),
            scope: super::law_evaluation::base_scope(&self.source.architecture, name)?,
        }))
    }

    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        match self.source.parts.get(self.index) {
            Some(
                Part::Scalar(s)
                | Part::ReadingValue { value: s, .. }
                | Part::ObservedBoolean { value: s, .. },
            ) => Some(s),
            _ => None,
        }
    }
    pub(super) fn scope_domain_type(&self) -> Option<&Type> {
        match self.source.parts.get(self.index) {
            Some(Part::ReadingDomain { ty, .. }) => Some(ty),
            _ => None,
        }
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        std::iter::once(self.source.reference)
            .chain(self.part().arguments())
            .collect()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction()
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        if let Part::ObservedBoolean { support, scope, .. } = self.part() {
            return (support.clone(), scope.clone());
        }
        let mut scope = self.source.scope.clone();
        scope
            .quantifiers
            .extend_from_slice(self.part().quantifiers());
        (self.source.support.clone(), scope)
    }
    pub(super) fn position(&self, at: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || self.source.base.checked_add(self.index) != Some(at)
        {
            return Err("多項式の生成位置が元計画と違う".into());
        }
        Ok(())
    }
}
fn push(
    parts: &mut Vec<Part>,
    base: usize,
    part: Part,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    tick(c)?;
    let index = base
        .checked_add(parts.len())
        .ok_or("多項式の生成番号が範囲外")?;
    parts.push(part);
    Ok(NodeRef(index))
}
fn polynomial(
    parts: &mut Vec<Part>,
    base: usize,
    p: &EquationPolynomial,
    ring: NodeRef,
    ty: &Type,
    variables: usize,
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    tick(c)?;
    if &p.ty != ty {
        return Err("多項式の係数型が元環と違う".into());
    }
    let zero = super::numeric::zero(ty, c)?;
    let mut terms = vec![];
    for term in &p.terms {
        tick(c)?;
        if term.coefficient.ty() != *ty || term.coefficient.scalar() == &zero {
            return Err("多項式に別型または零係数がある".into());
        }
        let mut powers = vec![0usize; variables];
        for variable in &term.variables {
            tick(c)?;
            let power = powers.get_mut(*variable).ok_or("多項式の元記号が範囲外")?;
            *power = power.checked_add(1).ok_or("多項式の冪が範囲外")?;
        }
        terms.push((powers, term.coefficient.scalar().clone()));
    }
    // 元計算核のsparse記号列順から、公開payloadのdense powers辞書順へ変換する。
    terms.sort_by(|a, b| a.0.cmp(&b.0));
    for pair in terms.windows(2) {
        tick(c)?;
        if pair[0].0 == pair[1].0 {
            return Err("多項式の同冪項が未集約".into());
        }
    }
    let mut values = vec![];
    for (powers, coefficient) in terms {
        tick(c)?;
        let coefficient = push(parts, base, Part::Scalar(coefficient), c)?;
        values.push((coefficient, powers));
    }
    push(
        parts,
        base,
        Part::Polynomial {
            ring,
            terms: values,
        },
        c,
    )
}
fn plan(
    core: &EquationPresentation,
    inputs: &CheckedInputs,
    base: usize,
    c: &mut Control,
) -> Result<(Vec<Part>, Diagram), ValidationFailure> {
    let mut parts = vec![];
    let out = object_plan(core, inputs, base, &mut parts, None, c)?;
    Ok((parts, out))
}
fn object_plan(
    core: &EquationPresentation,
    inputs: &CheckedInputs,
    base: usize,
    parts: &mut Vec<Part>,
    shared: Option<&[family::Basis]>,
    c: &mut Control,
) -> Result<Diagram, ValidationFailure> {
    tick(c)?;
    let (originals, expressions) = sources::append(core, inputs, parts, base, c)?;
    let mut out = Diagram {
        unavailable: None,
        context: None,
        presentations: vec![],
        originals,
        rings: vec![],
        domains: vec![],
        bases: vec![],
        required: vec![],
        evaluations: vec![],
        coordinates: vec![],
        readings: vec![],
        status: core.status(),
    };
    for ring in core.rings() {
        tick(c)?;
        if !matches!(ring.ty, Type::Z | Type::Q | Type::Fp(_)) {
            return Err("多項式の元係数環がscalarでない".into());
        }
        if let Some(shared) = shared {
            let basis = shared
                .iter()
                .find(|b| b.ty == ring.ty)
                .ok_or("共有係数環がない")?;
            out.bases.push(basis.scalar);
            out.rings.push(basis.ring);
            out.domains.push(basis.domain);
            out.evaluations.push(basis.evaluation);
            continue;
        }
        let scalar = push(parts, base, Part::Base(ring.ty.clone()), c)?;
        let variables = ring
            .symbols
            .iter()
            .map(|s| {
                tick(c)?;
                Ok(Variable {
                    field: Fact {
                        snapshot: s.slot.snapshot.clone(),
                        subject: s.slot.subject.clone(),
                        field: Some(s.slot.field.clone()),
                        atom: None,
                    },
                    component: s.slot.component.clone(),
                    ty: ring.ty.clone(),
                })
            })
            .collect::<Result<Vec<_>, ValidationFailure>>()?;
        let r = push(
            parts,
            base,
            Part::Ring {
                base: scalar,
                variables,
            },
            c,
        )?;
        let mut types = vec![];
        for _ in &ring.symbols {
            tick(c)?;
            types.push(ring.ty.clone());
        }
        let ty = match types.as_slice() {
            [] => Type::Unit,
            [ty] => ty.clone(),
            _ => Type::Tuple(types),
        };
        let domain = push(parts, base, Part::Domain { ring: r, ty }, c)?;
        out.bases.push(scalar);
        out.rings.push(r);
        out.domains.push(domain);
        let evaluation = if let Some(images) = &ring.evaluation_images {
            if images.len() != ring.symbols.len() {
                return Err("多項式の評価像が全記号と違う".into());
            }
            let mut values = vec![];
            for image in images {
                tick(c)?;
                values.push(polynomial(parts, base, image, scalar, &ring.ty, 0, c)?);
            }
            Some(push(
                parts,
                base,
                Part::Evaluation {
                    source: r,
                    target: scalar,
                    images: values,
                },
                c,
            )?)
        } else {
            None
        };
        out.evaluations.push(evaluation);
    }
    for (index, q) in core.occurrences().iter().enumerate() {
        tick(c)?;
        let mut coordinate = Coordinate {
            occurrence: index,
            instance: expressions[index].0,
            lhs: expressions[index].1,
            rhs: expressions[index].2,
            position: q.position,
            row: q.row,
            case: q.case,
            component: q.component.clone(),
            ty: q.ty.clone(),
            required: q.required,
            ring: None,
            left: None,
            right: None,
            nu: None,
            epsilon: None,
            residual: None,
            witness: None,
            guard: q.guard.clone(),
            status: q.status.clone(),
        };
        if let Some(index) = q.ring {
            let original = core.rings().get(index).ok_or("多項式の元環添字がない")?;
            let ring = *out.rings.get(index).ok_or("多項式の環参照がない")?;
            coordinate.ring = Some(ring);
            let mut make = |p: &Option<EquationPolynomial>| {
                p.as_ref()
                    .map(|p| {
                        family::polynomial(parts, base, p, ring, &original.ty, original, shared, c)
                    })
                    .transpose()
            };
            coordinate.left = make(&q.left)?;
            coordinate.right = make(&q.right)?;
            coordinate.nu = make(&q.nu)?;
            coordinate.epsilon = make(&q.epsilon_constant)?;
            coordinate.residual = make(&q.residual_constant)?;
            if let Some(nu) = coordinate.nu {
                coordinate.witness = Some(push(
                    parts,
                    base,
                    Part::Ideal {
                        ring,
                        generators: vec![nu],
                        required: false,
                    },
                    c,
                )?);
            }
        } else if q.left.is_some()
            || q.right.is_some()
            || q.nu.is_some()
            || q.epsilon_constant.is_some()
            || q.residual_constant.is_some()
        {
            return Err("多項式の元式に係数環がない".into());
        }
        out.coordinates.push(coordinate);
    }
    for (index, ring) in core.rings().iter().enumerate() {
        tick(c)?;
        let r = out.rings[index];
        let mut generators = vec![];
        for occurrence in &ring.required_generators {
            tick(c)?;
            let q = out
                .coordinates
                .get(*occurrence)
                .ok_or("required多項式の元出現がない")?;
            if q.ring != Some(r) {
                return Err("required多項式が別の環に属する".into());
            }
            generators.push(q.nu.ok_or("required多項式の元νがない")?);
        }
        out.required.push(push(
            parts,
            base,
            Part::Ideal {
                ring: r,
                generators,
                required: true,
            },
            c,
        )?);
    }
    tick(c)?;
    Ok(out)
}
/// 元Evaluatorの全読取りを使う。数値環に記号化できるslotだけに射影しない。
fn original_positions(
    core: &EquationPresentation,
    instance: Option<usize>,
    c: &mut Control,
) -> Result<Vec<Fact>, ValidationFailure> {
    let mut positions = std::collections::BTreeSet::new();
    for source in core.base().base().evaluations().iter().filter(|e| {
        e.position().object == core.object() && instance.is_none_or(|i| e.position().instance == i)
    }) {
        tick(c)?;
        if let super::object_evaluate::ObjectEvaluationOutcome::Evaluated(g) =
            source.evaluation().outcome()
        {
            for n in &g.nodes {
                tick(c)?;
                for f in n
                    .support
                    .iter()
                    .chain(n.reasons.iter().flat_map(|r| &r.missing))
                {
                    tick(c)?;
                    if f.field.is_some() {
                        positions.insert(Fact {
                            atom: None,
                            ..f.clone()
                        });
                    }
                }
            }
        }
    }
    Ok(positions.into_iter().collect())
}
fn append_presentations(
    inputs: &CheckedInputs,
    a: &Arc<ArchitectureWitness>,
    reference: NodeRef,
    core: &EquationPresentation,
    parts: &mut Vec<Part>,
    out: &mut Diagram,
    base: usize,
    shared: Option<&[family::Basis]>,
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    use super::equation_presentation_node::{self as common, Coordinate as C, Part as E};
    reading::append(a, core, parts, out, base, c)?;
    let mut positions = original_positions(core, None, c)?;
    if let Some(shared) = shared {
        for basis in shared {
            for v in &basis.variables {
                tick(c)?;
                positions.push(v.field.clone());
            }
        }
    }
    positions.sort();
    positions.dedup();
    // pushは同じControlを使うため、依存subjectの値だけを先に集めてから計画へ追加する。
    let dependencies = common::dependencies(inputs, &positions, c, |v| {
        let at = base
            .checked_add(parts.len())
            .ok_or("global Contextの生成番号が範囲外")?;
        parts.push(Part::Scalar(v));
        Ok(NodeRef(at))
    })?;
    let mut laws = vec![];
    for q in &out.coordinates {
        tick(c)?;
        if !laws.contains(&q.instance) {
            laws.push(q.instance);
        }
    }
    let mut quantifiers = vec![];
    for original in out.originals.iter().filter(|o| laws.contains(&o.reference)) {
        for q in &original.quantifiers {
            if !quantifiers.contains(q) {
                quantifiers.push(q.clone());
            }
        }
    }
    let context = push(
        parts,
        base,
        Part::Equation(E::Context {
            base: reference,
            carrier: common::carrier(a, c)?,
            dependencies: dependencies.slots.clone(),
            laws,
            quantifiers,
        }),
        c,
    )?;
    out.context = Some(context);
    let mut actual_values = std::collections::BTreeMap::<
        _,
        Option<super::numeric_transport::NumericTransportValue>,
    >::new();
    for (index, ring) in out.rings.iter().enumerate() {
        tick(c)?;
        let mut coordinates = Vec::<C>::new();
        let mut instances = vec![];
        let mut witnesses = vec![];
        let mut quantifiers = vec![];
        let mut omitted_positions = vec![];
        let mut seen = std::collections::BTreeMap::<_, (usize, usize)>::new();
        let mut ready = true;
        for q in out.coordinates.iter().filter(|q| q.ring == Some(*ring)) {
            tick(c)?;
            let (Some(nu), Some(witness)) = (q.nu, q.witness) else {
                ready = false;
                break;
            };
            if !instances.contains(&q.instance) {
                instances.push(q.instance);
            }
            let original = out
                .originals
                .iter()
                .find(|o| o.reference == q.instance)
                .ok_or("型別表示の元Law出現がない")?;
            let current = core
                .occurrences()
                .get(q.occurrence)
                .ok_or("表示の補完座標がない")?;
            let actual_key = (q.position.instance, q.row, q.component.clone());
            let actual = if let Some(value) = actual_values.get(&actual_key) {
                value.clone()
            } else {
                let source = core
                    .base()
                    .base()
                    .evaluations()
                    .iter()
                    .find(|e| e.position() == q.position)
                    .ok_or("表示の元Law評価がない")?;
                let residual = core
                    .base()
                    .evaluations()
                    .iter()
                    .find(|e| e.position == q.position)
                    .ok_or("表示の元Law成分がない")?;
                let value = super::object_law_residuals::observed_epsilon(
                    inputs,
                    source,
                    &residual.shape,
                    q.row,
                    &q.component,
                    c,
                )
                .map_err(|e| construction_failure(&e))?;
                actual_values.insert(actual_key, value.clone());
                value
            };
            if actual.is_some() && current.epsilon.is_some() && actual != current.epsilon {
                return Err("補完の生差が元実評価と違う".into());
            }
            if actual.is_none() {
                omitted_positions.extend(original_positions(core, Some(original.instance), c)?);
                if out.status == EquationPresentationStatus::Ready {
                    out.status = EquationPresentationStatus::Undetermined;
                }
            }
            let key = (q.instance.0, q.component.clone());
            if let Some((previous, at)) = seen.get(&key).copied() {
                let previous = core
                    .occurrences()
                    .get(previous)
                    .ok_or("表示の元補完座標がない")?;
                // 補完caseを新しいLaw出現にしない。同じ原式のνがcaseで変わるなら
                // 単一の多項式表示ではなく、既存diagramのcaseと原式を保持する。
                if previous.nu != current.nu
                    || previous.left != current.left
                    || previous.right != current.right
                {
                    ready = false;
                    if out.status == EquationPresentationStatus::Ready {
                        out.status = EquationPresentationStatus::Undetermined;
                    }
                    break;
                }
                if actual.is_none() || previous.epsilon != current.epsilon {
                    coordinates[at].epsilon = None;
                }
                continue;
            }
            seen.insert(key, (q.occurrence, coordinates.len()));
            for scope in &original.quantifiers {
                if !quantifiers.contains(scope) {
                    quantifiers.push(scope.clone());
                }
            }
            coordinates.push(C {
                instance: q.instance,
                component: q.component.clone(),
                lhs: q.lhs,
                rhs: q.rhs,
                nu,
                // 補完caseの値ではなく、補完前の同じ元rowのoperandが実εを供給する。
                epsilon: if actual.is_some() { q.epsilon } else { None },
            });
            witnesses.push(witness);
        }
        let presentation = if ready {
            if out.evaluations.get(index).is_some_and(Option::is_none) {
                for symbol in &core.rings()[index].symbols {
                    tick(c)?;
                    omitted_positions.push(Fact {
                        snapshot: symbol.slot.snapshot.clone(),
                        subject: symbol.slot.subject.clone(),
                        field: Some(symbol.slot.field.clone()),
                        atom: None,
                    });
                }
            }
            if out.evaluations.get(index).is_some_and(Option::is_none) {
                if let Some(shared) = shared {
                    let basis = shared
                        .iter()
                        .find(|b| b.ring == *ring)
                        .ok_or("表示の共有環がない")?;
                    for v in &basis.variables {
                        tick(c)?;
                        omitted_positions.push(v.field.clone());
                    }
                }
            }
            let omissions = dependencies.missing_reasons(
                inputs,
                &omitted_positions,
                &out.originals
                    .iter()
                    .filter(|o| instances.contains(&o.reference))
                    .flat_map(|o| std::iter::once(o.body).chain(o.guard))
                    .collect::<Vec<_>>(),
                Witness::Architecture(a.clone()).request(),
                c,
            )?;
            Some(push(
                parts,
                base,
                Part::Equation(E::Presentation {
                    instances,
                    domain: *out.domains.get(index).ok_or("型別表示のDomainがない")?,
                    ring: *ring,
                    coordinates,
                    witnesses,
                    required: *out
                        .required
                        .get(index)
                        .ok_or("型別表示のrequired idealがない")?,
                    evaluation: *out.evaluations.get(index).ok_or("型別表示の評価欄がない")?,
                    context,
                    quantifiers,
                    omissions,
                }),
                c,
            )?)
        } else {
            None
        };
        out.presentations.push(presentation);
    }
    tick(c)
}
fn metadata(
    inputs: &CheckedInputs,
    a: &Arc<ArchitectureWitness>,
    core: Option<&EquationPresentation>,
    c: &mut Control,
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let (mut support, mut scope) = native::metadata(&ConstructionValue {
        witness: Witness::Architecture(a.clone()),
        data: D::ConstructionLabel(Scalar::Text("polynomial_law".into())),
    })?;
    let env = Environment::new(inputs, c)?;
    for ring in core.into_iter().flat_map(|core| core.rings()) {
        for symbol in &ring.symbols {
            tick(c)?;
            let slot = env.field(
                &symbol.slot.snapshot,
                &symbol.slot.subject,
                &symbol.slot.field,
            )?;
            let fact = Fact {
                snapshot: symbol.slot.snapshot.clone(),
                subject: symbol.slot.subject.clone(),
                field: Some(symbol.slot.field.clone()),
                atom: match &slot.slot {
                    crate::archmap::Slot::Known { atom, .. } => Some(atom.clone()),
                    _ => None,
                },
            };
            let value = if fact.atom.is_some() {
                native::atom_value(Witness::Architecture(a.clone()), &fact, c)?
            } else {
                native::subject_value(
                    Witness::Architecture(a.clone()),
                    &Fact {
                        field: None,
                        atom: None,
                        ..fact
                    },
                )?
            };
            let (facts, s) = native::metadata(&value)?;
            support.extend(facts);
            scope.merge(&s);
        }
    }
    for instance in a
        .readings()
        .instances()
        .iter()
        .filter(|i| i.declaration().kind == "law")
    {
        for parameter in instance.parameters() {
            tick(c)?;
            let domain = env.object_parameter_domain(parameter, instance)?;
            support.extend(domain.support);
            scope.merge(&domain.scope);
        }
    }
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    scope.assignments = true;
    if core.is_some() {
        super::equation_presentation_node::global_metadata(a, &mut support, &mut scope)?;
    }
    tick(c)?;
    Ok((support, scope))
}
fn construction_failure(e: &crate::construction::ConstructionFailure) -> ValidationFailure {
    match e {
        crate::construction::ConstructionFailure::Stopped(stop) => {
            ValidationFailure::Stop(stop.clone())
        }
        crate::construction::ConstructionFailure::InvalidSelection(message)
        | crate::construction::ConstructionFailure::Inconsistent(message) => {
            format!("元多項式: {message}").into()
        }
    }
}
fn evaluation_failure(e: &super::object_evaluate::ObjectEvaluationFailure) -> ValidationFailure {
    use super::object_evaluate::ObjectEvaluationFailure as E;
    match e {
        E::Construction(e) => construction_failure(e),
        E::FiniteView { cause, .. } => evaluation_failure(cause),
        E::Evaluation(e) => match e.as_ref() {
            EvaluationFailure::NotImplemented {
                declaration,
                feature,
                ..
            } => format!("元Law `{declaration}` の評価: {feature}").into(),
            EvaluationFailure::Prepare(_) => "元Lawの評価要求の検査に失敗した".into(),
        },
        E::NotImplemented { instance, .. } => format!(
            "元Law `{}` の値parameterを評価できない",
            instance.declaration().name
        )
        .into(),
    }
}
fn failed(e: EquationPresentationFailure, c: &Control) -> ValidationFailure {
    if let Some(stop) = c.stop_reason() {
        return ValidationFailure::Stop(stop);
    }
    match e {
        EquationPresentationFailure::Selection(cause)
        | EquationPresentationFailure::Reading { cause, .. } => construction_failure(&cause),
        EquationPresentationFailure::Original(e) => match e {
            super::object_law_residuals::ObjectLawResidualsFailure::Reading { cause, .. } => {
                construction_failure(&cause)
            }
            super::object_law_residuals::ObjectLawResidualsFailure::Original(e) => {
                evaluation_failure(e.cause())
            }
        },
    }
}
fn unavailable(e: &super::object_evaluate::ObjectEvaluationFailure) -> Option<Unavailable> {
    use super::object_evaluate::ObjectEvaluationFailure as E;
    match e {
        E::NotImplemented { instance, .. } => Some(Unavailable {
            declaration: instance.declaration().name.clone(),
            feature: "値parameterの全域計算が未実装".into(),
        }),
        E::FiniteView { cause, .. } => unavailable(cause),
        E::Evaluation(e) => match e.as_ref() {
            EvaluationFailure::NotImplemented {
                declaration,
                feature,
                ..
            } => Some(Unavailable {
                declaration: declaration.clone(),
                feature: format!("未実装: {feature}"),
            }),
            _ => None,
        },
        _ => None,
    }
}
fn calculate(
    inputs: Arc<CheckedInputs>,
    a: &Arc<ArchitectureWitness>,
    object: usize,
    c: &mut Control,
) -> Result<(Option<Arc<EquationPresentation>>, Option<Unavailable>), ValidationFailure> {
    tick(c)?;
    if object >= a.readings().objects().len() {
        return Err("多項式の対象添字が域外".into());
    }
    let root = a.construction().root();
    match object_equation_presentation(
        inputs,
        a.construction().reading(),
        &root.snapshot,
        &root.subject,
        object,
        c,
    ) {
        Ok(core) => {
            if core.base().base().readings() != a.readings() {
                return Err("多項式が元対象族・readingと違う".into());
            }
            Ok((Some(Arc::new(core)), None))
        }
        Err(e) => {
            if let Some(stop) = c.stop_reason() {
                return Err(ValidationFailure::Stop(stop));
            }
            let reason = match &e {
                EquationPresentationFailure::Original(
                    super::object_law_residuals::ObjectLawResidualsFailure::Original(e),
                ) => unavailable(e.cause()),
                _ => None,
            };
            if let Some(reason) = reason {
                Ok((None, Some(reason)))
            } else {
                Err(failed(e, c))
            }
        }
    }
}
fn symbolic_plan(
    inputs: &CheckedInputs,
    a: &Arc<ArchitectureWitness>,
    reason: Unavailable,
    base: usize,
    c: &mut Control,
) -> Result<(Vec<Part>, Diagram), ValidationFailure> {
    tick(c)?;
    let mut parts = vec![];
    let originals = sources::symbolic(inputs, a.readings(), &mut parts, base, c)?;
    tick(c)?;
    Ok((
        parts,
        Diagram {
            unavailable: Some(reason),
            context: None,
            presentations: vec![],
            originals,
            rings: vec![],
            domains: vec![],
            bases: vec![],
            required: vec![],
            evaluations: vec![],
            coordinates: vec![],
            readings: vec![],
            status: EquationPresentationStatus::Undetermined,
        },
    ))
}
impl Source {
    fn compute(
        inputs: Arc<CheckedInputs>,
        a: Arc<ArchitectureWitness>,
        reference: NodeRef,
        object: usize,
        base: usize,
        c: &mut Control,
    ) -> Result<Self, ValidationFailure> {
        tick(c)?;
        if inputs.sources() != Witness::Architecture(a.clone()).inputs().sources() {
            return Err("多項式の元三入力とArchitectureが違う".into());
        }
        let (core, reason) = calculate(inputs.clone(), &a, object, c)?;
        let (mut parts, mut outputs) = match (&core, reason) {
            (Some(core), None) => plan(core, &inputs, base, c)?,
            (None, Some(reason)) => symbolic_plan(&inputs, &a, reason, base, c)?,
            _ => return Err("多項式の計算状態が不正".into()),
        };
        if let Some(core) = &core {
            append_presentations(
                &inputs,
                &a,
                reference,
                core,
                &mut parts,
                &mut outputs,
                base,
                None,
                c,
            )?;
        }
        let (support, scope) = metadata(&inputs, &a, core.as_deref(), c)?;
        tick(c)?;
        Ok(Self {
            inputs,
            architecture: a,
            reference,
            object,
            core,
            base,
            parts,
            outputs,
            owned_outputs: None,
            support,
            scope,
        })
    }
    fn recheck(
        &self,
        inputs: &CheckedInputs,
        a: &Arc<ArchitectureWitness>,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        if !Arc::ptr_eq(a, &self.architecture) || inputs.sources() != self.inputs.sources() {
            return Err("多項式の消費先・元三入力・対象・readingが違う".into());
        }
        if self.owned_outputs.is_some() {
            if self.object != 0 {
                return Err("共有多項式族のbase対象が違う".into());
            }
            let expected =
                Self::compute_family(self.inputs.clone(), a.clone(), self.reference, self.base, c)?;
            if self.parts != expected.parts
                || self.outputs != expected.outputs
                || self.owned_outputs != expected.owned_outputs
                || self.support != expected.support
                || self.scope != expected.scope
            {
                return Err("共有多項式族が元全対象・環・記号・計画と違う".into());
            }
            return tick(c);
        }
        let (mut parts, mut outputs) = if let Some(core) = &self.core {
            if core.object() != self.object || core.base().base().readings() != a.readings() {
                return Err("多項式の元計算が対象・readingと違う".into());
            }
            core.recheck(self.inputs.clone(), c)
                .map_err(|e| failed(e, c))?;
            plan(core, inputs, self.base, c)?
        } else {
            let (core, reason) = calculate(self.inputs.clone(), a, self.object, c)?;
            if core.is_some() {
                return Err("計算可能な多項式を未対応扱いした".into());
            }
            symbolic_plan(
                inputs,
                a,
                reason.ok_or("多項式の未対応理由がない")?,
                self.base,
                c,
            )?
        };
        if let Some(core) = &self.core {
            append_presentations(
                inputs,
                a,
                self.reference,
                core,
                &mut parts,
                &mut outputs,
                self.base,
                None,
                c,
            )?;
        }
        let (support, scope) = metadata(inputs, a, self.core.as_deref(), c)?;
        if parts != self.parts
            || outputs != self.outputs
            || support != self.support
            || scope != self.scope
        {
            return Err("多項式が元共有環・全計画・支持・Scopeと違う".into());
        }
        tick(c)
    }
}
pub(super) fn retain(
    graph: &mut Graph,
    inputs: Arc<CheckedInputs>,
    reference: NodeRef,
    object: usize,
    c: &mut Control,
) -> Result<Diagram, ValidationFailure> {
    Ok(retain_source(graph, inputs, reference, object, false, c)?
        .outputs
        .clone())
}
pub(super) fn retain_family(
    graph: &mut Graph,
    inputs: Arc<CheckedInputs>,
    reference: NodeRef,
    c: &mut Control,
) -> Result<Vec<Diagram>, ValidationFailure> {
    let source = retain_source(graph, inputs, reference, 0, true, c)?;
    let mut outputs = vec![source.outputs.clone()];
    outputs.extend(
        source
            .owned_outputs
            .as_ref()
            .ok_or("共有多項式族の全対象がない")?
            .iter()
            .cloned(),
    );
    tick(c)?;
    Ok(outputs)
}
fn retain_source(
    graph: &mut Graph,
    inputs: Arc<CheckedInputs>,
    reference: NodeRef,
    object: usize,
    all_objects: bool,
    c: &mut Control,
) -> Result<Arc<Source>, ValidationFailure> {
    tick(c)?;
    if graph.active != graph.context_at(reference.0) {
        return Err("多項式の生成が元ArchitectureのRequestでない".into());
    }
    let a = native::architecture_origin(graph, reference, object)?.clone();
    let Some(Payload::Construction(consumer)) = &graph.get(reference)?.payload else {
        return Err("多項式の元Architectureがない".into());
    };
    Environment::new(&inputs, c)?.recheck_object_components(graph, consumer)?;
    let source = Arc::new(if all_objects {
        Source::compute_family(inputs, a, reference, graph.nodes.len(), c)?
    } else {
        Source::compute(inputs, a, reference, object, graph.nodes.len(), c)?
    });
    for index in 0..source.parts.len() {
        tick(c)?;
        let data = Data {
            source: source.clone(),
            index,
        };
        data.position(graph.nodes.len())?;
        let reasons = match data.part() {
            Part::Equation(v) => v.reasons(),
            _ => vec![],
        };
        native::retain(
            graph,
            ConstructionValue {
                witness: Witness::Architecture(source.architecture.clone()),
                data: D::PolynomialLaw(data),
            },
            reasons,
            vec![],
            None,
        )?;
    }
    tick(c)?;
    Ok(source)
}
pub(super) fn validate_node(graph: &Graph, n: &Node, data: &Data) -> Result<(), ValidationFailure> {
    let part = data
        .source
        .parts
        .get(data.index)
        .ok_or("多項式の元計画添字がない")?;
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("多項式のpayloadがない".into());
    };
    let Witness::Architecture(a) = &v.witness else {
        return Err("多項式の元Architectureがない".into());
    };
    let current = native::architecture_origin(graph, data.source.reference, data.source.object)?;
    if !Arc::ptr_eq(a, current) || !Arc::ptr_eq(a, &data.source.architecture) {
        return Err("多項式の元Architecture参照が違う".into());
    }
    let (support, scope) = data.metadata();
    if n.ty != part.ty()
        || n.rule != Rule::Construction(part.construction())
        || n.arguments != data.arguments()
        || n.support != support
        || n.scope != scope
        || n.reasons
            != match part {
                Part::Equation(v) => v.reasons(),
                _ => vec![],
            }
        || !n.evidence.is_empty()
        || n.judgment.is_some()
    {
        return Err("多項式の型・導出・支持・Scopeが違う".into());
    }
    for reference in part.arguments() {
        let Some(Payload::Construction(v)) = &graph.get(reference)?.payload else {
            return Err("多項式の引数がnativeでない".into());
        };
        let D::PolynomialLaw(other) = &v.data else {
            return Err("多項式の引数が別由来".into());
        };
        if !Arc::ptr_eq(&data.source, &other.source)
            || other.index >= data.index
            || data.source.base.checked_add(other.index) != Some(reference.0)
        {
            return Err("多項式の引数が元計画の既出値でない".into());
        }
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_polynomial_law_diagram(
        &self,
        graph: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::PolynomialLaw(data) = &value.data else {
            return Ok(());
        };
        tick(&mut self.control.clone())?;
        let Witness::Architecture(a) = &value.witness else {
            return Err("多項式導出の元Architectureがない".into());
        };
        let current =
            native::architecture_origin(graph, data.source.reference, data.source.object)?;
        if !Arc::ptr_eq(a, current) || !Arc::ptr_eq(a, &data.source.architecture) {
            return Err("多項式の消費先Architectureが違う".into());
        }
        let Some(Payload::Construction(consumer)) = &graph.get(data.source.reference)?.payload
        else {
            return Err("多項式の元参照がない".into());
        };
        self.recheck_object_components(graph, consumer)?;
        if self
            .verified_polynomial_law_diagrams
            .borrow()
            .iter()
            .any(|s| Arc::ptr_eq(s, &data.source))
        {
            return Ok(());
        }
        data.source
            .recheck(self.inputs, a, &mut self.control.clone())?;
        self.verified_polynomial_law_diagrams
            .borrow_mut()
            .push(data.source.clone());
        Ok(())
    }
}

#[cfg(test)]
#[path = "polynomial_law_diagram_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "polynomial_law_family_tests.rs"]
mod family_tests;

#[cfg(test)]
#[path = "polynomial_law_reading_tests.rs"]
mod reading_tests;
