//! 元Architectureの有限Law表示を既存のnative導出DAGへ保持する。
use super::{
    construction_result::{
        self as native, ArchitectureWitness, ConstructionData as D, ConstructionType as T,
        ConstructionValue, Witness,
    },
    control::{Checkpoint, Control},
    environment::{
        Environment,
        finite_law_valuations::object::instances::realizations::automatic::{
            AutomaticLawValuations, finite_automatic_law_family,
        },
    },
    input::CheckedInputs,
    result::*,
};
use crate::{
    archmap::Slot,
    canonical::Json,
    issue::Location,
    law::{ast::Role, model::Signature},
    result::location_wire,
    types::Type,
};
use std::sync::Arc;

#[path = "finite_law_operands.rs"]
mod operands;

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::FiniteLawFunction)?;
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Original {
    pub column: usize,
    pub instance: usize,
    pub bindings: Vec<Binding>,
    pub body: NodeRef,
    pub guard: Option<NodeRef>,
    pub row: NodeRef,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Transform {
    Substitute,
    Project,
    Equal,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Part {
    Scalar(Scalar),
    Source {
        column: usize,
        expression: usize,
        location: Location,
        ty: Type,
        parameters: Vec<(String, Type)>,
        bindings: Vec<Binding>,
    },
    Transform {
        operation: Transform,
        ty: Type,
        operands: Vec<NodeRef>,
        bindings: Vec<Binding>,
        position: Option<usize>,
    },
    LawInstance {
        column: usize,
        original: usize,
        name: String,
        role: Role,
        occurrence: Location,
        bindings: Vec<Binding>,
        guard: Option<NodeRef>,
        body: NodeRef,
    },
    Domain {
        ty: Type,
        elements: Vec<NodeRef>,
    },
    IntegerRing,
    FunctionRing {
        domain: NodeRef,
    },
    Function {
        ring: NodeRef,
        values: Vec<NodeRef>,
    },
    Evaluation {
        source: NodeRef,
        target: NodeRef,
        basis_images: Vec<NodeRef>,
    },
    Ideal {
        ring: NodeRef,
        generators: Vec<NodeRef>,
        required: bool,
    },
}
impl Part {
    fn ty(&self) -> NodeType {
        match self {
            Self::Scalar(v) => NodeType::Value(v.ty()),
            Self::Source { ty, .. } | Self::Transform { ty, .. } => {
                NodeType::Expression(ty.clone())
            }
            Self::LawInstance { .. } => NodeType::LawInstance,
            Self::Domain { .. } => NodeType::Domain,
            Self::IntegerRing | Self::FunctionRing { .. } => NodeType::Construction(T::Ring),
            Self::Function { .. } => NodeType::Construction(T::FiniteFunction),
            Self::Evaluation { .. } => NodeType::Construction(T::RingMap),
            Self::Ideal { .. } => NodeType::Construction(T::Ideal),
        }
    }
    fn arguments(&self) -> Vec<NodeRef> {
        match self {
            Self::Scalar(_) | Self::IntegerRing => vec![],
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
            Self::Domain { elements, .. } => elements.clone(),
            Self::FunctionRing { domain } => vec![*domain],
            Self::Function { ring, values }
            | Self::Ideal {
                ring,
                generators: values,
                ..
            } => std::iter::once(*ring)
                .chain(values.iter().copied())
                .collect(),
            Self::Evaluation {
                source,
                target,
                basis_images,
            } => [*source, *target]
                .into_iter()
                .chain(basis_images.iter().copied())
                .collect(),
        }
    }
    fn construction(&self) -> &'static str {
        match self {
            Self::Scalar(_) => "binding",
            Self::Source { .. } | Self::Transform { .. } => "expression",
            Self::LawInstance { .. } => "law_instance",
            Self::Domain { .. } => "domain",
            Self::IntegerRing | Self::FunctionRing { .. } => "ring",
            Self::Function { .. } => "finite_function",
            Self::Evaluation { .. } => "ring_map",
            Self::Ideal { .. } => "ideal",
        }
    }
    fn wire(&self) -> Json {
        match self {
            Self::Scalar(v) => v.wire(),
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
                    ("parameters", Json::Arr(vec![])),
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
            Self::Domain { ty, elements } => Json::obj([
                ("kind", Json::str("finite")),
                ("type", ty.wire()),
                ("elements", refs(elements)),
            ]),
            Self::IntegerRing => {
                Json::obj([("kind", Json::str("scalar")), ("scalar", Json::str("Z"))])
            }
            Self::FunctionRing { domain } => Json::obj([
                ("kind", Json::str("finite_functions")),
                ("domain", domain.wire()),
            ]),
            Self::Function { ring, values } => {
                Json::obj([("ring", ring.wire()), ("values", refs(values))])
            }
            Self::Evaluation {
                source,
                target,
                basis_images,
            } => Json::obj([
                ("kind", Json::str("finite_functions")),
                ("source", source.wire()),
                ("target", target.wire()),
                ("basis_images", refs(basis_images)),
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
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Diagram {
    pub originals: Vec<Original>,
    pub operands: Vec<(NodeRef, NodeRef)>,
    pub points: Vec<usize>,
    pub domain: NodeRef,
    pub ring: NodeRef,
    pub target: NodeRef,
    pub evaluation: Option<NodeRef>,
    pub columns: Vec<usize>,
    pub components: Vec<(usize, Option<Vec<usize>>)>,
    pub nu: Vec<NodeRef>,
    pub epsilon: Vec<Option<NodeRef>>,
    pub witnesses: Vec<NodeRef>,
    pub required: NodeRef,
}
#[derive(Clone)]
pub(super) struct Source {
    inputs: Arc<CheckedInputs>,
    architecture: Arc<ArchitectureWitness>,
    reference: NodeRef,
    object: usize,
    base: usize,
    parts: Vec<Part>,
    outputs: Diagram,
    support: Vec<Fact>,
    scope: Scope,
}
impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FiniteLawDiagramSource")
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
    fn part(&self) -> &Part {
        &self.source.parts[self.index]
    }
    pub(super) fn scalar(&self) -> Option<&Scalar> {
        match self.source.parts.get(self.index) {
            Some(Part::Scalar(v)) => Some(v),
            _ => None,
        }
    }
    pub(super) fn ty(&self) -> NodeType {
        self.part().ty()
    }
    pub(super) fn construction(&self) -> &'static str {
        self.part().construction()
    }
    pub(super) fn arguments(&self) -> Vec<NodeRef> {
        std::iter::once(self.source.reference)
            .chain(self.part().arguments())
            .collect()
    }
    pub(super) fn wire(&self) -> Json {
        self.part().wire()
    }
    pub(super) fn metadata(&self) -> (Vec<Fact>, Scope) {
        (self.source.support.clone(), self.source.scope.clone())
    }
    pub(super) fn position(&self, position: usize) -> Result<(), ValidationFailure> {
        if self.index >= self.source.parts.len()
            || self.source.base.checked_add(self.index) != Some(position)
        {
            return Err("有限Law導出の元計画・生成位置が違う".into());
        }
        Ok(())
    }
}
fn push(parts: &mut Vec<Part>, base: usize, part: Part) -> Result<NodeRef, ValidationFailure> {
    let index = base
        .checked_add(parts.len())
        .ok_or("有限Law導出の番号が範囲外")?;
    parts.push(part);
    Ok(NodeRef(index))
}
fn function(
    parts: &mut Vec<Part>,
    base: usize,
    ring: NodeRef,
    values: &[num_bigint::BigInt],
    points: &[usize],
    c: &mut Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut elements = vec![];
    if points.len() != values.len() {
        return Err("有限Lawの公開順と関数の次元が違う".into());
    }
    for point in points {
        tick(c)?;
        let v = values.get(*point).ok_or("有限Lawの元関数座標が範囲外")?;
        elements.push(push(parts, base, Part::Scalar(Scalar::Z(v.clone())))?);
    }
    push(
        parts,
        base,
        Part::Function {
            ring,
            values: elements,
        },
    )
}
fn value_key(value: &Scalar, c: &mut Control) -> Result<String, ValidationFailure> {
    super::data::input_json(value, c)?
        .canonical_controlled::<super::control::CheckFailure<Box<crate::issue::Issue>>>(
            c,
            Checkpoint::FiniteLawFunction,
        )
        .map_err(|e| match e {
            super::control::CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
            super::control::CheckFailure::Input(_) => {
                ValidationFailure::Internal("有限Lawのcanonical値が構成できない".into())
            }
        })
}
// JSONのarray順ではなく、元型のSet/Mapの意味に沿って再帰的に並べる。
// 元のDの値・所属条件は保ち、公開する値の表示順だけを変える。
fn canonical_value(value: &Scalar, c: &mut Control) -> Result<Scalar, ValidationFailure> {
    fn visit(value: &mut Scalar, c: &mut Control) -> Result<(), ValidationFailure> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            tick(c)?;
            match value {
                Scalar::Set { items, .. } => {
                    let mut ordered = Vec::new();
                    for mut item in std::mem::take(items) {
                        visit(&mut item, c)?;
                        ordered.push((value_key(&item, c)?, item));
                    }
                    ordered.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                    tick(c)?;
                    for (_, item) in ordered {
                        tick(c)?;
                        items.push(item);
                    }
                }
                Scalar::Map { pairs, .. } => {
                    let mut ordered = Vec::new();
                    for (mut key, mut image) in std::mem::take(pairs) {
                        visit(&mut key, c)?;
                        visit(&mut image, c)?;
                        ordered.push((value_key(&key, c)?, (key, image)));
                    }
                    ordered.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                    tick(c)?;
                    for (_, pair) in ordered {
                        tick(c)?;
                        pairs.push(pair);
                    }
                }
                Scalar::Tuple(items)
                | Scalar::List { items, .. }
                | Scalar::Data { args: items, .. } => {
                    for item in items {
                        visit(item, c)?;
                    }
                }
                Scalar::Option {
                    value: Some(item), ..
                } => visit(item, c)?,
                Scalar::Path(_) | Scalar::Term(_) => {
                    return Err("有限LawのDに原始値でない値がある".into());
                }
                _ => {}
            }
            tick(c)
        })
    }
    tick(c)?;
    let mut result = value.clone();
    visit(&mut result, c)?;
    Ok(result)
}
fn original_rows(
    f: &AutomaticLawValuations,
    inputs: &CheckedInputs,
    columns: &[usize],
    parts: &mut Vec<Part>,
    base: usize,
    c: &mut Control,
) -> Result<Vec<Original>, ValidationFailure> {
    let mut originals = Vec::new();
    for &column in columns {
        tick(c)?;
        let source = f.columns().get(column).ok_or("有限Lawの元columnがない")?;
        let instance = source
            .source_instance()
            .ok_or("有限Lawの元instanceがない")?;
        let declaration = source.declaration();
        let Signature::Law {
            role,
            params,
            guard,
            body,
        } = &declaration.signature
        else {
            return Err("有限Lawの元宣言がLawでない".into());
        };
        if source.bindings().len() != params.len() {
            return Err("有限Lawの全parameter束縛が揃わない".into());
        }
        let mut bindings = Vec::new();
        for parameter in params {
            tick(c)?;
            let mut found = source
                .bindings()
                .iter()
                .filter(|(name, _)| name == &parameter.name);
            let (_, value) = found.next().ok_or("有限Lawの元parameter束縛がない")?;
            let ty = parameter
                .ty
                .erase_controlled::<super::control::CheckFailure<Box<crate::issue::Issue>>>(
                    c,
                    Checkpoint::FiniteLawFunction,
                )
                .map_err(|e| match e {
                    super::control::CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
                    super::control::CheckFailure::Input(_) => {
                        ValidationFailure::Internal("有限Lawのparameterの原始型がない".into())
                    }
                })?;
            if found.next().is_some() || value.ty() != ty {
                return Err("有限Lawの元parameterが重複または型違い".into());
            }
            let value = canonical_value(value, c)?;
            let reference = push(parts, base, Part::Scalar(value))?;
            bindings.push(Binding {
                name: parameter.name.clone(),
                ty,
                value: reference,
            });
        }
        let mut expression = |id: usize| -> Result<NodeRef, ValidationFailure> {
            tick(c)?;
            if inputs.law().expr_type(id) != Some(&Type::Bool) {
                return Err("有限Lawの元body/guardがBoolでない".into());
            }
            let ast = inputs.law().exprs.get(id).ok_or("有限Lawの元式がない")?;
            push(
                parts,
                base,
                Part::Source {
                    column,
                    expression: id,
                    location: Location::Law { span: ast.span },
                    ty: Type::Bool,
                    parameters: vec![],
                    bindings: bindings.clone(),
                },
            )
        };
        // 全bodyを指し、let/match内の自由変数を持つ部分式へ置き換えない。
        let body = expression(*body)?;
        let guard = guard.map(&mut expression).transpose()?;
        let row = push(
            parts,
            base,
            Part::LawInstance {
                column,
                original: instance,
                name: declaration.name.clone(),
                role: *role,
                occurrence: Location::Law {
                    span: declaration.span,
                },
                bindings: bindings.clone(),
                guard,
                body,
            },
        )?;
        originals.push(Original {
            column,
            instance,
            bindings,
            body,
            guard,
            row,
        });
    }
    tick(c)?;
    Ok(originals)
}
fn plan(
    f: &AutomaticLawValuations,
    inputs: &CheckedInputs,
    object: usize,
    base: usize,
    c: &mut Control,
) -> Result<(Vec<Part>, Diagram), ValidationFailure> {
    tick(c)?;
    let p = f
        .object_presentation(inputs, object, c)?
        .ok_or("有限Lawの元表示が未完成")?;
    // 元の所属条件を満たすDは変えず、原始値のencodingだけをRefへ表す。
    let mut value_types = vec![];
    for ty in f.types() {
        tick(c)?;
        value_types.push(
            ty.erase_controlled::<super::control::CheckFailure<Box<crate::issue::Issue>>>(
                c,
                Checkpoint::FiniteLawFunction,
            )
            .map_err(|e| match e {
                super::control::CheckFailure::Stopped(stop) => ValidationFailure::Stop(stop),
                super::control::CheckFailure::Input(_) => {
                    ValidationFailure::Internal("有限Lawの原始表示型が解決できない".into())
                }
            })?,
        );
    }
    let ty = match value_types.as_slice() {
        [] => Type::Unit,
        [ty] => ty.clone(),
        items => Type::Tuple(items.to_vec()),
    };
    let mut ordered = vec![];
    for (point, values) in f.domain().iter().enumerate() {
        tick(c)?;
        let value = match values.as_slice() {
            [] => Scalar::Unit,
            [v] => v.clone(),
            items => Scalar::Tuple(items.to_vec()),
        };
        if value.ty() != ty {
            return Err("有限Lawの全Dの型が違う".into());
        }
        let value = canonical_value(&value, c)?;
        let key = value_key(&value, c)?;
        ordered.push((key, point, value));
    }
    // 内部の数値/直積順を変えず、公開集合表のUTF-8 byte辞書順と対応させる。
    ordered.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    tick(c)?;
    for pair in ordered.windows(2) {
        tick(c)?;
        if pair[0].0 == pair[1].0 {
            return Err("有限Lawの公開Dに重複した値がある".into());
        }
    }
    let mut points = vec![];
    let mut parts = vec![];
    let mut elements = vec![];
    for (_, point, value) in ordered {
        tick(c)?;
        points.push(point);
        elements.push(push(&mut parts, base, Part::Scalar(value))?);
    }
    let domain = push(&mut parts, base, Part::Domain { ty, elements })?;
    let ring = push(&mut parts, base, Part::FunctionRing { domain })?;
    let target = push(&mut parts, base, Part::IntegerRing)?;
    let evaluation = if let Some(ev) = f.object_evaluation(c)? {
        let mut images = vec![];
        for point in &points {
            tick(c)?;
            let v = ev
                .basis_images()
                .get(*point)
                .ok_or("有限Lawの元評価座標が範囲外")?;
            images.push(push(&mut parts, base, Part::Scalar(Scalar::Z(v.clone())))?);
        }
        Some(push(
            &mut parts,
            base,
            Part::Evaluation {
                source: ring,
                target,
                basis_images: images,
            },
        )?)
    } else {
        None
    };
    let mut columns = vec![];
    let mut components = vec![];
    let mut nu = vec![];
    let mut epsilon = vec![];
    let mut witnesses = vec![];
    for (index, eq) in p.equations().iter().enumerate() {
        tick(c)?;
        columns.push(eq.column());
        components.push((eq.instance(), eq.component().map(<[usize]>::to_vec)));
        let symbol = function(&mut parts, base, ring, eq.nu().values(), &points, c)?;
        nu.push(symbol);
        epsilon.push(
            eq.constant()
                .map(|value| function(&mut parts, base, ring, value.values(), &points, c))
                .transpose()?,
        );
        let ideal = p.witness_ideal(index, c)?;
        if ideal.equations() != [index] {
            return Err("有限witnessの元成分が違う".into());
        }
        witnesses.push(push(
            &mut parts,
            base,
            Part::Ideal {
                ring,
                generators: vec![symbol],
                required: false,
            },
        )?);
    }
    let required = p.required_ideal(c)?;
    let mut generators = vec![];
    for index in required.equations() {
        tick(c)?;
        generators.push(*nu.get(*index).ok_or("requiredの元νがない")?);
    }
    let required = push(
        &mut parts,
        base,
        Part::Ideal {
            ring,
            generators,
            required: true,
        },
    )?;
    let originals = original_rows(f, inputs, p.columns(), &mut parts, base, c)?;
    let operands = operands::append(
        f,
        inputs,
        &originals,
        &columns,
        &components,
        &mut parts,
        base,
        c,
    )?;
    tick(c)?;
    Ok((
        parts,
        Diagram {
            originals,
            operands,
            points,
            domain,
            ring,
            target,
            evaluation,
            columns,
            components,
            nu,
            epsilon,
            witnesses,
            required,
        },
    ))
}
fn metadata(
    inputs: &CheckedInputs,
    a: &Arc<ArchitectureWitness>,
    f: &AutomaticLawValuations,
    c: &mut Control,
) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    let value = ConstructionValue {
        witness: Witness::Architecture(a.clone()),
        data: D::ConstructionLabel(Scalar::Text("finite_law".into())),
    };
    let (mut support, mut scope) = native::metadata(&value)?;
    let env = Environment::new(inputs, c)?;
    for position in f.positions() {
        tick(c)?;
        let field = env.field(
            &position.snapshot,
            &position.subject,
            position.field.as_deref().ok_or("有限Lawの元fieldがない")?,
        )?;
        let mut fact = position.clone();
        if let Slot::Known { atom, .. } = &field.slot {
            fact.atom = Some(atom.clone());
            let value = native::atom_value(Witness::Architecture(a.clone()), &fact, c)?;
            let (facts, s) = native::metadata(&value)?;
            support.extend(facts);
            scope.merge(&s);
        } else {
            fact.field = None;
            fact.atom = None;
            let value = native::subject_value(Witness::Architecture(a.clone()), &fact)?;
            let (facts, s) = native::metadata(&value)?;
            support.extend(facts);
            scope.merge(&s);
        }
    }
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    scope.assignments = true;
    tick(c)?;
    Ok((support, scope))
}
impl Source {
    fn compute(
        inputs: Arc<CheckedInputs>,
        architecture: Arc<ArchitectureWitness>,
        reference: NodeRef,
        object: usize,
        base: usize,
        c: &mut Control,
    ) -> Result<Option<Self>, ValidationFailure> {
        tick(c)?;
        if Witness::Architecture(architecture.clone())
            .inputs()
            .sources()
            != inputs.sources()
        {
            return Err("有限Lawの三入力とArchitectureが違う".into());
        }
        architecture
            .readings()
            .objects()
            .get(object)
            .ok_or("有限Lawの対象が範囲外")?;
        let full = finite_automatic_law_family(&inputs, architecture.readings(), c)
            .map_err(|e| e.cause)?;
        let Some(f) = full.family() else {
            return Ok(None);
        };
        if !f.is_complete() || !f.domain_complete() {
            return Ok(None);
        }
        let (parts, outputs) = plan(f, &inputs, object, base, c)?;
        let (support, scope) = metadata(&inputs, &architecture, f, c)?;
        tick(c)?;
        Ok(Some(Self {
            inputs,
            architecture,
            reference,
            object,
            base,
            parts,
            outputs,
            support,
            scope,
        }))
    }
    fn recheck(
        &self,
        inputs: &CheckedInputs,
        architecture: &Arc<ArchitectureWitness>,
        object: usize,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        if !Arc::ptr_eq(architecture, &self.architecture)
            || object != self.object
            || inputs.sources() != self.inputs.sources()
        {
            return Err("有限Law導出の消費先Architecture・対象・三入力が違う".into());
        }
        architecture
            .readings()
            .recheck(inputs, c)
            .map_err(|e| match e {
                crate::construction::ConstructionFailure::Stopped(s) => ValidationFailure::Stop(s),
                other => format!("有限Lawの元reading: {other:?}").into(),
            })?;
        let other = Self::compute(
            self.inputs.clone(),
            architecture.clone(),
            self.reference,
            object,
            self.base,
            c,
        )?
        .ok_or("有限Law導出の元族が未完成")?;
        if self.parts != other.parts
            || self.outputs != other.outputs
            || self.support != other.support
            || self.scope != other.scope
        {
            return Err("有限Law導出が元全D・成分・生成元・支持と違う".into());
        }
        tick(c)
    }
}
pub(super) fn retain(
    graph: &mut Graph,
    inputs: Arc<CheckedInputs>,
    architecture: NodeRef,
    object: usize,
    c: &mut Control,
) -> Result<Option<Diagram>, ValidationFailure> {
    tick(c)?;
    if graph.active != graph.context_at(architecture.0) {
        return Err("有限Law導出が消費先ArchitectureのRequestでない".into());
    }
    let a = native::architecture_origin(graph, architecture, object)?.clone();
    let Some(Payload::Construction(consumer)) = &graph.get(architecture)?.payload else {
        return Err("有限Lawの消費先Architectureがない".into());
    };
    Environment::new(&inputs, c)?.recheck_object_components(graph, consumer)?;
    let Some(source) = Source::compute(
        inputs,
        a.clone(),
        architecture,
        object,
        graph.nodes.len(),
        c,
    )?
    else {
        return Ok(None);
    };
    let source = Arc::new(source);
    for index in 0..source.parts.len() {
        tick(c)?;
        let data = Data {
            source: source.clone(),
            index,
        };
        data.position(graph.nodes.len())?;
        native::retain(
            graph,
            ConstructionValue {
                witness: Witness::Architecture(source.architecture.clone()),
                data: D::FiniteLaw(data),
            },
            vec![],
            vec![],
            None,
        )?;
    }
    tick(c)?;
    Ok(Some(source.outputs.clone()))
}
pub(super) fn validate_node(graph: &Graph, n: &Node, data: &Data) -> Result<(), ValidationFailure> {
    let Some(part) = data.source.parts.get(data.index) else {
        return Err("有限Lawの元計画添字がない".into());
    };
    let Some(Payload::Construction(v)) = &n.payload else {
        return Err("有限Law導出payloadがない".into());
    };
    let Witness::Architecture(a) = &v.witness else {
        return Err("有限Lawの元Architectureがない".into());
    };
    let current = native::architecture_origin(graph, data.source.reference, data.source.object)?;
    if !Arc::ptr_eq(a, current) || !Arc::ptr_eq(a, &data.source.architecture) {
        return Err("有限Lawの元Architecture参照が違う".into());
    }
    if n.ty != part.ty()
        || n.rule != Rule::Construction(part.construction())
        || n.arguments != data.arguments()
        || n.support != data.source.support
        || n.scope != data.source.scope
        || !n.reasons.is_empty()
        || !n.evidence.is_empty()
        || n.judgment.is_some()
    {
        return Err("有限Lawの型・導出・原始支持・scopeが違う".into());
    }
    for reference in part.arguments() {
        let child = graph.get(reference)?;
        let Some(Payload::Construction(v)) = &child.payload else {
            return Err("有限Lawの構成引数がnativeでない".into());
        };
        let D::FiniteLaw(other) = &v.data else {
            return Err("有限Lawの構成引数が別由来".into());
        };
        if !Arc::ptr_eq(&data.source, &other.source)
            || other.index >= data.index
            || data.source.base.checked_add(other.index) != Some(reference.0)
        {
            return Err("有限Lawの構成引数が元計画の既出値でない".into());
        }
    }
    Ok(())
}
impl Environment<'_> {
    pub(super) fn recheck_finite_law_diagram(
        &self,
        graph: &Graph,
        value: &ConstructionValue,
    ) -> Result<(), ValidationFailure> {
        let D::FiniteLaw(data) = &value.data else {
            return Ok(());
        };
        tick(&mut self.control.clone())?;
        let Witness::Architecture(a) = &value.witness else {
            return Err("有限Law導出の元Architectureがない".into());
        };
        let current =
            native::architecture_origin(graph, data.source.reference, data.source.object)?;
        if !Arc::ptr_eq(a, current) || !Arc::ptr_eq(a, &data.source.architecture) {
            return Err("有限Lawの消費先Architectureが違う".into());
        }
        let Some(Payload::Construction(consumer)) = &graph.get(data.source.reference)?.payload
        else {
            return Err("有限Lawの消費先Architectureがない".into());
        };
        self.recheck_object_components(graph, consumer)?;
        // immutable Arcを保持し、別のreading/根の検査成功を再利用しない。
        if self
            .verified_finite_law_diagrams
            .borrow()
            .iter()
            .any(|s| Arc::ptr_eq(s, &data.source))
        {
            return Ok(());
        }
        data.source.recheck(
            self.inputs,
            a,
            data.source.object,
            &mut self.control.clone(),
        )?;
        self.verified_finite_law_diagrams
            .borrow_mut()
            .push(data.source.clone());
        Ok(())
    }
}
#[cfg(test)]
#[path = "finite_law_diagram_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "finite_law_owned_tests.rs"]
mod owned_tests;
