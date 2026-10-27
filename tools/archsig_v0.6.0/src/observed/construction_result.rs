//! native構成の不変な検査結果を、公開DAGの型付きrecordとして保持する。
use super::control::{Control, StopReason};
use super::{
    input::CheckedInputs,
    projection::{MapProjection, ProjectionStep, ProjectionType},
    request::Request,
    result::{
        Binding, Decision, Fact, Graph, Judgment, Node, NodeRef, NodeType, Payload, Reason,
        ReasonKind, Rule, Scalar, Scope, ValidationFailure,
    },
};
use crate::construction::{ConstructionFailure, construct, readings::object_reading_instances};
use crate::{
    canonical::Json,
    construction::{
        Configuration, ConfigurationConstruction,
        maps::{ConfigurationOperation, CorrespondenceResult},
        readings::ObjectReadingInstances,
    },
    issue::Location,
    result::location_wire,
    types::Type,
};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ConstructionType {
    Configuration,
    Architecture,
    AtomUniverse,
    AtomMap,
    MapCandidate,
    ConfigurationMap,
    Operation,
    Comparison,
    Ring,
    FiniteFunction,
    RingMap,
    Ideal,
    ObjectComponent,
    Polynomial,
    Context,
    EquationPresentation,
    EquationFamily,
    CircuitPattern,
    CircuitCase,
    CircuitDetector,
    ObjectAlgebra,
    ObjectAlgebraMap,
    EquationMap,
    CircuitMap,
    InvariantMap,
    SignatureMap,
    DeclarationTransport,
    ValueMap,
    ValueEquivalence,
    Invariant,
    SignatureAxis,
    CandidateSpace,
    SolutionSet,
    StateSpace,
    StateMap,
    Assignment,
    Repair,
    Module,
    Quotient,
    LocalSystem,
    Diagnostic,
    Complex,
    CochainMap,
    Action,
    Cohomology,
    Class,
    Cover,
    Topology,
    ContextMap,
    Overlap,
    EquationSpace,
    EquationSolutionSet,

}
impl ConstructionType {
    pub fn name(self) -> &'static str {
        match self {
            Self::Configuration => "Configuration",
            Self::Architecture => "Architecture",
            Self::AtomUniverse => "AtomUniverse",
            Self::AtomMap => "AtomMap",
            Self::MapCandidate => "MapCandidate",
            Self::ConfigurationMap => "ConfigurationMap",
            Self::Operation => "Operation",
            Self::Comparison => "Comparison",
            Self::Ring => "Ring",
            Self::FiniteFunction => "FiniteFunction",
            Self::RingMap => "RingMap",
            Self::Ideal => "Ideal",
            Self::ObjectComponent => "ObjectComponent",
            Self::Polynomial => "Polynomial",
            Self::Context => "Context",
            Self::EquationPresentation => "EquationPresentation",
            Self::EquationFamily => "EquationFamily",
            Self::CircuitPattern => "CircuitPattern",
            Self::CircuitCase => "CircuitCase",
            Self::CircuitDetector => "CircuitDetector",
            Self::ObjectAlgebra => "ObjectAlgebra",
            Self::ObjectAlgebraMap => "ObjectAlgebraMap",
            Self::EquationMap => "EquationMap",
            Self::CircuitMap => "CircuitMap",
            Self::InvariantMap => "InvariantMap",
            Self::SignatureMap => "SignatureMap",
            Self::DeclarationTransport => "DeclarationTransport",
            Self::ValueMap => "ValueMap",
            Self::ValueEquivalence => "ValueEquivalence",
            Self::Invariant => "Invariant",
            Self::SignatureAxis => "SignatureAxis",
            Self::CandidateSpace => "CandidateSpace",
            Self::SolutionSet => "SolutionSet",
            Self::StateSpace => "StateSpace",
            Self::StateMap => "StateMap",
            Self::Assignment => "Assignment",
            Self::Repair => "Repair",
            Self::Module => "Module",
            Self::Quotient => "Quotient",
            Self::LocalSystem => "LocalSystem",
            Self::Diagnostic => "Diagnostic",
            Self::Complex => "Complex",
            Self::CochainMap => "CochainMap",
            Self::Action => "Action",
            Self::Cohomology => "Cohomology",
            Self::Class => "Class",
            Self::Cover => "Cover",
            Self::Topology => "Topology",
            Self::ContextMap => "ContextMap",
            Self::Overlap => "Overlap",
            Self::EquationSpace => "EquationSpace",
            Self::EquationSolutionSet => "EquationSolutionSet",

        }
    }
}

/// この型の生成は同じ三入力を使ったnative構成器との接続内だけで行う。
#[derive(Clone, Debug)]
pub(crate) struct ArchitectureWitness {
    inputs: Arc<CheckedInputs>,
    request: Request,
    construction: ConfigurationConstruction,
    readings: ObjectReadingInstances,
    arrows: Vec<Fact>,
    support: Vec<Fact>,
}
impl PartialEq for ArchitectureWitness {
    fn eq(&self, other: &Self) -> bool {
        self.inputs.sources() == other.inputs.sources()
            && self.request == other.request
            && self.construction == other.construction
            && self.readings == other.readings
            && self.arrows == other.arrows
            && self.support == other.support
    }
}
impl Eq for ArchitectureWitness {}
#[derive(Clone, Debug)]
pub(crate) struct MapWitness {
    inputs: Arc<CheckedInputs>,
    request: Request,
    subject: Fact,
    result: CorrespondenceResult,
    operation: Option<ConfigurationOperation>,
    stopped: Option<StopReason>,
    universe: Vec<Fact>,
    shape: MapProjection,
}
impl PartialEq for MapWitness {
    fn eq(&self, other: &Self) -> bool {
        self.inputs.sources() == other.inputs.sources()
            && self.request == other.request
            && self.subject == other.subject
            && self.result == other.result
            && self.operation == other.operation
            && self.stopped == other.stopped
            && self.universe == other.universe
            && self.shape == other.shape
    }
}
impl Eq for MapWitness {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Witness {
    Architecture(Arc<ArchitectureWitness>),
    Map(Arc<MapWitness>),
    Compose(Arc<super::public_compose::ComposeWitness>),
    PathCompose(Arc<super::public_path_compose::PathWitness>),
    Compare(Arc<super::public_compare::CompareWitness>),
}
#[derive(Clone, Debug)]
pub(crate) struct AtomWitness {
    inputs: Arc<CheckedInputs>,
    fact: Fact,
    value: Scalar,
    location: Location,
}
impl PartialEq for AtomWitness {
    fn eq(&self, other: &Self) -> bool {
        self.inputs.sources() == other.inputs.sources()
            && self.fact == other.fact
            && self.value == other.value
            && self.location == other.location
    }
}
impl Eq for AtomWitness {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ConstructionData {
    FiniteLaw(super::finite_law_diagram::Data),
    PolynomialLaw(super::polynomial_law_diagram::Data),
    LawFrame(super::law_evaluation::Data),
    ObjectReadingFrame(super::object_reading_evaluation::Data),
    ViewFamily(super::view_family::Data),
    ViewInvariant(super::view_invariant::Data),
    PredicateInvariant(super::predicate_invariant::Data),
    OutsideLaw(super::law_inapplicable::Data),
    LawInstantiation(super::law_instantiation::Data),
    LawFamily(super::law_family::Data),
    ObjectComponents(super::object_component_diagram::Data),
    InternalArrows(super::internal_arrow_diagram::Data),
    EquationFamily(super::equation_family::Data),
    CircuitPattern(super::circuit_pattern::Data),
    Build(super::build_result::Data),
    ObjectMap(super::object_map_result::Data),
    Change(super::change_result::Data),
    Quotient(super::quotient_result::Data),
    Local(super::local_result::Data),
    Composition(super::public_compose::Part),
    PathComposition(super::public_path_compose::Part),
    Comparison(super::public_compare::Part),
    Atom(Arc<AtomWitness>),
    ConstructionLabel(Scalar),
    CandidateCondition {
        name: NodeRef,
        subject: NodeRef,
        source: NodeRef,
        target: NodeRef,
    },
    Subject {
        value: Scalar,
        location: Location,
    },
    Pending {
        ty: ConstructionType,
        parts: Vec<(Vec<ProjectionStep>, NodeRef)>,
    },
    PendingPreservation {
        parts: Vec<(Vec<ProjectionStep>, NodeRef)>,
    },
    PendingLawInstance {
        instance: usize,
        parts: Vec<(Vec<ProjectionStep>, NodeRef)>,
    },
    Configuration(Configuration),
    Architecture {
        reading: String,
        root: NodeRef,
        configuration: NodeRef,
        laws: Vec<NodeRef>,
        arrows: Vec<NodeRef>,
    },
    AtomUniverse(Vec<Fact>),
    AtomMap {
        universe: NodeRef,
        images: Vec<Fact>,
    },
    MapCandidate {
        declaration: String,
        subject: NodeRef,
        source: NodeRef,
        target: NodeRef,
        action: NodeRef,
    },
    ConfigurationMap {
        candidate: NodeRef,
        preservation: NodeRef,
    },
    Operation {
        source: NodeRef,
        target: NodeRef,
        candidate: NodeRef,
        configuration_map: NodeRef,
        preservation: NodeRef,
        action: NodeRef,
        subject: NodeRef,
    },
    Source {
        instance: usize,
        guard: bool,
        location: Location,
        bindings: Vec<Binding>,
        parameters: Vec<(String, Type)>,
    },
    LawInstance {
        instance: usize,
        name: String,
        role: crate::law::ast::Role,
        occurrence: Location,
        bindings: Vec<Binding>,
        guard: Option<NodeRef>,
        body: NodeRef,
    },
    Preservation {
        candidate: NodeRef,
    },
    Counterexample {
        index: usize,
        subject: NodeRef,
        left: NodeRef,
        right: NodeRef,
        facts: Vec<Fact>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ConstructionValue {
    pub(super) witness: Witness,
    pub(super) data: ConstructionData,
}
fn refs(rs: &[NodeRef]) -> Json {
    Json::Arr(rs.iter().map(|r| r.wire()).collect())
}
fn bindings(bs: &[Binding]) -> Json {
    Json::Arr(
        bs.iter()
            .map(|b| Json::obj([("name", Json::str(&b.name)), ("value", b.value.wire())]))
            .collect(),
    )
}
impl ConstructionValue {
    pub fn scalar(&self) -> Option<&Scalar> {
        match &self.data {
            ConstructionData::FiniteLaw(data) => data.scalar(),
            ConstructionData::PolynomialLaw(data) => data.scalar(),
            ConstructionData::LawFrame(data) => data.scalar(),
            ConstructionData::ObjectReadingFrame(data) => data.scalar(),
            ConstructionData::ViewFamily(data) => data.scalar(),
            ConstructionData::Build(data) => data.scalar(),
            ConstructionData::Change(data) => data.scalar(),
            ConstructionData::Quotient(data) => data.scalar(),
            ConstructionData::Local(data) => data.scalar(),
            ConstructionData::ObjectMap(data) => data.scalar(),
            ConstructionData::OutsideLaw(data) => data.scalar(),
            ConstructionData::LawInstantiation(data) => data.scalar(),
            ConstructionData::LawFamily(data) => data.scalar(),
            ConstructionData::ObjectComponents(data) => data.scalar(),
            ConstructionData::InternalArrows(data) => data.scalar(),
            ConstructionData::PathComposition(part) => part.scalar(),
            ConstructionData::Comparison(part) => part.scalar(),
            ConstructionData::Subject { value, .. }
            | ConstructionData::ConstructionLabel(value) => Some(value),
            ConstructionData::Atom(a) => Some(&a.value),
            _ => None,
        }
    }
    pub fn is_blocked(&self) -> bool {
        matches!(
            self.data,
            ConstructionData::Pending { .. }
                | ConstructionData::PendingPreservation { .. }
                | ConstructionData::PendingLawInstance { .. }
        )
    }
    pub fn partial(&self, reasons: &[Reason]) -> Option<Json> {
        let parts = match &self.data {
            ConstructionData::Pending { parts, .. }
            | ConstructionData::PendingPreservation { parts }
            | ConstructionData::PendingLawInstance { parts, .. } => parts,
            _ => return None,
        };
        Some(Json::obj([(
            "entries",
            Json::Arr(
                parts
                    .iter()
                    .map(|(path, value)| {
                        Json::obj([
                            (
                                "path",
                                Json::Arr(path.iter().map(ProjectionStep::wire).collect()),
                            ),
                            ("value", value.wire()),
                            (
                                "reasons",
                                Json::Arr(reasons.iter().map(Reason::wire).collect()),
                            ),
                        ])
                    })
                    .collect(),
            ),
        )]))
    }
    pub fn rule(&self) -> Rule {
        match &self.data {
            ConstructionData::Subject { location, .. } => Rule::Input {
                kind: "subject",
                location: location.clone(),
            },
            ConstructionData::Atom(a) => Rule::Input {
                kind: "atom",
                location: a.location.clone(),
            },
            _ => Rule::Construction(self.construction()),
        }
    }
    pub fn ty(&self) -> NodeType {
        use ConstructionData as D;
        let ty = match &self.data {
            D::FiniteLaw(data) => return data.ty(),
            D::PolynomialLaw(data) => return data.ty(),
            D::LawFrame(data) => return data.ty(),
            D::ObjectReadingFrame(data) => return data.ty(),
            D::ViewFamily(data) => return data.ty(),
            D::ViewInvariant(data) => return data.ty(),
            D::PredicateInvariant(data) => return data.ty(),
            D::OutsideLaw(data) => return data.ty(),
            D::LawInstantiation(data) => return data.ty(),
            D::LawFamily(data) => return data.ty(),
            D::ObjectComponents(data) => return data.ty(),
            D::InternalArrows(data) => return data.ty(),
            D::EquationFamily(data) => return data.ty(),
            D::CircuitPattern(data) => return data.ty(),
            D::Build(data) => return data.ty(),
            D::Change(data) => return data.ty(),
            D::Quotient(data) => return data.ty(),
            D::Local(data) => return data.ty(),
            D::ObjectMap(data) => return data.ty(),
            D::Composition(part) => return part.ty(),
            D::PathComposition(part) => return part.ty(),
            D::Comparison(part) => return part.ty(),
            D::Subject { value, .. } => return NodeType::Value(value.ty()),
            D::Atom(a) => return NodeType::Value(a.value.ty()),
            D::ConstructionLabel(_) => return NodeType::Value(Type::Text),
            D::CandidateCondition { .. } => return NodeType::Proposition,
            D::Pending { ty, .. } => *ty,
            D::PendingPreservation { .. } => return NodeType::Proposition,
            D::PendingLawInstance { .. } => return NodeType::LawInstance,
            D::Configuration(_) => ConstructionType::Configuration,
            D::Architecture { .. } => ConstructionType::Architecture,
            D::AtomUniverse(_) => ConstructionType::AtomUniverse,
            D::AtomMap { .. } => ConstructionType::AtomMap,
            D::MapCandidate { .. } => ConstructionType::MapCandidate,
            D::ConfigurationMap { .. } => ConstructionType::ConfigurationMap,
            D::Operation { .. } => ConstructionType::Operation,
            D::Source { .. } => return NodeType::Expression(Type::Bool),
            D::LawInstance { .. } => return NodeType::LawInstance,
            D::Preservation { .. } => return NodeType::Proposition,
            D::Counterexample { .. } => return NodeType::Evidence,
        };
        NodeType::Construction(ty)
    }
    pub fn arguments(&self) -> Vec<NodeRef> {
        use ConstructionData as D;
        match &self.data {
            D::FiniteLaw(data) => data.arguments(),
            D::PolynomialLaw(data) => data.arguments(),
            D::LawFrame(data) => data.arguments(),
            D::ObjectReadingFrame(data) => data.arguments(),
            D::ViewFamily(data) => data.arguments(),
            D::ViewInvariant(data) => data.arguments(),
            D::PredicateInvariant(data) => data.arguments(),
            D::OutsideLaw(data) => data.arguments(),
            D::LawInstantiation(data) => data.arguments(),
            D::LawFamily(data) => data.arguments(),
            D::ObjectComponents(data) => data.arguments(),
            D::InternalArrows(data) => data.arguments(),
            D::EquationFamily(data) => data.arguments(),
            D::CircuitPattern(data) => data.arguments(),
            D::Build(data) => data.arguments(),
            D::Change(data) => data.arguments(),
            D::Quotient(data) => data.arguments(),
            D::Local(data) => data.arguments(),
            D::ObjectMap(data) => data.arguments(),
            D::Composition(part) => part.arguments(),
            D::PathComposition(part) => part.arguments(),
            D::Comparison(part) => {
                let mut arguments = part.arguments();
                if matches!(part, super::public_compare::Part::Comparison { .. } | super::public_compare::Part::Claim { .. })
                    && let Witness::Compare(w) = &self.witness
                    && let Some(plan) = &w.relation_plan {
                    arguments.extend(plan.dependencies.iter().copied());
                }
                arguments
            },
            D::Subject { .. } | D::Atom(_) | D::ConstructionLabel(_) => vec![],
            D::CandidateCondition {
                name,
                subject,
                source,
                target,
            } => vec![*name, *subject, *source, *target],
            D::Pending { parts, .. }
            | D::PendingPreservation { parts }
            | D::PendingLawInstance { parts, .. } => parts.iter().map(|(_, r)| *r).collect(),
            D::Configuration(_) | D::AtomUniverse(_) => vec![],
            D::Architecture {
                root,
                configuration,
                laws,
                arrows,
                ..
            } => std::iter::once(*root)
                .chain(std::iter::once(*configuration))
                .chain(laws.iter().copied())
                .chain(arrows.iter().copied())
                .collect(),
            D::AtomMap { universe, .. } => vec![*universe],
            D::MapCandidate {
                subject,
                source,
                target,
                action,
                ..
            } => vec![*subject, *source, *target, *action],
            D::ConfigurationMap { candidate, .. } | D::Preservation { candidate } => {
                vec![*candidate]
            }
            D::Operation {
                source,
                target,
                candidate,
                configuration_map,
                action,
                subject,
                ..
            } => vec![
                *source,
                *target,
                *candidate,
                *configuration_map,
                *action,
                *subject,
            ],
            D::Source { bindings, .. } => bindings.iter().map(|b| b.value).collect(),
            D::LawInstance {
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
            D::Counterexample {
                subject,
                left,
                right,
                ..
            } => vec![*subject, *left, *right],
        }
    }
    pub fn conditions(&self) -> Vec<NodeRef> {
        match &self.data {
            ConstructionData::Change(data) => data.conditions(),
            ConstructionData::Quotient(data) => data.conditions(),
            ConstructionData::Local(data) => data.conditions(),
            ConstructionData::ObjectMap(data) => data.conditions(),
            ConstructionData::Composition(part) => part.conditions(),
            ConstructionData::PathComposition(part) => part.conditions(),
            ConstructionData::Comparison(part) => part.conditions(),
            ConstructionData::ConfigurationMap { preservation, .. }
            | ConstructionData::Operation { preservation, .. } => vec![*preservation],
            _ => vec![],
        }
    }
    pub fn construction(&self) -> &'static str {
        use ConstructionData as D;
        match self.data {
            D::FiniteLaw(ref data) => data.construction(),
            D::PolynomialLaw(ref data) => data.construction(),
            D::LawFrame(_) => "domain",
            D::ObjectReadingFrame(ref data) => data.construction(),
            D::ViewFamily(ref data) => data.construction(),
            D::ViewInvariant(ref data) => data.construction(),
            D::PredicateInvariant(ref data) => data.construction(),
            D::OutsideLaw(ref data) => data.construction(),
            D::LawInstantiation(ref data) => data.construction(),
            D::LawFamily(ref data) => data.construction(),
            D::ObjectComponents(ref data) => data.construction(),
            D::InternalArrows(ref data) => data.construction(),
            D::EquationFamily(_) => "equation_family",
            D::CircuitPattern(_) => "circuit_pattern",
            D::Build(ref data) => data.construction(),
            D::Change(ref data) => data.construction(),
            D::Quotient(ref data) => data.construction(),
            D::Local(ref data) => data.construction(),
            D::ObjectMap(ref data) => data.construction(),
            D::Composition(ref part) => part.construction(),
            D::PathComposition(ref part) => part.construction(),
            D::Comparison(ref part) => part.construction(),
            D::ConstructionLabel(_) => "binding",
            D::CandidateCondition { .. } => "proposition",
            D::Subject { .. } => "binding",
            D::Atom(_) => "binding",
            D::Pending { ty, .. } => match ty {
                ConstructionType::Configuration => "configuration",
                ConstructionType::Architecture => "architecture",
                ConstructionType::AtomUniverse => "atom_universe",
                ConstructionType::AtomMap => "atom_map",
                ConstructionType::MapCandidate => "map_candidate",
                ConstructionType::ConfigurationMap => "configuration_map",
                ConstructionType::Operation => "operation",
                ConstructionType::Comparison => "comparison",
                ConstructionType::Ring => "ring",
                ConstructionType::FiniteFunction => "finite_function",
                ConstructionType::RingMap => "ring_map",
                ConstructionType::Ideal => "ideal",
                ConstructionType::ObjectComponent => "object_component",
                ConstructionType::Polynomial => "polynomial",
                ConstructionType::Context => "context",
                ConstructionType::EquationPresentation => "equation_presentation",
                ConstructionType::EquationFamily => "equation_family",
                ConstructionType::CircuitPattern => "circuit_pattern",
                ConstructionType::CircuitCase => "circuit_case",
                ConstructionType::CircuitDetector => "circuit_detector",
                ConstructionType::ObjectAlgebra => "object_algebra",
                ConstructionType::ObjectAlgebraMap => "object_algebra_map",
                ConstructionType::EquationMap => "equation_map",
                ConstructionType::CircuitMap => "circuit_map",
                ConstructionType::InvariantMap => "invariant_map",
                ConstructionType::SignatureMap => "signature_map",
                ConstructionType::DeclarationTransport => "declaration_transport",
                ConstructionType::ValueMap => "value_map",
                ConstructionType::ValueEquivalence => "value_equivalence",
                ConstructionType::Invariant => "invariant",
                ConstructionType::SignatureAxis => "signature_axis",
                ConstructionType::CandidateSpace => "candidate_space",
                ConstructionType::SolutionSet => "solution_set",
                ConstructionType::StateSpace => "state_space",
                ConstructionType::StateMap => "state_map",
                ConstructionType::Assignment => "assignment",
                ConstructionType::Repair => "repair",
                ConstructionType::Module => "module",
                ConstructionType::Quotient => "quotient",
                ConstructionType::LocalSystem => "local_system",
                ConstructionType::Diagnostic => "diagnostic",
                ConstructionType::Complex => "complex",
                ConstructionType::CochainMap => "cochain_map",
                ConstructionType::Action => "action",
                ConstructionType::Cohomology => "cohomology",
                ConstructionType::Class => "class",
                ConstructionType::Cover => "cover",
                ConstructionType::Topology => "topology",
                ConstructionType::ContextMap => "context_map",
                ConstructionType::Overlap => "overlap",
                ConstructionType::EquationSpace => "equation_space",
                ConstructionType::EquationSolutionSet => "equation_solution_set",
            },
            D::PendingPreservation { .. } => "proposition",
            D::PendingLawInstance { .. } => "law_instance",
            D::Configuration(_) => "configuration",
            D::Architecture { .. } => "architecture",
            D::AtomUniverse(_) => "atom_universe",
            D::AtomMap { .. } => "atom_map",
            D::MapCandidate { .. } => "map_candidate",
            D::ConfigurationMap { .. } => "configuration_map",
            D::Operation { .. } => "operation",
            D::Source { .. } => "expression",
            D::LawInstance { .. } => "law_instance",
            D::Preservation { .. } => "proposition",
            D::Counterexample { .. } => "evidence",
        }
    }
    pub fn projection_type(&self) -> Option<ProjectionType> {
        use ConstructionData as D;
        match (&self.data, &self.witness) {
            (D::Change(data), _) => data.projection_type(),
            (D::Quotient(data), _) => data.projection_type(),
            (D::Local(data), _) => data.projection_type(),
            (D::ObjectMap(data), _) => data.projection_type(),
            (D::Build(data), Witness::Architecture(a)) if data.algebra_base().is_some() => {
                Some(ProjectionType::ObjectAlgebraRoot(
                    a.inputs
                        .archmap()
                        .snapshots
                        .iter()
                        .find(|s| s.id == a.construction.root().snapshot)?
                        .subjects
                        .iter()
                        .find(|s| s.id == a.construction.root().subject)?
                        .ty
                        .clone(),
                ))
            }
            (D::ObjectComponents(data), Witness::Architecture(a))
                if data.base_component().is_some() =>
            {
                Some(ProjectionType::ObjectComponentRoot(
                    a.inputs
                        .archmap()
                        .snapshots
                        .iter()
                        .find(|s| s.id == a.construction.root().snapshot)?
                        .subjects
                        .iter()
                        .find(|s| s.id == a.construction.root().subject)?
                        .ty
                        .clone(),
                ))
            }
            (D::InternalArrows(data), Witness::Architecture(_)) => data.projection_type(),
            (D::ObjectComponents(data), Witness::Architecture(_)) => {
                data.root_type().map(ProjectionType::ArchitectureRoot)
            }
            (D::Composition(part), Witness::Compose(c)) => part.projection_type(c),
            (D::PathComposition(part), Witness::PathCompose(_)) => part.projection_type(),
            (D::Comparison(part), Witness::Compare(_)) => part.projection_type(),
            (D::Architecture { .. }, Witness::Architecture(a)) => {
                Some(ProjectionType::ArchitectureRoot(
                    a.inputs
                        .archmap()
                        .snapshots
                        .iter()
                        .find(|s| s.id == a.construction.root().snapshot)?
                        .subjects
                        .iter()
                        .find(|s| s.id == a.construction.root().subject)?
                        .ty
                        .clone(),
                ))
            }
            (D::MapCandidate { .. }, Witness::Map(m)) => {
                Some(ProjectionType::MapCandidate(m.shape.clone()))
            }
            (D::ConfigurationMap { .. }, Witness::Map(m)) => {
                Some(ProjectionType::ConfigurationMap(m.shape.clone()))
            }
            (D::Operation { .. }, Witness::Map(m)) => {
                Some(ProjectionType::Operation(m.shape.clone()))
            }
            (D::AtomMap { .. }, _) => Some(ProjectionType::AtomMap),
            _ => None,
        }
    }
    pub(super) fn scalar_projection(&self, path: &[ProjectionStep]) -> Option<Scalar> {
        match &self.data { ConstructionData::Local(data) => data.scalar_projection(path), _ => None }
    }
    pub fn project(&self, path: &[ProjectionStep]) -> Option<(NodeRef, usize)> {
        use ConstructionData as D;
        if let D::Change(data) = &self.data { return data.project(path); }
        if let D::Quotient(data) = &self.data { return data.project(path); }
        if let D::Local(data) = &self.data { return data.project(path); }
        if let D::ObjectMap(data) = &self.data { return data.project(path); }
        if let D::Build(data) = &self.data {
            return match path.first()? {
                ProjectionStep::Field(f) if f == "base" => data.algebra_base().map(|r| (r, 1)),
                _ => None,
            };
        }
        if let D::ObjectComponents(data) = &self.data
            && let Some((subject, object)) = data.base_component()
        {
            return match path.first()? {
                ProjectionStep::Field(f) if f == "subject" => Some((subject, 1)),
                ProjectionStep::Field(f) if f == "object" => Some((object, 1)),
                _ => None,
            };
        }
        if let D::InternalArrows(data) = &self.data {
            return data.project(path);
        }
        if let D::ObjectComponents(data) = &self.data {
            return match path.first()? {
                ProjectionStep::Field(f) if f == "root" => data.root().map(|r| (r, 1)),
                _ => None,
            };
        }
        if let D::Composition(part) = &self.data { return part.project(path); }
        if let D::PathComposition(part) = &self.data { return part.project(path); }
        if let D::Comparison(part) = &self.data { return part.project(path); }
        let ProjectionStep::Field(field) = path.first()? else {
            return None;
        };
        let r = match (&self.data, field.as_str()) {
            (D::Architecture { root, .. }, "root") => *root,
            (D::MapCandidate { subject, .. }, "subject") => *subject,
            (D::MapCandidate { source, .. } | D::Operation { source, .. }, "source") => *source,
            (D::MapCandidate { target, .. } | D::Operation { target, .. }, "target") => *target,
            (D::MapCandidate { action, .. } | D::Operation { action, .. }, "action") => *action,
            (
                D::ConfigurationMap { candidate, .. } | D::Operation { candidate, .. },
                "candidate",
            ) => *candidate,
            (
                D::Operation {
                    configuration_map, ..
                },
                "configuration_map",
            ) => *configuration_map,
            (D::Operation { subject, .. }, "word")
                if path.get(1) == Some(&ProjectionStep::Index(0)) =>
            {
                return Some((*subject, 2));
            }
            _ => return None,
        };
        Some((r, 1))
    }
    pub fn wire(&self) -> Json {
        use ConstructionData as D;
        match &self.data {
            D::FiniteLaw(data) => data.wire(),
            D::PolynomialLaw(data) => data.wire(),
            D::LawFrame(data) => data.wire(),
            D::ObjectReadingFrame(data) => data.wire(),
            D::ViewFamily(data) => data.wire(),
            D::ViewInvariant(data) => data.wire(),
            D::PredicateInvariant(data) => data.wire(),
            D::OutsideLaw(data) => data.wire(),
            D::LawInstantiation(data) => data.wire(),
            D::LawFamily(data) => data.wire(),
            D::ObjectComponents(data) => data.wire(),
            D::InternalArrows(data) => data.wire(),
            D::EquationFamily(data) => data.wire(),
            D::CircuitPattern(data) => data.wire(),
            D::Build(data) => data.wire(),
            D::Change(data) => data.wire(),
            D::Quotient(data) => data.wire(),
            D::Local(data) => data.wire(),
            D::ObjectMap(data) => data.wire(),
            D::Composition(part) => part.wire(),
            D::PathComposition(part) => part.wire(),
            D::Comparison(part) => match &self.witness { Witness::Compare(w) => part.wire(w), _ => unreachable!("比較は元検査を持つ") },
            D::Subject { value, .. } => value.wire(),
            D::Atom(a) => a.value.wire(),
            D::Pending { .. } | D::PendingPreservation { .. } | D::PendingLawInstance { .. } => {
                Json::obj([])
            }
            D::Configuration(c) => c.wire(),
            D::Architecture {
                reading,
                root,
                configuration,
                laws,
                arrows,
                ..
            } => Json::obj([
                ("reading", Json::str(reading)),
                ("root", root.wire()),
                ("configuration", configuration.wire()),
                ("laws", refs(laws)),
                ("internal_arrows", refs(arrows)),
                ("overrides", Json::Arr(vec![])),
            ]),
            D::AtomUniverse(atoms) => {
                Json::obj([("atoms", Json::Arr(atoms.iter().map(Fact::wire).collect()))])
            }
            D::AtomMap { universe, images } => Json::obj([
                ("universe", universe.wire()),
                ("images", Json::Arr(images.iter().map(Fact::wire).collect())),
            ]),
            D::MapCandidate {
                declaration,
                subject,
                source,
                target,
                action,
                ..
            } => Json::obj([
                ("declaration", Json::str(declaration)),
                ("subject", subject.wire()),
                ("source", source.wire()),
                ("target", target.wire()),
                ("action", action.wire()),
            ]),
            D::ConfigurationMap { candidate, .. } => Json::obj([("candidate", candidate.wire())]),
            D::Operation {
                source,
                target,
                candidate,
                configuration_map,
                action,
                subject,
                ..
            } => Json::obj([
                ("source", source.wire()),
                ("target", target.wire()),
                ("candidate", candidate.wire()),
                ("configuration_map", configuration_map.wire()),
                ("action", action.wire()),
                (
                    "name",
                    Json::obj([
                        ("kind", Json::str("generator")),
                        ("subject", subject.wire()),
                    ]),
                ),
                ("word", refs(&[*subject])),
            ]),
            D::Source {
                location,
                bindings: bs,
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
                ("bindings", bindings(bs)),
            ]),
            D::LawInstance {
                name,
                role,
                occurrence,
                bindings: bs,
                guard,
                body,
                ..
            } => {
                let mut j = Json::obj([
                    ("name", Json::str(name)),
                    (
                        "role",
                        Json::str(match role {
                            crate::law::ast::Role::Required => "required",
                            crate::law::ast::Role::Optional => "optional",
                        }),
                    ),
                    ("bindings", bindings(bs)),
                    ("body", body.wire()),
                    ("occurrence", location_wire(occurrence)),
                ]);
                if let (Some(g), Json::Obj(fields)) = (guard, &mut j) {
                    fields.insert("guard".into(), g.wire());
                }
                j
            }
            D::ConstructionLabel(label) => label.wire(),
            D::CandidateCondition {
                name,
                subject,
                source,
                target,
            } => Json::obj([
                ("predicate", Json::str("constructible")),
                ("operands", refs(&[*name, *subject, *source, *target])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            D::Preservation { candidate } => Json::obj([
                ("predicate", Json::str("configuration_preserved")),
                ("operands", refs(&[*candidate])),
                ("quantifiers", Json::Arr(vec![])),
            ]),
            D::Counterexample {
                subject,
                left,
                right,
                facts,
                ..
            } => Json::obj([
                ("kind", Json::str("counterexample")),
                (
                    "data",
                    Json::obj([
                        (
                            "bindings",
                            Json::Arr(vec![Json::obj([
                                ("name", Json::str("on")),
                                ("value", subject.wire()),
                            ])]),
                        ),
                        ("paths", Json::Arr(vec![])),
                        ("left", left.wire()),
                        ("right", right.wire()),
                        ("facts", Json::Arr(facts.iter().map(Fact::wire).collect())),
                    ]),
                ),
            ]),
        }
    }
}

pub(crate) fn counterexample_facts(c: &crate::construction::maps::Counterexample) -> Vec<Fact> {
    use crate::construction::maps::Counterexample as C;
    let mut facts = match c {
        C::Field {
            source,
            target_subject,
            ..
        } => vec![source.clone(), target_subject.clone()],
        C::ReferenceStructure { source, target } => vec![source.clone(), target.clone()],
        C::ReferenceConstraints {
            fields,
            unresolved_fields,
        } => fields
            .iter()
            .flat_map(|(a, b)| [a.clone(), b.clone()])
            .chain(unresolved_fields.iter().cloned())
            .collect(),
        C::Family { source, image } => vec![source.clone(), image.clone()],
        C::Relation {
            source: (a, b),
            image: (c, d),
        }
        | C::Identification {
            source: (a, b),
            image: (c, d),
        } => vec![a.clone(), b.clone(), c.clone(), d.clone()],
    };
    facts.sort_by_key(|f| f.wire().canonical());
    facts.dedup();
    facts
}
fn value<'a>(graph: &'a Graph, r: NodeRef) -> Result<&'a ConstructionValue, ValidationFailure> {
    match graph.get(r)?.payload.as_ref() {
        Some(Payload::Construction(v)) => Ok(v),
        _ => Err("native構成の参照先が別の型".into()),
    }
}
fn subject_fact(graph: &Graph, r: NodeRef) -> Result<Fact, ValidationFailure> {
    match graph.scalar(r)? {
        Scalar::Subject {
            snapshot, subject, ..
        } => Ok(Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: None,
            atom: None,
        }),
        _ => Err("native構成のsubject参照が原始参照でない".into()),
    }
}
impl Witness {
    pub(super) fn shared_inputs(&self) -> Arc<CheckedInputs> {
        match self {
            Self::Architecture(a) => a.inputs.clone(),
            Self::Map(m) => m.inputs.clone(),
            Self::Compose(c) => c.inputs.clone(),
            Self::PathCompose(c) => c.inputs.clone(),
            Self::Compare(c) => c.inputs.clone(),
        }
    }
    pub fn inputs(&self) -> &CheckedInputs {
        match self {
            Self::Architecture(a) => &a.inputs,
            Self::Map(m) => &m.inputs,
            Self::Compose(c) => &c.inputs,
            Self::PathCompose(c) => &c.inputs,
            Self::Compare(c) => &c.inputs,
        }
    }
    pub fn request(&self) -> &Request {
        match self {
            Self::Architecture(a) => &a.request,
            Self::Map(m) => &m.request,
            Self::Compose(c) => &c.request,
            Self::PathCompose(c) => &c.request,
            Self::Compare(c) => &c.request,
        }
    }
}
impl ArchitectureWitness {
    /// 外からnative値や由来を注入せず、検査済み三入力から一緒に生成する。
    pub fn compute(
        inputs: Arc<CheckedInputs>,
        request: &Request,
        reading: &str,
        root: &Fact,
        control: &mut Control,
    ) -> Result<Arc<Self>, ConstructionFailure> {
        let construction = construct(&inputs, reading, &root.snapshot, &root.subject, control)?;
        let readings = object_reading_instances(&inputs, &construction, control)?;
        let mut arrows = vec![];
        for fact in construction.local_domain().known().iter().chain(
            construction
                .local_domain()
                .conditional()
                .iter()
                .filter(|m| !m.is_entity())
                .map(|m| m.subject()),
        ) {
            control.checkpoint(super::control::Checkpoint::ObjectInstances)?;
            let subject = find_subject(&inputs, fact).map_err(ConstructionFailure::Inconsistent)?;
            if matches!(
                inputs.definitions().declarations[&subject.ty].signature,
                crate::definition::PrimitiveSignature::Arrow { .. }
            ) {
                arrows.push(fact.clone());
            }
        }
        arrows.sort_by_key(|f| f.wire().canonical());
        arrows.dedup();
        let namespaces = crate::construction::reading_namespaces(inputs.law(), reading, control)?;
        let root_type = &find_subject(&inputs, root)
            .map_err(ConstructionFailure::Inconsistent)?
            .ty;
        let mut support = construction.base().known().family().to_vec();
        for snapshot in &inputs.archmap().snapshots {
            for subject in &snapshot.subjects {
                control.checkpoint(super::control::Checkpoint::ObjectInstances)?;
                let declaration = &inputs.definitions().declarations[&subject.ty];
                let owner = match &declaration.signature {
                    crate::definition::PrimitiveSignature::Entity {
                        owner: Some(owner), ..
                    }
                    | crate::definition::PrimitiveSignature::Arrow { owner, .. } => owner,
                    _ => continue,
                };
                if owner != root_type || !namespaces.contains(&declaration.namespace) {
                    continue;
                }
                // 別root所属として除外した根拠も支持へ残す。
                support.push(Fact {
                    snapshot: subject.snapshot.clone(),
                    subject: subject.id.clone(),
                    field: None,
                    atom: None,
                });
                for field in &subject.fields {
                    if field.name.rsplit('.').next() != Some("owner") {
                        continue;
                    }
                    if let crate::archmap::Slot::Known { atom, .. } = &field.slot {
                        support.push(Fact {
                            snapshot: subject.snapshot.clone(),
                            subject: subject.id.clone(),
                            field: Some(field.name.clone()),
                            atom: Some(atom.clone()),
                        });
                    }
                }
            }
        }
        for row in readings.instances() {
            for binding in row.bindings() {
                control.checkpoint(super::control::Checkpoint::ObjectInstances)?;
                support.push(binding.subject().clone());
                if matches!(binding.parameter().ty, Type::Owned(..)) {
                    let subject = find_subject(&inputs, binding.subject())
                        .map_err(ConstructionFailure::Inconsistent)?;
                    for field in &subject.fields {
                        if field.name.rsplit('.').next() == Some("owner")
                            && let crate::archmap::Slot::Known { atom, .. } = &field.slot
                        {
                            support.push(Fact {
                                snapshot: subject.snapshot.clone(),
                                subject: subject.id.clone(),
                                field: Some(field.name.clone()),
                                atom: Some(atom.clone()),
                            });
                        }
                    }
                }
            }
        }
        support.sort_by_key(|f| f.wire().canonical());
        support.dedup();
        Ok(Arc::new(Self {
            inputs,
            request: request.clone(),
            construction,
            readings,
            arrows,
            support,
        }))
    }
    pub fn construction(&self) -> &ConfigurationConstruction {
        &self.construction
    }
    pub fn readings(&self) -> &ObjectReadingInstances {
        &self.readings
    }
    pub fn arrows(&self) -> &[Fact] {
        &self.arrows
    }
}
impl MapWitness {
    pub fn compute(
        inputs: Arc<CheckedInputs>,
        request: &Request,
        subject: Fact,
        universe: Option<&ArchitectureWitness>,
        control: &mut Control,
    ) -> Result<(Arc<Self>, Option<StopReason>), ConstructionFailure> {
        let universe = match universe {
            Some(a) if a.inputs.sources() == inputs.sources() => a.construction.universe().to_vec(),
            Some(_) => {
                return Err(ConstructionFailure::Inconsistent(
                    "別入力の共通Uをmapへ渡した".into(),
                ));
            }
            None => vec![],
        };
        let name = match &request.head {
            super::request::Selector::Declaration { name } => name,
            _ => {
                return Err(ConstructionFailure::Inconsistent(
                    "mapの原始宣言がない".into(),
                ));
            }
        };
        let crate::definition::PrimitiveSignature::Correspondence { from, to, .. } =
            &inputs.definitions().declarations[name].signature
        else {
            return Err(ConstructionFailure::Inconsistent(
                "mapの宣言がcorrespondenceでない".into(),
            ));
        };
        let shape = MapProjection {
            declaration: name.clone(),
            source: from.clone(),
            target: to.clone(),
        };
        let reading = reading(request, "reading").map_err(ConstructionFailure::Inconsistent)?;
        let to = reading_name(request, "to_reading").map_err(ConstructionFailure::Inconsistent)?;
        let (result, mut stopped) = match crate::construction::maps::correspondence_retained(
            &inputs,
            &subject.snapshot,
            &subject.subject,
            reading,
            Some(to),
            control,
        ) {
            Ok(value) => (value, None),
            Err(failure) => match failure.into_parts() {
                (ConstructionFailure::Stopped(stop), Some(partial)) => (*partial, Some(stop)),
                (cause, _) => return Err(cause),
            },
        };
        let mut operation = None;
        if stopped.is_none()
            && let Some(map) = result.map()
        {
            match ConfigurationOperation::from_map_retained(&inputs, map, control) {
                Ok(value) => operation = Some(value),
                Err(failure) => match failure.into_parts() {
                    (ConstructionFailure::Stopped(stop), partial) => {
                        stopped = Some(stop);
                        operation = partial.map(|p| *p);
                    }
                    (cause, _) => return Err(cause),
                },
            }
        }
        Ok((
            Arc::new(Self {
                inputs,
                request: request.clone(),
                subject,
                result,
                operation,
                shape,
                stopped: stopped.clone(),
                universe,
            }),
            stopped,
        ))
    }
    pub fn result(&self) -> &CorrespondenceResult {
        &self.result
    }
    pub fn operation(&self) -> Option<&ConfigurationOperation> {
        self.operation.as_ref()
    }
    pub fn shape(&self) -> &MapProjection {
        &self.shape
    }
    pub fn subject(&self) -> &Fact {
        &self.subject
    }
    pub fn failed_candidate(&self) -> bool {
        self.result.candidate().is_none()
            && self.result.missing().is_empty()
            && self.stopped.is_none()
            && !self.result.counterexamples().is_empty()
    }
    pub fn reasons(&self) -> Vec<Reason> {
        let mut reasons = missing(&self.request, self.result.missing().to_vec());
        if let Some(stop) = &self.stopped {
            reasons.push(Reason::stopped(&self.request.id, stop.clone()));
        }
        super::result::sort_reasons(&mut reasons);
        reasons
    }
}
pub fn reading_name<'a>(request: &'a Request, key: &str) -> Result<&'a str, String> {
    match request
        .arguments
        .iter()
        .find(|a| a.name == key)
        .map(|a| &a.value)
    {
        Some(super::request::Selector::Declaration { name }) => Ok(name),
        _ => Err(format!("mapの{key}がない")),
    }
}
pub fn instance_missing(row: &crate::construction::readings::ObjectInstance) -> Vec<Fact> {
    match row.applications().first() {
        Some(crate::construction::readings::InstanceApplication::Applicable { conditions }) => {
            conditions.iter().map(|c| c.slot().clone()).collect()
        }
        _ => vec![],
    }
}
pub fn missing(request: &Request, facts: Vec<Fact>) -> Vec<Reason> {
    if facts.is_empty() {
        return vec![];
    }
    let mut facts = facts;
    facts.sort_by_key(|f| f.wire().canonical());
    facts.dedup();
    vec![Reason {
        kind: ReasonKind::Missing,
        request: request.id.clone(),
        dependencies: vec![],
        missing: facts,
        location: None,
    }]
}
fn reading<'a>(request: &'a Request, key: &str) -> Result<&'a str, String> {
    reading_name(request, key)
}
fn find_subject<'a>(
    inputs: &'a CheckedInputs,
    fact: &Fact,
) -> Result<&'a crate::archmap::Subject, String> {
    inputs
        .archmap()
        .snapshots
        .iter()
        .find(|s| s.id == fact.snapshot)
        .and_then(|s| s.subjects.iter().find(|s| s.id == fact.subject))
        .ok_or_else(|| "native構成の元subjectが現在の入力にない".into())
}
pub fn subject_value(
    witness: Witness,
    fact: &Fact,
) -> Result<ConstructionValue, ValidationFailure> {
    let subject = find_subject(witness.inputs(), fact)?;
    let value = Scalar::Subject {
        entity: subject.ty.clone(),
        snapshot: subject.snapshot.clone(),
        subject: subject.id.clone(),
    };
    let location = Location::ArchMap {
        pointer: subject.pointer.clone(),
        span: None,
    };
    Ok(ConstructionValue {
        witness,
        data: ConstructionData::Subject { value, location },
    })
}
pub fn atom_value(
    witness: Witness,
    fact: &Fact,
    control: &Control,
) -> Result<ConstructionValue, ValidationFailure> {
    if fact.field.is_none() {
        return subject_value(witness, fact);
    }
    let inputs = witness.shared_inputs();
    let subject = find_subject(&inputs, fact)?;
    let field = subject
        .fields
        .iter()
        .find(|f| Some(&f.name) == fact.field.as_ref())
        .ok_or("元fieldがない")?;
    let crate::archmap::Slot::Known {
        value,
        atom,
        pointer,
        ..
    } = &field.slot
    else {
        return Err("未観測Atomを通常値へ昇格した".into());
    };
    if Some(atom) != fact.atom.as_ref() {
        return Err("元Atomのidentityが違う".into());
    }
    let value = super::environment::scalar_from(value, &field.ty, inputs.law(), control)?
        .ok_or("既知Atomの型付き値がない")?;
    let location = Location::ArchMap {
        pointer: pointer.clone(),
        span: None,
    };
    let leaf = Arc::new(AtomWitness {
        inputs,
        fact: fact.clone(),
        value,
        location,
    });
    Ok(ConstructionValue {
        witness,
        data: ConstructionData::Atom(leaf),
    })
}
pub fn metadata(value: &ConstructionValue) -> Result<(Vec<Fact>, Scope), ValidationFailure> {
    if let ConstructionData::Change(data) = &value.data { return Ok(data.metadata()); }
    if let ConstructionData::Quotient(data) = &value.data { return Ok(data.metadata()); }
    if let ConstructionData::Local(data) = &value.data { return Ok(data.metadata()); }
    if let ConstructionData::ObjectMap(data) = &value.data { return Ok(data.metadata()); }
    if let ConstructionData::Build(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::LawFamily(data) = &value.data {
        return Ok((data.support.clone(), data.scope.clone()));
    }
    if let ConstructionData::LawInstantiation(data) = &value.data {
        return Ok((data.support.clone(), data.scope.clone()));
    }
    if let ConstructionData::OutsideLaw(data) = &value.data {
        return Ok((data.support.clone(), data.scope.clone()));
    }
    if let ConstructionData::ObjectReadingFrame(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::ViewFamily(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::ViewInvariant(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::PredicateInvariant(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::LawFrame(data) = &value.data {
        return Ok((data.support.clone(), data.scope.clone()));
    }
    if let ConstructionData::FiniteLaw(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::PolynomialLaw(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::ObjectComponents(data) = &value.data {
        let (support, scope) = data.metadata();
        return Ok((support.to_vec(), scope));
    }
    if let ConstructionData::InternalArrows(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::EquationFamily(data) = &value.data {
        return Ok(data.metadata());
    }
    if let ConstructionData::CircuitPattern(data) = &value.data {
        return Ok(data.metadata());
    }
    if let Witness::PathCompose(c) = &value.witness {
        return Ok((c.support.clone(), c.scope.clone()));
    }
    if let (
        Witness::Compare(w),
        ConstructionData::Comparison(super::public_compare::Part::RelationSource(data)),
    ) = (&value.witness, &value.data)
    {
        let _ = w;
        return Ok((data.support.clone(), data.scope.clone()));
    }
    if let (Witness::Compare(w), ConstructionData::Comparison(super::public_compare::Part::RelationDerived { index, .. })) = (&value.witness, &value.data) {
        let plan = w.relation_plan.as_ref().ok_or("relationの元証拠がない")?;
        return Ok((
            w.support.clone(),
            super::public_compare::relations::scope_at(plan, Some(plan.base + index)),
        ));
    }
    if let Witness::Compare(c) = &value.witness { return Ok((c.support.clone(), c.scope.clone())); }
    if let Witness::Compose(c) = &value.witness {
        return Ok((c.support.clone(), c.scope.clone()));
    }
    let inputs = value.witness.inputs();
    let mut support = match (&value.data, &value.witness) {
        (ConstructionData::Atom(a), _) => vec![a.fact.clone()],
        (ConstructionData::AtomUniverse(atoms), _) => atoms.clone(),
        (
            ConstructionData::Subject {
                value: Scalar::Subject {
                    snapshot, subject, ..
                },
                ..
            },
            _,
        ) => vec![Fact {
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            field: None,
            atom: None,
        }],
        (_, Witness::Architecture(a)) => a.support.clone(),
        (_, Witness::Map(m)) => {
            let mut facts = m.universe.clone();
            facts.push(m.subject.clone());
            for f in &find_subject(inputs, &m.subject)?.fields {
                if let crate::archmap::Slot::Known { atom, .. } = &f.slot {
                    facts.push(Fact {
                        snapshot: m.subject.snapshot.clone(),
                        subject: m.subject.subject.clone(),
                        field: Some(f.name.clone()),
                        atom: Some(atom.clone()),
                    });
                }
            }
            facts
        }
        (_, Witness::Compose(_) | Witness::PathCompose(_) | Witness::Compare(_)) => unreachable!(),
    };
    support.sort_by_key(|f| f.wire().canonical());
    support.dedup();
    let mut scope = Scope::default();
    if let Witness::Map(m) = &value.witness {
        scope.completions = match value.data {
            ConstructionData::Counterexample { index, .. } => {
                m.result.counterexample_uses_completions(index) == Some(true)
            }
            ConstructionData::Preservation { .. }
            | ConstructionData::PendingPreservation { .. } => (0..m.result.counterexamples().len())
                .any(|index| m.result.counterexample_uses_completions(index) == Some(true)),
            _ => false,
        };
    }
    if !matches!(
        value.data,
        ConstructionData::Subject { .. }
            | ConstructionData::Atom(_)
            | ConstructionData::AtomUniverse(_)
    ) {
        match &value.witness {
            Witness::Architecture(a) => {
                scope.readings.insert(a.construction.reading().into());
            }
            Witness::Map(m) => {
                scope.readings.insert(m.result.reading().into());
                scope.readings.insert(m.result.to_reading().into());
            }
            Witness::Compose(_) | Witness::PathCompose(_) | Witness::Compare(_) => unreachable!(),
        }
    }
    for fact in &support {
        scope.snapshots.insert(fact.snapshot.clone());
        let subject = find_subject(inputs, fact)?;
        let origin = if let Some(field) = &fact.field {
            subject
                .fields
                .iter()
                .find(|f| &f.name == field)
                .and_then(|f| match &f.slot {
                    crate::archmap::Slot::Known { origin, .. } => Some(origin),
                    _ => None,
                })
                .ok_or("native支持が既知fieldでない")?
        } else {
            &subject.origin
        };
        let origin = inputs
            .archmap()
            .origins
            .iter()
            .find(|o| &o.id == origin)
            .ok_or("native支持のoriginがない")?;
        scope.modes.insert(origin.mode.wire().into());
    }
    Ok((support, scope))
}
/// native計算を終えた不変値だけを転記する。凍結後にも新しい計算は行わない。
pub(super) fn architecture_origin(
    graph: &Graph,
    reference: NodeRef,
    object: usize,
) -> Result<&Arc<ArchitectureWitness>, ValidationFailure> {
    let Some(Payload::Construction(v)) = &graph.get(reference)?.payload else {
        return Err("有限Lawの元Architectureがない".into());
    };
    match (&v.witness, &v.data) {
        (Witness::Architecture(a), ConstructionData::Architecture { .. } | ConstructionData::Change(_)) if v.ty()==NodeType::Construction(ConstructionType::Architecture) => {
            let context = graph.context_at(reference.0);
            if context.frame.is_some()
                || context.iteration.is_some()
                || context.instance.is_some()
                || context.case.is_some()
                || graph.requests.get(context.request)
                    != Some(Witness::Architecture(a.clone()).request())
            {
                return Err("有限Law導出が元Architectureのroot Requestでない".into());
            }
            Ok(a)
        }
        (Witness::Architecture(a), ConstructionData::Quotient(d)) if v.ty()==NodeType::Construction(ConstructionType::Architecture) => {
            let context = graph.context_at(reference.0);
            if context.frame.is_some() || context.iteration.is_some() || context.instance.is_some() || context.case.is_some()
                || graph.requests.get(context.request) != Some(d.request()) {
                return Err("商の候補Architectureの元Requestが違う".into());
            }
            Ok(a)
        }
        (_, ConstructionData::ObjectComponents(_)) => {
            super::object_component_diagram::architecture_origin(graph, reference, object)
        }
        _ => Err("有限Lawの元参照が完成Architectureでない".into()),
    }
}
pub fn retain(
    graph: &mut Graph,
    value: ConstructionValue,
    reasons: Vec<Reason>,
    evidence: Vec<NodeRef>,
    judgment: Option<Judgment>,
) -> Result<NodeRef, ValidationFailure> {
    for reason in &reasons {
        if matches!(reason.kind, ReasonKind::Missing) && reason.dependencies.is_empty() {
            for fact in &reason.missing {
                let root = Fact {
                    snapshot: fact.snapshot.clone(),
                    subject: fact.subject.clone(),
                    field: None,
                    atom: None,
                };
                if missing_reference(graph, &value.witness, &root).is_none() {
                    retain(
                        graph,
                        subject_value(value.witness.clone(), &root)?,
                        vec![],
                        vec![],
                        None,
                    )?;
                }
            }
        }
    }
    let reasons = connected_reasons(graph, &value.witness, reasons)?;
    let judgment = judgment
        .map(|mut j| {
            j.reasons = connected_reasons(graph, &value.witness, j.reasons)?;
            Ok::<_, ValidationFailure>(j)
        })
        .transpose()?;
    let (support, scope) = metadata(&value)?;
    let node = Node {
        ty: value.ty(),
        rule: value.rule(),
        arguments: value.arguments(),
        payload: Some(Payload::Construction(Box::new(value))),
        support,
        scope,
        reasons,
        evidence,
        judgment,
    };
    validate_shape(graph, &node)?;
    graph.retain_native(node)
}
fn missing_reference(graph: &Graph, witness: &Witness, root: &Fact) -> Option<NodeRef> {
    graph
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, n)| match &n.payload {
            Some(Payload::Construction(v))
                if &v.witness == witness
                    && matches!(v.data, ConstructionData::Subject { .. })
                    && subject_fact(graph, NodeRef(i)).ok().as_ref() == Some(root) =>
            {
                Some(NodeRef(i))
            }
            _ => None,
        })
}
fn connected_reasons(
    graph: &Graph,
    witness: &Witness,
    reasons: Vec<Reason>,
) -> Result<Vec<Reason>, ValidationFailure> {
    let mut reasons = reasons;
    for reason in &mut reasons {
        if matches!(reason.kind, ReasonKind::Missing) && reason.dependencies.is_empty() {
            for fact in &reason.missing {
                let root = Fact {
                    snapshot: fact.snapshot.clone(),
                    subject: fact.subject.clone(),
                    field: None,
                    atom: None,
                };
                reason.dependencies.push(
                    missing_reference(graph, witness, &root)
                        .ok_or("native欠測の元subject参照がない")?,
                );
            }
            reason.dependencies.sort_by_key(|r| r.0);
            reason.dependencies.dedup();
        }
    }
    super::result::sort_reasons(&mut reasons);
    Ok(reasons)
}
/// wireのlabelではなく、同じ入力から得たnative結果と既出参照の実体を照合する。
fn part<'a>(
    parts: &'a [(Vec<ProjectionStep>, NodeRef)],
    name: &str,
    index: Option<usize>,
) -> Result<NodeRef, ValidationFailure> {
    let mut path = vec![ProjectionStep::Field(name.into())];
    if let Some(index) = index {
        path.push(ProjectionStep::Index(index as u64));
    }
    let mut found = parts.iter().filter(|(p, _)| p == &path);
    let r = found.next().ok_or("部分結果の既知field/pathを落とした")?.1;
    if found.next().is_some() {
        return Err("部分結果のpathが重複した".into());
    }
    Ok(r)
}
fn atom_fact(graph: &Graph, r: NodeRef) -> Result<Fact, ValidationFailure> {
    match &value(graph, r)?.data {
        ConstructionData::Atom(a) => Ok(a.fact.clone()),
        ConstructionData::Subject { .. } => subject_fact(graph, r),
        _ => Err("部分configurationの元Atomがない".into()),
    }
}
fn architecture_reasons(a: &ArchitectureWitness) -> Vec<Reason> {
    let mut reasons = missing(&a.request, a.construction.base().blocking_slots().to_vec());
    for row in a
        .readings
        .instances()
        .iter()
        .filter(|r| r.declaration().kind == "law")
    {
        reasons.extend(missing(&a.request, instance_missing(row)));
    }
    super::result::sort_reasons(&mut reasons);
    reasons
}
fn validate_partial(
    graph: &Graph,
    v: &ConstructionValue,
    ty: ConstructionType,
    parts: &[(Vec<ProjectionStep>, NodeRef)],
) -> Result<Vec<Reason>, ValidationFailure> {
    use ConstructionData as D;
    let mut expected_count = 0;
    let reasons = match (&v.witness, ty) {
        (Witness::Architecture(a), ConstructionType::Configuration) => {
            if a.construction.base().configuration().is_some() {
                return Err("完成configurationを欠測扱いした".into());
            }
            let known = a.construction.base().known();
            for (i, fact) in known.family().iter().enumerate() {
                if atom_fact(graph, part(parts, "family", Some(i))?)? != *fact {
                    return Err("部分familyの元位置が違う".into());
                }
                expected_count += 1;
            }
            for (name, pairs) in [
                ("relations", known.relations()),
                ("identifications", known.identifications()),
            ] {
                for (i, (left, right)) in pairs.iter().enumerate() {
                    for (j, fact) in [left, right].into_iter().enumerate() {
                        let path = vec![
                            ProjectionStep::Field(name.into()),
                            ProjectionStep::Index(i as u64),
                            ProjectionStep::Index(j as u64),
                        ];
                        let rs = parts.iter().filter(|(p, _)| p == &path).collect::<Vec<_>>();
                        if rs.len() != 1 || atom_fact(graph, rs[0].1)? != *fact {
                            return Err("部分R/Eの元位置が違う".into());
                        }
                        expected_count += 1;
                    }
                }
            }
            missing(&a.request, a.construction.base().blocking_slots().to_vec())
        }
        (Witness::Architecture(a), ConstructionType::Architecture) => {
            let reasons = architecture_reasons(a);
            if reasons.is_empty() {
                return Err("完成Architectureを未決にした".into());
            }
            if subject_fact(graph, part(parts, "root", None)?)? != *a.construction.root() {
                return Err("部分Architectureの根が違う".into());
            }
            let c = value(graph, part(parts, "configuration", None)?)?;
            if c.witness != v.witness
                || !matches!(
                    c.data,
                    D::Configuration(_)
                        | D::Pending {
                            ty: ConstructionType::Configuration,
                            ..
                        }
                )
            {
                return Err("部分Architectureの元configurationが違う".into());
            }
            expected_count = 2;
            for (i, (instance, _)) in a
                .readings
                .instances()
                .iter()
                .enumerate()
                .filter(|(_, r)| r.declaration().kind == "law")
                .enumerate()
            {
                let law = value(graph, part(parts, "laws", Some(i))?)?;
                if law.witness != v.witness
                    || !matches!(law.data,D::LawInstance {instance:n,..}|D::PendingLawInstance {instance:n,..} if n==instance)
                {
                    return Err("部分ArchitectureのLaw族が違う".into());
                }
                expected_count += 1;
            }
            for (i, arrow) in a.arrows.iter().enumerate() {
                if subject_fact(graph, part(parts, "internal_arrows", Some(i))?)? != *arrow {
                    return Err("部分Architectureの内部arrowが違う".into());
                }
                expected_count += 1;
            }
            reasons
        }
        (Witness::Map(m), ConstructionType::MapCandidate) => {
            if subject_fact(graph, part(parts, "subject", None)?)? != m.subject {
                return Err("部分候補の元correspondenceが違う".into());
            }
            expected_count = 1;
            let holder = find_subject(&m.inputs, &m.subject)?;
            let mut reasons = m.reasons();
            let mut architectures_complete = true;
            for (name, reading, expected) in [
                ("source", m.result.reading(), m.result.source()),
                ("target", m.result.to_reading(), m.result.target()),
            ] {
                let endpoint = if name == "source" { "from" } else { "to" };
                if let Some(crate::archmap::Field {
                    slot:
                        crate::archmap::Slot::Known {
                            value: crate::archmap::Value::Ref { snapshot, subject },
                            ..
                        },
                    ..
                }) = holder
                    .fields
                    .iter()
                    .find(|f| f.name.rsplit('.').next() == Some(endpoint))
                {
                    let r = part(parts, name, None)?;
                    let av = value(graph, r)?;
                    let Witness::Architecture(a) = &av.witness else {
                        return Err("部分候補の始終域がArchitectureでない".into());
                    };
                    if a.construction.root().snapshot != *snapshot
                        || a.construction.root().subject != *subject
                        || a.construction.reading() != reading
                        || expected.is_some_and(|e| e != &a.construction)
                        || !matches!(
                            av.data,
                            D::Architecture { .. }
                                | D::Pending {
                                    ty: ConstructionType::Architecture,
                                    ..
                                }
                        )
                    {
                        return Err("部分候補の始終域・readingが違う".into());
                    }
                    architectures_complete &= !av.is_blocked();
                    reasons.extend(graph.get(r)?.reasons.iter().cloned());
                    expected_count += 1;
                } else {
                    architectures_complete = false;
                }
            }
            if let Some(candidate) = m.result.candidate() {
                let action = value(graph, part(parts, "action", None)?)?;
                if action.witness != v.witness
                    || !matches!(&action.data,D::AtomMap {images,..} if images==candidate.images())
                {
                    return Err("部分候補の既知作用が違う".into());
                }
                expected_count += 1;
                if architectures_complete {
                    return Err("完成候補を未決にした".into());
                }
            }
            if m.failed_candidate() {
                let mut condition = None;
                for (index, node) in graph.nodes.iter().enumerate() {
                    if matches!(&node.payload, Some(Payload::Construction(c)) if c.witness == v.witness && matches!(c.data, D::CandidateCondition { .. }))
                    {
                        if condition.replace(NodeRef(index)).is_some() {
                            return Err("候補構成条件が重複した".into());
                        }
                    }
                }
                let condition = condition.ok_or("元候補の構成条件反証がない")?;
                reasons.push(Reason {
                    kind: ReasonKind::ConditionFailed {
                        condition,
                        construction: "map_candidate",
                    },
                    request: m.request.id.clone(),
                    dependencies: vec![condition],
                    missing: vec![],
                    location: None,
                });
            }
            super::result::sort_reasons(&mut reasons);
            reasons
        }
        _ => return Err("部分構成の元検査・型が違う".into()),
    };
    if parts.len() != expected_count || reasons.is_empty() {
        return Err("部分構成の既知field数・元理由が違う".into());
    }
    connected_reasons(graph, &v.witness, reasons)
}
pub(crate) fn validate_shape(graph: &Graph, node: &Node) -> Result<(), ValidationFailure> {
    let Some(Payload::Construction(v)) = &node.payload else {
        return Err("native構成のpayloadがない".into());
    };
    if let ConstructionData::LawFamily(data) = &v.data {
        return super::law_family::validate_node(graph, node, v, data);
    }
    if let ConstructionData::LawInstantiation(data) = &v.data {
        return super::law_instantiation::validate_node(graph, node, v, data);
    }
    if let ConstructionData::OutsideLaw(data) = &v.data {
        return super::law_inapplicable::validate_node(graph, node, v, data);
    }
    if let ConstructionData::ObjectReadingFrame(data) = &v.data {
        return super::object_reading_evaluation::validate_node(graph, node, v, data);
    }
    if let ConstructionData::ViewFamily(data) = &v.data {
        return super::view_family::validate_node(graph, node, v, data);
    }
    if let ConstructionData::ViewInvariant(data) = &v.data {
        return super::view_invariant::validate_node(graph, node, v, data);
    }
    if let ConstructionData::PredicateInvariant(data) = &v.data {
        return super::predicate_invariant::validate_node(graph, node, v, data);
    }
    if let ConstructionData::LawFrame(data) = &v.data {
        return super::law_evaluation::validate_node(graph, node, v, data);
    }
    if let ConstructionData::FiniteLaw(data) = &v.data {
        return super::finite_law_diagram::validate_node(graph, node, data);
    }
    if let ConstructionData::PolynomialLaw(data) = &v.data {
        return super::polynomial_law_diagram::validate_node(graph, node, data);
    }
    if let ConstructionData::ObjectComponents(data) = &v.data {
        return super::object_component_diagram::validate_node(graph, node, data);
    }
    if let ConstructionData::InternalArrows(data) = &v.data {
        return super::internal_arrow_diagram::validate_node(graph, node, data);
    }
    if let ConstructionData::EquationFamily(data) = &v.data {
        return super::equation_family::validate_node(graph, node, data);
    }
    if let ConstructionData::CircuitPattern(data) = &v.data {
        return super::circuit_pattern::validate_node(graph, node, data);
    }
    if let ConstructionData::Change(data) = &v.data { return super::change_result::validate_node(graph, node, v, data); }
    if let ConstructionData::Quotient(data) = &v.data { return super::quotient_result::validate_node(graph, node, v, data); }
    if let ConstructionData::Local(data) = &v.data { return super::local_result::validate_node(graph, node, v, data); }
    if let ConstructionData::ObjectMap(data) = &v.data { return super::object_map_result::validate_node(graph, node, v, data); }
    if let ConstructionData::Build(data) = &v.data {
        return super::build_result::validate_node(graph, node, v, data);
    }
    if let Witness::Compose(c) = &v.witness {
        return super::public_compose::validate_node(graph, node, c);
    }
    if let Witness::PathCompose(c) = &v.witness {
        return super::public_path_compose::validate_node(graph, node, c);
    }
    if let Witness::Compare(c) = &v.witness {
        return super::public_compare::validate_node(graph, node, c);
    }
    if node.ty != v.ty() || node.rule != v.rule() || node.arguments != v.arguments() {
        return Err("native構成の型・規則・既出引数が違う".into());
    }
    let (support, scope) = metadata(v)?;
    if node.support != support || node.scope != scope {
        return Err("native構成の原始支持・Scopeが元入力と違う".into());
    }
    for r in node
        .arguments
        .iter()
        .chain(&node.evidence)
        .chain(v.conditions().iter())
    {
        graph.get(*r)?;
    }
    for condition in v.conditions() {
        let p = graph.get(condition)?;
        let expected_candidate = match v.data {
            D::ConfigurationMap { candidate, .. } | D::Operation { candidate, .. } => candidate,
            _ => return Err("構成条件が写像・操作以外に付いた".into()),
        };
        if p.ty != NodeType::Proposition
            || !matches!(&p.payload, Some(Payload::Construction(c)) if c.witness==v.witness && matches!(c.data,D::Preservation { candidate } if candidate==expected_candidate))
            || !p
                .judgment
                .as_ref()
                .is_some_and(|j| j.status == Decision::Established && j.reasons.is_empty())
        {
            return Err("写像・操作の保存条件が元候補の成立命題でない".into());
        }
    }
    macro_rules! require {
        ($condition:expr,$message:literal) => {
            if !$condition {
                return Err($message.into());
            }
        };
    }
    use ConstructionData as D;
    if node.ty != NodeType::Proposition && (node.judgment.is_some() || !node.evidence.is_empty()) {
        return Err("命題以外のnative構成に判断・証拠がある".into());
    }
    if !v.is_blocked() && !node.reasons.is_empty() {
        return Err("完成native構成へ別の未決理由を付けた".into());
    }
    match (&v.data, &v.witness) {
        (D::ConstructionLabel(label), Witness::Map(m)) => require!(
            m.failed_candidate() && label == &Scalar::Text("map_candidate".into()),
            "候補構成の名前・元反証が違う"
        ),
        (
            D::CandidateCondition {
                name,
                subject,
                source,
                target,
            },
            Witness::Map(m),
        ) => {
            require!(m.failed_candidate(), "未確認候補を構成不成立にした");
            let label = value(graph, *name)?;
            require!(
                label.witness == v.witness
                    && matches!(&label.data, D::ConstructionLabel(Scalar::Text(n)) if n == "map_candidate"),
                "候補構成の元名前が違う"
            );
            require!(
                subject_fact(graph, *subject)? == m.subject,
                "構成不成立の元対応が違う"
            );
            for (r, expected) in [(*source, m.result.source()), (*target, m.result.target())] {
                let a = value(graph, r)?;
                require!(
                    matches!(&a.witness,Witness::Architecture(a) if Some(&a.construction)==expected),
                    "構成不成立の元始終域が違う"
                );
            }
            require!(
                node.evidence.len() == m.result.counterexamples().len(),
                "候補構成条件の反例を落とした"
            );
            for (index, e) in node.evidence.iter().enumerate() {
                let e = value(graph, *e)?;
                require!(
                    e.witness == v.witness
                        && matches!(&e.data,D::Counterexample { index:i,.. } if *i==index),
                    "候補構成条件の元反例が違う"
                );
            }
            require!(
                node.judgment
                    == Some(Judgment {
                        status: Decision::Refuted,
                        evidence: node.evidence.clone(),
                        reasons: vec![]
                    }),
                "候補構成条件の反証判断が違う"
            );
        }
        (D::Atom(a), _) => require!(
            a.inputs.sources() == v.witness.inputs().sources(),
            "別入力のAtomを転記した"
        ),
        (D::Subject { value, location }, _) => {
            let Scalar::Subject {
                snapshot,
                subject,
                entity,
            } = value
            else {
                return Err("原始参照が別の値".into());
            };
            let original = find_subject(
                v.witness.inputs(),
                &Fact {
                    snapshot: snapshot.clone(),
                    subject: subject.clone(),
                    field: None,
                    atom: None,
                },
            )?;
            require!(
                *entity == original.ty
                    && *location
                        == Location::ArchMap {
                            pointer: original.pointer.clone(),
                            span: None
                        },
                "元subjectの型・出現が違う"
            );
        }
        (D::Pending { ty, parts }, _) => {
            require!(
                node.reasons == validate_partial(graph, v, *ty, parts)?,
                "部分構成の元理由が違う"
            );
            require!(!node.reasons.is_empty(), "未完成構成に元理由がない");
            require!(
                matches!(
                    ty,
                    ConstructionType::Configuration
                        | ConstructionType::Architecture
                        | ConstructionType::MapCandidate
                ),
                "未対応の未完成型を追加した"
            );
            let mut paths = std::collections::BTreeSet::new();
            for (path, r) in parts {
                require!(
                    !path.is_empty()
                        && paths.insert(
                            path.iter()
                                .map(ProjectionStep::wire)
                                .map(|j| j.canonical())
                                .collect::<Vec<_>>()
                        ),
                    "部分構成のpathが空または重複"
                );
                require!(
                    matches!(&graph.get(*r)?.payload,Some(Payload::Construction(c)) if c.witness.request()==v.witness.request() && c.witness.inputs().sources()==v.witness.inputs().sources())
                        || matches!((&v.witness, ty, path.as_slice()), (Witness::Map(m), ConstructionType::MapCandidate, [ProjectionStep::Field(field)]) if field=="subject" && subject_fact(graph,*r).is_ok_and(|f| f==m.subject))
                        || matches!((&v.witness, ty, path.as_slice()), (Witness::Architecture(a), ConstructionType::Architecture, [ProjectionStep::Field(field)])
                            if field=="root" && a.request.kind==super::request::QuestionKind::Build
                                && a.request.arguments.iter().any(|arg| arg.name=="on" && matches!(arg.value,super::request::Selector::Answer { .. }))
                                && subject_fact(graph,*r).is_ok_and(|f| &f==a.construction.root())),
                    "部分構成が別入力・要求を参照した"
                );
            }
            match (&v.witness, ty) {
                (Witness::Architecture(a), ConstructionType::Configuration) => require!(
                    a.construction.base().configuration().is_none(),
                    "完成configurationを欠測扱いした"
                ),
                (Witness::Architecture(_), ConstructionType::Architecture)
                | (Witness::Map(_), ConstructionType::MapCandidate) => {}
                _ => return Err("部分構成の由来・型が違う".into()),
            }
        }
        (D::PendingPreservation { parts }, Witness::Map(m)) => {
            require!(
                !node.reasons.is_empty() && parts.len() == 1,
                "未完成保存命題に元理由・候補がない"
            );
            let candidate = value(graph, parts[0].1)?;
            require!(
                parts[0].0 == vec![ProjectionStep::Field("candidate".into())]
                    && node.reasons == graph.get(parts[0].1)?.reasons,
                "未完成保存命題のpath・元理由が違う"
            );
            require!(
                candidate.witness == v.witness
                    && matches!(
                        candidate.data,
                        D::Pending {
                            ty: ConstructionType::MapCandidate,
                            ..
                        }
                    ),
                "未完成保存命題の元候補が違う"
            );
            require!(
                node.evidence.len() == m.result.counterexamples().len(),
                "未完成候補の独立反例を落とした"
            );
            let j = node.judgment.as_ref().ok_or("未完成保存命題の判断がない")?;
            require!(
                j.status == Decision::Undetermined
                    && j.evidence == node.evidence
                    && j.reasons == node.reasons,
                "未完成保存命題を確定させた"
            );
            for (index, &e) in node.evidence.iter().enumerate() {
                let e = value(graph, e)?;
                require!(
                    e.witness == v.witness
                        && matches!(e.data,D::Counterexample {index:i,..} if i==index),
                    "未完成保存命題の独立反例が違う"
                );
            }
        }
        (D::PendingLawInstance { instance, parts }, Witness::Architecture(a)) => {
            let row = a
                .readings
                .instances()
                .get(*instance)
                .ok_or("未完成Lawの元instanceがない")?;
            require!(
                row.declaration().kind == "law"
                    && !instance_missing(row).is_empty()
                    && !node.reasons.is_empty(),
                "条件のないLawを未完成にした"
            );
            require!(!parts.is_empty(), "未完成Lawが元式を落とした");
            require!(
                node.reasons
                    == connected_reasons(
                        graph,
                        &v.witness,
                        missing(&a.request, instance_missing(row))
                    )?,
                "未完成Lawの元の所属条件が違う"
            );
            let body = value(graph, part(parts, "body", None)?)?;
            require!(
                matches!(body.data,D::Source {instance:i,guard:false,..} if i==*instance),
                "未完成Lawの元bodyが違う"
            );
            let guard = row
                .declaration()
                .expressions
                .iter()
                .any(|e| e.kind == crate::law::model::ExpressionKind::Guard);
            if guard {
                let g = value(graph, part(parts, "guard", None)?)?;
                require!(
                    matches!(g.data,D::Source {instance:i,guard:true,..} if i==*instance),
                    "未完成Lawの元guardが違う"
                );
            }
            require!(
                parts.len() == 1 + usize::from(guard) + row.bindings().len(),
                "未完成Lawが参照束縛・元式を落とした"
            );
            for (i, binding) in row.bindings().iter().enumerate() {
                require!(
                    subject_fact(graph, part(parts, "bindings", Some(i))?)? == *binding.subject(),
                    "未完成Lawの参照束縛が違う"
                );
            }
            for (_, r) in parts {
                require!(
                    value(graph, *r)?.witness == v.witness,
                    "未完成Lawが別の構成を参照した"
                );
            }
        }
        (D::Configuration(c), Witness::Architecture(a)) => {
            require!(
                a.construction.base().configuration() == Some(c),
                "未完成または別のconfiguration"
            );
        }
        (
            D::Architecture {
                reading,
                root,
                configuration,
                laws,
                arrows,
            },
            Witness::Architecture(a),
        ) => {
            require!(
                reading == a.construction.reading()
                    && subject_fact(graph, *root)? == *a.construction.root(),
                "Architectureのreading/rootが違う"
            );
            let config = value(graph, *configuration)?;
            require!(
                config.witness == v.witness
                    && matches!(&config.data,D::Configuration(c) if a.construction.base().configuration()==Some(c)),
                "Architectureのconfigurationが違う"
            );
            let indices = a
                .readings
                .instances()
                .iter()
                .enumerate()
                .filter(|(_, r)| r.declaration().kind == "law")
                .map(|(i, _)| i)
                .collect::<Vec<_>>();
            require!(
                indices.len() == laws.len() && a.arrows.len() == arrows.len(),
                "ArchitectureがLaw/内部arrowを落とした"
            );
            for (&expected, &law) in indices.iter().zip(laws) {
                let row = value(graph, law)?;
                require!(
                    row.witness == v.witness
                        && matches!(row.data,D::LawInstance{instance,..} if instance==expected),
                    "ArchitectureのLaw instanceが違う"
                );
            }
            for (expected, &arrow) in a.arrows.iter().zip(arrows) {
                require!(
                    subject_fact(graph, arrow)? == *expected,
                    "Architectureの内部arrowが違う"
                );
            }
        }
        (D::AtomUniverse(atoms), Witness::Architecture(a)) => require!(
            atoms == a.construction.universe(),
            "共通AtomUniverseの全元が違う"
        ),
        (D::AtomUniverse(atoms), Witness::Map(m)) => {
            let source = m.result.source().ok_or("AtomUniverseの元構成がない")?;
            require!(atoms == source.universe(), "共通AtomUniverseの全元が違う");
        }
        (D::AtomMap { universe, images }, Witness::Map(m)) => {
            let c = m
                .result
                .candidate()
                .ok_or("未完成候補のAtomMapを生成した")?;
            require!(images == c.images(), "総作用の像が元候補と違う");
            require!(
                matches!(&value(graph,*universe)?.data,D::AtomUniverse(atoms) if atoms==c.universe()),
                "総作用の共通Uが違う"
            );
        }
        (
            D::MapCandidate {
                declaration,
                subject,
                source,
                target,
                action,
            },
            Witness::Map(m),
        ) => {
            let c = m
                .result
                .candidate()
                .ok_or("未完成の候補を完成MapCandidateへ昇格した")?;
            require!(
                declaration == &m.shape.declaration && subject_fact(graph, *subject)? == m.subject,
                "候補の元宣言・subjectが違う"
            );
            for (r, expected) in [(*source, m.result.source()), (*target, m.result.target())] {
                let Witness::Architecture(a) = &value(graph, r)?.witness else {
                    return Err("候補の始終域がArchitectureでない".into());
                };
                require!(
                    Some(&a.construction) == expected
                        && matches!(value(graph, r)?.data, D::Architecture { .. }),
                    "候補の始終Architectureが違う"
                );
            }
            require!(
                matches!(&value(graph,*action)?.data,D::AtomMap{images,..} if images==c.images()),
                "候補の作用が違う"
            );
        }
        (D::ConfigurationMap { candidate, .. }, Witness::Map(m)) => {
            require!(
                m.result.map().is_some(),
                "未決・反証候補をConfigurationMapへ昇格した"
            );
            let c = value(graph, *candidate)?;
            require!(
                c.witness == v.witness && matches!(c.data, D::MapCandidate { .. }),
                "保存済みmapの候補が違う"
            );
        }
        (
            D::Operation {
                source,
                target,
                candidate,
                configuration_map,
                action,
                subject,
                ..
            },
            Witness::Map(m),
        ) => {
            let op = m
                .operation
                .as_ref()
                .ok_or("未確認の候補をOperationへ昇格した")?;
            require!(
                op.word() == [m.subject.clone()] && Some(op.map()) == m.result.map(),
                "元Operationの作用・語が違う"
            );
            let c = value(graph, *candidate)?;
            require!(
                c.witness == v.witness
                    && matches!(c.data,D::MapCandidate{subject:s,source:a,target:b,action:f,..} if s==*subject&&a==*source&&b==*target&&f==*action),
                "Operationの始終域・候補・作用・語が違う"
            );
            let map = value(graph, *configuration_map)?;
            require!(
                map.witness == v.witness
                    && matches!(map.data,D::ConfigurationMap{candidate:c,..} if c==*candidate),
                "OperationのConfigurationMapが違う"
            );
        }
        (
            D::Source {
                instance,
                guard,
                location,
                bindings,
                parameters,
            },
            Witness::Architecture(a),
        ) => {
            let row = a
                .readings
                .instances()
                .get(*instance)
                .ok_or("元Law instanceがない")?;
            require!(
                row.declaration().kind == "law",
                "viewをLaw Sourceへ昇格した"
            );
            let kind = if *guard {
                crate::law::model::ExpressionKind::Guard
            } else {
                crate::law::model::ExpressionKind::Body
            };
            let expression = row
                .declaration()
                .expressions
                .iter()
                .find(|e| e.kind == kind)
                .ok_or("元のLaw式がない")?;
            require!(
                *location
                    == Location::Law {
                        span: expression.span
                    },
                "元のLaw式の出現が違う"
            );
            let expected = row
                .parameters()
                .iter()
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect::<Vec<_>>();
            require!(
                parameters == &expected && bindings.len() == row.bindings().len(),
                "Law式の残parameter・参照束縛が違う"
            );
            for (b, original) in bindings.iter().zip(row.bindings()) {
                require!(
                    b.name == original.parameter().name
                        && b.ty == original.parameter().ty.erase()
                        && subject_fact(graph, b.value)? == *original.subject(),
                    "Law式の参照束縛が違う"
                );
            }
        }
        (
            D::LawInstance {
                instance,
                name,
                role,
                occurrence,
                bindings,
                guard,
                body,
            },
            Witness::Architecture(a),
        ) => {
            let row = a
                .readings
                .instances()
                .get(*instance)
                .ok_or("元Law instanceがない")?;
            require!(
                name == &row.declaration().name
                    && Some(*role) == row.declaration().role
                    && *occurrence
                        == Location::Law {
                            span: row.declaration().span
                        },
                "元Lawの名前・role・出現が違う"
            );
            let b = value(graph, *body)?;
            require!(
                b.witness == v.witness
                    && matches!(&b.data,D::Source{instance:i,guard:false,bindings:bs,..} if i==instance && bs==bindings),
                "Law bodyの元instance/束縛が違う"
            );
            let has_guard = row
                .declaration()
                .expressions
                .iter()
                .any(|e| e.kind == crate::law::model::ExpressionKind::Guard);
            require!(
                guard.is_some() == has_guard,
                "Lawの明示guardが欠落または追加された"
            );
            if let Some(guard) = guard {
                let g = value(graph, *guard)?;
                require!(
                    g.witness == v.witness
                        && matches!(&g.data,D::Source{instance:i,guard:true,bindings:bs,..} if i==instance && bs==bindings),
                    "Law guardの元instance/束縛が違う"
                );
            }
        }
        (D::Preservation { candidate }, Witness::Map(m)) => {
            let c = value(graph, *candidate)?;
            require!(
                c.witness == v.witness && matches!(c.data, D::MapCandidate { .. }),
                "保存命題の元候補が違う"
            );
            let expected = if m.result.map().is_some() {
                Decision::Established
            } else if !m.result.counterexamples().is_empty() {
                Decision::Refuted
            } else {
                Decision::Undetermined
            };
            let j = node.judgment.as_ref().ok_or("保存命題の判断がない")?;
            require!(
                j.status == expected && j.evidence == node.evidence,
                "保存命題の真偽・証拠がnative検査と違う"
            );
            require!(
                j.reasons
                    == if expected == Decision::Undetermined {
                        connected_reasons(graph, &v.witness, m.reasons())?
                    } else {
                        vec![]
                    },
                "保存判断の元停止・欠測理由が違う"
            );
            require!(
                node.evidence.len() == m.result.counterexamples().len(),
                "保存命題が確認済み反例を落とした"
            );
            for (index, &e) in node.evidence.iter().enumerate() {
                let e = value(graph, e)?;
                require!(
                    e.witness == v.witness
                        && matches!(e.data,D::Counterexample{index:i,..} if i==index),
                    "保存命題の反例が違う"
                );
            }
        }
        (
            D::Counterexample {
                index,
                subject,
                left,
                right,
                facts,
            },
            Witness::Map(m),
        ) => {
            let c = m
                .result
                .counterexamples()
                .get(*index)
                .ok_or("元検査に存在しない反例")?;
            require!(facts == &counterexample_facts(c), "保存反例の元位置が違う");
            require!(
                subject_fact(graph, *subject)? == m.subject,
                "保存反例の元correspondenceが違う"
            );
            let source = m.result.source().ok_or("反例のsourceがない")?;
            let target = m.result.target().ok_or("反例のtargetがない")?;
            require!(
                subject_fact(graph, *left)? == *source.root()
                    && subject_fact(graph, *right)? == *target.root(),
                "保存反例の始終rootが違う"
            );
        }
        _ => return Err("native構成と検査済み由来が違う".into()),
    }
    Ok(())
}
