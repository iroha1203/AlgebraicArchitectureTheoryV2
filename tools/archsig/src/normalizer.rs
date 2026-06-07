use std::collections::{BTreeMap, BTreeSet};

use crate::{
    ArchMapAtomV1, ArchMapDocumentV1, ArchMapMoleculeV1, NORMALIZED_ARCHMAP_V1_SCHEMA,
    NormalizedArchMapSummaryV1, NormalizedArchMapV1, NormalizedAtomBindingV1,
    NormalizedAtomPredicateV1, NormalizedAtomV1, NormalizedMoleculeV1,
};

const NORMALIZER_ID: &str = "archmap-v1-aat-presentation@1";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArchMapAtomConstructorV1 {
    Component,
    Relation,
    Capability,
    DataState,
    Effect,
    Authority,
    Contract,
    Semantic,
    Runtime,
}

impl ArchMapAtomConstructorV1 {
    fn from_atom(atom: &ArchMapAtomV1) -> Option<Self> {
        match atom.kind.as_str() {
            "component" => Some(Self::Component),
            "relation" => Some(Self::Relation),
            "capability" => Some(Self::Capability),
            "dataState" => Some(Self::DataState),
            "effect" => Some(Self::Effect),
            "authority" => Some(Self::Authority),
            "contract" => Some(Self::Contract),
            "semantic" => Some(Self::Semantic),
            "runtime" => Some(Self::Runtime),
            _ => None,
        }
    }

    fn atom_kind(self) -> &'static str {
        match self {
            Self::Component => "existence",
            Self::Relation => "relation",
            Self::Capability => "capability",
            Self::DataState => "dataState",
            Self::Effect => "effect",
            Self::Authority => "boundaryAuthority",
            Self::Contract => "contractSpecification",
            Self::Semantic => "semanticInterpretation",
            Self::Runtime => "runtimeInteraction",
        }
    }

    fn axis(self) -> &'static str {
        match self {
            Self::Component | Self::Relation | Self::Capability => "static",
            Self::DataState => "dataflow",
            Self::Effect | Self::Semantic => "semantic",
            Self::Authority => "boundary",
            Self::Contract => "specification",
            Self::Runtime => "runtime",
        }
    }

    fn valence_template_id(self) -> &'static str {
        match self {
            Self::Component => "valence:existence@1",
            Self::Relation => "valence:relation@1",
            Self::Capability => "valence:capability@1",
            Self::DataState => "valence:dataState@1",
            Self::Effect => "valence:effect@1",
            Self::Authority => "valence:boundaryAuthority@1",
            Self::Contract => "valence:contractSpecification@1",
            Self::Semantic => "valence:semanticInterpretation@1",
            Self::Runtime => "valence:runtimeInteraction@1",
        }
    }
}

pub fn normalize_archmap_v1(document: &ArchMapDocumentV1, input_path: &str) -> NormalizedArchMapV1 {
    let molecule_memberships = molecule_memberships(document);
    let atoms = document
        .atoms
        .iter()
        .map(|atom| normalize_atom(atom, &molecule_memberships))
        .collect::<Vec<_>>();
    let atoms_by_id = atoms
        .iter()
        .map(|atom| (atom.source_atom_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let molecules = document
        .molecules
        .iter()
        .map(|molecule| normalize_molecule(molecule, &atoms_by_id))
        .collect::<Vec<_>>();
    let generated_molecule_candidate_count = molecules
        .iter()
        .filter(|molecule| molecule.generated_molecule_candidate_status == "generated")
        .count();
    let blocked_molecule_candidate_count = molecules
        .iter()
        .filter(|molecule| {
            molecule.generated_molecule_candidate_status == "blockedForNormalization"
        })
        .count();

    NormalizedArchMapV1 {
        schema: NORMALIZED_ARCHMAP_V1_SCHEMA.to_string(),
        normalizer_id: NORMALIZER_ID.to_string(),
        source_archmap_ref: input_path.to_string(),
        source_archmap_id: document.id.clone(),
        summary: NormalizedArchMapSummaryV1 {
            atom_count: atoms.len(),
            normalized_atom_count: atoms
                .iter()
                .filter(|atom| atom.normalization_status == "normalized")
                .count(),
            molecule_count: molecules.len(),
            generated_molecule_candidate_count,
            blocked_molecule_candidate_count,
        },
        atoms,
        molecules,
        non_conclusions: vec![
            "Normalized ArchMap is a deterministic tooling presentation, not a Lean proof object."
                .to_string(),
            "Generated molecule candidates are evaluator input; they are not obstruction, holonomy, risk, or lawfulness conclusions."
                .to_string(),
        ],
    }
}

fn molecule_memberships(document: &ArchMapDocumentV1) -> BTreeMap<String, Vec<String>> {
    let mut memberships: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for molecule in &document.molecules {
        for atom_id in &molecule.atoms {
            memberships
                .entry(atom_id.clone())
                .or_default()
                .push(molecule.id.clone());
        }
    }
    memberships
}

fn normalize_atom(
    atom: &ArchMapAtomV1,
    molecule_memberships: &BTreeMap<String, Vec<String>>,
) -> NormalizedAtomV1 {
    let constructor = ArchMapAtomConstructorV1::from_atom(atom);
    let predicate = normalized_predicate(atom);
    NormalizedAtomV1 {
        source_atom_id: atom.id.clone(),
        normalized_atom_id: format!("n:{}", atom.id),
        atom_kind: constructor
            .map(ArchMapAtomConstructorV1::atom_kind)
            .unwrap_or("unknown")
            .to_string(),
        axis: constructor
            .map(ArchMapAtomConstructorV1::axis)
            .unwrap_or("unknown")
            .to_string(),
        predicate,
        shape_coordinate_status: "resolved".to_string(),
        valence_template_id: constructor
            .map(ArchMapAtomConstructorV1::valence_template_id)
            .unwrap_or("valence:unknown")
            .to_string(),
        molecule_memberships: molecule_memberships
            .get(&atom.id)
            .cloned()
            .unwrap_or_default(),
        normalization_status: "normalized".to_string(),
        normalization_blocker_reason: None,
    }
}

fn normalized_predicate(atom: &ArchMapAtomV1) -> NormalizedAtomPredicateV1 {
    match atom.kind.as_str() {
        "component" => predicate(
            "component",
            vec![binding("component", atom.subject.as_deref())],
        ),
        "relation" => {
            if atom
                .edge
                .as_deref()
                .is_some_and(|edge| !edge.trim().is_empty())
            {
                predicate("relation", vec![binding("edge", atom.edge.as_deref())])
            } else {
                let edge = format!(
                    "edge:{}:{}:{}",
                    atom.subject.as_deref().unwrap_or_default(),
                    atom.predicate.as_deref().unwrap_or_default(),
                    atom.object.as_deref().unwrap_or_default()
                );
                predicate(
                    "relation",
                    vec![
                        NormalizedAtomBindingV1 {
                            role: "edge".to_string(),
                            value: edge,
                        },
                        binding("subject", atom.subject.as_deref()),
                        binding("predicate", atom.predicate.as_deref()),
                        binding("object", atom.object.as_deref()),
                    ],
                )
            }
        }
        "capability" => predicate(
            "capability",
            vec![
                binding("subject", atom.subject.as_deref()),
                binding("capability", atom.predicate.as_deref()),
            ],
        ),
        "dataState" => predicate(
            "dataState",
            vec![
                binding("diagram", atom.diagram.as_deref()),
                binding("state", atom.state.as_deref()),
            ],
        ),
        "effect" => predicate(
            "effect",
            vec![
                binding("diagram", atom.diagram.as_deref()),
                binding("effect", atom.effect.as_deref()),
            ],
        ),
        "authority" => predicate(
            "boundaryAuthority",
            vec![
                binding("subject", atom.subject.as_deref()),
                binding("authority", atom.authority.as_deref()),
            ],
        ),
        "contract" => predicate(
            "contractSpecification",
            vec![
                binding("diagram", atom.diagram.as_deref()),
                binding("contract", atom.contract.as_deref()),
            ],
        ),
        "semantic" => predicate(
            "semanticInterpretation",
            vec![
                binding("diagram", atom.diagram.as_deref()),
                binding("meaning", atom.meaning.as_deref()),
            ],
        ),
        "runtime" => predicate(
            "runtimeInteraction",
            vec![
                binding("edge", atom.edge.as_deref()),
                binding("interaction", atom.interaction.as_deref()),
            ],
        ),
        _ => predicate("invalid", vec![]),
    }
}

fn predicate(
    constructor: &str,
    bindings: Vec<NormalizedAtomBindingV1>,
) -> NormalizedAtomPredicateV1 {
    let normalized_name = format!(
        "{}({})",
        constructor,
        bindings
            .iter()
            .map(|binding| binding.value.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    );
    NormalizedAtomPredicateV1 {
        constructor: constructor.to_string(),
        normalized_name,
        bindings,
    }
}

fn binding(role: &str, value: Option<&str>) -> NormalizedAtomBindingV1 {
    NormalizedAtomBindingV1 {
        role: role.to_string(),
        value: value.unwrap_or_default().to_string(),
    }
}

fn normalize_molecule(
    molecule: &ArchMapMoleculeV1,
    atoms_by_id: &BTreeMap<&str, &NormalizedAtomV1>,
) -> NormalizedMoleculeV1 {
    let atom_ids = molecule
        .atoms
        .iter()
        .map(|atom_id| format!("n:{atom_id}"))
        .collect::<Vec<_>>();
    let axes = molecule
        .atoms
        .iter()
        .filter_map(|atom_id| {
            atoms_by_id
                .get(atom_id.as_str())
                .map(|atom| atom.axis.as_str())
        })
        .collect::<BTreeSet<_>>();

    let blocker = if molecule.atoms.len() < 2 {
        Some("generated molecule candidate requires at least two explicit member atoms".to_string())
    } else if axes.len() < 2 {
        Some(
            "generated molecule candidate requires member atoms spanning at least two normalized axes"
                .to_string(),
        )
    } else {
        None
    };
    let status = if blocker.is_some() {
        "blockedForNormalization"
    } else {
        "generated"
    };

    NormalizedMoleculeV1 {
        source_molecule_id: molecule.id.clone(),
        normalized_molecule_id: format!("n:{}", molecule.id),
        atom_ids,
        generated_molecule_candidate_status: status.to_string(),
        required_port_status: if molecule.atoms.is_empty() {
            "missingMemberAtoms"
        } else {
            "resolvedFromExplicitMembership"
        }
        .to_string(),
        composition_status: if blocker.is_some() {
            "blockedForNormalization"
        } else {
            "compatibleCandidate"
        }
        .to_string(),
        normalization_blocker_reason: blocker,
    }
}
