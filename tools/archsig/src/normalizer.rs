use std::collections::BTreeMap;

use crate::{
    ArchMapContextV2, ArchMapCoverV2, ArchMapDocumentV2, NORMALIZED_ARCHMAP_V2_SCHEMA,
    NormalizedArchMapSummaryV2, NormalizedArchMapV2, NormalizedAtomV2, NormalizedContextV2,
    NormalizedCoverV2,
};

const NORMALIZER_V2_ID: &str = "archmap-schema050-finite-poset-site@1";

pub fn normalize_archmap_v2(document: &ArchMapDocumentV2, input_path: &str) -> NormalizedArchMapV2 {
    let mut context_memberships: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for context in &document.contexts {
        for atom_id in &context.atoms {
            context_memberships
                .entry(atom_id.clone())
                .or_default()
                .push(prefixed_id("ctx", &context.id));
        }
    }
    for memberships in context_memberships.values_mut() {
        memberships.sort();
        memberships.dedup();
    }

    let mut atoms = document
        .atoms
        .iter()
        .map(|atom| {
            let mut refs = atom.refs.clone();
            refs.sort();
            refs.dedup();
            NormalizedAtomV2 {
                source_atom_id: atom.id.clone(),
                normalized_atom_id: prefixed_id("atom", &atom.id),
                atom_kind: atom.kind.clone(),
                subject: atom.subject.clone(),
                axis: atom.axis.clone(),
                predicate: atom.predicate.clone().unwrap_or_else(|| atom.kind.clone()),
                object: atom.object.clone(),
                source_refs: refs,
                context_memberships: context_memberships
                    .get(&atom.id)
                    .cloned()
                    .unwrap_or_default(),
                normalization_status: "normalized".to_string(),
            }
        })
        .collect::<Vec<_>>();
    atoms.sort_by(|left, right| left.normalized_atom_id.cmp(&right.normalized_atom_id));

    let mut contexts = document
        .contexts
        .iter()
        .map(normalize_context_v2)
        .collect::<Vec<_>>();
    contexts.sort_by(|left, right| left.normalized_context_id.cmp(&right.normalized_context_id));

    let mut covers = document
        .covers
        .iter()
        .map(normalize_cover_v2)
        .collect::<Vec<_>>();
    covers.sort_by(|left, right| left.normalized_cover_id.cmp(&right.normalized_cover_id));

    NormalizedArchMapV2 {
        schema: NORMALIZED_ARCHMAP_V2_SCHEMA.to_string(),
        normalizer_id: NORMALIZER_V2_ID.to_string(),
        source_archmap_ref: input_path.to_string(),
        source_archmap_id: document.id.clone(),
        extraction_doctrine_ref: document.extraction_doctrine_ref.clone(),
        summary: NormalizedArchMapSummaryV2 {
            atom_count: atoms.len(),
            normalized_atom_count: atoms
                .iter()
                .filter(|atom| atom.normalization_status == "normalized")
                .count(),
            context_count: contexts.len(),
            cover_count: covers.len(),
            doctrine_fingerprint: document.extraction_doctrine_ref.fingerprint.clone(),
        },
        atoms,
        contexts,
        covers,
        non_conclusions: vec![
            "Normalized ArchMap v2 is a deterministic finite-poset-site presentation, not proof of source extraction soundness.".to_string(),
            "Contexts and covers are observation structure; measurement choices live in MeasurementProfile.".to_string(),
        ],
    }
}

fn normalize_context_v2(context: &ArchMapContextV2) -> NormalizedContextV2 {
    let mut atom_ids = context
        .atoms
        .iter()
        .map(|atom| prefixed_id("atom", atom))
        .collect::<Vec<_>>();
    atom_ids.sort();
    atom_ids.dedup();
    let mut restricts_to = context
        .restricts_to
        .iter()
        .map(|context| prefixed_id("ctx", context))
        .collect::<Vec<_>>();
    restricts_to.sort();
    restricts_to.dedup();
    let mut source_refs = context.refs.clone();
    source_refs.sort();
    source_refs.dedup();
    NormalizedContextV2 {
        source_context_id: context.id.clone(),
        normalized_context_id: prefixed_id("ctx", &context.id),
        atom_ids,
        restricts_to,
        source_refs,
        poset_status: "finiteObserved".to_string(),
    }
}

fn normalize_cover_v2(cover: &ArchMapCoverV2) -> NormalizedCoverV2 {
    let mut context_ids = cover
        .contexts
        .iter()
        .map(|context| prefixed_id("ctx", context))
        .collect::<Vec<_>>();
    context_ids.sort();
    context_ids.dedup();
    let mut source_refs = cover.refs.clone();
    source_refs.sort();
    source_refs.dedup();
    NormalizedCoverV2 {
        source_cover_id: cover.id.clone(),
        normalized_cover_id: prefixed_id("cover", &cover.id),
        context_ids,
        source_refs,
        coverage_status: "selectedCandidate".to_string(),
    }
}

fn prefixed_id(prefix: &str, id: &str) -> String {
    let expected = format!("{prefix}:");
    if id.starts_with(&expected) {
        id.to_string()
    } else {
        format!("{prefix}:{id}")
    }
}
