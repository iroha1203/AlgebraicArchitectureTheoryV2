use std::collections::{BTreeMap, BTreeSet};

use crate::DerivedSagaComplexV1;
use crate::schema::{
    DerivedSagaComplexDataV1, DerivedSagaOverlapV1, DerivedSagaTripleV1, MeasurementProfileV1,
    NormalizedArchMapV2,
};

/// ArchSig内部で、選択されたArchMap coverと観測済みの制限関係からSAGAの
/// 有限複体を導出する。外部のauthoring artifactや作者宣言は受け取らない。
pub(crate) fn derive_saga_complex_from_normalized(
    normalized: &NormalizedArchMapV2,
    profile: &MeasurementProfileV1,
) -> DerivedSagaComplexV1 {
    let charts = normalized
        .covers
        .iter()
        .find(|cover| {
            cover.normalized_cover_id == profile.cover_ref
                || cover.source_cover_id == profile.cover_ref
        })
        .map(|cover| cover.context_ids.clone())
        .unwrap_or_default();
    let chart_set = charts.iter().collect::<BTreeSet<_>>();
    let pairs = normalized
        .contexts
        .iter()
        .filter(|context| chart_set.contains(&context.normalized_context_id))
        .flat_map(|context| {
            context
                .restricts_to
                .iter()
                .filter(|target| chart_set.contains(*target))
                .map(|target| sorted_pair(&context.normalized_context_id, target))
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    let overlaps = pairs
        .iter()
        .map(|(left, right)| DerivedSagaOverlapV1 {
            id: derived_overlap_id(left, right),
            left: left.clone(),
            right: right.clone(),
            archmap_context_ref: None,
        })
        .collect::<Vec<_>>();
    let overlap_ids = pairs
        .iter()
        .map(|(left, right)| {
            (
                (left.clone(), right.clone()),
                derived_overlap_id(left, right),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let context_atoms = normalized
        .contexts
        .iter()
        .filter(|context| chart_set.contains(&context.normalized_context_id))
        .map(|context| {
            (
                context.normalized_context_id.clone(),
                context.atom_ids.iter().cloned().collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut triple_overlaps = Vec::new();
    for first in 0..charts.len() {
        for second in first + 1..charts.len() {
            for third in second + 1..charts.len() {
                let contexts = [&charts[first], &charts[second], &charts[third]];
                let mut shared = context_atoms.get(contexts[0]).cloned().unwrap_or_default();
                for context in &contexts[1..] {
                    let Some(atoms) = context_atoms.get(*context) else {
                        shared.clear();
                        break;
                    };
                    shared = shared.intersection(atoms).cloned().collect();
                }
                if shared.is_empty() {
                    continue;
                }
                let pairs_for_face = [
                    sorted_pair(contexts[0], contexts[1]),
                    sorted_pair(contexts[0], contexts[2]),
                    sorted_pair(contexts[1], contexts[2]),
                ];
                let Some(overlap_refs) = pairs_for_face
                    .iter()
                    .map(|pair| overlap_ids.get(pair).cloned())
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                triple_overlaps.push(DerivedSagaTripleV1 {
                    id: format!("triple:{}:{}:{}", contexts[0], contexts[1], contexts[2]),
                    overlap_refs,
                    archmap_context_ref: None,
                });
            }
        }
    }
    DerivedSagaComplexV1 {
        schema: "archsig-derived-saga-complex/v1".to_string(),
        id: format!("derived:saga-complex:{}", profile.profile_id),
        complex: DerivedSagaComplexDataV1 {
            charts,
            archmap_cover_ref: Some(profile.cover_ref.clone()),
            overlaps,
            triple_overlaps,
            enumeration_complete: true,
        },
    }
}

fn derived_overlap_id(left: &str, right: &str) -> String {
    format!("overlap:{left}:{right}")
}

fn sorted_pair(left: &str, right: &str) -> (String, String) {
    if left < right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}

pub(crate) fn saga_complex_has_valid_finite_incidence(complex: &DerivedSagaComplexDataV1) -> bool {
    let charts = complex.charts.iter().cloned().collect::<BTreeSet<_>>();
    let overlap_ids = complex
        .overlaps
        .iter()
        .map(|overlap| overlap.id.clone())
        .collect::<BTreeSet<_>>();
    let triple_ids = complex
        .triple_overlaps
        .iter()
        .map(|triple| triple.id.clone())
        .collect::<BTreeSet<_>>();
    charts.len() == complex.charts.len()
        && overlap_ids.len() == complex.overlaps.len()
        && triple_ids.len() == complex.triple_overlaps.len()
        && complex
            .overlaps
            .iter()
            .all(|overlap| charts.contains(&overlap.left) && charts.contains(&overlap.right))
        && complex.triple_overlaps.iter().all(|triple| {
            if triple.overlap_refs.len() != 3
                || triple.overlap_refs.iter().collect::<BTreeSet<_>>().len() != 3
                || triple
                    .overlap_refs
                    .iter()
                    .any(|overlap_ref| !overlap_ids.contains(overlap_ref))
            {
                return false;
            }
            let triple_overlaps = triple
                .overlap_refs
                .iter()
                .filter_map(|overlap_ref| {
                    complex
                        .overlaps
                        .iter()
                        .find(|overlap| &overlap.id == overlap_ref)
                })
                .collect::<Vec<_>>();
            let vertices = triple_overlaps
                .iter()
                .flat_map(|overlap| [&overlap.left, &overlap.right])
                .cloned()
                .collect::<BTreeSet<_>>();
            if vertices.len() != 3 {
                return false;
            }
            let edge_pairs = triple_overlaps
                .iter()
                .filter_map(|overlap| {
                    if overlap.left == overlap.right {
                        None
                    } else if overlap.left < overlap.right {
                        Some((overlap.left.clone(), overlap.right.clone()))
                    } else {
                        Some((overlap.right.clone(), overlap.left.clone()))
                    }
                })
                .collect::<BTreeSet<_>>();
            let vertices = vertices.into_iter().collect::<Vec<_>>();
            let expected_pairs = [(0, 1), (0, 2), (1, 2)]
                .into_iter()
                .map(|(left, right)| (vertices[left].clone(), vertices[right].clone()))
                .collect::<BTreeSet<_>>();
            edge_pairs == expected_pairs
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finite_incidence_requires_all_three_triangle_edges() {
        let triangle = DerivedSagaComplexDataV1 {
            charts: vec!["A".to_string(), "B".to_string(), "C".to_string()],
            overlaps: [("e1", "A", "B"), ("e2", "B", "C"), ("e3", "A", "C")]
                .into_iter()
                .map(|(id, left, right)| DerivedSagaOverlapV1 {
                    id: id.to_string(),
                    left: left.to_string(),
                    right: right.to_string(),
                    archmap_context_ref: None,
                })
                .collect(),
            triple_overlaps: vec![DerivedSagaTripleV1 {
                id: "t".to_string(),
                overlap_refs: vec!["e1".to_string(), "e2".to_string(), "e3".to_string()],
                archmap_context_ref: None,
            }],
            archmap_cover_ref: None,
            enumeration_complete: true,
        };
        assert!(saga_complex_has_valid_finite_incidence(&triangle));
    }
}
