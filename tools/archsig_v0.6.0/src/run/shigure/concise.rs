//! `--detail concise` 時の SHIGURE stdout 要約分離（PRD AC3 / AC6 仕様に準拠）。

use archsig_common::canonical::{Json, JsonObject};

const MAX_CONCISE_EXAMPLES: usize = 3;

/// `ShigureOutcome::to_json()` から stdout 要約に必要な結論・反例・不足情報だけを抽出し、
/// 通過済み `applicability`、内部 `*_verified`、詳細証明配列、全 `provenance` を省略する。
pub(super) fn trim_shigure_outcome_concise(outcome_json: &Json) -> Json {
    let Json::Obj(fields) = outcome_json else {
        return outcome_json.clone();
    };
    let mut out = JsonObject::new();
    let mut omitted_fields: Vec<Json> = Vec::new();

    for (key, value) in fields {
        match key.as_str() {
            "residual_ideal" => {
                if let Json::Arr(items) = value
                    && !items.is_empty()
                {
                    omitted_fields.push(Json::str("residual_ideal"));
                    out.insert("residual_ideal_count".into(), Json::Nat(items.len() as u64));
                }
            }
            "provenance" => {
                omitted_fields.push(Json::str("provenance"));
                if let Json::Obj(prov) = value
                    && let Some(Json::Arr(origins)) = prov.get("origins")
                {
                    let origin_ids: Vec<Json> = origins
                        .iter()
                        .filter_map(|o| match o {
                            Json::Obj(m) => m.get("origin_id").cloned(),
                            _ => None,
                        })
                        .take(MAX_CONCISE_EXAMPLES)
                        .collect();
                    if !origin_ids.is_empty() {
                        out.insert("origin_ids".into(), Json::Arr(origin_ids));
                    }
                }
            }
            "applicability" => {
                if let Json::Arr(items) = value {
                    let failed: Vec<Json> = items
                        .iter()
                        .filter(|item| {
                            !matches!(
                                item,
                                Json::Obj(m) if m.get("satisfied") == Some(&Json::Bool(true))
                            )
                        })
                        .cloned()
                        .collect();
                    let passed_count = items.len().saturating_sub(failed.len());
                    if passed_count > 0 {
                        omitted_fields.push(Json::str("passed_applicability"));
                        out.insert(
                            "passed_applicability_count".into(),
                            Json::Nat(passed_count as u64),
                        );
                    }
                    if !failed.is_empty() {
                        out.insert("applicability".into(), Json::Arr(failed));
                    }
                }
            }
            "empty_witness" => {
                if let Json::Obj(w) = value {
                    let mut slim = JsonObject::new();
                    if let Some(gens) = w.get("generators")
                        && let Json::Arr(arr) = gens
                    {
                        slim.insert(
                            "generators".into(),
                            Json::Arr(arr.iter().take(MAX_CONCISE_EXAMPLES).cloned().collect()),
                        );
                        if arr.len() > MAX_CONCISE_EXAMPLES {
                            slim.insert("generators_total".into(), Json::Nat(arr.len() as u64));
                        }
                    }
                    omitted_fields.push(Json::str("empty_witness.cofactors"));
                    omitted_fields.push(Json::str("empty_witness.verified"));
                    out.insert("empty_witness".into(), Json::Obj(slim));
                }
            }
            _ => {
                out.insert(key.clone(), trim_nested(value, &mut omitted_fields));
            }
        }
    }

    if !omitted_fields.is_empty() {
        out.insert("omitted_fields".into(), Json::Arr(omitted_fields));
        out.insert(
            "detail_hint".into(),
            Json::str("pass `--detail full` or `--out DIR` for full proof evidence"),
        );
    }
    Json::Obj(out)
}

fn trim_nested(value: &Json, omitted_fields: &mut Vec<Json>) -> Json {
    const CAP_LIST_KEYS: &[&str] = &[
        "distinguishing_pairs",
        "rejected_candidates",
        "minimal_conflict_sets",
        "counterexamples",
        "minimal_origin_supports",
        "minimal_observation_sets",
    ];
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match value {
        Json::Arr(items) => Json::Arr(
            items
                .iter()
                .map(|i| trim_nested(i, omitted_fields))
                .collect(),
        ),
        Json::Obj(entries) => {
            let mut out = JsonObject::new();
            for (k, v) in entries {
                if k == "syzygy_generators" || k.ends_with("_verified") || k == "verified" {
                    record_omitted(omitted_fields, k);
                    if let Json::Arr(arr) = v {
                        out.insert(format!("{k}_total"), Json::Nat(arr.len() as u64));
                    }
                    continue;
                }
                if k == "reevaluation" {
                    record_omitted(omitted_fields, "reevaluation");
                    continue;
                }
                if CAP_LIST_KEYS.contains(&k.as_str())
                    && let Json::Arr(items) = v
                    && items.len() > MAX_CONCISE_EXAMPLES
                {
                    record_omitted(omitted_fields, k);
                    out.insert(format!("{k}_total"), Json::Nat(items.len() as u64));
                    out.insert(
                        k.clone(),
                        Json::Arr(
                            items
                                .iter()
                                .take(MAX_CONCISE_EXAMPLES)
                                .map(|i| trim_nested(i, omitted_fields))
                                .collect(),
                        ),
                    );
                    continue;
                }
                out.insert(k.clone(), trim_nested(v, omitted_fields));
            }
            Json::Obj(out)
        }
        other => other.clone(),
    })
}

fn record_omitted(omitted_fields: &mut Vec<Json>, key: &str) {
    let entry = Json::str(key);
    if !omitted_fields.contains(&entry) {
        omitted_fields.push(entry);
    }
}
