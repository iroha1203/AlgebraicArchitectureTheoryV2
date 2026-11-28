//! AAT 第17章（出現の同定・使用文脈同値・補助属性の最小値域）の検証済み IR
//! （`OccurrenceTaskSpec` / `CheckedOccurrenceTask`）。

use crate::algebra::congruence::{
    DEFAULT_MAX_CONGRUENCE_STEPS, OpOutputRecord, PredicateRecord, PredicateRecordKind,
};
use crate::algebra::partition::DEFAULT_MAX_SET_PARTITIONS;
use crate::ir::provenance::Provenance;
use crate::ir::validate::{ValidationError, require_non_empty, validate_provenance};
use std::collections::{BTreeMap, BTreeSet};

/// sort 仕様（固定値 sort かどうかを区別する）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceSortSpec {
    pub name: String,
    pub elements: Vec<String>,
    pub is_fixed_value: bool,
}

/// 操作・部分操作仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceOpSpec {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    pub is_total: bool,
}

/// 関係仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceRelSpec {
    pub name: String,
    pub arg_sorts: Vec<String>,
}

/// 基本使用文脈（読取り $c: D_c \to Z_c$、未定義は `None`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceReadingSpec {
    pub name: String,
    pub sort: String,
    pub values: BTreeMap<String, Option<String>>,
}

/// 初期読み出し $p_s: E_s \to W_s$（設定 17.9）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceInitialReadoutSpec {
    pub sort: String,
    pub values: BTreeMap<String, String>,
}

/// 出現同定タスク仕様。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrenceTaskSpec {
    pub name: String,
    pub sorts: Vec<OccurrenceSortSpec>,
    pub operations: Vec<OccurrenceOpSpec>,
    pub relations: Vec<OccurrenceRelSpec>,
    /// 同一視要求 `(sort, lhs, rhs)`。
    pub identity_requests: Vec<(String, String, String)>,
    pub op_records: Vec<OpOutputRecord>,
    pub pred_records: Vec<PredicateRecord>,
    pub base_readings: Vec<OccurrenceReadingSpec>,
    /// 設定 17.5 の文脈閉性を仮定するか（false の場合は一般有限列挙で健全同定全体・最粗商有無を判定）。
    pub context_closed_17_5: bool,
    /// 一般系で明示指定する追加文脈（定義域と値）。
    pub explicit_contexts: Vec<OccurrenceReadingSpec>,
    /// 商上で保ちたい全定義域/関係部分集合（一般系の定義 17.4 第 2 項用）。
    pub preserve_full_domains: Vec<String>,
    /// 初期読み出し（設定 17.9: 評価分離 vs 操作保存の最小補助属性値域）。
    pub initial_readouts: Vec<OccurrenceInitialReadoutSpec>,
    /// 出力に継承する由来参照。
    pub provenance: Provenance,
    pub max_congruence_steps: usize,
    pub max_partitions: usize,
    /// 未宣言の欠測 observed 参照が残る場合のスロット一覧。
    pub undeclared_unobserved_slots: Vec<String>,
}

/// 検証済みの出現同定タスク。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedOccurrenceTask {
    name: String,
    sorts: Vec<OccurrenceSortSpec>,
    operations: Vec<OccurrenceOpSpec>,
    relations: Vec<OccurrenceRelSpec>,
    identity_requests: Vec<(String, String, String)>,
    op_records: Vec<OpOutputRecord>,
    pred_records: Vec<PredicateRecord>,
    base_readings: Vec<OccurrenceReadingSpec>,
    context_closed_17_5: bool,
    explicit_contexts: Vec<OccurrenceReadingSpec>,
    preserve_full_domains: Vec<String>,
    initial_readouts: Vec<OccurrenceInitialReadoutSpec>,
    provenance: Provenance,
    max_congruence_steps: usize,
    max_partitions: usize,
    undeclared_unobserved_slots: Vec<String>,
}

impl CheckedOccurrenceTask {
    pub fn validate(spec: OccurrenceTaskSpec) -> Result<Self, ValidationError> {
        validate_occurrence_task(spec)
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn sorts(&self) -> &[OccurrenceSortSpec] {
        &self.sorts
    }

    pub fn operations(&self) -> &[OccurrenceOpSpec] {
        &self.operations
    }

    pub fn relations(&self) -> &[OccurrenceRelSpec] {
        &self.relations
    }

    pub fn identity_requests(&self) -> &[(String, String, String)] {
        &self.identity_requests
    }

    pub fn op_records(&self) -> &[OpOutputRecord] {
        &self.op_records
    }

    pub fn pred_records(&self) -> &[PredicateRecord] {
        &self.pred_records
    }

    pub fn base_readings(&self) -> &[OccurrenceReadingSpec] {
        &self.base_readings
    }

    pub fn context_closed_17_5(&self) -> bool {
        self.context_closed_17_5
    }

    pub fn explicit_contexts(&self) -> &[OccurrenceReadingSpec] {
        &self.explicit_contexts
    }

    pub fn preserve_full_domains(&self) -> &[String] {
        &self.preserve_full_domains
    }

    pub fn initial_readouts(&self) -> &[OccurrenceInitialReadoutSpec] {
        &self.initial_readouts
    }

    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }

    pub fn max_congruence_steps(&self) -> usize {
        self.max_congruence_steps
    }

    pub fn max_partitions(&self) -> usize {
        self.max_partitions
    }

    pub fn undeclared_unobserved_slots(&self) -> &[String] {
        &self.undeclared_unobserved_slots
    }
}

pub fn validate_occurrence_task(
    mut spec: OccurrenceTaskSpec,
) -> Result<CheckedOccurrenceTask, ValidationError> {
    require_non_empty(&spec.name, "occurrence.name")?;
    validate_provenance(&spec.provenance, &format!("occurrence `{}`", spec.name))?;
    if spec.max_congruence_steps == 0 {
        spec.max_congruence_steps = DEFAULT_MAX_CONGRUENCE_STEPS;
    }
    if spec.max_partitions == 0 {
        spec.max_partitions = DEFAULT_MAX_SET_PARTITIONS;
    }

    let mut sort_elems: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for s in &spec.sorts {
        require_non_empty(&s.name, "occurrence.sort.name")?;
        if sort_elems.contains_key(&s.name) {
            return Err(ValidationError::DuplicateDecl {
                kind: "occurrence_sort",
                name: s.name.clone(),
            });
        }
        let mut elems = BTreeSet::new();
        for e in &s.elements {
            require_non_empty(e, "occurrence.sort.element")?;
            if !elems.insert(e.clone()) {
                return Err(ValidationError::DuplicateDecl {
                    kind: "occurrence_element",
                    name: format!("{}.{e}", s.name),
                });
            }
        }
        sort_elems.insert(s.name.clone(), elems);
    }

    let mut ops_map: BTreeMap<String, &OccurrenceOpSpec> = BTreeMap::new();
    for op in &spec.operations {
        require_non_empty(&op.name, "occurrence.operation.name")?;
        if ops_map.contains_key(&op.name) {
            return Err(ValidationError::DuplicateDecl {
                kind: "occurrence_operation",
                name: op.name.clone(),
            });
        }
        for s in &op.arg_sorts {
            if !sort_elems.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("operation `{}`", op.name),
                });
            }
        }
        if !sort_elems.contains_key(&op.out_sort) {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: op.out_sort.clone(),
                context: format!("operation `{}`", op.name),
            });
        }
        ops_map.insert(op.name.clone(), op);
    }

    let mut rels_map: BTreeMap<String, &OccurrenceRelSpec> = BTreeMap::new();
    for rel in &spec.relations {
        require_non_empty(&rel.name, "occurrence.relation.name")?;
        if rels_map.contains_key(&rel.name) {
            return Err(ValidationError::DuplicateDecl {
                kind: "occurrence_relation",
                name: rel.name.clone(),
            });
        }
        for s in &rel.arg_sorts {
            if !sort_elems.contains_key(s) {
                return Err(ValidationError::UnknownRef {
                    kind: "sort",
                    name: s.clone(),
                    context: format!("relation `{}`", rel.name),
                });
            }
        }
        rels_map.insert(rel.name.clone(), rel);
    }

    for (s, l, r) in &spec.identity_requests {
        let Some(elems) = sort_elems.get(s) else {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: s.clone(),
                context: "occurrence.identity_request".to_owned(),
            });
        };
        if !elems.contains(l) {
            return Err(ValidationError::UnknownRef {
                kind: "occurrence",
                name: l.clone(),
                context: format!("identity_request in sort `{s}`"),
            });
        }
        if !elems.contains(r) {
            return Err(ValidationError::UnknownRef {
                kind: "occurrence",
                name: r.clone(),
                context: format!("identity_request in sort `{s}`"),
            });
        }
    }

    for rec in &spec.op_records {
        let Some(op) = ops_map.get(&rec.op_name) else {
            return Err(ValidationError::UnknownRef {
                kind: "operation",
                name: rec.op_name.clone(),
                context: "occurrence.op_record".to_owned(),
            });
        };
        if rec.arg_sorts != op.arg_sorts || rec.out_sort != op.out_sort {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "op_record for `{}` signature does not match operation declaration",
                    rec.op_name
                ),
            });
        }
        if rec.args.len() != op.arg_sorts.len() {
            return Err(ValidationError::ArityMismatch {
                context: format!("op_record `{}`", rec.op_name),
                expected: op.arg_sorts.len(),
                actual: rec.args.len(),
            });
        }
        for (s, a) in rec.arg_sorts.iter().zip(&rec.args) {
            if !sort_elems[s].contains(a) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: a.clone(),
                    context: format!("op_record `{}` arg", rec.op_name),
                });
            }
        }
        if !sort_elems[&rec.out_sort].contains(&rec.output) {
            return Err(ValidationError::UnknownRef {
                kind: "occurrence",
                name: rec.output.clone(),
                context: format!("op_record `{}` output", rec.op_name),
            });
        }
    }

    for rec in &spec.pred_records {
        let expected_sorts = match rec.kind {
            PredicateRecordKind::Domain => {
                let Some(op) = ops_map.get(&rec.name) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "operation",
                        name: rec.name.clone(),
                        context: "occurrence.domain_record".to_owned(),
                    });
                };
                &op.arg_sorts
            }
            PredicateRecordKind::Relation => {
                let Some(rel) = rels_map.get(&rec.name) else {
                    return Err(ValidationError::UnknownRef {
                        kind: "relation",
                        name: rec.name.clone(),
                        context: "occurrence.relation_record".to_owned(),
                    });
                };
                &rel.arg_sorts
            }
        };
        if rec.arg_sorts != *expected_sorts {
            return Err(ValidationError::ConversionError {
                detail: format!("predicate record for `{}` signature mismatch", rec.name),
            });
        }
        if rec.args.len() != expected_sorts.len() {
            return Err(ValidationError::ArityMismatch {
                context: format!("predicate_record `{}`", rec.name),
                expected: expected_sorts.len(),
                actual: rec.args.len(),
            });
        }
        for (s, a) in rec.arg_sorts.iter().zip(&rec.args) {
            if !sort_elems[s].contains(a) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: a.clone(),
                    context: format!("predicate_record `{}`", rec.name),
                });
            }
        }
    }

    let mut seen_base_readings = BTreeSet::new();
    for r in &spec.base_readings {
        require_non_empty(&r.name, "occurrence.reading.name")?;
        if !seen_base_readings.insert(r.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "occurrence_base_reading",
                name: r.name.clone(),
            });
        }
        let Some(elems) = sort_elems.get(&r.sort) else {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: r.sort.clone(),
                context: format!("reading `{}`", r.name),
            });
        };
        for k in r.values.keys() {
            if !elems.contains(k) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: k.clone(),
                    context: format!("reading `{}`", r.name),
                });
            }
        }
        if spec.context_closed_17_5 && r.values.len() != elems.len() {
            return Err(ValidationError::ConversionError {
                detail: format!(
                    "base_reading `{}` must cover all elements of sort `{}` under setting 17.5",
                    r.name, r.sort
                ),
            });
        }
    }

    let mut seen_explicit_contexts = BTreeSet::new();
    for r in &spec.explicit_contexts {
        require_non_empty(&r.name, "occurrence.explicit_context.name")?;
        if !seen_explicit_contexts.insert(r.name.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "occurrence_explicit_context",
                name: r.name.clone(),
            });
        }
        let Some(elems) = sort_elems.get(&r.sort) else {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: r.sort.clone(),
                context: format!("explicit_context `{}`", r.name),
            });
        };
        for k in r.values.keys() {
            if !elems.contains(k) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: k.clone(),
                    context: format!("explicit_context `{}`", r.name),
                });
            }
        }
    }

    for dom_name in &spec.preserve_full_domains {
        if !ops_map.contains_key(dom_name) && !rels_map.contains_key(dom_name) {
            return Err(ValidationError::UnknownRef {
                kind: "operation_or_relation",
                name: dom_name.clone(),
                context: "occurrence.preserve_full_domains".to_owned(),
            });
        }
    }

    let mut seen_readouts = BTreeSet::new();
    for ro in &spec.initial_readouts {
        let Some(elems) = sort_elems.get(&ro.sort) else {
            return Err(ValidationError::UnknownRef {
                kind: "sort",
                name: ro.sort.clone(),
                context: "occurrence.initial_readout".to_owned(),
            });
        };
        if !seen_readouts.insert(ro.sort.clone()) {
            return Err(ValidationError::DuplicateDecl {
                kind: "initial_readout",
                name: ro.sort.clone(),
            });
        }
        for e in elems {
            if !ro.values.contains_key(e) {
                return Err(ValidationError::ConversionError {
                    detail: format!(
                        "initial_readout for sort `{}` missing element `{e}`",
                        ro.sort
                    ),
                });
            }
        }
        for k in ro.values.keys() {
            if !elems.contains(k) {
                return Err(ValidationError::UnknownRef {
                    kind: "occurrence",
                    name: k.clone(),
                    context: format!("initial_readout `{}`", ro.sort),
                });
            }
        }
    }

    Ok(CheckedOccurrenceTask {
        name: spec.name,
        sorts: spec.sorts,
        operations: spec.operations,
        relations: spec.relations,
        identity_requests: spec.identity_requests,
        op_records: spec.op_records,
        pred_records: spec.pred_records,
        base_readings: spec.base_readings,
        context_closed_17_5: spec.context_closed_17_5,
        explicit_contexts: spec.explicit_contexts,
        preserve_full_domains: spec.preserve_full_domains,
        initial_readouts: spec.initial_readouts,
        provenance: spec.provenance,
        max_congruence_steps: spec.max_congruence_steps,
        max_partitions: spec.max_partitions,
        undeclared_unobserved_slots: spec.undeclared_unobserved_slots,
    })
}
