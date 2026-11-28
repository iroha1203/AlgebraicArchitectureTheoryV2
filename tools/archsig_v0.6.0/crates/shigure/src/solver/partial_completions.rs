//! AAT 第18章 有限表補完探索・包含極小不整合部分提示（MUS）抽出/検算・超評価比較ヘルパ。

use crate::ir::partial::{
    BackgroundConstraint, FinitePartialPresentation, PartialEvalLawSpec, PartialRecordKind,
    PartialRecordSpec, PartialTruth, PartialValue,
};
use crate::ir::provenance::MathClause;
use crate::ir::result::{ApplicabilityCheck, SilenceReason};
use crate::ir::result_phase5_obs::PartialLawEvalSummary;
use crate::solver::partial_kleene::{
    CompleteFiniteWorld, KleeneVal, build_partial_world_summary, eval_formula_complete,
    eval_law_kleene,
};
use std::collections::{BTreeMap, BTreeSet};

const MAX_MUS_RECORDS: usize = 14;

pub(super) struct CompletionEvalOutput {
    pub consistent: bool,
    pub completion_count: Option<usize>,
    pub minimal_inconsistent_subsets: Vec<Vec<String>>,
    pub mus_verified: bool,
    pub law_evaluations: Vec<PartialLawEvalSummary>,
    pub kleene_soundness_verified: bool,
}

#[derive(Clone, Debug)]
enum DecisionVar {
    Slot {
        name: String,
        domain: Vec<String>,
    },
    OpCell {
        op_name: String,
        args: Vec<String>,
        options: Vec<Option<String>>,
    },
    RelCell {
        rel_name: String,
        args: Vec<String>,
        options: Vec<bool>,
    },
}

pub(super) fn analyze_finite_partial(
    fin: &FinitePartialPresentation,
    eval_laws: &[PartialEvalLawSpec],
    checks: &mut Vec<ApplicabilityCheck>,
) -> Result<CompletionEvalOutput, SilenceReason> {
    // 例 18.2: 補完集合 Comp(T_S) の計算には評価対象 Law を一切混入しない。
    let completions = enumerate_completions_for_records(fin, &fin.records, true)?;
    if completions.is_empty() {
        let (mus, mus_verified) = extract_and_verify_finite_mus(fin)?;
        checks.push(ApplicabilityCheck::passed(
            "finite_partial_inconsistent_mus_extracted",
            MathClause::AatCh18Thm18Dot3,
        ));
        let partial_world = build_partial_world_summary(fin, &fin.records);
        let laws: Vec<PartialLawEvalSummary> = eval_laws
            .iter()
            .map(|l| PartialLawEvalSummary {
                law_name: l.name.clone(),
                strong_kleene: eval_law_kleene(l, fin, &partial_world).as_str().to_owned(),
                supervaluation: "vacuously_true".to_owned(),
                antecedent_regime: None,
                conditional_conclusion_eval: None,
                affine_normalized_eval: None,
            })
            .collect();
        return Ok(CompletionEvalOutput {
            consistent: false,
            completion_count: Some(0),
            minimal_inconsistent_subsets: mus,
            mus_verified,
            law_evaluations: laws,
            kleene_soundness_verified: true,
        });
    }

    checks.push(ApplicabilityCheck::passed(
        "finite_partial_completions_enumerated",
        MathClause::AatCh18Thm18Dot3,
    ));

    let partial_world = build_partial_world_summary(fin, &fin.records);
    let mut law_summaries = Vec::new();
    let mut all_sound = true;

    for law in eval_laws {
        let k_conc = eval_law_kleene(law, fin, &partial_world);
        let mut t_count = 0usize;
        let mut f_count = 0usize;
        let mut ante_true_conc_true = 0usize;
        let mut ante_true_conc_false = 0usize;
        let mut ante_true_total = 0usize;

        for comp in &completions {
            let env = BTreeMap::new();
            let ante_holds = match &law.antecedent {
                Some(ant) => eval_formula_complete(ant, &fin.sorts, comp, &env).unwrap_or(false),
                None => true,
            };
            let conc_holds =
                eval_formula_complete(&law.conclusion, &fin.sorts, comp, &env).unwrap_or(false);
            let imp_holds = !ante_holds || conc_holds;
            if imp_holds {
                t_count += 1;
            } else {
                f_count += 1;
            }
            if ante_holds {
                ante_true_total += 1;
                if conc_holds {
                    ante_true_conc_true += 1;
                } else {
                    ante_true_conc_false += 1;
                }
            }
        }

        let supervaluation = if f_count == 0 {
            "true"
        } else if t_count == 0 {
            "false"
        } else {
            "indeterminate"
        };

        let sound = match k_conc {
            KleeneVal::True => supervaluation == "true",
            KleeneVal::False => supervaluation == "false",
            KleeneVal::Unknown => true,
        };
        if !sound {
            all_sound = false;
        }

        let (antecedent_regime, conditional_conclusion_eval) = if law.antecedent.is_some() {
            let reg = if ante_true_total == 0 {
                "antecedent_never_holds"
            } else if ante_true_total == completions.len() {
                "antecedent_always_holds"
            } else {
                "antecedent_contingent"
            };
            let cond = if ante_true_total == 0 {
                "vacuous_on_antecedent"
            } else if ante_true_conc_false == 0 {
                "valid_on_antecedent_domain"
            } else if ante_true_conc_true == 0 {
                "refuted_on_antecedent_domain"
            } else {
                "indeterminate_on_antecedent_domain"
            };
            (Some(reg.to_owned()), Some(cond.to_owned()))
        } else {
            (None, None)
        };

        law_summaries.push(PartialLawEvalSummary {
            law_name: law.name.clone(),
            strong_kleene: k_conc.as_str().to_owned(),
            supervaluation: supervaluation.to_owned(),
            antecedent_regime,
            conditional_conclusion_eval,
            affine_normalized_eval: None,
        });
    }

    checks.push(ApplicabilityCheck::passed(
        "strong_kleene_supervaluation_checked",
        MathClause::AatCh18Thm18Dot6,
    ));

    Ok(CompletionEvalOutput {
        consistent: true,
        completion_count: Some(completions.len()),
        minimal_inconsistent_subsets: vec![],
        mus_verified: true,
        law_evaluations: law_summaries,
        kleene_soundness_verified: all_sound,
    })
}

fn enumerate_completions_for_records(
    fin: &FinitePartialPresentation,
    records: &[PartialRecordSpec],
    enforce_limit: bool,
) -> Result<Vec<CompleteFiniteWorld>, SilenceReason> {
    let vars = build_decision_vars(fin, records);
    let max_c = fin.max_completions.max(1);
    let mut results = Vec::new();
    let mut cur = CompleteFiniteWorld {
        slots: BTreeMap::new(),
        op_tables: fin
            .operations
            .iter()
            .map(|op| (op.name.clone(), BTreeMap::new()))
            .collect(),
        rel_tables: fin
            .relations
            .iter()
            .map(|r| (r.name.clone(), BTreeSet::new()))
            .collect(),
    };

    backtrack_completions(
        0,
        &vars,
        fin,
        records,
        enforce_limit,
        max_c,
        &mut cur,
        &mut results,
    )?;
    Ok(results)
}

fn build_decision_vars(
    fin: &FinitePartialPresentation,
    records: &[PartialRecordSpec],
) -> Vec<DecisionVar> {
    let mut pinned_slots: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for rec in records {
        if let PartialRecordKind::SlotAssignment { slot, value } = &rec.kind {
            pinned_slots
                .entry(slot.as_str())
                .or_default()
                .insert(value.as_str());
        }
    }

    let mut vars = Vec::new();
    for s in &fin.slots {
        let domain = if let Some(pinned) = pinned_slots.get(s.name.as_str()) {
            if pinned.len() == 1 {
                pinned.iter().map(|&v| v.to_owned()).collect()
            } else {
                vec![]
            }
        } else {
            s.domain_values.clone()
        };
        vars.push(DecisionVar::Slot {
            name: s.name.clone(),
            domain,
        });
    }

    for op in &fin.operations {
        let tuples = cartesian_args(&op.arg_sorts, &fin.sorts);
        let out_elems = &fin.sorts[&op.out_sort];
        for args in tuples {
            let mut options = Vec::new();
            let forced_val = records.iter().find_map(|r| match &r.kind {
                PartialRecordKind::OpValue {
                    op_name,
                    args: r_args,
                    value: PartialValue::Known(v),
                } if op_name == &op.name && r_args == &args => Some(Some(v.clone())),
                PartialRecordKind::OpValue {
                    op_name,
                    args: r_args,
                    value: PartialValue::ExplicitAbsent,
                } if op_name == &op.name && r_args == &args => Some(None),
                PartialRecordKind::OpDomain {
                    op_name,
                    args: r_args,
                    defined: PartialTruth::ExplicitAbsent,
                } if op_name == &op.name && r_args == &args => Some(None),
                PartialRecordKind::OpGraph {
                    op_name,
                    args: r_args,
                    output,
                    present: PartialTruth::True,
                } if op_name == &op.name && r_args == &args => Some(Some(output.clone())),
                _ => None,
            });
            if let Some(v) = forced_val {
                if !op.is_total || v.is_some() {
                    options.push(v);
                }
            } else {
                if !op.is_total {
                    options.push(None);
                }
                for e in out_elems {
                    options.push(Some(e.clone()));
                }
            }
            vars.push(DecisionVar::OpCell {
                op_name: op.name.clone(),
                args,
                options,
            });
        }
    }

    for rel in &fin.relations {
        for args in cartesian_args(&rel.arg_sorts, &fin.sorts) {
            let forced = records.iter().find_map(|r| match &r.kind {
                PartialRecordKind::Relation {
                    rel_name,
                    args: r_args,
                    holds: PartialTruth::True,
                } if rel_name == &rel.name && r_args == &args => Some(true),
                PartialRecordKind::Relation {
                    rel_name,
                    args: r_args,
                    holds: PartialTruth::ExplicitAbsent,
                } if rel_name == &rel.name && r_args == &args => Some(false),
                _ => None,
            });
            let options = match forced {
                Some(b) => vec![b],
                None => vec![false, true],
            };
            vars.push(DecisionVar::RelCell {
                rel_name: rel.name.clone(),
                args,
                options,
            });
        }
    }
    vars
}

#[allow(clippy::too_many_arguments)]
fn backtrack_completions(
    idx: usize,
    vars: &[DecisionVar],
    fin: &FinitePartialPresentation,
    records: &[PartialRecordSpec],
    enforce_limit: bool,
    max_c: usize,
    cur: &mut CompleteFiniteWorld,
    out: &mut Vec<CompleteFiniteWorld>,
) -> Result<(), SilenceReason> {
    if !world_consistent_so_far(fin, records, cur) {
        return Ok(());
    }
    if idx == vars.len() {
        if !full_world_constraints_hold(fin, records, cur) {
            return Ok(());
        }
        out.push(cur.clone());
        if enforce_limit && out.len() > max_c {
            return Err(SilenceReason::FiniteEnumerationOutOfScope {
                detail: format!("finite completions exceed max_completions ({max_c})"),
            });
        }
        return Ok(());
    }

    match &vars[idx] {
        DecisionVar::Slot { name, domain } => {
            for v in domain {
                cur.slots.insert(name.clone(), v.clone());
                backtrack_completions(idx + 1, vars, fin, records, enforce_limit, max_c, cur, out)?;
                cur.slots.remove(name);
                if !enforce_limit && !out.is_empty() {
                    return Ok(());
                }
            }
        }
        DecisionVar::OpCell {
            op_name,
            args,
            options,
        } => {
            for opt in options {
                cur.op_tables
                    .get_mut(op_name)
                    .expect("op table")
                    .insert(args.clone(), opt.clone());
                backtrack_completions(idx + 1, vars, fin, records, enforce_limit, max_c, cur, out)?;
                cur.op_tables
                    .get_mut(op_name)
                    .expect("op table")
                    .remove(args);
                if !enforce_limit && !out.is_empty() {
                    return Ok(());
                }
            }
        }
        DecisionVar::RelCell {
            rel_name,
            args,
            options,
        } => {
            for &b in options {
                if b {
                    cur.rel_tables
                        .get_mut(rel_name)
                        .expect("rel table")
                        .insert(args.clone());
                } else {
                    cur.rel_tables
                        .get_mut(rel_name)
                        .expect("rel table")
                        .remove(args);
                }
                backtrack_completions(idx + 1, vars, fin, records, enforce_limit, max_c, cur, out)?;
                cur.rel_tables
                    .get_mut(rel_name)
                    .expect("rel table")
                    .remove(args);
                if !enforce_limit && !out.is_empty() {
                    return Ok(());
                }
            }
        }
    }
    Ok(())
}

fn slot_truth(val: &str) -> Option<bool> {
    match val {
        "true" | "1" | "True" => Some(true),
        "false" | "0" | "False" => Some(false),
        _ => None,
    }
}

fn world_consistent_so_far(
    fin: &FinitePartialPresentation,
    records: &[PartialRecordSpec],
    cur: &CompleteFiniteWorld,
) -> bool {
    for bg in &fin.background_constraints {
        match bg {
            BackgroundConstraint::SlotEquality(a, b) => {
                if let (Some(va), Some(vb)) = (cur.slots.get(a), cur.slots.get(b))
                    && va != vb
                {
                    return false;
                }
            }
            BackgroundConstraint::SlotNotEqual(a, b) => {
                if let (Some(va), Some(vb)) = (cur.slots.get(a), cur.slots.get(b))
                    && va == vb
                {
                    return false;
                }
            }
            BackgroundConstraint::OperationInjective(_)
            | BackgroundConstraint::OperationSurjective(_) => {}
        }
    }

    for rec in records {
        match &rec.kind {
            PartialRecordKind::SlotAssignment { slot, value } => {
                if let Some(v) = cur.slots.get(slot)
                    && v != value
                {
                    return false;
                }
            }
            PartialRecordKind::OpValue {
                op_name,
                args,
                value,
            } => {
                if let Some(cell) = cur.op_tables[op_name].get(args) {
                    match value {
                        PartialValue::Known(expected) => {
                            if cell.as_deref() != Some(expected.as_str()) {
                                return false;
                            }
                        }
                        PartialValue::ExplicitAbsent => {
                            if cell.is_some() {
                                return false;
                            }
                        }
                        PartialValue::UnobservedSlot(s) => {
                            if let Some(sv) = cur.slots.get(s)
                                && cell.as_deref() != Some(sv.as_str())
                            {
                                return false;
                            }
                        }
                    }
                }
            }
            PartialRecordKind::OpDomain {
                op_name,
                args,
                defined,
            } => {
                if let Some(cell) = cur.op_tables[op_name].get(args) {
                    match defined {
                        PartialTruth::True => {
                            if cell.is_none() {
                                return false;
                            }
                        }
                        PartialTruth::ExplicitAbsent => {
                            if cell.is_some() {
                                return false;
                            }
                        }
                        PartialTruth::UnobservedSlot(s) => {
                            if let Some(sv) = cur.slots.get(s) {
                                let want = slot_truth(sv).unwrap_or(true);
                                if cell.is_some() != want {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
            PartialRecordKind::OpGraph {
                op_name,
                args,
                output,
                present,
            } => {
                if let Some(cell) = cur.op_tables[op_name].get(args) {
                    let is_match = cell.as_deref() == Some(output.as_str());
                    match present {
                        PartialTruth::True => {
                            if !is_match {
                                return false;
                            }
                        }
                        PartialTruth::ExplicitAbsent => {
                            if is_match {
                                return false;
                            }
                        }
                        PartialTruth::UnobservedSlot(s) => {
                            if let Some(sv) = cur.slots.get(s) {
                                let want = slot_truth(sv).unwrap_or(true);
                                if is_match != want {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
            PartialRecordKind::Relation { .. } => {}
        }
    }
    true
}

fn full_world_constraints_hold(
    fin: &FinitePartialPresentation,
    records: &[PartialRecordSpec],
    cur: &CompleteFiniteWorld,
) -> bool {
    for bg in &fin.background_constraints {
        match bg {
            BackgroundConstraint::OperationInjective(op_name) => {
                let tbl = &cur.op_tables[op_name];
                let mut seen = BTreeSet::new();
                for out in tbl.values().flatten() {
                    if !seen.insert(out.as_str()) {
                        return false;
                    }
                }
            }
            BackgroundConstraint::OperationSurjective(op_name) => {
                let op = fin
                    .operations
                    .iter()
                    .find(|o| o.name == *op_name)
                    .expect("validated op");
                let images: BTreeSet<&str> = cur.op_tables[op_name]
                    .values()
                    .flatten()
                    .map(String::as_str)
                    .collect();
                for target in &fin.sorts[&op.out_sort] {
                    if !images.contains(target.as_str()) {
                        return false;
                    }
                }
            }
            BackgroundConstraint::SlotEquality(_, _) | BackgroundConstraint::SlotNotEqual(_, _) => {
            }
        }
    }

    for rec in records {
        if let PartialRecordKind::Relation {
            rel_name,
            args,
            holds,
        } = &rec.kind
        {
            let in_rel = cur.rel_tables[rel_name].contains(args);
            let ok = match holds {
                PartialTruth::True => in_rel,
                PartialTruth::ExplicitAbsent => !in_rel,
                PartialTruth::UnobservedSlot(s) => cur
                    .slots
                    .get(s)
                    .and_then(|v| slot_truth(v))
                    .is_some_and(|want| in_rel == want),
            };
            if !ok {
                return false;
            }
        }
    }
    true
}

fn extract_and_verify_finite_mus(
    fin: &FinitePartialPresentation,
) -> Result<(Vec<Vec<String>>, bool), SilenceReason> {
    let n = fin.records.len();
    if n > MAX_MUS_RECORDS {
        return Err(SilenceReason::FiniteEnumerationOutOfScope {
            detail: format!(
                "record count ({n}) exceeds bounded MUS enumeration limit ({MAX_MUS_RECORDS})"
            ),
        });
    }
    let is_consistent = |mask: usize| -> Result<bool, SilenceReason> {
        let subset: Vec<PartialRecordSpec> = fin
            .records
            .iter()
            .enumerate()
            .filter(|(i, _)| (mask & (1usize << i)) != 0)
            .map(|(_, r)| r.clone())
            .collect();
        let found = enumerate_completions_for_records(fin, &subset, false)?;
        Ok(!found.is_empty())
    };

    let mut mus_masks: Vec<usize> = Vec::new();
    for size in 0..=n {
        for mask in 0usize..(1usize << n) {
            if mask.count_ones() as usize != size {
                continue;
            }
            if mus_masks.iter().copied().any(|m| (m & mask) == m) {
                continue;
            }
            if !is_consistent(mask)? {
                mus_masks.push(mask);
            }
        }
    }

    let mut verified = !mus_masks.is_empty();
    let mut mus_ids = Vec::with_capacity(mus_masks.len());
    for mask in mus_masks {
        if is_consistent(mask)? {
            verified = false;
        }
        for i in 0..n {
            if (mask & (1usize << i)) != 0 && !is_consistent(mask & !(1usize << i))? {
                verified = false;
            }
        }
        let mut ids: Vec<String> = (0..n)
            .filter(|i| (mask & (1usize << i)) != 0)
            .map(|i| fin.records[i].id.clone())
            .collect();
        ids.sort();
        mus_ids.push(ids);
    }
    mus_ids.sort();
    Ok((mus_ids, verified))
}

fn cartesian_args(arg_sorts: &[String], sorts: &BTreeMap<String, Vec<String>>) -> Vec<Vec<String>> {
    let mut out = vec![vec![]];
    for s in arg_sorts {
        let mut next = Vec::new();
        for prefix in &out {
            for e in &sorts[s] {
                let mut row = prefix.clone();
                row.push(e.clone());
                next.push(row);
            }
        }
        out = next;
    }
    out
}
