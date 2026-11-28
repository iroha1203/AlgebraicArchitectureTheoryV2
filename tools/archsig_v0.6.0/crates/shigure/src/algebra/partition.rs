//! 反復細分による文脈同値 $\approx_{\mathcal{V}}$ と分離文脈生成、および有限分割列挙
//! （AAT 第17章 定義 17.4・設定 17.5・定理 17.6・例 17.7・命題 17.8）。

use crate::algebra::poly::AlgebraError;
use std::collections::{BTreeMap, BTreeSet};

/// 既定の分割列挙上限（一般有限系での同値関係列挙）。
pub const DEFAULT_MAX_SET_PARTITIONS: usize = 4_096;

/// 基本使用文脈（読取り $c: D_c \to Z_c$、未定義は `None`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaseReading {
    pub name: String,
    pub sort: String,
    /// `elem -> Some(value)`（定義済み値）または `elem -> None`（明示未定義 $\bot_c$）。
    pub values: BTreeMap<String, Option<String>>,
}

/// 設定 17.5 の部分操作写像表（全入力で定義可能性が確定）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialOpTable {
    pub name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    /// `args -> Some(output)`（定義済み）または `args -> None`（未定義 $\bot$）。
    pub entries: BTreeMap<Vec<String>, Option<String>>,
}

/// 二つの出現を区別する分離文脈木。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeparatingContext {
    FixedIdentity {
        sort: String,
    },
    Base {
        reading_name: String,
    },
    OpDomain {
        op_name: String,
        arg_index: usize,
        prefix_args: Vec<String>,
        suffix_args: Vec<String>,
    },
    OpSub {
        op_name: String,
        arg_index: usize,
        prefix_args: Vec<String>,
        suffix_args: Vec<String>,
        inner: Box<SeparatingContext>,
    },
}

impl SeparatingContext {
    /// 人間可読な合成文脈式を整形する（例: `o(T(x))`）。
    pub fn format_expr(&self, var: &str) -> String {
        match self {
            SeparatingContext::FixedIdentity { .. } => var.to_owned(),
            SeparatingContext::Base { reading_name } => format!("{reading_name}({var})"),
            SeparatingContext::OpDomain {
                op_name,
                prefix_args,
                suffix_args,
                ..
            } => {
                let mut args = prefix_args.clone();
                args.push(var.to_owned());
                args.extend(suffix_args.iter().cloned());
                format!("dom_{op_name}({})", args.join(", "))
            }
            SeparatingContext::OpSub {
                op_name,
                prefix_args,
                suffix_args,
                inner,
                ..
            } => {
                let mut args = prefix_args.clone();
                args.push(var.to_owned());
                args.extend(suffix_args.iter().cloned());
                inner.format_expr(&format!("{op_name}({})", args.join(", ")))
            }
        }
    }

    /// 出現 `elem` に対する文脈評価 $\widehat{c}(\text{elem}) \in Z_c \amalg \{\bot_c\}$ を計算する。
    /// 外側 `None` は入力表欠落、内側 `None` は $\bot_c$（未定義）を表す。
    pub fn evaluate(
        &self,
        elem: &str,
        readings: &[BaseReading],
        ops: &[PartialOpTable],
    ) -> Option<Option<String>> {
        match self {
            SeparatingContext::FixedIdentity { .. } => Some(Some(elem.to_owned())),
            SeparatingContext::Base { reading_name } => {
                let r = readings.iter().find(|r| r.name == *reading_name)?;
                r.values.get(elem).cloned()
            }
            SeparatingContext::OpDomain {
                op_name,
                prefix_args,
                suffix_args,
                ..
            } => {
                let op = ops.iter().find(|o| o.name == *op_name)?;
                let mut full_args = Vec::with_capacity(prefix_args.len() + 1 + suffix_args.len());
                full_args.extend(prefix_args.iter().cloned());
                full_args.push(elem.to_owned());
                full_args.extend(suffix_args.iter().cloned());
                match op.entries.get(&full_args)? {
                    Some(_) => Some(Some("defined".to_owned())),
                    None => Some(Some("undefined".to_owned())),
                }
            }
            SeparatingContext::OpSub {
                op_name,
                prefix_args,
                suffix_args,
                inner,
                ..
            } => {
                let op = ops.iter().find(|o| o.name == *op_name)?;
                let mut full_args = Vec::with_capacity(prefix_args.len() + 1 + suffix_args.len());
                full_args.extend(prefix_args.iter().cloned());
                full_args.push(elem.to_owned());
                full_args.extend(suffix_args.iter().cloned());
                match op.entries.get(&full_args)? {
                    Some(next_elem) => inner.evaluate(next_elem, readings, ops),
                    None => Some(None),
                }
            }
        }
    }
}

/// 反復細分の入力。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefinementInput {
    pub sorts: BTreeMap<String, Vec<String>>,
    pub fixed_sorts: BTreeSet<String>,
    pub base_readings: Vec<BaseReading>,
    pub ops: Vec<PartialOpTable>,
    pub max_iterations: usize,
}

/// 異なる文脈同値類のペアに対する分離文脈 witness。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeparatingWitness {
    pub sort: String,
    pub lhs: String,
    pub rhs: String,
    pub context: SeparatingContext,
    pub context_expr: String,
    pub lhs_value: Option<String>,
    pub rhs_value: Option<String>,
    pub verified: bool,
}

/// 反復細分の結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartitionRefinementResult {
    pub classes: BTreeMap<String, Vec<Vec<String>>>,
    pub witnesses: Vec<SeparatingWitness>,
    pub iterations: usize,
    pub all_witnesses_verified: bool,
}

/// 設定 17.5 の反復細分を実行し、文脈同値 $\approx_{\mathcal{V}}$ と分離文脈を構成する。
pub fn refine_partition(
    input: &RefinementInput,
) -> Result<PartitionRefinementResult, AlgebraError> {
    // 入力妥当性確認
    let sort_sets: BTreeMap<&str, BTreeSet<&str>> = input
        .sorts
        .iter()
        .map(|(s, elems)| (s.as_str(), elems.iter().map(String::as_str).collect()))
        .collect();
    for (s, uniq) in &sort_sets {
        if uniq.len() != input.sorts[*s].len() {
            return Err(AlgebraError::OutOfScope {
                detail: format!("duplicate elements in sort `{s}`"),
            });
        }
    }
    for r in &input.base_readings {
        let Some(elems) = input.sorts.get(&r.sort) else {
            return Err(AlgebraError::UnknownVariable {
                name: r.sort.clone(),
            });
        };
        for e in elems {
            if !r.values.contains_key(e) {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("base reading `{}` missing entry for `{e}`", r.name),
                });
            }
        }
    }
    for op in &input.ops {
        let Some(out_set) = sort_sets.get(op.out_sort.as_str()) else {
            return Err(AlgebraError::UnknownVariable {
                name: op.out_sort.clone(),
            });
        };
        for s in &op.arg_sorts {
            if !sort_sets.contains_key(s.as_str()) {
                return Err(AlgebraError::UnknownVariable { name: s.clone() });
            }
        }
        for (args, out_opt) in &op.entries {
            if args.len() != op.arg_sorts.len() {
                return Err(AlgebraError::OutOfScope {
                    detail: format!(
                        "operation `{}` entry arity mismatch: expected {}, got {}",
                        op.name,
                        op.arg_sorts.len(),
                        args.len()
                    ),
                });
            }
            for (arg, sort_name) in args.iter().zip(&op.arg_sorts) {
                if !sort_sets[sort_name.as_str()].contains(arg.as_str()) {
                    return Err(AlgebraError::UnknownVariable { name: arg.clone() });
                }
            }
            if let Some(out_elem) = out_opt
                && !out_set.contains(out_elem.as_str())
            {
                return Err(AlgebraError::UnknownVariable {
                    name: out_elem.clone(),
                });
            }
        }
    }

    // 各要素の現在クラス ID とクラスごとの分離文脈木を保持する。
    let mut class_of: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
    let mut class_ctx: BTreeMap<String, Vec<Option<SeparatingContext>>> = BTreeMap::new();

    for (s_name, elems) in &input.sorts {
        let is_fixed = input.fixed_sorts.contains(s_name);
        let mut sig_to_cid: BTreeMap<Vec<Option<Option<String>>>, usize> = BTreeMap::new();
        let mut elem_cid = BTreeMap::new();
        let mut ctxs = Vec::new();

        for e in elems {
            let mut sig = Vec::new();
            if is_fixed {
                sig.push(Some(Some(e.clone())));
            }
            for r in input.base_readings.iter().filter(|r| r.sort == *s_name) {
                sig.push(Some(r.values.get(e).cloned().flatten()));
            }
            let cid = if let Some(&existing) = sig_to_cid.get(&sig) {
                existing
            } else {
                let id = ctxs.len();
                sig_to_cid.insert(sig, id);
                ctxs.push(None);
                id
            };
            elem_cid.insert(e.clone(), cid);
        }
        class_of.insert(s_name.clone(), elem_cid);
        class_ctx.insert(s_name.clone(), ctxs);
    }

    // 各 sort で初期分割が 2 クラス以上なら、分離する基本読取りを記録した `pair_sep` を構築する。
    let mut pair_sep: BTreeMap<(String, String, String), SeparatingContext> = BTreeMap::new();
    for (s_name, elems) in &input.sorts {
        let is_fixed = input.fixed_sorts.contains(s_name);
        for i in 0..elems.len() {
            for j in (i + 1)..elems.len() {
                let a = &elems[i];
                let b = &elems[j];
                if class_of[s_name][a] == class_of[s_name][b] {
                    continue;
                }
                if is_fixed {
                    pair_sep.insert(
                        ordered_key(s_name, a, b),
                        SeparatingContext::FixedIdentity {
                            sort: s_name.clone(),
                        },
                    );
                } else if let Some(r) = input
                    .base_readings
                    .iter()
                    .find(|r| r.sort == *s_name && r.values[a] != r.values[b])
                {
                    pair_sep.insert(
                        ordered_key(s_name, a, b),
                        SeparatingContext::Base {
                            reading_name: r.name.clone(),
                        },
                    );
                }
            }
        }
    }

    // 反復細分
    let mut iterations = 0usize;
    loop {
        if iterations >= input.max_iterations {
            return Err(AlgebraError::OutOfScope {
                detail: format!(
                    "partition refinement iteration bound ({}) exceeded",
                    input.max_iterations
                ),
            });
        }
        iterations += 1;
        let mut any_split = false;

        // 1 つの操作と一座標・固定引数組合せで分割を細分する
        for op in &input.ops {
            let arity = op.arg_sorts.len();
            if arity == 0 {
                continue;
            }
            for arg_idx in 0..arity {
                let target_sort = &op.arg_sorts[arg_idx];
                let fixed_combos =
                    enumerate_fixed_arg_combos(&input.sorts, &op.arg_sorts, arg_idx)?;
                for (prefix, suffix) in fixed_combos {
                    let target_elems = &input.sorts[target_sort];
                    // 各クラス内で (old_cid, out_cid_or_bot) でグループ分けする
                    let mut new_sig_map: BTreeMap<(usize, Option<usize>), usize> = BTreeMap::new();
                    let mut new_elem_cid: BTreeMap<String, usize> = BTreeMap::new();
                    let mut rep_by_new_cid: Vec<String> = Vec::new();
                    let mut key_by_new_cid: Vec<(usize, Option<usize>)> = Vec::new();

                    for e in target_elems {
                        let old_cid = class_of[target_sort][e];
                        let mut full_args = prefix.clone();
                        full_args.push(e.clone());
                        full_args.extend(suffix.iter().cloned());
                        let out_entry =
                            op.entries
                                .get(&full_args)
                                .ok_or_else(|| AlgebraError::OutOfScope {
                                    detail: format!(
                                        "operation `{}` missing entry for ({}) in setting 17.5",
                                        op.name,
                                        full_args.join(", ")
                                    ),
                                })?;
                        let out_cid = out_entry
                            .as_ref()
                            .map(|out_elem| class_of[&op.out_sort][out_elem]);
                        let sig = (old_cid, out_cid);
                        let nid = if let Some(&id) = new_sig_map.get(&sig) {
                            id
                        } else {
                            let id = rep_by_new_cid.len();
                            new_sig_map.insert(sig, id);
                            rep_by_new_cid.push(e.clone());
                            key_by_new_cid.push(sig);
                            id
                        };
                        new_elem_cid.insert(e.clone(), nid);
                    }

                    let old_count = class_of[target_sort]
                        .values()
                        .copied()
                        .collect::<BTreeSet<_>>()
                        .len();
                    if rep_by_new_cid.len() > old_count {
                        any_split = true;
                        // 新たに分離されたクラス対へ分離文脈を記録
                        for i in 0..target_elems.len() {
                            for j in (i + 1)..target_elems.len() {
                                let a = &target_elems[i];
                                let b = &target_elems[j];
                                if class_of[target_sort][a] == class_of[target_sort][b]
                                    && new_elem_cid[a] != new_elem_cid[b]
                                {
                                    let mut full_a = prefix.clone();
                                    full_a.push(a.clone());
                                    full_a.extend(suffix.iter().cloned());
                                    let mut full_b = prefix.clone();
                                    full_b.push(b.clone());
                                    full_b.extend(suffix.iter().cloned());

                                    let ctx = match (&op.entries[&full_a], &op.entries[&full_b]) {
                                        (Some(oa), Some(ob)) => {
                                            let inner = pair_sep
                                                .get(&ordered_key(&op.out_sort, oa, ob))
                                                .cloned()
                                                .ok_or_else(|| AlgebraError::OutOfScope {
                                                    detail: "missing inner separating context"
                                                        .to_owned(),
                                                })?;
                                            SeparatingContext::OpSub {
                                                op_name: op.name.clone(),
                                                arg_index: arg_idx,
                                                prefix_args: prefix.clone(),
                                                suffix_args: suffix.clone(),
                                                inner: Box::new(inner),
                                            }
                                        }
                                        // 片方のみ定義: 操作の定義域読取り自体で区別する。
                                        (Some(_), None) | (None, Some(_)) => {
                                            SeparatingContext::OpDomain {
                                                op_name: op.name.clone(),
                                                arg_index: arg_idx,
                                                prefix_args: prefix.clone(),
                                                suffix_args: suffix.clone(),
                                            }
                                        }
                                        (None, None) => unreachable!("same out_cid_or_bot"),
                                    };
                                    pair_sep.insert(ordered_key(target_sort, a, b), ctx);
                                }
                            }
                        }
                        class_of.insert(target_sort.clone(), new_elem_cid);
                    }
                }
            }
        }
        if !any_split {
            break;
        }
    }

    // 結果クラスを正規化
    let mut classes = BTreeMap::new();
    for (s_name, elems) in &input.sorts {
        let mut by_cid: BTreeMap<usize, Vec<String>> = BTreeMap::new();
        for e in elems {
            by_cid
                .entry(class_of[s_name][e])
                .or_default()
                .push(e.clone());
        }
        let mut cls: Vec<Vec<String>> = by_cid
            .into_values()
            .map(|mut c| {
                c.sort();
                c
            })
            .collect();
        cls.sort();
        classes.insert(s_name.clone(), cls);
    }

    // 異なるクラス代表間の witness を構築・独立検算
    let mut witnesses = Vec::new();
    for (s_name, cls) in &classes {
        for i in 0..cls.len() {
            for j in (i + 1)..cls.len() {
                let a = &cls[i][0];
                let b = &cls[j][0];
                let Some(ctx) = pair_sep.get(&ordered_key(s_name, a, b)).cloned() else {
                    continue;
                };
                let (lhs_value, rhs_value, verified) = match (
                    ctx.evaluate(a, &input.base_readings, &input.ops),
                    ctx.evaluate(b, &input.base_readings, &input.ops),
                ) {
                    (Some(va), Some(vb)) => (va.clone(), vb.clone(), va != vb),
                    _ => (None, None, false),
                };
                witnesses.push(SeparatingWitness {
                    sort: s_name.clone(),
                    lhs: a.clone(),
                    rhs: b.clone(),
                    context_expr: ctx.format_expr("x"),
                    context: ctx,
                    lhs_value,
                    rhs_value,
                    verified,
                });
            }
        }
    }

    let all_witnesses_verified = witnesses.iter().all(|w| w.verified);
    let _ = class_ctx;
    Ok(PartitionRefinementResult {
        classes,
        witnesses,
        iterations,
        all_witnesses_verified,
    })
}

fn ordered_key(sort: &str, a: &str, b: &str) -> (String, String, String) {
    if a <= b {
        (sort.to_owned(), a.to_owned(), b.to_owned())
    } else {
        (sort.to_owned(), b.to_owned(), a.to_owned())
    }
}

type FixedArgCombos = Vec<(Vec<String>, Vec<String>)>;

fn enumerate_fixed_arg_combos(
    sorts: &BTreeMap<String, Vec<String>>,
    arg_sorts: &[String],
    hole_idx: usize,
) -> Result<FixedArgCombos, AlgebraError> {
    let mut prefix_combos: Vec<Vec<String>> = vec![vec![]];
    for s in &arg_sorts[..hole_idx] {
        let elems = &sorts[s];
        let mut next = Vec::new();
        for p in &prefix_combos {
            for e in elems {
                let mut item = p.clone();
                item.push(e.clone());
                next.push(item);
            }
        }
        prefix_combos = next;
    }
    let mut suffix_combos: Vec<Vec<String>> = vec![vec![]];
    for s in &arg_sorts[(hole_idx + 1)..] {
        let elems = &sorts[s];
        let mut next = Vec::new();
        for p in &suffix_combos {
            for e in elems {
                let mut item = p.clone();
                item.push(e.clone());
                next.push(item);
            }
        }
        suffix_combos = next;
    }
    let mut out = Vec::with_capacity(prefix_combos.len() * suffix_combos.len());
    for p in &prefix_combos {
        for s in &suffix_combos {
            out.push((p.clone(), s.clone()));
        }
    }
    Ok(out)
}

/// 有限集合 `elements` 上の同値関係（集合分割）を全列挙する（例 17.7・定理 17.11 用）。
pub fn enumerate_set_partitions(
    elements: &[String],
    max_partitions: usize,
) -> Result<Vec<Vec<Vec<String>>>, AlgebraError> {
    if elements.is_empty() {
        return if max_partitions == 0 {
            Err(AlgebraError::OutOfScope {
                detail: "partition enumeration bound (0) exceeded".to_owned(),
            })
        } else {
            Ok(vec![vec![]])
        };
    }
    let mut sorted = elements.to_vec();
    sorted.sort();
    sorted.dedup();
    if sorted.len() != elements.len() {
        return Err(AlgebraError::OutOfScope {
            detail: "duplicate element in partition enumeration".to_owned(),
        });
    }

    let n = sorted.len();
    let mut result = Vec::new();
    let mut blocks: Vec<Vec<String>> = Vec::new();

    fn backtrack(
        idx: usize,
        sorted: &[String],
        blocks: &mut Vec<Vec<String>>,
        result: &mut Vec<Vec<Vec<String>>>,
        max_partitions: usize,
    ) -> Result<(), AlgebraError> {
        if idx == sorted.len() {
            if result.len() >= max_partitions {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("partition enumeration bound ({max_partitions}) exceeded"),
                });
            }
            let mut normalized = blocks.clone();
            for b in &mut normalized {
                b.sort();
            }
            normalized.sort();
            result.push(normalized);
            return Ok(());
        }
        let elem = &sorted[idx];
        for bi in 0..blocks.len() {
            blocks[bi].push(elem.clone());
            backtrack(idx + 1, sorted, blocks, result, max_partitions)?;
            blocks[bi].pop();
        }
        blocks.push(vec![elem.clone()]);
        backtrack(idx + 1, sorted, blocks, result, max_partitions)?;
        blocks.pop();
        Ok(())
    }

    let _ = n;
    backtrack(0, &sorted, &mut blocks, &mut result, max_partitions)?;
    Ok(result)
}

/// 分割 `coarse` が `fine` を包含する（`fine ⊆ coarse`、つまり `coarse` がより粗い）か。
pub fn partition_refines(fine: &[Vec<String>], coarse: &[Vec<String>]) -> bool {
    let mut coarse_id = BTreeMap::new();
    for (cid, blk) in coarse.iter().enumerate() {
        for e in blk {
            coarse_id.insert(e.as_str(), cid);
        }
    }
    fine.iter().all(|blk| {
        let Some(first) = blk.first() else {
            return true;
        };
        let Some(&cid) = coarse_id.get(first.as_str()) else {
            return false;
        };
        blk.iter().all(|e| coarse_id.get(e.as_str()) == Some(&cid))
    })
}
