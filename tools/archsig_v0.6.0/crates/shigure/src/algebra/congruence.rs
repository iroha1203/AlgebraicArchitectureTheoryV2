//! 最小機能閉包（congruence closure）と衝突の有限導出列（AAT 第17章 定理 17.2・命題 17.3）。

use crate::algebra::poly::AlgebraError;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// 既定の導出・閉包ステップ上限。
pub use crate::limits::DEFAULT_MAX_CONGRUENCE_STEPS;

/// sort 定義（固定値 sort かどうかを区別する）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CongruenceSort {
    pub name: String,
    pub elements: Vec<String>,
    pub is_fixed_value: bool,
}

/// 操作・部分操作・量の出力記録（`positive == true` なら $G_e^+$、`false` なら $G_e^-$）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpOutputRecord {
    pub op_name: String,
    pub arg_sorts: Vec<String>,
    pub out_sort: String,
    pub args: Vec<String>,
    pub output: String,
    pub positive: bool,
}

/// 定義域・関係の成立/不在記録の種別。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PredicateRecordKind {
    Domain,
    Relation,
}

/// 定義域（$D_p^+, D_p^-$）または関係（$r^+, r^-$）の記録。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateRecord {
    pub name: String,
    pub kind: PredicateRecordKind,
    pub arg_sorts: Vec<String>,
    pub args: Vec<String>,
    pub positive: bool,
}

/// 最小機能閉包計算の入力。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CongruenceInput {
    pub sorts: Vec<CongruenceSort>,
    /// 同一視要求 $(s, x, y) \in \mathscr{R}_s$。
    pub requests: Vec<(String, String, String)>,
    pub op_records: Vec<OpOutputRecord>,
    pub predicate_records: Vec<PredicateRecord>,
    pub max_steps: usize,
}

/// 導出ステップの根拠。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivationReason {
    IdentityRequest {
        sort: String,
        lhs: String,
        rhs: String,
    },
    Reflexivity {
        sort: String,
        elem: String,
    },
    Symmetry {
        sort: String,
        lhs: String,
        rhs: String,
    },
    Transitivity {
        sort: String,
        a: String,
        b: String,
        c: String,
    },
    Functionality {
        op_name: String,
        args_a: Vec<String>,
        args_b: Vec<String>,
        out_a: String,
        out_b: String,
    },
}

/// 有限導出列の 1 ステップ（`lhs ~ rhs` in `sort`）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivationStep {
    pub sort: String,
    pub lhs: String,
    pub rhs: String,
    pub reason: DerivationReason,
}

/// 定理 17.2 の 2 条件で検出される衝突種別。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollisionKind {
    FixedValueCollision {
        sort: String,
        lhs: String,
        rhs: String,
    },
    OutputRecordCollision {
        op_name: String,
        pos_args: Vec<String>,
        pos_out: String,
        neg_args: Vec<String>,
        neg_out: String,
    },
    DomainRecordCollision {
        op_name: String,
        pos_args: Vec<String>,
        neg_args: Vec<String>,
    },
    RelationRecordCollision {
        rel_name: String,
        pos_args: Vec<String>,
        neg_args: Vec<String>,
    },
}

/// 衝突とその有限導出列。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollisionWitness {
    pub kind: CollisionKind,
    pub derivation: Vec<DerivationStep>,
}

/// 最小機能閉包の計算結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CongruenceClosureResult {
    /// sort ごとの同値類分割（各類および類リストは辞書順正規化済み）。
    pub classes: BTreeMap<String, Vec<Vec<String>>>,
    /// 定理 17.2 の衝突一覧（空なら無矛盾）。
    pub collisions: Vec<CollisionWitness>,
    /// すべての導出列が独立検算に合格したか。
    pub derivation_verified: bool,
    pub steps_used: usize,
}

#[derive(Clone, Debug)]
enum ProofEdgeReason {
    Request,
    Functionality {
        op_name: String,
        arg_sorts: Vec<String>,
        args_a: Vec<String>,
        args_b: Vec<String>,
    },
}

#[derive(Clone, Debug)]
struct ProofEdge {
    to: usize,
    reason: ProofEdgeReason,
}

struct SortUf {
    is_fixed_value: bool,
    elems: Vec<String>,
    elem_to_idx: BTreeMap<String, usize>,
    parent: Vec<usize>,
    graph: Vec<Vec<ProofEdge>>,
}

impl SortUf {
    fn new(sort: &CongruenceSort) -> Result<Self, AlgebraError> {
        let mut elem_to_idx = BTreeMap::new();
        for (i, e) in sort.elements.iter().enumerate() {
            if e.trim().is_empty() || elem_to_idx.insert(e.clone(), i).is_some() {
                return Err(AlgebraError::OutOfScope {
                    detail: format!(
                        "invalid or duplicate occurrence `{e}` in sort `{}`",
                        sort.name
                    ),
                });
            }
        }
        let n = sort.elements.len();
        Ok(Self {
            is_fixed_value: sort.is_fixed_value,
            elems: sort.elements.clone(),
            elem_to_idx,
            parent: (0..n).collect(),
            graph: vec![Vec::new(); n],
        })
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn same(&mut self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }

    fn union(&mut self, a: usize, b: usize, reason: ProofEdgeReason) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        self.parent[rb] = ra;
        self.graph[a].push(ProofEdge {
            to: b,
            reason: reason.clone(),
        });
        self.graph[b].push(ProofEdge { to: a, reason });
        true
    }
}

/// 最小機能閉包 $\theta^{\min}(\mathcal{E})$ を構成し、定理 17.2 の衝突と導出列を抽出する。
pub fn compute_congruence_closure(
    input: &CongruenceInput,
) -> Result<CongruenceClosureResult, AlgebraError> {
    let mut sorts_map: BTreeMap<String, SortUf> = BTreeMap::new();
    for s in &input.sorts {
        if s.name.trim().is_empty() || sorts_map.contains_key(&s.name) {
            return Err(AlgebraError::OutOfScope {
                detail: format!("invalid or duplicate sort `{}`", s.name),
            });
        }
        sorts_map.insert(s.name.clone(), SortUf::new(s)?);
    }

    let mut steps_used = 0usize;
    let check_budget = |steps: &mut usize| -> Result<(), AlgebraError> {
        *steps += 1;
        if *steps > input.max_steps {
            return Err(AlgebraError::OutOfScope {
                detail: format!(
                    "congruence closure step bound ({}) exceeded",
                    input.max_steps
                ),
            });
        }
        Ok(())
    };

    // 同一視要求 R_s を追加
    for (sort_name, lhs, rhs) in &input.requests {
        check_budget(&mut steps_used)?;
        let suf = sorts_map
            .get_mut(sort_name)
            .ok_or_else(|| AlgebraError::UnknownVariable {
                name: sort_name.clone(),
            })?;
        let li = *suf
            .elem_to_idx
            .get(lhs)
            .ok_or_else(|| AlgebraError::UnknownVariable { name: lhs.clone() })?;
        let ri = *suf
            .elem_to_idx
            .get(rhs)
            .ok_or_else(|| AlgebraError::UnknownVariable { name: rhs.clone() })?;
        suf.union(li, ri, ProofEdgeReason::Request);
    }

    // 記録の参照妥当性を検証しつつ positive op records を操作名でグループ化
    let mut pos_ops: BTreeMap<String, Vec<&OpOutputRecord>> = BTreeMap::new();
    let mut neg_ops: BTreeMap<String, Vec<&OpOutputRecord>> = BTreeMap::new();
    for rec in &input.op_records {
        if rec.args.len() != rec.arg_sorts.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: rec.arg_sorts.len(),
                actual: rec.args.len(),
            });
        }
        for (s, a) in rec.arg_sorts.iter().zip(&rec.args) {
            let suf = sorts_map
                .get(s)
                .ok_or_else(|| AlgebraError::UnknownVariable { name: s.clone() })?;
            if !suf.elem_to_idx.contains_key(a) {
                return Err(AlgebraError::UnknownVariable { name: a.clone() });
            }
        }
        let out_suf =
            sorts_map
                .get(&rec.out_sort)
                .ok_or_else(|| AlgebraError::UnknownVariable {
                    name: rec.out_sort.clone(),
                })?;
        if !out_suf.elem_to_idx.contains_key(&rec.output) {
            return Err(AlgebraError::UnknownVariable {
                name: rec.output.clone(),
            });
        }
        if rec.positive {
            pos_ops.entry(rec.op_name.clone()).or_default().push(rec);
        } else {
            neg_ops.entry(rec.op_name.clone()).or_default().push(rec);
        }
    }

    let mut pos_preds: BTreeMap<(PredicateRecordKind, String), Vec<&PredicateRecord>> =
        BTreeMap::new();
    let mut neg_preds: BTreeMap<(PredicateRecordKind, String), Vec<&PredicateRecord>> =
        BTreeMap::new();
    for rec in &input.predicate_records {
        if rec.args.len() != rec.arg_sorts.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: rec.arg_sorts.len(),
                actual: rec.args.len(),
            });
        }
        for (s, a) in rec.arg_sorts.iter().zip(&rec.args) {
            let suf = sorts_map
                .get(s)
                .ok_or_else(|| AlgebraError::UnknownVariable { name: s.clone() })?;
            if !suf.elem_to_idx.contains_key(a) {
                return Err(AlgebraError::UnknownVariable { name: a.clone() });
            }
        }
        let key = (rec.kind, rec.name.clone());
        if rec.positive {
            pos_preds.entry(key).or_default().push(rec);
        } else {
            neg_preds.entry(key).or_default().push(rec);
        }
    }

    // 機能閉包の不動点反復
    loop {
        let mut changed = false;
        for (op_name, recs) in &pos_ops {
            for i in 0..recs.len() {
                for j in (i + 1)..recs.len() {
                    check_budget(&mut steps_used)?;
                    let r1 = recs[i];
                    let r2 = recs[j];
                    if r1.arg_sorts != r2.arg_sorts || r1.out_sort != r2.out_sort {
                        return Err(AlgebraError::OutOfScope {
                            detail: format!("inconsistent signature for operation `{op_name}`"),
                        });
                    }
                    let all_args_eq = r1.arg_sorts.iter().enumerate().all(|(k, s)| {
                        let suf = sorts_map.get_mut(s).expect("checked sort");
                        let a = suf.elem_to_idx[&r1.args[k]];
                        let b = suf.elem_to_idx[&r2.args[k]];
                        suf.same(a, b)
                    });
                    if !all_args_eq {
                        continue;
                    }
                    let out_suf = sorts_map.get_mut(&r1.out_sort).expect("checked sort");
                    let oa = out_suf.elem_to_idx[&r1.output];
                    let ob = out_suf.elem_to_idx[&r2.output];
                    if out_suf.union(
                        oa,
                        ob,
                        ProofEdgeReason::Functionality {
                            op_name: op_name.clone(),
                            arg_sorts: r1.arg_sorts.clone(),
                            args_a: r1.args.clone(),
                            args_b: r2.args.clone(),
                        },
                    ) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // 分割の構築
    let mut classes: BTreeMap<String, Vec<Vec<String>>> = BTreeMap::new();
    for (s_name, suf) in &mut sorts_map {
        let mut by_root: BTreeMap<usize, Vec<String>> = BTreeMap::new();
        for idx in 0..suf.elems.len() {
            let r = suf.find(idx);
            by_root.entry(r).or_default().push(suf.elems[idx].clone());
        }
        let mut cls: Vec<Vec<String>> = by_root
            .into_values()
            .map(|mut c| {
                c.sort();
                c
            })
            .collect();
        cls.sort();
        classes.insert(s_name.clone(), cls);
    }

    // 衝突検出と導出列抽出
    let mut collisions = Vec::new();
    let mut seen_steps_cache = BTreeSet::new();

    // 1. 固定値 sort 衝突
    for (s_name, cls) in &classes {
        let is_fixed = sorts_map[s_name].is_fixed_value;
        if is_fixed {
            for c in cls {
                if c.len() > 1 {
                    let mut steps = Vec::new();
                    seen_steps_cache.clear();
                    emit_pair_derivation(
                        &sorts_map,
                        s_name,
                        &c[0],
                        &c[1],
                        &mut steps,
                        &mut seen_steps_cache,
                    )?;
                    collisions.push(CollisionWitness {
                        kind: CollisionKind::FixedValueCollision {
                            sort: s_name.clone(),
                            lhs: c[0].clone(),
                            rhs: c[1].clone(),
                        },
                        derivation: steps,
                    });
                }
            }
        }
    }

    // 2. 操作グラフの正負記録衝突
    for (op_name, pos_list) in &pos_ops {
        let Some(neg_list) = neg_ops.get(op_name) else {
            continue;
        };
        for p in pos_list {
            for n in neg_list {
                if p.arg_sorts != n.arg_sorts || p.out_sort != n.out_sort {
                    continue;
                }
                let args_eq = p.arg_sorts.iter().enumerate().all(|(k, s)| {
                    let suf = sorts_map.get_mut(s).expect("checked");
                    let a = suf.elem_to_idx[&p.args[k]];
                    let b = suf.elem_to_idx[&n.args[k]];
                    suf.same(a, b)
                });
                let out_eq = {
                    let suf = sorts_map.get_mut(&p.out_sort).expect("checked");
                    let a = suf.elem_to_idx[&p.output];
                    let b = suf.elem_to_idx[&n.output];
                    suf.same(a, b)
                };
                if args_eq && out_eq {
                    let mut steps = Vec::new();
                    seen_steps_cache.clear();
                    for (k, s) in p.arg_sorts.iter().enumerate() {
                        emit_pair_derivation(
                            &sorts_map,
                            s,
                            &p.args[k],
                            &n.args[k],
                            &mut steps,
                            &mut seen_steps_cache,
                        )?;
                    }
                    emit_pair_derivation(
                        &sorts_map,
                        &p.out_sort,
                        &p.output,
                        &n.output,
                        &mut steps,
                        &mut seen_steps_cache,
                    )?;
                    collisions.push(CollisionWitness {
                        kind: CollisionKind::OutputRecordCollision {
                            op_name: op_name.clone(),
                            pos_args: p.args.clone(),
                            pos_out: p.output.clone(),
                            neg_args: n.args.clone(),
                            neg_out: n.output.clone(),
                        },
                        derivation: steps,
                    });
                }
            }
        }
    }

    // 3. 定義域・関係の正負記録衝突
    for ((kind, pred_name), pos_list) in &pos_preds {
        let Some(neg_list) = neg_preds.get(&(*kind, pred_name.clone())) else {
            continue;
        };
        for p in pos_list {
            for n in neg_list {
                if p.arg_sorts != n.arg_sorts {
                    continue;
                }
                let args_eq = p.arg_sorts.iter().enumerate().all(|(k, s)| {
                    let suf = sorts_map.get_mut(s).expect("checked");
                    let a = suf.elem_to_idx[&p.args[k]];
                    let b = suf.elem_to_idx[&n.args[k]];
                    suf.same(a, b)
                });
                if args_eq {
                    let mut steps = Vec::new();
                    seen_steps_cache.clear();
                    for (k, s) in p.arg_sorts.iter().enumerate() {
                        emit_pair_derivation(
                            &sorts_map,
                            s,
                            &p.args[k],
                            &n.args[k],
                            &mut steps,
                            &mut seen_steps_cache,
                        )?;
                    }
                    let ckind = match kind {
                        PredicateRecordKind::Domain => CollisionKind::DomainRecordCollision {
                            op_name: pred_name.clone(),
                            pos_args: p.args.clone(),
                            neg_args: n.args.clone(),
                        },
                        PredicateRecordKind::Relation => CollisionKind::RelationRecordCollision {
                            rel_name: pred_name.clone(),
                            pos_args: p.args.clone(),
                            neg_args: n.args.clone(),
                        },
                    };
                    collisions.push(CollisionWitness {
                        kind: ckind,
                        derivation: steps,
                    });
                }
            }
        }
    }

    let derivation_verified = collisions
        .iter()
        .all(|w| verify_collision_witness(input, w));

    Ok(CongruenceClosureResult {
        classes,
        collisions,
        derivation_verified,
        steps_used,
    })
}

fn emit_pair_derivation(
    sorts_map: &BTreeMap<String, SortUf>,
    sort: &str,
    lhs: &str,
    rhs: &str,
    steps: &mut Vec<DerivationStep>,
    proven: &mut BTreeSet<(String, String, String)>,
) -> Result<(), AlgebraError> {
    if proven.contains(&(sort.to_owned(), lhs.to_owned(), rhs.to_owned())) {
        return Ok(());
    }
    if lhs == rhs {
        let step = DerivationStep {
            sort: sort.to_owned(),
            lhs: lhs.to_owned(),
            rhs: rhs.to_owned(),
            reason: DerivationReason::Reflexivity {
                sort: sort.to_owned(),
                elem: lhs.to_owned(),
            },
        };
        proven.insert((sort.to_owned(), lhs.to_owned(), rhs.to_owned()));
        steps.push(step);
        return Ok(());
    }

    let suf = &sorts_map[sort];
    let start = suf.elem_to_idx[lhs];
    let goal = suf.elem_to_idx[rhs];
    let n = suf.elems.len();
    let mut prev: Vec<Option<(usize, ProofEdgeReason)>> = vec![None; n];
    let mut visited = vec![false; n];
    let mut queue = VecDeque::new();
    visited[start] = true;
    queue.push_back(start);

    while let Some(u) = queue.pop_front() {
        if u == goal {
            break;
        }
        for edge in &suf.graph[u] {
            if !visited[edge.to] {
                visited[edge.to] = true;
                prev[edge.to] = Some((u, edge.reason.clone()));
                queue.push_back(edge.to);
            }
        }
    }
    if !visited[goal] {
        return Err(AlgebraError::OutOfScope {
            detail: format!("internal error: missing derivation path for `{lhs}` ~ `{rhs}`"),
        });
    }

    let mut path = Vec::new();
    let mut cur = goal;
    while cur != start {
        let (p, reason) = prev[cur].clone().expect("visited");
        path.push((p, cur, reason));
        cur = p;
    }
    path.reverse();

    for &(u, v, ref reason) in &path {
        let u_name = &suf.elems[u];
        let v_name = &suf.elems[v];
        match reason {
            ProofEdgeReason::Request => {
                // `requests` が `(u, v)` か `(v, u)` かは入力の向きを確認せずとも
                // `compute_congruence_closure` では両方同値として追加されているため、
                // 無向辺ならどちらかを `IdentityRequest`、逆向きを `Symmetry` として出せるが、
                // ここでは正方向を仮定せず、もし逆向きなら呼び出し側 `verify_derivation_chain` が
                // Symmetry も許せるよう、まず `(u_name, v_name)` をチェックせず
                // 後続で正規化する。具体的には Request の向きがどちらかを判定する代わりに
                // `emit_request_step` を使う。
                let step = DerivationStep {
                    sort: sort.to_owned(),
                    lhs: u_name.clone(),
                    rhs: v_name.clone(),
                    reason: DerivationReason::IdentityRequest {
                        sort: sort.to_owned(),
                        lhs: u_name.clone(),
                        rhs: v_name.clone(),
                    },
                };
                if proven.insert((sort.to_owned(), u_name.clone(), v_name.clone())) {
                    steps.push(step);
                }
            }
            ProofEdgeReason::Functionality {
                op_name,
                arg_sorts,
                args_a,
                args_b,
            } => {
                for (k, s) in arg_sorts.iter().enumerate() {
                    emit_pair_derivation(sorts_map, s, &args_a[k], &args_b[k], steps, proven)?;
                }
                // `Functionality` は無向に張ったため `(u_name, v_name)` が `(out_a, out_b)` または逆。
                let step = DerivationStep {
                    sort: sort.to_owned(),
                    lhs: u_name.clone(),
                    rhs: v_name.clone(),
                    reason: DerivationReason::Functionality {
                        op_name: op_name.clone(),
                        args_a: args_a.clone(),
                        args_b: args_b.clone(),
                        out_a: u_name.clone(),
                        out_b: v_name.clone(),
                    },
                };
                if proven.insert((sort.to_owned(), u_name.clone(), v_name.clone())) {
                    steps.push(step);
                }
            }
        }
    }

    // 推移律で `lhs ~ rhs` を連結
    let mut acc = suf.elems[path[0].0].clone();
    for &(_, v, _) in &path {
        let next = suf.elems[v].clone();
        debug_assert!(
            acc == next || proven.contains(&(sort.to_owned(), acc.clone(), next.clone()))
        );
        if acc != lhs {
            let mid = acc.clone();
            if !proven.contains(&(sort.to_owned(), lhs.to_owned(), next.clone())) {
                proven.insert((sort.to_owned(), lhs.to_owned(), next.clone()));
                steps.push(DerivationStep {
                    sort: sort.to_owned(),
                    lhs: lhs.to_owned(),
                    rhs: next.clone(),
                    reason: DerivationReason::Transitivity {
                        sort: sort.to_owned(),
                        a: lhs.to_owned(),
                        b: mid,
                        c: next.clone(),
                    },
                });
            }
        }
        acc = next;
    }

    Ok(())
}

/// 衝突 witness と導出列の独立検算。
pub fn verify_collision_witness(input: &CongruenceInput, witness: &CollisionWitness) -> bool {
    let mut proven: BTreeSet<(String, String, String)> = BTreeSet::new();
    let req_set: BTreeSet<(String, String, String)> = input.requests.iter().cloned().collect();

    for step in &witness.derivation {
        let valid = match &step.reason {
            DerivationReason::IdentityRequest { sort, lhs, rhs } => {
                sort == &step.sort
                    && lhs == &step.lhs
                    && rhs == &step.rhs
                    && (req_set.contains(&(sort.clone(), lhs.clone(), rhs.clone()))
                        || req_set.contains(&(sort.clone(), rhs.clone(), lhs.clone())))
            }
            DerivationReason::Reflexivity { sort, elem } => {
                sort == &step.sort && elem == &step.lhs && elem == &step.rhs
            }
            DerivationReason::Symmetry { sort, lhs, rhs } => {
                sort == &step.sort
                    && rhs == &step.lhs
                    && lhs == &step.rhs
                    && proven.contains(&(sort.clone(), lhs.clone(), rhs.clone()))
            }
            DerivationReason::Transitivity { sort, a, b, c } => {
                sort == &step.sort
                    && a == &step.lhs
                    && c == &step.rhs
                    && proven.contains(&(sort.clone(), a.clone(), b.clone()))
                    && proven.contains(&(sort.clone(), b.clone(), c.clone()))
            }
            DerivationReason::Functionality {
                op_name,
                args_a,
                args_b,
                out_a,
                out_b,
            } => {
                if out_a != &step.lhs || out_b != &step.rhs {
                    false
                } else {
                    let match_rec = |r: &OpOutputRecord, target_out: &str| {
                        r.positive
                            && r.op_name == *op_name
                            && r.out_sort == step.sort
                            && r.output == target_out
                            && (r.args == *args_a || r.args == *args_b)
                    };
                    input.op_records.iter().any(|r1| {
                        match_rec(r1, out_a)
                            && r1.arg_sorts.len() == args_a.len()
                            && r1.arg_sorts.len() == args_b.len()
                            && r1.arg_sorts.iter().enumerate().all(|(k, s)| {
                                proven.contains(&(s.clone(), args_a[k].clone(), args_b[k].clone()))
                                    || proven.contains(&(
                                        s.clone(),
                                        args_b[k].clone(),
                                        args_a[k].clone(),
                                    ))
                            })
                            && input
                                .op_records
                                .iter()
                                .any(|r2| match_rec(r2, out_b) && r2.arg_sorts == r1.arg_sorts)
                    })
                }
            }
        };
        if !valid {
            return false;
        }
        proven.insert((step.sort.clone(), step.lhs.clone(), step.rhs.clone()));
    }

    match &witness.kind {
        CollisionKind::FixedValueCollision { sort, lhs, rhs } => {
            lhs != rhs
                && input
                    .sorts
                    .iter()
                    .any(|s| s.name == *sort && s.is_fixed_value)
                && proven.contains(&(sort.clone(), lhs.clone(), rhs.clone()))
        }
        CollisionKind::OutputRecordCollision {
            op_name,
            pos_args,
            pos_out,
            neg_args,
            neg_out,
        } => {
            let Some(pos) = input.op_records.iter().find(|r| {
                r.positive
                    && r.op_name == *op_name
                    && r.args.len() == r.arg_sorts.len()
                    && r.args == *pos_args
                    && r.output == *pos_out
            }) else {
                return false;
            };
            let has_neg = input.op_records.iter().any(|r| {
                !r.positive
                    && r.op_name == *op_name
                    && r.args.len() == r.arg_sorts.len()
                    && r.args == *neg_args
                    && r.output == *neg_out
                    && r.arg_sorts == pos.arg_sorts
                    && r.out_sort == pos.out_sort
            });
            has_neg
                && pos.arg_sorts.len() == pos_args.len()
                && pos.arg_sorts.len() == neg_args.len()
                && pos.arg_sorts.iter().enumerate().all(|(k, s)| {
                    proven.contains(&(s.clone(), pos_args[k].clone(), neg_args[k].clone()))
                })
                && proven.contains(&(pos.out_sort.clone(), pos_out.clone(), neg_out.clone()))
        }
        CollisionKind::DomainRecordCollision {
            op_name,
            pos_args,
            neg_args,
        } => {
            let Some(pos) = input.predicate_records.iter().find(|r| {
                r.positive
                    && r.kind == PredicateRecordKind::Domain
                    && r.name == *op_name
                    && r.args.len() == r.arg_sorts.len()
                    && r.args == *pos_args
            }) else {
                return false;
            };
            let has_neg = input.predicate_records.iter().any(|r| {
                !r.positive
                    && r.kind == PredicateRecordKind::Domain
                    && r.name == *op_name
                    && r.args.len() == r.arg_sorts.len()
                    && r.args == *neg_args
                    && r.arg_sorts == pos.arg_sorts
            });
            has_neg
                && pos.arg_sorts.len() == pos_args.len()
                && pos.arg_sorts.len() == neg_args.len()
                && pos.arg_sorts.iter().enumerate().all(|(k, s)| {
                    proven.contains(&(s.clone(), pos_args[k].clone(), neg_args[k].clone()))
                })
        }
        CollisionKind::RelationRecordCollision {
            rel_name,
            pos_args,
            neg_args,
        } => {
            let Some(pos) = input.predicate_records.iter().find(|r| {
                r.positive
                    && r.kind == PredicateRecordKind::Relation
                    && r.name == *rel_name
                    && r.args.len() == r.arg_sorts.len()
                    && r.args == *pos_args
            }) else {
                return false;
            };
            let has_neg = input.predicate_records.iter().any(|r| {
                !r.positive
                    && r.kind == PredicateRecordKind::Relation
                    && r.name == *rel_name
                    && r.args.len() == r.arg_sorts.len()
                    && r.args == *neg_args
                    && r.arg_sorts == pos.arg_sorts
            });
            has_neg
                && pos.arg_sorts.len() == pos_args.len()
                && pos.arg_sorts.len() == neg_args.len()
                && pos.arg_sorts.iter().enumerate().all(|(k, s)| {
                    proven.contains(&(s.clone(), pos_args[k].clone(), neg_args[k].clone()))
                })
        }
    }
}
