//! 極小横断集合（最小ヒット集合）列挙と費用最小化
//! （AAT 第18章 定理 18.12・第19章 定理 19.9 / 定理 19.11 / 命題 19.12）。

use crate::algebra::poly::AlgebraError;
use crate::algebra::scalar::{Rat, RingCoeff};
use std::collections::{BTreeMap, BTreeSet};

/// 既定の探索ステップ・結果上限。
pub use crate::limits::{DEFAULT_MAX_HITTING_SET_RESULTS, DEFAULT_MAX_HITTING_SET_STEPS};

/// 極小横断集合列挙の入力。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HittingSetInput {
    pub universe: Vec<String>,
    pub hyperedges: Vec<Vec<String>>,
    /// 任意の非負重み（指定時は包含極小集合の中から費用最小のものを抽出する）。
    pub weights: Option<BTreeMap<String, Rat>>,
    pub max_steps: usize,
    pub max_results: usize,
}

/// 極小横断集合列挙の結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HittingSetOutcome {
    /// 空の超辺が存在するため横断集合が存在しない（不足 witness）。
    EmptyHyperedge { edge_index: usize },
    /// 全包含極小横断集合の列挙に成功。
    Enumerated {
        minimal_sets: Vec<Vec<String>>,
        min_cost_sets: Vec<(Vec<String>, Rat)>,
        verified: bool,
        steps_used: usize,
    },
}

/// 全包含極小横断集合（および重み指定時の費用最小集合）を列挙・検算する。
pub fn enumerate_minimal_hitting_sets(
    input: &HittingSetInput,
) -> Result<HittingSetOutcome, AlgebraError> {
    let mut universe_set = BTreeSet::new();
    for u in &input.universe {
        if u.trim().is_empty() || !universe_set.insert(u.clone()) {
            return Err(AlgebraError::OutOfScope {
                detail: format!("invalid or duplicate universe element `{u}`"),
            });
        }
    }
    if let Some(weights) = &input.weights {
        for u in &input.universe {
            let Some(w) = weights.get(u) else {
                return Err(AlgebraError::UnknownVariable { name: u.clone() });
            };
            if *w < Rat::zero() {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("negative weight for `{u}` is not allowed"),
                });
            }
        }
    }

    // 各超辺を BTreeSet 化し、空超辺を検出し、包含縮約（A ⊆ B なら B を除去）する。
    let mut raw_edges: Vec<BTreeSet<String>> = Vec::with_capacity(input.hyperedges.len());
    for (idx, edge) in input.hyperedges.iter().enumerate() {
        let mut set = BTreeSet::new();
        for item in edge {
            if !universe_set.contains(item) {
                return Err(AlgebraError::UnknownVariable { name: item.clone() });
            }
            set.insert(item.clone());
        }
        if set.is_empty() {
            return Ok(HittingSetOutcome::EmptyHyperedge { edge_index: idx });
        }
        raw_edges.push(set);
    }

    raw_edges.sort_by_key(BTreeSet::len);
    let mut reduced_edges: Vec<BTreeSet<String>> = Vec::new();
    for e in raw_edges {
        if reduced_edges.iter().any(|existing| existing.is_subset(&e)) {
            continue;
        }
        reduced_edges.push(e);
    }

    if reduced_edges.is_empty() {
        let min_cost_sets = if input.weights.is_some() {
            vec![(vec![], Rat::zero())]
        } else {
            Vec::new()
        };
        return Ok(HittingSetOutcome::Enumerated {
            minimal_sets: vec![vec![]],
            min_cost_sets,
            verified: true,
            steps_used: 1,
        });
    }

    // インデックス表現へ変換して探索を高速化
    let elems: Vec<String> = universe_set.into_iter().collect();
    let elem_to_idx: BTreeMap<&str, usize> = elems
        .iter()
        .enumerate()
        .map(|(i, s)| (s.as_str(), i))
        .collect();
    let indexed_edges: Vec<Vec<usize>> = reduced_edges
        .iter()
        .map(|s| s.iter().map(|name| elem_to_idx[name.as_str()]).collect())
        .collect();

    let mut steps_used = 0usize;
    let mut minimal_indexed: Vec<BTreeSet<usize>> = Vec::new();
    let mut current: BTreeSet<usize> = BTreeSet::new();

    // 最小未カバー超辺を優先して分枝し、発見された極小集合で枝刈りする。
    fn search(
        edges: &[Vec<usize>],
        current: &mut BTreeSet<usize>,
        minimal: &mut Vec<BTreeSet<usize>>,
        steps: &mut usize,
        max_steps: usize,
        max_results: usize,
    ) -> Result<(), AlgebraError> {
        *steps += 1;
        if *steps > max_steps {
            return Err(AlgebraError::OutOfScope {
                detail: format!("hitting set search step bound ({max_steps}) exceeded"),
            });
        }
        // 既に発見済みの横断集合を真包含または一致する枝は極小になり得ない
        if minimal.iter().any(|m| m.is_subset(current)) {
            return Ok(());
        }

        // 未カバー超辺のうち最小サイズのものを選ぶ
        let mut best_edge: Option<&Vec<usize>> = None;
        for e in edges {
            if !e.iter().any(|x| current.contains(x)) && best_edge.is_none_or(|b| e.len() < b.len())
            {
                best_edge = Some(e);
            }
        }
        let Some(target) = best_edge else {
            // 全超辺をカバーした。既存結果のうち `current` が真部分集合になるものを除き追加
            minimal.retain(|m| !current.is_subset(m));
            if minimal.len() >= max_results {
                return Err(AlgebraError::OutOfScope {
                    detail: format!("hitting set result bound ({max_results}) exceeded"),
                });
            }
            minimal.push(current.clone());
            return Ok(());
        };

        for &cand in target {
            current.insert(cand);
            search(edges, current, minimal, steps, max_steps, max_results)?;
            current.remove(&cand);
        }
        Ok(())
    }

    search(
        &indexed_edges,
        &mut current,
        &mut minimal_indexed,
        &mut steps_used,
        input.max_steps,
        input.max_results,
    )?;

    let mut minimal_sets: Vec<Vec<String>> = minimal_indexed
        .into_iter()
        .map(|s| s.into_iter().map(|i| elems[i].clone()).collect())
        .collect();
    minimal_sets.sort();

    let verified = verify_minimal_hitting_sets(&input.hyperedges, &minimal_sets);

    let min_cost_sets = if let Some(weights) = &input.weights {
        let mut best_cost: Option<Rat> = None;
        let mut scored: Vec<(Vec<String>, Rat)> = Vec::with_capacity(minimal_sets.len());
        for set in &minimal_sets {
            let mut cost = Rat::zero();
            for item in set {
                cost = cost.add_ref(&weights[item]);
            }
            match &best_cost {
                None => best_cost = Some(cost.clone()),
                Some(b) if cost < *b => best_cost = Some(cost.clone()),
                _ => {}
            }
            scored.push((set.clone(), cost));
        }
        if let Some(best) = best_cost {
            scored.into_iter().filter(|(_, c)| *c == best).collect()
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    Ok(HittingSetOutcome::Enumerated {
        minimal_sets,
        min_cost_sets,
        verified,
        steps_used,
    })
}

/// 列挙された極小横断集合の横断性・包含極小性・無重複性を独立検算する。
pub fn verify_minimal_hitting_sets(
    hyperedges: &[Vec<String>],
    minimal_sets: &[Vec<String>],
) -> bool {
    let edge_sets: Vec<BTreeSet<&str>> = hyperedges
        .iter()
        .map(|e| e.iter().map(String::as_str).collect())
        .collect();
    let mut seen: BTreeSet<Vec<&str>> = BTreeSet::new();
    for set in minimal_sets {
        let mut s: Vec<&str> = set.iter().map(String::as_str).collect();
        s.sort();
        s.dedup();
        if s.len() != set.len() || !seen.insert(s.clone()) {
            return false;
        }
        let hs: BTreeSet<&str> = s.into_iter().collect();
        // 全超辺を横断すること
        if !edge_sets.iter().all(|e| !e.is_disjoint(&hs)) {
            return false;
        }
        // いずれの 1 要素を削除しても横断でなくなること（包含極小性）
        for &elem in &hs {
            let reduced: BTreeSet<&str> = hs.iter().copied().filter(|&x| x != elem).collect();
            if edge_sets.iter().all(|e| !e.is_disjoint(&reduced)) {
                return false;
            }
        }
    }
    true
}
