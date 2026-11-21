//! 座標面支持による相互作用参加変数数 r と極小不成立部分族（G-141 F10–F12 / AC4）。

use crate::algebra::poly::{AlgebraError, Poly, VarOrder};
use crate::algebra::scalar::RingCoeff;
use crate::ir::result::{InteractionSummary, SilenceReason};
use std::collections::{BTreeMap, BTreeSet};

/// 閉条件の自由パラメータ chart `k[t_1, ..., t_n]` 上の残差 ideal `J` に対し、
/// 座標面支持から最小相互作用参加変数数・最大零化サイズ r・包含極小不成立部分族を計算する（G-141 F11–F12）。
///
/// 同一多重次数の係数は `Poly<C>` 構築時に加算・零消去済みであることを前提とし、
/// 開条件が本質的に絡む場合は呼び出し側で閉条件へ丸めず `check_closed_for_interaction` により沈黙する。
pub fn analyze_coordinate_interaction<C: RingCoeff>(
    residuals: &[Poly<C>],
    vars: &VarOrder,
) -> Result<InteractionSummary, AlgebraError> {
    let mut ring_ref: Option<&C> = None;
    for poly in residuals {
        if poly.num_vars() != vars.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: vars.len(),
                actual: poly.num_vars(),
            });
        }
        let coeff = poly.zero_coeff();
        if let Some(expected) = ring_ref {
            if !expected.same_ring(coeff) {
                return Err(AlgebraError::DomainMismatch {
                    expected: format!("{expected:?}"),
                    actual: format!("{coeff:?}"),
                });
            }
        } else {
            ring_ref = Some(coeff);
        }
    }

    // すべての非零単項式の変数支持 S(m) を収集する（F12）。
    let mut supports: BTreeSet<Vec<usize>> = BTreeSet::new();
    for poly in residuals {
        for mono in poly.terms().keys() {
            let support: Vec<usize> = mono.support().into_iter().collect();
            supports.insert(support);
        }
    }

    // 包含極小な支持だけを残す。
    let all_supports: Vec<Vec<usize>> = supports.into_iter().collect();
    let mut minimal_indices: Vec<Vec<usize>> = Vec::new();
    for candidate in &all_supports {
        let has_proper_subset = all_supports
            .iter()
            .any(|other| other.len() < candidate.len() && is_subset(other, candidate));
        if !has_proper_subset {
            minimal_indices.push(candidate.clone());
        }
    }

    // 最小相互作用参加変数数および F11 の最大零化部分集合サイズ r を算出する。
    let (min_interacting_variables, max_vanishing_subset_size) =
        if let Some(min_size) = minimal_indices.iter().map(Vec::len).min() {
            if min_size == 0 {
                // 定数残差（空集合でも不成立）: 参加変数数 0、零化部分集合なし。
                (Some(0), None)
            } else {
                // サイズ min_size - 1 以下の全座標面で J = 0、サイズ min_size で不成立。
                (Some(min_size), Some(min_size - 1))
            }
        } else {
            // 残差ゼロ（全座標面で成立）: 不成立なし、r = n。
            (None, Some(vars.len()))
        };

    let mut minimal_failing_subsets: Vec<Vec<String>> = minimal_indices
        .into_iter()
        .map(|indices| {
            let mut names: Vec<String> = indices
                .into_iter()
                .map(|i| vars.vars()[i].clone())
                .collect();
            names.sort();
            names
        })
        .collect();
    minimal_failing_subsets.sort_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));

    Ok(InteractionSummary {
        min_interacting_variables,
        max_vanishing_subset_size,
        minimal_failing_subsets,
        parameters: vars.vars().to_vec(),
    })
}

/// 一部の変数へ定数値を代入した座標面・切断面上で相互作用解析を行う。
/// 例: `mu * delta * (1 - rho)` に対し `rho = 0` 面（`{delta, mu}` 不成立）と
/// `rho = 1` 面（不成立解消、残差 0）を区別する（AC4）。
pub fn analyze_interaction_on_face<C: RingCoeff>(
    residuals: &[Poly<C>],
    vars: &VarOrder,
    fixed_values: &BTreeMap<String, C>,
) -> Result<InteractionSummary, AlgebraError> {
    let mut ring_ref: Option<&C> = None;
    for poly in residuals {
        if poly.num_vars() != vars.len() {
            return Err(AlgebraError::ArityMismatch {
                expected: vars.len(),
                actual: poly.num_vars(),
            });
        }
        let coeff = poly.zero_coeff();
        if let Some(expected) = ring_ref {
            if !expected.same_ring(coeff) {
                return Err(AlgebraError::DomainMismatch {
                    expected: format!("{expected:?}"),
                    actual: format!("{coeff:?}"),
                });
            }
        } else {
            ring_ref = Some(coeff);
        }
    }
    for val in fixed_values.values() {
        if let Some(expected) = ring_ref {
            if !expected.same_ring(val) {
                return Err(AlgebraError::DomainMismatch {
                    expected: format!("{expected:?}"),
                    actual: format!("{val:?}"),
                });
            }
        } else {
            ring_ref = Some(val);
        }
    }
    let mut fixed_by_idx = BTreeMap::new();
    let mut remaining_names = Vec::new();
    for (idx, name) in vars.vars().iter().enumerate() {
        if let Some(val) = fixed_values.get(name) {
            fixed_by_idx.insert(idx, val.clone());
        } else {
            remaining_names.push(name.clone());
        }
    }
    for name in fixed_values.keys() {
        if vars.index_of(name).is_none() {
            return Err(AlgebraError::UnknownVariable { name: name.clone() });
        }
    }

    let remaining_order = VarOrder::new(remaining_names)?;
    let projected: Vec<Poly<C>> = residuals
        .iter()
        .map(|poly| {
            let evaluated = poly.partial_eval(&fixed_by_idx);
            let mut proj = Poly::zero(remaining_order.len(), poly.zero_coeff().clone());
            for (mono, coeff) in evaluated.terms() {
                let mut exps = Vec::with_capacity(remaining_order.len());
                for (i, &e) in mono.exps().iter().enumerate() {
                    if !fixed_by_idx.contains_key(&i) {
                        exps.push(e);
                    }
                }
                proj.add_term(
                    crate::algebra::poly::Monomial::from_exps(exps),
                    coeff.clone(),
                );
            }
            proj
        })
        .collect();

    analyze_coordinate_interaction(&projected, &remaining_order)
}

/// 開条件が本質的に絡む変更を F10–F12 の閉条件相互作用へ丸めないための検査。
pub fn require_closed_for_interaction(has_open_conditions: bool) -> Result<(), SilenceReason> {
    if has_open_conditions {
        Err(SilenceReason::OpenConditionInInteraction {
            detail: "open/invertible conditions cannot be rounded to closed coordinate-plane interaction analysis (G-141 F10)".to_owned(),
        })
    } else {
        Ok(())
    }
}

fn is_subset(small: &[usize], large: &[usize]) -> bool {
    let mut j = 0;
    for &x in small {
        while j < large.len() && large[j] < x {
            j += 1;
        }
        if j >= large.len() || large[j] != x {
            return false;
        }
        j += 1;
    }
    true
}
