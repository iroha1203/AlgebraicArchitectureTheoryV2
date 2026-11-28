//! 構成可能集合の表現・Rabinowitsch 剪定・ブール演算（G-141 D6–D7 / G-142 G7）。
//!
//! 局所閉層 `V(equations) ∩ D(invertibles)` の有限和として構成可能集合を表現し、
//! 空な層を `rabinowitsch_solve` によって即時剪定する不変条件を保つ。

use crate::algebra::MonomialOrder;
use crate::algebra::groebner::{GroebnerBasis, rabinowitsch_solve};
use crate::algebra::poly::{AlgebraError, Poly, VarOrder};
use crate::algebra::scalar::Rat;
use crate::ir::result::SilenceReason;

/// 構成可能集合が保持できる最大局所閉層数（組合せ爆発時に fail-closed 沈黙する）。
pub use crate::limits::DEFAULT_MAX_CONSTRUCTIBLE_STRATA;

/// 単一の局所閉層 `V(equations) ∩ D(invertibles)`。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocallyClosedStratum {
    pub equations: Vec<Poly<Rat>>,
    pub invertibles: Vec<Poly<Rat>>,
}

impl LocallyClosedStratum {
    pub fn contains_point(&self, point: &[Rat]) -> Result<bool, AlgebraError> {
        for eq in &self.equations {
            if !eq.eval_at(point)?.is_zero() {
                return Ok(false);
            }
        }
        for inv in &self.invertibles {
            if inv.eval_at(point)?.is_zero() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn display_pair(&self, vars: &VarOrder) -> (Vec<String>, Vec<String>) {
        let eqs = self
            .equations
            .iter()
            .map(|p| p.display(vars, MonomialOrder::Grevlex))
            .collect();
        let invs = self
            .invertibles
            .iter()
            .map(|p| p.display(vars, MonomialOrder::Grevlex))
            .collect();
        (eqs, invs)
    }
}

/// 有限個の局所閉層の和集合 `⋃_i (V(I_i) ∩ D(g_i))` として表される構成可能集合。
///
/// 不変条件:
/// - `strata` 内のすべての層は標数 0 代数閉包 $\overline{\mathbb{Q}}$ 上で非空（`1 ∉ (E_i, u_j g_j - 1)`）。
/// - `strata.is_empty()` と「幾何点として空集合」が同値である。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructibleSet {
    vars: VarOrder,
    strata: Vec<LocallyClosedStratum>,
}

impl ConstructibleSet {
    pub fn empty(vars: VarOrder) -> Self {
        Self {
            vars,
            strata: Vec::new(),
        }
    }

    pub fn whole_space(vars: VarOrder) -> Self {
        Self {
            vars,
            strata: vec![LocallyClosedStratum {
                equations: Vec::new(),
                invertibles: Vec::new(),
            }],
        }
    }

    pub fn closed(vars: VarOrder, equations: Vec<Poly<Rat>>) -> Result<Self, SilenceReason> {
        Self::from_strata(
            vars,
            vec![LocallyClosedStratum {
                equations,
                invertibles: Vec::new(),
            }],
        )
    }

    pub fn open(vars: VarOrder, invertibles: Vec<Poly<Rat>>) -> Result<Self, SilenceReason> {
        Self::from_strata(
            vars,
            vec![LocallyClosedStratum {
                equations: Vec::new(),
                invertibles,
            }],
        )
    }

    pub fn locally_closed(
        vars: VarOrder,
        equations: Vec<Poly<Rat>>,
        invertibles: Vec<Poly<Rat>>,
    ) -> Result<Self, SilenceReason> {
        Self::from_strata(
            vars,
            vec![LocallyClosedStratum {
                equations,
                invertibles,
            }],
        )
    }

    pub fn from_strata(
        vars: VarOrder,
        raw_strata: Vec<LocallyClosedStratum>,
    ) -> Result<Self, SilenceReason> {
        let mut strata = Vec::new();
        for st in raw_strata {
            if let Some(norm) = normalize_and_prune_stratum(&st.equations, &st.invertibles, &vars)?
            {
                push_canonical_stratum(&mut strata, norm)?;
            }
        }
        Ok(Self { vars, strata })
    }

    pub fn vars(&self) -> &VarOrder {
        &self.vars
    }

    pub fn strata(&self) -> &[LocallyClosedStratum] {
        &self.strata
    }

    pub fn into_strata(self) -> Vec<LocallyClosedStratum> {
        self.strata
    }

    pub fn is_empty(&self) -> bool {
        self.strata.is_empty()
    }

    pub fn contains_point(&self, point: &[Rat]) -> Result<bool, SilenceReason> {
        if point.len() != self.vars.len() {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "constructible_point_arity".to_owned(),
                detail: format!(
                    "expected {} coordinates, got {}",
                    self.vars.len(),
                    point.len()
                ),
            });
        }
        for st in &self.strata {
            if st
                .contains_point(point)
                .map_err(map_constructible_silence)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// 構成可能集合の和集合 `self ∪ other`。
    pub fn union(&self, other: &Self) -> Result<Self, SilenceReason> {
        require_same_vars(&self.vars, &other.vars)?;
        if self.is_empty() {
            return Ok(other.clone());
        }
        if other.is_empty() {
            return Ok(self.clone());
        }
        let mut strata = Vec::new();
        for st in self.strata.iter().chain(&other.strata) {
            push_canonical_stratum(&mut strata, st.clone())?;
        }
        Ok(Self {
            vars: self.vars.clone(),
            strata,
        })
    }

    /// 構成可能集合の交わり `self ∩ other`。
    pub fn intersect(&self, other: &Self) -> Result<Self, SilenceReason> {
        require_same_vars(&self.vars, &other.vars)?;
        if self.is_empty() || other.is_empty() {
            return Ok(Self::empty(self.vars.clone()));
        }
        let mut strata = Vec::new();
        for a in &self.strata {
            for b in &other.strata {
                let mut eqs = a.equations.clone();
                eqs.extend(b.equations.iter().cloned());
                let mut invs = a.invertibles.clone();
                invs.extend(b.invertibles.iter().cloned());
                if let Some(norm) = normalize_and_prune_stratum(&eqs, &invs, &self.vars)? {
                    push_canonical_stratum(&mut strata, norm)?;
                }
            }
        }
        Ok(Self {
            vars: self.vars.clone(),
            strata,
        })
    }

    /// 構成可能集合の補集合 `|X| \ self`。
    pub fn complement(&self) -> Result<Self, SilenceReason> {
        if self.is_empty() {
            return Ok(Self::whole_space(self.vars.clone()));
        }
        let mut acc = Self::whole_space(self.vars.clone());
        for st in &self.strata {
            let comp = stratum_complement(st, &self.vars)?;
            acc = acc.intersect(&comp)?;
            if acc.is_empty() {
                break;
            }
        }
        Ok(acc)
    }

    /// 構成可能集合の差集合 `self \ other = self ∩ (|X| \ other)`。
    pub fn difference(&self, other: &Self) -> Result<Self, SilenceReason> {
        require_same_vars(&self.vars, &other.vars)?;
        if self.is_empty() || other.is_empty() {
            return Ok(self.clone());
        }
        let mut acc = self.clone();
        for st in &other.strata {
            let comp = stratum_complement(st, &self.vars)?;
            acc = acc.intersect(&comp)?;
            if acc.is_empty() {
                break;
            }
        }
        Ok(acc)
    }

    /// 幾何点としての包含判定 `self ⊆ other`。
    pub fn is_subset_of(&self, other: &Self) -> Result<bool, SilenceReason> {
        Ok(self.difference(other)?.is_empty())
    }

    /// 幾何点としての等値判定 `self == other`。
    pub fn equals(&self, other: &Self) -> Result<bool, SilenceReason> {
        Ok(self.is_subset_of(other)? && other.is_subset_of(self)?)
    }

    pub fn display_strata(&self) -> Vec<(Vec<String>, Vec<String>)> {
        self.strata
            .iter()
            .map(|st| st.display_pair(&self.vars))
            .collect()
    }
}

fn stratum_complement(
    stratum: &LocallyClosedStratum,
    vars: &VarOrder,
) -> Result<ConstructibleSet, SilenceReason> {
    let mut pieces = Vec::new();

    // |X| \ V(f_1, ..., f_r) = ⨆_i (V(f_1, ..., f_{i-1}) ∩ D(f_i))
    let mut prefix_eqs = Vec::new();
    for f in &stratum.equations {
        pieces.push(LocallyClosedStratum {
            equations: prefix_eqs.clone(),
            invertibles: vec![f.clone()],
        });
        prefix_eqs.push(f.clone());
    }

    // V(E) \ D(g_1, ..., g_s) = ⨆_j (V(E, g_j) ∩ D(g_1, ..., g_{j-1}))
    let mut prefix_invs = Vec::new();
    for g in &stratum.invertibles {
        let mut eqs = stratum.equations.clone();
        eqs.push(g.clone());
        pieces.push(LocallyClosedStratum {
            equations: eqs,
            invertibles: prefix_invs.clone(),
        });
        prefix_invs.push(g.clone());
    }

    ConstructibleSet::from_strata(vars.clone(), pieces)
}

fn push_canonical_stratum(
    strata: &mut Vec<LocallyClosedStratum>,
    candidate: LocallyClosedStratum,
) -> Result<(), SilenceReason> {
    let is_whole = candidate.equations.is_empty() && candidate.invertibles.is_empty();
    if is_whole {
        strata.clear();
        strata.push(candidate);
        return Ok(());
    }
    if strata
        .first()
        .is_some_and(|s| s.equations.is_empty() && s.invertibles.is_empty())
    {
        return Ok(());
    }
    if !strata.contains(&candidate) {
        strata.push(candidate);
        let max_strata = crate::limits::active_limits().max_constructible_strata;
        if strata.len() > max_strata {
            return Err(SilenceReason::ConstructibleStratificationOutOfScope {
                detail: format!("constructible set exceeded stratum limit ({max_strata})"),
            });
        }
    }
    Ok(())
}

pub(crate) fn normalize_and_prune_stratum(
    equations: &[Poly<Rat>],
    invertibles: &[Poly<Rat>],
    vars: &VarOrder,
) -> Result<Option<LocallyClosedStratum>, SilenceReason> {
    let n = vars.len();
    for p in equations.iter().chain(invertibles) {
        if p.num_vars() != n {
            return Err(SilenceReason::ConstructibleStratificationOutOfScope {
                detail: format!(
                    "stratum polynomial arity mismatch: expected {n}, got {}",
                    p.num_vars()
                ),
            });
        }
    }
    let rab =
        rabinowitsch_solve(equations, invertibles, vars).map_err(map_constructible_silence)?;
    if rab.is_empty_over_closure {
        return Ok(None);
    }

    let eq_gb = GroebnerBasis::compute(
        &rab.parameter_equations,
        vars.clone(),
        MonomialOrder::Grevlex,
    )
    .map_err(map_constructible_silence)?;
    if eq_gb.contains_one() {
        return Ok(None);
    }
    let clean_eqs: Vec<Poly<Rat>> = eq_gb.basis_polys().into_iter().cloned().collect();

    let mut clean_invs = Vec::new();
    for inv in invertibles {
        let red = eq_gb.normal_form(inv).map_err(map_constructible_silence)?;
        if red.is_zero() {
            return Ok(None);
        }
        if red.is_constant() {
            continue;
        }
        let monic = red.monic(MonomialOrder::Grevlex);
        if !clean_invs.contains(&monic) {
            clean_invs.push(monic);
        }
    }

    Ok(Some(LocallyClosedStratum {
        equations: clean_eqs,
        invertibles: clean_invs,
    }))
}

fn require_same_vars(lhs: &VarOrder, rhs: &VarOrder) -> Result<(), SilenceReason> {
    if lhs != rhs {
        return Err(SilenceReason::ConstructibleStratificationOutOfScope {
            detail: format!(
                "variable order mismatch between constructible sets: {:?} vs {:?}",
                lhs.vars(),
                rhs.vars()
            ),
        });
    }
    Ok(())
}

pub(crate) fn map_constructible_silence(err: AlgebraError) -> SilenceReason {
    match err {
        AlgebraError::UnobservedDependency { slots } => {
            SilenceReason::UnobservedDependency { slots }
        }
        other => SilenceReason::ConstructibleStratificationOutOfScope {
            detail: other.to_string(),
        },
    }
}
