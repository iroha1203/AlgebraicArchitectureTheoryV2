//! 次数 0–2 の有限自由 $\Lambda$-加群コチェーン複体 $C^0 \xrightarrow{d^0} C^1 \xrightarrow{d^1} C^2$
//! （$\Lambda \in \{\mathbb{Z}, \mathbb{Q}, \mathbb{F}_p\}$）・$d^1 d^0 = 0$ 検算・
//! $H^0/H^1/H^2$（自由階数＋$\mathbb{Z}$ torsion）・cocycle 零性判定・cochain 射誘導写像核/余核
//! （G-141 E2–E5・G1–G5 / G-142 A1–A3・C1–C4・E1–E6・F3）。

use crate::algebra::artin::{
    AffineSolutionField, check_same_ring, rref_field, solve_affine_field,
};
pub use crate::algebra::linear::{SmithFormZ, smith_normal_form_z};
use crate::algebra::poly::AlgebraError;
use crate::algebra::scalar::RingCoeff;
use crate::algebra::syzygy::FieldCoeff;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

/// 有限生成可換群 / 有限次元ベクトル空間のコホモロジー群構造（自由階数＋`Z` torsion 不変因子）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CohomologyGroup {
    pub free_rank: usize,
    /// `Z` 上の torsion 不変因子（各要素 `> 1`、昇順整除列）。体係数では常に空。
    pub torsion_invariants: Vec<BigInt>,
}

impl CohomologyGroup {
    pub fn free(rank: usize) -> Self {
        Self {
            free_rank: rank,
            torsion_invariants: Vec::new(),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.free_rank == 0 && self.torsion_invariants.is_empty()
    }

    pub fn display(&self, ring_name: &str) -> String {
        let mut parts = Vec::new();
        if self.free_rank == 1 {
            parts.push(ring_name.to_owned());
        } else if self.free_rank > 1 {
            parts.push(format!("{ring_name}^{}", self.free_rank));
        }
        for d in &self.torsion_invariants {
            parts.push(format!("{ring_name}/{d}"));
        }
        if parts.is_empty() {
            "0".to_owned()
        } else {
            parts.join(" + ")
        }
    }
}

/// 次数 0–2 の有限自由加群コチェーン複体 `C^0 --d0--> C^1 --d1--> C^2`。
/// 構築時（`CochainComplex::new`）にサイズ・環一致・`d1 * d0 == 0` を検証し、
/// フィールドを非公開とすることで不変条件を型レベルで維持する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CochainComplex<C: RingCoeff> {
    dim0: usize,
    dim1: usize,
    dim2: usize,
    /// `dim1 x dim0` 行列。
    d0: Vec<Vec<C>>,
    /// `dim2 x dim1` 行列。
    d1: Vec<Vec<C>>,
    zero_coeff: C,
}

impl<C: RingCoeff> CochainComplex<C> {
    pub fn dim0(&self) -> usize {
        self.dim0
    }

    pub fn dim1(&self) -> usize {
        self.dim1
    }

    pub fn dim2(&self) -> usize {
        self.dim2
    }

    pub fn d0(&self) -> &[Vec<C>] {
        &self.d0
    }

    pub fn d1(&self) -> &[Vec<C>] {
        &self.d1
    }

    pub fn zero_coeff(&self) -> &C {
        &self.zero_coeff
    }

    /// 複体条件 `d1 * d0 == 0` と行列サイズを検証して構築する。
    pub fn new(
        dim0: usize,
        dim1: usize,
        dim2: usize,
        d0: Vec<Vec<C>>,
        d1: Vec<Vec<C>>,
        zero_coeff: C,
    ) -> Result<Self, AlgebraError> {
        if d0.len() != dim1 {
            return Err(AlgebraError::ArityMismatch {
                expected: dim1,
                actual: d0.len(),
            });
        }
        for r in &d0 {
            if r.len() != dim0 {
                return Err(AlgebraError::ArityMismatch {
                    expected: dim0,
                    actual: r.len(),
                });
            }
            for v in r {
                check_same_ring(&zero_coeff, v)?;
            }
        }
        if d1.len() != dim2 {
            return Err(AlgebraError::ArityMismatch {
                expected: dim2,
                actual: d1.len(),
            });
        }
        for r in &d1 {
            if r.len() != dim1 {
                return Err(AlgebraError::ArityMismatch {
                    expected: dim1,
                    actual: r.len(),
                });
            }
            for v in r {
                check_same_ring(&zero_coeff, v)?;
            }
        }
        let prod = mat_mul(&d1, &d0, dim0, &zero_coeff);
        for row in &prod {
            for val in row {
                if !val.coeff_is_zero() {
                    return Err(AlgebraError::OutOfScope {
                        detail: "cochain complex condition d^1 * d^0 = 0 violated".to_owned(),
                    });
                }
            }
        }
        Ok(Self {
            dim0,
            dim1,
            dim2,
            d0,
            d1,
            zero_coeff: zero_coeff.zero_like(),
        })
    }

    pub fn apply_d0(&self, x: &[C]) -> Result<Vec<C>, AlgebraError> {
        if x.len() != self.dim0 {
            return Err(AlgebraError::ArityMismatch {
                expected: self.dim0,
                actual: x.len(),
            });
        }
        for v in x {
            check_same_ring(&self.zero_coeff, v)?;
        }
        Ok(mat_vec(&self.d0, x, &self.zero_coeff))
    }

    pub fn apply_d1(&self, y: &[C]) -> Result<Vec<C>, AlgebraError> {
        if y.len() != self.dim1 {
            return Err(AlgebraError::ArityMismatch {
                expected: self.dim1,
                actual: y.len(),
            });
        }
        for v in y {
            check_same_ring(&self.zero_coeff, v)?;
        }
        Ok(mat_vec(&self.d1, y, &self.zero_coeff))
    }
}

/// 体 `K`（`Q`・`F_p`）上のコホモロジー計算結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldCohomology<C: FieldCoeff> {
    pub h0_dim: usize,
    pub h0_basis: Vec<Vec<C>>,
    pub h1_dim: usize,
    pub h1_cycle_basis: Vec<Vec<C>>,
    pub h1_coboundary_basis: Vec<Vec<C>>,
    /// `H^1 = Z^1 / B^1` の代表元基底（長さ `h1_dim`、各元は `C^1` の cocycle）。
    pub h1_rep_basis: Vec<Vec<C>>,
    pub h2_dim: usize,
}

/// 体上 1-cocycle のコホモロジー類・零性判定結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CocycleCheckField<C: FieldCoeff> {
    pub is_cocycle: bool,
    pub is_zero_class: bool,
    /// `is_zero_class == true` のときの `d^0(coboundary_witness) == cocycle` を満たす witness。
    pub coboundary_witness: Option<Vec<C>>,
    /// `h1_rep_basis` における `[cocycle]` の座標。
    pub class_coords: Vec<C>,
}

impl<C: FieldCoeff> CochainComplex<C> {
    /// 体係数上の `H^0, H^1, H^2` と基底を厳密計算する。
    pub fn cohomology_field(&self) -> Result<FieldCohomology<C>, AlgebraError> {
        let z = self.zero_coeff.zero_like();
        // H^0 = ker(d^0)
        let h0_basis = kernel_basis_field(&self.d0, self.dim0, &z)?;
        let h0_dim = h0_basis.len();

        // Z^1 = ker(d^1)
        let h1_cycle_basis = kernel_basis_field(&self.d1, self.dim1, &z)?;

        // B^1 = im(d^0) の列空間基底
        let b1_cols = matrix_columns(&self.d0, self.dim0);
        let h1_coboundary_basis = independent_vectors_field(&b1_cols, self.dim1, &z)?;

        // H^1 代表元基底: B^1 を Z^1 の基底へ延長した増分ベクトル
        let h1_rep_basis =
            quotient_complement_basis_field(&h1_coboundary_basis, &h1_cycle_basis, self.dim1, &z)?;
        let h1_dim = h1_rep_basis.len();

        // H^2 = C^2 / im(d^1)
        let im_d1_rank = rref_field(&self.d1, self.dim1, &z)?.rank;
        let h2_dim = self.dim2 - im_d1_rank;

        Ok(FieldCohomology {
            h0_dim,
            h0_basis,
            h1_dim,
            h1_cycle_basis,
            h1_coboundary_basis,
            h1_rep_basis,
            h2_dim,
        })
    }

    /// 1-cochain `z_vec` の cocycle 条件・`[z_vec] == 0` 判定・`h1_rep_basis` 座標を計算する。
    pub fn check_h1_cocycle_field(
        &self,
        coh: &FieldCohomology<C>,
        z_vec: &[C],
    ) -> Result<CocycleCheckField<C>, AlgebraError> {
        let d1z = self.apply_d1(z_vec)?;
        let is_cocycle = d1z.iter().all(RingCoeff::coeff_is_zero);
        if !is_cocycle {
            return Ok(CocycleCheckField {
                is_cocycle: false,
                is_zero_class: false,
                coboundary_witness: None,
                class_coords: Vec::new(),
            });
        }
        let z = self.zero_coeff.zero_like();
        let coboundary_witness = match solve_affine_field(&self.d0, z_vec, self.dim0, &z)? {
            AffineSolutionField::Consistent { particular, .. } => Some(particular),
            AffineSolutionField::Inconsistent { .. } => None,
        };
        let is_zero_class = coboundary_witness.is_some();

        // z_vec = sum a_i b_i + sum c_j r_j  (b_i in B^1, r_j in h1_rep_basis)
        let nb = coh.h1_coboundary_basis.len();
        let nr = coh.h1_rep_basis.len();
        let total = nb + nr;
        let mut mat = vec![vec![z.clone(); total]; self.dim1];
        for (col, v) in coh
            .h1_coboundary_basis
            .iter()
            .chain(&coh.h1_rep_basis)
            .enumerate()
        {
            if v.len() != self.dim1 {
                return Err(AlgebraError::ArityMismatch {
                    expected: self.dim1,
                    actual: v.len(),
                });
            }
            for (row, val) in v.iter().enumerate() {
                check_same_ring(&self.zero_coeff, val)?;
                mat[row][col] = val.clone();
            }
        }
        let class_coords = if total == 0 {
            Vec::new()
        } else {
            match solve_affine_field(&mat, z_vec, total, &z)? {
                AffineSolutionField::Consistent { particular, .. } => particular[nb..].to_vec(),
                AffineSolutionField::Inconsistent { .. } => {
                    return Err(AlgebraError::OutOfScope {
                        detail: "cocycle could not be decomposed into B^1 + H^1 reps".to_owned(),
                    });
                }
            }
        };
        Ok(CocycleCheckField {
            is_cocycle: true,
            is_zero_class,
            coboundary_witness,
            class_coords,
        })
    }
}

/// 整数環 `Z` 上のコホモロジー計算結果（自由階数＋torsion 不変因子）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntegerCohomology {
    pub h0: CohomologyGroup,
    pub h0_basis: Vec<Vec<BigInt>>,
    pub h1: CohomologyGroup,
    pub h1_cycle_basis: Vec<Vec<BigInt>>,
    pub h2: CohomologyGroup,
}

/// 整数 1-cocycle のコホモロジー類判定結果（`Z` 零性・`Q` への係数変更での零性・torsion 位数）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CocycleCheckZ {
    pub is_cocycle: bool,
    pub is_zero_in_z: bool,
    pub coboundary_witness_z: Option<Vec<BigInt>>,
    pub is_zero_in_q: bool,
    /// `is_zero_in_z == false && is_zero_in_q == true` のときの最小正整数位数 `m > 1`。
    pub torsion_order: Option<BigInt>,
}

impl CochainComplex<BigInt> {
    /// 整数係数上の `H^0, H^1, H^2`（自由階数＋torsion 不変因子）を Smith 標準形で厳密計算する。
    pub fn cohomology_z(&self) -> Result<IntegerCohomology, AlgebraError> {
        // H^0 = ker(d^0)
        let snf0 = smith_normal_form_z(&self.d0, self.dim0)?;
        let mut h0_basis = Vec::new();
        for free_col in snf0.rank..self.dim0 {
            h0_basis.push(snf0.v.iter().map(|r| r[free_col].clone()).collect());
        }
        let h0 = CohomologyGroup::free(h0_basis.len());

        // Z^1 = ker(d^1) の Z-基底
        let snf1 = smith_normal_form_z(&self.d1, self.dim1)?;
        let mut h1_cycle_basis: Vec<Vec<BigInt>> = Vec::new();
        for free_col in snf1.rank..self.dim1 {
            h1_cycle_basis.push(snf1.v.iter().map(|r| r[free_col].clone()).collect());
        }
        let z1_rank = h1_cycle_basis.len();

        // B^1 = im(d^0) ⊆ Z^1 の各列を h1_cycle_basis 上の整数座標へ変換する。
        let h1 = if z1_rank == 0 {
            CohomologyGroup::free(0)
        } else if self.dim0 == 0 {
            CohomologyGroup::free(z1_rank)
        } else {
            let mut basis_mat = vec![vec![BigInt::zero(); z1_rank]; self.dim1];
            for (col, z_vec) in h1_cycle_basis.iter().enumerate() {
                for (row, val) in z_vec.iter().enumerate() {
                    basis_mat[row][col] = val.clone();
                }
            }
            // 不変行列 `basis_mat` の Smith 標準形をループ外で 1 回だけ計算し、各列を変換する。
            let snf_basis = smith_normal_form_z(&basis_mat, z1_rank)?;
            let mut b_in_z1 = vec![vec![BigInt::zero(); self.dim0]; z1_rank];
            for col in 0..self.dim0 {
                let d0_col: Vec<BigInt> = self.d0.iter().map(|r| r[col].clone()).collect();
                let u_rhs = mat_vec(&snf_basis.u, &d0_col, &BigInt::zero());
                if u_rhs[snf_basis.rank..].iter().any(|v| !v.is_zero()) {
                    return Err(AlgebraError::OutOfScope {
                        detail: "im(d^0) is not contained in ker(d^1) over Z".to_owned(),
                    });
                }
                let mut y = vec![BigInt::zero(); z1_rank];
                for i in 0..snf_basis.rank {
                    let diag = &snf_basis.diagonals[i];
                    if !(&u_rhs[i] % diag).is_zero() {
                        return Err(AlgebraError::OutOfScope {
                            detail: "im(d^0) is not contained in ker(d^1) over Z".to_owned(),
                        });
                    }
                    y[i] = &u_rhs[i] / diag;
                }
                let particular = mat_vec(&snf_basis.v, &y, &BigInt::zero());
                for row in 0..z1_rank {
                    b_in_z1[row][col] = particular[row].clone();
                }
            }
            let snf_b = smith_normal_form_z(&b_in_z1, self.dim0)?;
            let free_rank = z1_rank - snf_b.rank;
            let torsion_invariants: Vec<BigInt> = snf_b
                .diagonals
                .into_iter()
                .filter(|d| *d > BigInt::one())
                .collect();
            CohomologyGroup {
                free_rank,
                torsion_invariants,
            }
        };

        // H^2 = C^2 / im(d^1)
        let h2_free = self.dim2 - snf1.rank;
        let h2_torsion: Vec<BigInt> = snf1
            .diagonals
            .into_iter()
            .filter(|d| *d > BigInt::one())
            .collect();
        let h2 = CohomologyGroup {
            free_rank: h2_free,
            torsion_invariants: h2_torsion,
        };

        Ok(IntegerCohomology {
            h0,
            h0_basis,
            h1,
            h1_cycle_basis,
            h2,
        })
    }

    /// 整数 1-cocycle の `H^1(C_Z)` での零性・`H^1(C_Q)` での零性・torsion 位数を厳密判定する。
    pub fn check_h1_cocycle_z(&self, z_vec: &[BigInt]) -> Result<CocycleCheckZ, AlgebraError> {
        let d1z = self.apply_d1(z_vec)?;
        if !d1z.iter().all(BigInt::is_zero) {
            return Ok(CocycleCheckZ {
                is_cocycle: false,
                is_zero_in_z: false,
                coboundary_witness_z: None,
                is_zero_in_q: false,
                torsion_order: None,
            });
        }
        // 単一の Smith 標準形 U * d^0 * V = D から Z 零性・Q 零性・最小 torsion 位数を一括判定する。
        let snf0 = smith_normal_form_z(&self.d0, self.dim0)?;
        let uz = mat_vec(&snf0.u, z_vec, &BigInt::zero());
        if uz[snf0.rank..].iter().any(|v| !v.is_zero()) {
            return Ok(CocycleCheckZ {
                is_cocycle: true,
                is_zero_in_z: false,
                coboundary_witness_z: None,
                is_zero_in_q: false,
                torsion_order: None,
            });
        }
        let mut y = vec![BigInt::zero(); self.dim0];
        let mut divisible_over_z = true;
        for (i, diag) in snf0.diagonals.iter().enumerate() {
            if !(&uz[i] % diag).is_zero() {
                divisible_over_z = false;
                break;
            }
            y[i] = &uz[i] / diag;
        }
        if divisible_over_z {
            let witness = mat_vec(&snf0.v, &y, &BigInt::zero());
            return Ok(CocycleCheckZ {
                is_cocycle: true,
                is_zero_in_z: true,
                coboundary_witness_z: Some(witness),
                is_zero_in_q: true,
                torsion_order: None,
            });
        }
        // Q 上では可解だが Z 上では非可解: 最小正整数位数 m = lcm_i (d_i / gcd(d_i, (Uz)_i)) > 1
        let mut order = BigInt::one();
        for (i, diag) in snf0.diagonals.iter().enumerate() {
            let g = diag.gcd(&uz[i]);
            let factor = diag / g;
            order = order.lcm(&factor);
        }
        Ok(CocycleCheckZ {
            is_cocycle: true,
            is_zero_in_z: false,
            coboundary_witness_z: None,
            is_zero_in_q: true,
            torsion_order: Some(order),
        })
    }
}

/// 次数 0–2 の cochain 射 `f = (f^0, f^1, f^2): C^\bullet -> D^\bullet`。
/// 構築時（`CochainMap::new`）および `induced_field` 適用時に可換性を検証する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CochainMap<C: RingCoeff> {
    f0: Vec<Vec<C>>,
    f1: Vec<Vec<C>>,
    f2: Vec<Vec<C>>,
}

/// 誘導コホモロジー写像 `H^i(f)` の核・像・余核の次元と単射/全射/同型判定。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InducedDegreeMap {
    pub src_dim: usize,
    pub dst_dim: usize,
    pub ker_dim: usize,
    pub im_dim: usize,
    pub coker_dim: usize,
    pub injective: bool,
    pub surjective: bool,
    pub isomorphism: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InducedCohomologyMapField {
    pub h0: InducedDegreeMap,
    pub h1: InducedDegreeMap,
    pub h2: InducedDegreeMap,
}

fn validate_cochain_map<C: RingCoeff>(
    src: &CochainComplex<C>,
    dst: &CochainComplex<C>,
    f0: &[Vec<C>],
    f1: &[Vec<C>],
    f2: &[Vec<C>],
) -> Result<(), AlgebraError> {
    check_same_ring(&src.zero_coeff, &dst.zero_coeff)?;
    for (mat, exp_rows, exp_cols) in [
        (f0, dst.dim0, src.dim0),
        (f1, dst.dim1, src.dim1),
        (f2, dst.dim2, src.dim2),
    ] {
        if mat.len() != exp_rows {
            return Err(AlgebraError::ArityMismatch {
                expected: exp_rows,
                actual: mat.len(),
            });
        }
        for row in mat {
            if row.len() != exp_cols {
                return Err(AlgebraError::ArityMismatch {
                    expected: exp_cols,
                    actual: row.len(),
                });
            }
            for v in row {
                check_same_ring(&src.zero_coeff, v)?;
            }
        }
    }
    let lhs0 = mat_mul(&dst.d0, f0, src.dim0, &src.zero_coeff);
    let rhs0 = mat_mul(f1, &src.d0, src.dim0, &src.zero_coeff);
    if lhs0 != rhs0 {
        return Err(AlgebraError::OutOfScope {
            detail: "cochain map commutativity d_dst^0 * f^0 = f^1 * d_src^0 violated".to_owned(),
        });
    }
    let lhs1 = mat_mul(&dst.d1, f1, src.dim1, &src.zero_coeff);
    let rhs1 = mat_mul(f2, &src.d1, src.dim1, &src.zero_coeff);
    if lhs1 != rhs1 {
        return Err(AlgebraError::OutOfScope {
            detail: "cochain map commutativity d_dst^1 * f^1 = f^2 * d_src^1 violated".to_owned(),
        });
    }
    Ok(())
}

impl<C: RingCoeff> CochainMap<C> {
    pub fn f0(&self) -> &[Vec<C>] {
        &self.f0
    }

    pub fn f1(&self) -> &[Vec<C>] {
        &self.f1
    }

    pub fn f2(&self) -> &[Vec<C>] {
        &self.f2
    }

    /// 可換性 `d_D^0 f^0 = f^1 d_C^0` と `d_D^1 f^1 = f^2 d_C^1` を検証して構築する。
    pub fn new(
        src: &CochainComplex<C>,
        dst: &CochainComplex<C>,
        f0: Vec<Vec<C>>,
        f1: Vec<Vec<C>>,
        f2: Vec<Vec<C>>,
    ) -> Result<Self, AlgebraError> {
        validate_cochain_map(src, dst, &f0, &f1, &f2)?;
        Ok(Self { f0, f1, f2 })
    }
}

impl<C: FieldCoeff> CochainMap<C> {
    /// 体係数上の誘導写像 `H^0(f), H^1(f), H^2(f)` の核・像・余核を厳密計算する。
    /// 別の複体対が渡された場合も fail-closed に可換性を再検証する。
    pub fn induced_field(
        &self,
        src: &CochainComplex<C>,
        dst: &CochainComplex<C>,
    ) -> Result<InducedCohomologyMapField, AlgebraError> {
        validate_cochain_map(src, dst, &self.f0, &self.f1, &self.f2)?;
        let z = src.zero_coeff.zero_like();
        let sc = src.cohomology_field()?;
        let dc = dst.cohomology_field()?;

        // H^0(f): 各 src H^0 基底元の f0 像を dst H^0 基底座標へ展開。
        let h0 = induced_from_bases(
            &sc.h0_basis,
            &[],
            &dc.h0_basis,
            &self.f0,
            dst.dim0,
            &z,
        )?;
        // H^1(f): 各 src H^1 代表元を f1 で送り、dst B^1 + dst H^1 代表元で座標展開。
        let h1 = induced_from_bases(
            &sc.h1_rep_basis,
            &dc.h1_coboundary_basis,
            &dc.h1_rep_basis,
            &self.f1,
            dst.dim1,
            &z,
        )?;
        // H^2(f): C^2 / im(d^1) の代表元基底を構成して計算。
        let src_b2 = independent_vectors_field(&matrix_columns(&src.d1, src.dim1), src.dim2, &z)?;
        let src_std2 = standard_basis(src.dim2, &z);
        let src_h2_reps = quotient_complement_basis_field(&src_b2, &src_std2, src.dim2, &z)?;
        let dst_b2 = independent_vectors_field(&matrix_columns(&dst.d1, dst.dim1), dst.dim2, &z)?;
        let dst_std2 = standard_basis(dst.dim2, &z);
        let dst_h2_reps = quotient_complement_basis_field(&dst_b2, &dst_std2, dst.dim2, &z)?;
        let h2 = induced_from_bases(
            &src_h2_reps,
            &dst_b2,
            &dst_h2_reps,
            &self.f2,
            dst.dim2,
            &z,
        )?;

        Ok(InducedCohomologyMapField { h0, h1, h2 })
    }
}

fn induced_from_bases<C: FieldCoeff>(
    src_reps: &[Vec<C>],
    dst_coboundaries: &[Vec<C>],
    dst_reps: &[Vec<C>],
    map_mat: &[Vec<C>],
    dst_ambient_dim: usize,
    zero: &C,
) -> Result<InducedDegreeMap, AlgebraError> {
    let s_dim = src_reps.len();
    let d_dim = dst_reps.len();
    if s_dim == 0 || d_dim == 0 {
        return Ok(InducedDegreeMap {
            src_dim: s_dim,
            dst_dim: d_dim,
            ker_dim: s_dim,
            im_dim: 0,
            coker_dim: d_dim,
            injective: s_dim == 0,
            surjective: d_dim == 0,
            isomorphism: s_dim == 0 && d_dim == 0,
        });
    }
    let nb = dst_coboundaries.len();
    let total = nb + d_dim;
    let mut basis_mat = vec![vec![zero.zero_like(); total]; dst_ambient_dim];
    for (col, v) in dst_coboundaries.iter().chain(dst_reps).enumerate() {
        for (row, val) in v.iter().enumerate() {
            basis_mat[row][col] = val.clone();
        }
    }
    let mut induced = vec![vec![zero.zero_like(); s_dim]; d_dim];
    for (col, rep) in src_reps.iter().enumerate() {
        let img = mat_vec(map_mat, rep, zero);
        match solve_affine_field(&basis_mat, &img, total, zero)? {
            AffineSolutionField::Consistent { particular, .. } => {
                for row in 0..d_dim {
                    induced[row][col] = particular[nb + row].clone();
                }
            }
            AffineSolutionField::Inconsistent { .. } => {
                return Err(AlgebraError::OutOfScope {
                    detail: "cochain map image did not land in target cycle subspace".to_owned(),
                });
            }
        }
    }
    let im_dim = rref_field(&induced, s_dim, zero)?.rank;
    let ker_dim = s_dim - im_dim;
    let coker_dim = d_dim - im_dim;
    Ok(InducedDegreeMap {
        src_dim: s_dim,
        dst_dim: d_dim,
        ker_dim,
        im_dim,
        coker_dim,
        injective: ker_dim == 0,
        surjective: coker_dim == 0,
        isomorphism: ker_dim == 0 && coker_dim == 0,
    })
}

fn kernel_basis_field<C: FieldCoeff>(
    mat: &[Vec<C>],
    num_cols: usize,
    zero: &C,
) -> Result<Vec<Vec<C>>, AlgebraError> {
    let rhs = vec![zero.zero_like(); mat.len()];
    match solve_affine_field(mat, &rhs, num_cols, zero)? {
        AffineSolutionField::Consistent { kernel_basis, .. } => Ok(kernel_basis),
        AffineSolutionField::Inconsistent { .. } => Err(AlgebraError::OutOfScope {
            detail: "homogeneous field system unexpectedly inconsistent".to_owned(),
        }),
    }
}

fn matrix_columns<C: RingCoeff>(mat: &[Vec<C>], num_cols: usize) -> Vec<Vec<C>> {
    (0..num_cols)
        .map(|c| mat.iter().map(|r| r[c].clone()).collect())
        .collect()
}

fn independent_vectors_field<C: FieldCoeff>(
    vectors: &[Vec<C>],
    dim: usize,
    zero: &C,
) -> Result<Vec<Vec<C>>, AlgebraError> {
    if vectors.is_empty() || dim == 0 {
        return Ok(Vec::new());
    }
    let mut mat = vec![vec![zero.zero_like(); vectors.len()]; dim];
    for (col, v) in vectors.iter().enumerate() {
        for (row, val) in v.iter().enumerate() {
            mat[row][col] = val.clone();
        }
    }
    let rref = rref_field(&mat, vectors.len(), zero)?;
    Ok(rref
        .pivot_cols
        .into_iter()
        .map(|col| vectors[col].clone())
        .collect())
}

fn quotient_complement_basis_field<C: FieldCoeff>(
    subspace_basis: &[Vec<C>],
    ambient_basis: &[Vec<C>],
    dim: usize,
    zero: &C,
) -> Result<Vec<Vec<C>>, AlgebraError> {
    let nb = subspace_basis.len();
    let total = nb + ambient_basis.len();
    if total == 0 || dim == 0 {
        return Ok(Vec::new());
    }
    let mut mat = vec![vec![zero.zero_like(); total]; dim];
    for (col, v) in subspace_basis.iter().chain(ambient_basis).enumerate() {
        for (row, val) in v.iter().enumerate() {
            mat[row][col] = val.clone();
        }
    }
    let rref = rref_field(&mat, total, zero)?;
    Ok(rref
        .pivot_cols
        .into_iter()
        .filter(|&col| col >= nb)
        .map(|col| ambient_basis[col - nb].clone())
        .collect())
}

fn standard_basis<C: RingCoeff>(dim: usize, zero: &C) -> Vec<Vec<C>> {
    let z = zero.zero_like();
    let o = z.one_like();
    (0..dim)
        .map(|i| {
            let mut v = vec![z.clone(); dim];
            v[i] = o.clone();
            v
        })
        .collect()
}

pub fn mat_vec<C: RingCoeff>(mat: &[Vec<C>], x: &[C], zero: &C) -> Vec<C> {
    mat.iter()
        .map(|row| {
            let mut acc = zero.zero_like();
            for (a, v) in row.iter().zip(x) {
                if !a.coeff_is_zero() && !v.coeff_is_zero() {
                    acc = acc.add_ref(&a.mul_ref(v));
                }
            }
            acc
        })
        .collect()
}

pub fn mat_mul<C: RingCoeff>(
    lhs: &[Vec<C>],
    rhs: &[Vec<C>],
    rhs_cols: usize,
    zero: &C,
) -> Vec<Vec<C>> {
    let m = lhs.len();
    let mut out = vec![vec![zero.zero_like(); rhs_cols]; m];
    for i in 0..m {
        for (k, aik) in lhs[i].iter().enumerate() {
            if aik.coeff_is_zero() {
                continue;
            }
            for j in 0..rhs_cols {
                let bkj = &rhs[k][j];
                if !bkj.coeff_is_zero() {
                    out[i][j] = out[i][j].add_ref(&aik.mul_ref(bkj));
                }
            }
        }
    }
    out
}
