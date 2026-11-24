//! Z / Q アフィン系解法（Q の RREF、Z の Smith 標準形）、F_p 有限全列挙、
//! および係数域・点集合域に応じた沈黙（`SilenceReason`）判定（G-141 D4–D6 / AC5）。

use crate::algebra::artin::{AffineSolutionField, solve_affine_field};
use crate::algebra::groebner::rabinowitsch_solve;
use crate::algebra::poly::{AlgebraError, Poly, VarOrder};
use crate::algebra::scalar::{FpElem, Rat};
use crate::ir::change::PointDomain;
use crate::ir::result::{EmptyWitness, SilenceReason};
use archsig_common::prime::is_prime;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// F_p 有限全列挙の既定上限（`p^m` がこれを超える場合は部分列挙を返さず沈黙する）。
pub const DEFAULT_MAX_FP_POINTS: usize = 65_536;

/// Q アフィン系 `L x = b` の全解または不存在 certificate（G-141 D4）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AffineSolutionQ {
    Consistent {
        particular: Vec<Rat>,
        kernel_basis: Vec<Vec<Rat>>,
        verified: bool,
    },
    Inconsistent {
        /// `certificate * L == 0` かつ `certificate * b != 0` を満たす行ベクトル。
        certificate: Vec<Rat>,
        verified: bool,
    },
}

/// Z アフィン系 `L x = b` の Smith 標準形による全解または不存在 certificate（G-141 D4）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AffineSolutionZ {
    Consistent {
        particular: Vec<BigInt>,
        kernel_basis: Vec<Vec<BigInt>>,
        smith_diagonals: Vec<BigInt>,
        verified: bool,
    },
    Inconsistent {
        /// `U L V = diag(d_1, ..., d_r, 0, ...)` で `d_i ∤ (U b)_i` または零行非零右辺の行ベクトル。
        row_certificate: Vec<BigInt>,
        divisor: Option<BigInt>,
        rhs_value: BigInt,
        verified: bool,
    },
}

/// F_p 有限全列挙の結果。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FpEnumerationResult {
    pub modulus: BigUint,
    pub total_domain_size: usize,
    pub solutions: Vec<Vec<FpElem>>,
}

/// 一般多項式系 `(equations, invertibles)` の点集合域に応じた判定結果（AC5(b)）。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SystemPointOutcome {
    /// 代数閉包上の幾何点が非空（`1 not in I`）。
    NonEmptyOverClosure { parameter_equations: Vec<Poly<Rat>> },
    /// Q アフィン系の完全解。
    AffineQ(AffineSolutionQ),
    /// Z アフィン系の完全解。
    AffineZ(AffineSolutionZ),
    /// F_p 上の全解列挙。
    FiniteField(FpEnumerationResult),
    /// 空集合（不存在証明 witness 付き）。
    Empty { witness: Option<EmptyWitness> },
    /// 適用条件外による沈黙（例: `x^2 + 1 = 0` の Q 点 / Z 点存在判定）。
    Undetermined(SilenceReason),
}

/// 整数行列の Smith 標準形 `U * A * V = diag(d_1, ..., d_r, 0, ...)`。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmithFormZ {
    pub u: Vec<Vec<BigInt>>,
    pub v: Vec<Vec<BigInt>>,
    pub diagonals: Vec<BigInt>,
    pub rank: usize,
}

/// 整数行列 `matrix` (`m x num_cols`) の Smith 標準形を計算する。
pub fn smith_normal_form_z(
    matrix: &[Vec<BigInt>],
    num_cols: usize,
) -> Result<SmithFormZ, AlgebraError> {
    let m = matrix.len();
    for row in matrix {
        if row.len() != num_cols {
            return Err(AlgebraError::ArityMismatch {
                expected: num_cols,
                actual: row.len(),
            });
        }
    }
    let mut d: Vec<Vec<BigInt>> = matrix.to_vec();
    let mut u = identity_z(m);
    let mut v = identity_z(num_cols);

    let mut k = 0usize;
    while k < m && k < num_cols {
        let Some((pr, pc)) = find_min_nonzero_pivot(&d, k, m, num_cols) else {
            break;
        };
        if pr != k {
            d.swap(k, pr);
            u.swap(k, pr);
        }
        if pc != k {
            swap_cols(&mut d, k, pc);
            swap_cols(&mut v, k, pc);
        }
        loop {
            if d[k][k].is_negative() {
                negate_row(&mut d, k);
                negate_row(&mut u, k);
            }
            let mut changed = false;
            for r in (k + 1)..m {
                if !d[r][k].is_zero() {
                    let q = d[r][k].div_floor(&d[k][k]);
                    row_sub_mul(&mut d, r, k, &q);
                    row_sub_mul(&mut u, r, k, &q);
                    if !d[r][k].is_zero() {
                        d.swap(k, r);
                        u.swap(k, r);
                        changed = true;
                        break;
                    }
                }
            }
            if changed {
                continue;
            }
            for c in (k + 1)..num_cols {
                if !d[k][c].is_zero() {
                    let q = d[k][c].div_floor(&d[k][k]);
                    col_sub_mul(&mut d, c, k, &q);
                    col_sub_mul(&mut v, c, k, &q);
                    if !d[k][c].is_zero() {
                        swap_cols(&mut d, k, c);
                        swap_cols(&mut v, k, c);
                        changed = true;
                        break;
                    }
                }
            }
            if changed {
                continue;
            }
            if d[k][k].is_negative() {
                negate_row(&mut d, k);
                negate_row(&mut u, k);
            }
            let mut non_div = None;
            'outer: for r in (k + 1)..m {
                for c in (k + 1)..num_cols {
                    if !(&d[r][c] % &d[k][k]).is_zero() {
                        non_div = Some(r);
                        break 'outer;
                    }
                }
            }
            if let Some(r) = non_div {
                row_add(&mut d, k, r);
                row_add(&mut u, k, r);
                continue;
            }
            break;
        }
        k += 1;
    }
    let diagonals: Vec<BigInt> = (0..k).map(|i| d[i][i].clone()).collect();
    Ok(SmithFormZ {
        u,
        v,
        diagonals,
        rank: k,
    })
}

/// Q 上の線形系 `L x = b` を共通体 RREF エンジン（`solve_affine_field`）で解き、独立検算する。
pub fn solve_affine_q(
    matrix: &[Vec<Rat>],
    rhs: &[Rat],
    num_vars: usize,
) -> Result<AffineSolutionQ, AlgebraError> {
    match solve_affine_field(matrix, rhs, num_vars, &Rat::zero())? {
        AffineSolutionField::Consistent {
            particular,
            kernel_basis,
            verified,
        } => Ok(AffineSolutionQ::Consistent {
            particular,
            kernel_basis,
            verified,
        }),
        AffineSolutionField::Inconsistent {
            certificate,
            verified,
        } => Ok(AffineSolutionQ::Inconsistent {
            certificate,
            verified,
        }),
    }
}

/// Z 上の線形系 `L x = b` を Smith 標準形 `U L V = diag(d_1, ..., d_r, 0, ...)` で解き、独立検算する（G-141 D4）。
pub fn solve_affine_z(
    matrix: &[Vec<BigInt>],
    rhs: &[BigInt],
    num_vars: usize,
) -> Result<AffineSolutionZ, AlgebraError> {
    let m = matrix.len();
    if rhs.len() != m {
        return Err(AlgebraError::ArityMismatch {
            expected: m,
            actual: rhs.len(),
        });
    }
    let snf = smith_normal_form_z(matrix, num_vars)?;
    let rank = snf.rank;
    let u = snf.u;
    let v = snf.v;
    let beta: Vec<BigInt> = (0..m)
        .map(|r| {
            let mut acc = BigInt::zero();
            for c in 0..m {
                acc += &u[r][c] * &rhs[c];
            }
            acc
        })
        .collect();

    // 不整合検査: d_i ∤ beta_i または零行で beta_j != 0。
    for (i, diag) in snf.diagonals.iter().enumerate() {
        if !(&beta[i] % diag).is_zero() {
            let cert = u[i].clone();
            let verified =
                verify_inconsistent_z(matrix, rhs, &cert, Some(diag), &beta[i], num_vars);
            return Ok(AffineSolutionZ::Inconsistent {
                row_certificate: cert,
                divisor: Some(diag.clone()),
                rhs_value: beta[i].clone(),
                verified,
            });
        }
    }
    for j in rank..m {
        if !beta[j].is_zero() {
            let cert = u[j].clone();
            let verified = verify_inconsistent_z(matrix, rhs, &cert, None, &beta[j], num_vars);
            return Ok(AffineSolutionZ::Inconsistent {
                row_certificate: cert,
                divisor: None,
                rhs_value: beta[j].clone(),
                verified,
            });
        }
    }

    let mut y0 = vec![BigInt::zero(); num_vars];
    for (i, diag) in snf.diagonals.iter().enumerate() {
        y0[i] = &beta[i] / diag;
    }
    let smith_diagonals = snf.diagonals;

    let particular: Vec<BigInt> = (0..num_vars)
        .map(|row| {
            let mut acc = BigInt::zero();
            for col in 0..num_vars {
                acc += &v[row][col] * &y0[col];
            }
            acc
        })
        .collect();

    let mut kernel_basis = Vec::new();
    for free_col in rank..num_vars {
        let col_vec: Vec<BigInt> = v.iter().map(|row| row[free_col].clone()).collect();
        kernel_basis.push(col_vec);
    }

    let verified = verify_consistent_z(matrix, rhs, &particular, &kernel_basis);
    Ok(AffineSolutionZ::Consistent {
        particular,
        kernel_basis,
        smith_diagonals,
        verified,
    })
}

fn identity_z(n: usize) -> Vec<Vec<BigInt>> {
    (0..n)
        .map(|i| {
            let mut row = vec![BigInt::zero(); n];
            row[i] = BigInt::one();
            row
        })
        .collect()
}

fn find_min_nonzero_pivot(
    d: &[Vec<BigInt>],
    start: usize,
    m: usize,
    n: usize,
) -> Option<(usize, usize)> {
    let mut best: Option<(usize, usize, BigInt)> = None;
    for (r, row) in d.iter().enumerate().take(m).skip(start) {
        for (c, val) in row.iter().enumerate().take(n).skip(start) {
            if !val.is_zero() {
                let abs = val.abs();
                if best.as_ref().is_none_or(|(_, _, b)| abs < *b) {
                    best = Some((r, c, abs));
                }
            }
        }
    }
    best.map(|(r, c, _)| (r, c))
}

fn swap_cols(mat: &mut [Vec<BigInt>], c1: usize, c2: usize) {
    for row in mat.iter_mut() {
        row.swap(c1, c2);
    }
}

fn row_sub_mul(mat: &mut [Vec<BigInt>], target: usize, src: usize, factor: &BigInt) {
    let src_row = mat[src].clone();
    for (dst, s) in mat[target].iter_mut().zip(&src_row) {
        *dst -= factor * s;
    }
}

fn row_add(mat: &mut [Vec<BigInt>], target: usize, src: usize) {
    let src_row = mat[src].clone();
    for (dst, s) in mat[target].iter_mut().zip(&src_row) {
        *dst += s;
    }
}

fn col_sub_mul(mat: &mut [Vec<BigInt>], target: usize, src: usize, factor: &BigInt) {
    for row in mat.iter_mut() {
        let sub = factor * &row[src];
        row[target] -= sub;
    }
}

fn negate_row(mat: &mut [Vec<BigInt>], row_idx: usize) {
    for v in &mut mat[row_idx] {
        *v = -v.clone();
    }
}

fn verify_consistent_z(
    matrix: &[Vec<BigInt>],
    rhs: &[BigInt],
    particular: &[BigInt],
    kernel_basis: &[Vec<BigInt>],
) -> bool {
    for (row, target) in matrix.iter().zip(rhs) {
        let mut acc = BigInt::zero();
        for (a, x) in row.iter().zip(particular) {
            acc += a * x;
        }
        if acc != *target {
            return false;
        }
    }
    for v in kernel_basis {
        for row in matrix {
            let mut acc = BigInt::zero();
            for (a, x) in row.iter().zip(v) {
                acc += a * x;
            }
            if !acc.is_zero() {
                return false;
            }
        }
    }
    true
}

fn verify_inconsistent_z(
    matrix: &[Vec<BigInt>],
    rhs: &[BigInt],
    row_cert: &[BigInt],
    divisor: Option<&BigInt>,
    rhs_value: &BigInt,
    num_vars: usize,
) -> bool {
    let mut lhs_row = vec![BigInt::zero(); num_vars];
    for (r_idx, row) in matrix.iter().enumerate() {
        for c in 0..num_vars {
            lhs_row[c] += &row_cert[r_idx] * &row[c];
        }
    }
    let mut actual_rhs = BigInt::zero();
    for (c, b) in row_cert.iter().zip(rhs) {
        actual_rhs += c * b;
    }
    if actual_rhs != *rhs_value {
        return false;
    }
    match divisor {
        Some(d) => {
            !d.is_zero() && lhs_row.iter().all(|v| (v % d).is_zero()) && !(actual_rhs % d).is_zero()
        }
        None => lhs_row.iter().all(BigInt::is_zero) && !actual_rhs.is_zero(),
    }
}

/// 有限体 `F_p` 上の多項式系 `V(equations) ∩ D(invertibles)` を全列挙する（G-141 D4）。
///
/// 全候補数 `p^m` が `max_points` を超える場合は部分列挙を完全解として返さず `SilenceReason` を返す。
pub fn solve_fp_enumeration(
    equations: &[Poly<FpElem>],
    invertibles: &[Poly<FpElem>],
    num_vars: usize,
    modulus: &BigUint,
    max_points: usize,
) -> Result<FpEnumerationResult, SilenceReason> {
    if !is_prime(modulus) {
        return Err(SilenceReason::UnsupportedCoeffRing {
            domain: crate::ir::term::CoeffDomain::Fp(modulus.clone()),
            detail: format!("modulus `{modulus}` is not prime"),
        });
    }
    for poly in equations.iter().chain(invertibles) {
        if poly.num_vars() != num_vars {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "finite_field_variable_arity".to_owned(),
                detail: format!(
                    "polynomial has {} variables, expected {num_vars}",
                    poly.num_vars()
                ),
            });
        }
        if poly.zero_coeff().modulus() != modulus {
            return Err(SilenceReason::UnsupportedCoeffRing {
                domain: crate::ir::term::CoeffDomain::Fp(poly.zero_coeff().modulus().clone()),
                detail: format!(
                    "polynomial modulus `{}` does not match target modulus `{modulus}`",
                    poly.zero_coeff().modulus()
                ),
            });
        }
    }

    if num_vars == 0 {
        if max_points == 0 {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "finite_field_enumeration_size".to_owned(),
                detail: "domain size 1 exceeds bound (0)".to_owned(),
            });
        }
        let mut eq_ok = true;
        for eq in equations {
            let val = eq
                .eval_at(&[])
                .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
                    condition: "finite_field_evaluation".to_owned(),
                    detail: e.to_string(),
                })?;
            if !val.is_zero() {
                eq_ok = false;
                break;
            }
        }
        let mut inv_ok = true;
        if eq_ok {
            for inv in invertibles {
                let val =
                    inv.eval_at(&[])
                        .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
                            condition: "finite_field_evaluation".to_owned(),
                            detail: e.to_string(),
                        })?;
                if val.is_zero() {
                    inv_ok = false;
                    break;
                }
            }
        }
        return Ok(FpEnumerationResult {
            modulus: modulus.clone(),
            total_domain_size: 1,
            solutions: if eq_ok && inv_ok {
                vec![vec![]]
            } else {
                vec![]
            },
        });
    }

    let Some(p_usize) = modulus.to_usize() else {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "finite_field_enumeration_size".to_owned(),
            detail: format!("prime modulus `{modulus}` exceeds enumeration bound ({max_points})"),
        });
    };
    let mut total = 1usize;
    if total > max_points {
        return Err(SilenceReason::ApplicabilityConditionNotMet {
            condition: "finite_field_enumeration_size".to_owned(),
            detail: format!("domain size exceeds bound ({max_points})"),
        });
    }
    for _ in 0..num_vars {
        let Some(next) = total.checked_mul(p_usize) else {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "finite_field_enumeration_size".to_owned(),
                detail: format!("domain size {p_usize}^{num_vars} exceeds bound ({max_points})"),
            });
        };
        if next > max_points {
            return Err(SilenceReason::ApplicabilityConditionNotMet {
                condition: "finite_field_enumeration_size".to_owned(),
                detail: format!("domain size {p_usize}^{num_vars} exceeds bound ({max_points})"),
            });
        }
        total = next;
    }

    let field_elems: Vec<FpElem> = (0..p_usize)
        .map(|v| FpElem::from_checked_prime(BigInt::from(v), modulus.clone()))
        .collect();
    let mut solutions = Vec::new();
    let mut current = vec![field_elems[0].clone(); num_vars];
    for mut idx in 0..total {
        for slot in current.iter_mut().rev() {
            *slot = field_elems[idx % p_usize].clone();
            idx /= p_usize;
        }
        let mut eq_ok = true;
        for eq in equations {
            let val =
                eq.eval_at(&current)
                    .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
                        condition: "finite_field_evaluation".to_owned(),
                        detail: e.to_string(),
                    })?;
            if !val.is_zero() {
                eq_ok = false;
                break;
            }
        }
        if !eq_ok {
            continue;
        }
        let mut inv_ok = true;
        for inv in invertibles {
            let val =
                inv.eval_at(&current)
                    .map_err(|e| SilenceReason::ApplicabilityConditionNotMet {
                        condition: "finite_field_evaluation".to_owned(),
                        detail: e.to_string(),
                    })?;
            if val.is_zero() {
                inv_ok = false;
                break;
            }
        }
        if inv_ok {
            solutions.push(current.clone());
        }
    }

    Ok(FpEnumerationResult {
        modulus: modulus.clone(),
        total_domain_size: total,
        solutions,
    })
}

/// Q 上の多項式系 `(equations, invertibles)` を `PointDomain` に従って判定する（AC5(b) 沈黙規律）。
///
/// - `AlgebraicClosure`: Rabinowitsch + Gröbner 基底で `1 in I` を厳密判定。
/// - `RationalPoints`: 可逆条件なしの全式が affine なら `solve_affine_q` で完全判定。
///   非線形の場合はまず代数閉包空性（`1 in I`）を確認し、空なら `Empty`（Q 点も確実に不在）、
///   非空なら簡約基底が純 affine であれば `solve_affine_q`、なお非線形なら
///   `Undetermined(NonLinearRationalOrIntegerExistence)` を返す（例: `x^2 + 1 = 0`）。
/// - `IntegerPoints`: 整数係数 affine なら `solve_affine_z`、非整数係数アフィンや非線形は理由付き `Undetermined`。
pub fn solve_polynomial_system_q(
    equations: &[Poly<Rat>],
    invertibles: &[Poly<Rat>],
    vars: &VarOrder,
    point_domain: &PointDomain,
) -> SystemPointOutcome {
    for poly in equations.iter().chain(invertibles) {
        if poly.num_vars() != vars.len() {
            return SystemPointOutcome::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
                condition: "polynomial_variable_arity".to_owned(),
                detail: format!(
                    "polynomial has {} variables, expected {}",
                    poly.num_vars(),
                    vars.len()
                ),
            });
        }
    }
    match point_domain {
        PointDomain::AlgebraicClosure => match rabinowitsch_solve(equations, invertibles, vars) {
            Ok(rab) if rab.is_empty_over_closure => SystemPointOutcome::Empty {
                witness: rab.empty_witness,
            },
            Ok(rab) => SystemPointOutcome::NonEmptyOverClosure {
                parameter_equations: rab.parameter_equations,
            },
            Err(e) => {
                SystemPointOutcome::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
                    condition: "groebner_computation".to_owned(),
                    detail: e.to_string(),
                })
            }
        },
        PointDomain::RationalPoints => {
            if invertibles.is_empty() && equations.iter().all(Poly::is_affine) {
                let (mat, rhs) = extract_affine_q(equations, vars.len());
                return match solve_affine_q(&mat, &rhs, vars.len()) {
                    Ok(sol) => SystemPointOutcome::AffineQ(sol),
                    Err(e) => SystemPointOutcome::Undetermined(
                        SilenceReason::ApplicabilityConditionNotMet {
                            condition: "rational_affine_solver".to_owned(),
                            detail: e.to_string(),
                        },
                    ),
                };
            }
            match rabinowitsch_solve(equations, invertibles, vars) {
                Ok(rab) if rab.is_empty_over_closure => SystemPointOutcome::Empty {
                    witness: rab.empty_witness,
                },
                Ok(rab) => {
                    // 代数閉包上は非空。可逆条件がなく消去後基底が純 affine なら Q 点を厳密決定できる。
                    if invertibles.is_empty() && rab.parameter_equations.iter().all(Poly::is_affine)
                    {
                        let (mat, rhs) = extract_affine_q(&rab.parameter_equations, vars.len());
                        if let Ok(sol) = solve_affine_q(&mat, &rhs, vars.len()) {
                            return SystemPointOutcome::AffineQ(sol);
                        }
                    }
                    SystemPointOutcome::Undetermined(
                        SilenceReason::NonLinearRationalOrIntegerExistence {
                            point_domain: PointDomain::RationalPoints,
                            detail: "ideal is nonempty over algebraic closure, but rational point existence for nonlinear or open-condition systems is outside affine scope (G-141 D5–D6)".to_owned(),
                        },
                    )
                }
                Err(e) => {
                    SystemPointOutcome::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "groebner_computation".to_owned(),
                        detail: e.to_string(),
                    })
                }
            }
        }
        PointDomain::IntegerPoints => {
            if invertibles.is_empty() && equations.iter().all(Poly::is_affine) {
                return match extract_affine_z_from_q(equations, vars.len()) {
                    Some((mat, rhs)) => match solve_affine_z(&mat, &rhs, vars.len()) {
                        Ok(sol) => SystemPointOutcome::AffineZ(sol),
                        Err(e) => SystemPointOutcome::Undetermined(
                            SilenceReason::ApplicabilityConditionNotMet {
                                condition: "integer_affine_solver".to_owned(),
                                detail: e.to_string(),
                            },
                        ),
                    },
                    None => SystemPointOutcome::Undetermined(
                        SilenceReason::ApplicabilityConditionNotMet {
                            condition: "integer_coefficients_required".to_owned(),
                            detail: "affine equation contains non-integer rational coefficients; integer Smith solver requires Z coefficients".to_owned(),
                        },
                    ),
                };
            }
            match rabinowitsch_solve(equations, invertibles, vars) {
                Ok(rab) if rab.is_empty_over_closure => SystemPointOutcome::Empty {
                    witness: rab.empty_witness,
                },
                Ok(_) => SystemPointOutcome::Undetermined(
                    SilenceReason::NonLinearRationalOrIntegerExistence {
                        point_domain: PointDomain::IntegerPoints,
                        detail: "general nonlinear or open-condition integer point existence is outside Smith normal form affine scope (G-141 D4–D6)".to_owned(),
                    },
                ),
                Err(e) => {
                    SystemPointOutcome::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
                        condition: "groebner_computation".to_owned(),
                        detail: e.to_string(),
                    })
                }
            }
        }
        other => SystemPointOutcome::Undetermined(SilenceReason::ApplicabilityConditionNotMet {
            condition: "point_domain_dispatch".to_owned(),
            detail: format!("point domain `{other}` is not handled by Q polynomial solver"),
        }),
    }
}

fn extract_affine_q(equations: &[Poly<Rat>], num_vars: usize) -> (Vec<Vec<Rat>>, Vec<Rat>) {
    let mut matrix = Vec::with_capacity(equations.len());
    let mut rhs = Vec::with_capacity(equations.len());
    for poly in equations {
        let mut row = vec![Rat::zero(); num_vars];
        let mut constant = Rat::zero();
        for (mono, coeff) in poly.terms() {
            if mono.is_one() {
                constant = coeff.clone();
            } else if let Some((idx, _)) = mono.exps().iter().enumerate().find(|(_, e)| **e == 1) {
                row[idx] = coeff.clone();
            }
        }
        // `row * x + constant = 0`  <=>  `row * x = -constant`
        matrix.push(row);
        rhs.push(-constant);
    }
    (matrix, rhs)
}

fn extract_affine_z_from_q(
    equations: &[Poly<Rat>],
    num_vars: usize,
) -> Option<(Vec<Vec<BigInt>>, Vec<BigInt>)> {
    let (mat_q, rhs_q) = extract_affine_q(equations, num_vars);
    let mut mat_z = Vec::with_capacity(mat_q.len());
    let mut rhs_z = Vec::with_capacity(rhs_q.len());
    for (row, b) in mat_q.into_iter().zip(rhs_q) {
        if !b.den().is_one() {
            return None;
        }
        let mut row_z = Vec::with_capacity(num_vars);
        for v in row {
            if !v.den().is_one() {
                return None;
            }
            row_z.push(v.num().clone());
        }
        mat_z.push(row_z);
        rhs_z.push(b.num().clone());
    }
    Some((mat_z, rhs_z))
}
