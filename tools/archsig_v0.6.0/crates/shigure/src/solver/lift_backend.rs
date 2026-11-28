//! `shigure_lift` の係数環バックエンド（体 `Q` / `F_p` と整数環 `Z`）と共有文脈。

use crate::algebra::MonomialOrder;
use crate::algebra::artin::{AffineSolutionField, FiniteAlgebra, rref_field, solve_affine_field};
use crate::algebra::artin_quotient::SquareZeroExtension;
use crate::algebra::cochain::{CochainComplex, smith_normal_form_z};
use crate::algebra::linear::{AffineSolutionZ, solve_affine_z};
use crate::algebra::poly::{AlgebraError, Poly};
use crate::algebra::poly_expr::{ExprBindings, VarOrder};
use crate::algebra::scalar::{FpElem, Rat, RingCoeff};
use crate::algebra::syzygy::{
    FieldCoeff, SyzygyModule, compute_syzygies_field, compute_syzygies_z, ideal_membership_field,
};
use crate::ir::lift::LiftTaskSpec;
use crate::ir::result::SilenceReason;
use crate::ir::term::{PolyExpr, ScalarLit};
use crate::solver::lift_common::{lit_to_fp, lit_to_q, lit_to_z, map_lift_algebra_error};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

pub(crate) type AffineSolveOutput<C> = Option<(Vec<C>, Vec<Vec<C>>)>;

pub(crate) struct CohomologyAndCocycle<C: RingCoeff> {
    pub(crate) h0_dim: usize,
    pub(crate) h0_torsion: Vec<BigInt>,
    pub(crate) h1_dim: usize,
    pub(crate) h1_torsion: Vec<BigInt>,
    pub(crate) h0_basis: Vec<Vec<C>>,
    pub(crate) is_cocycle: bool,
    pub(crate) is_zero_class: bool,
    pub(crate) class_coords: Vec<String>,
    pub(crate) coboundary_witness: Option<Vec<C>>,
}

pub(crate) struct RawCechStats {
    pub(crate) h0_t_raw_dim: usize,
    pub(crate) h1_t_raw_dim: usize,
    pub(crate) d1_rank: usize,
}

/// 体係数（`Q` / `F_p`）と整数環 `Z` の計算核差分のみを切り出すバックエンドトレイト。
pub(crate) trait LiftRingBackend {
    type Coeff: RingCoeff;

    fn coeff_label(&self) -> String;
    fn zero(&self) -> Self::Coeff;
    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<Self::Coeff>, AlgebraError>;
    fn convert_lit(&self, lit: &ScalarLit) -> Result<Self::Coeff, AlgebraError>;
    fn build_truncated_ext(
        &self,
        var_name: &str,
        base_degree: usize,
    ) -> Result<SquareZeroExtension<Self::Coeff>, AlgebraError>;
    fn build_explicit_ext(
        &self,
        r_prime: FiniteAlgebra<Self::Coeff>,
        r_base: FiniteAlgebra<Self::Coeff>,
        projection: Vec<Vec<Self::Coeff>>,
    ) -> Result<SquareZeroExtension<Self::Coeff>, AlgebraError>;
    fn extract_kernel_coords(
        &self,
        ext: &SquareZeroExtension<Self::Coeff>,
        elem: &[Self::Coeff],
    ) -> Result<Vec<Self::Coeff>, AlgebraError>;
    fn solve_affine(
        &self,
        mat: &[Vec<Self::Coeff>],
        rhs: &[Self::Coeff],
        cols: usize,
    ) -> Result<AffineSolveOutput<Self::Coeff>, AlgebraError>;
    fn compute_syzygies(
        &self,
        law_polys: &[Poly<Self::Coeff>],
        vars: VarOrder,
        max_pairs: usize,
    ) -> Result<SyzygyModule<Self::Coeff>, SilenceReason>;
    fn cohomology_and_cocycle(
        &self,
        complex: &CochainComplex<Self::Coeff>,
        cocycle: &[Self::Coeff],
    ) -> Result<CohomologyAndCocycle<Self::Coeff>, AlgebraError>;
    fn raw_cech_stats(
        &self,
        complex_d: &CochainComplex<Self::Coeff>,
    ) -> Result<RawCechStats, AlgebraError>;
    fn check_obs_laws_supported(&self, has_obs_laws: bool) -> Result<(), SilenceReason>;
    fn ideal_membership(
        &self,
        poly: &Poly<Self::Coeff>,
        gens: &[Poly<Self::Coeff>],
        vars: &VarOrder,
        max_pairs: usize,
    ) -> Result<Option<Vec<Poly<Self::Coeff>>>, AlgebraError>;
}

pub(crate) trait FieldRingAdapter {
    type Coeff: FieldCoeff;

    fn coeff_label(&self) -> String;
    fn zero(&self) -> Self::Coeff;
    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<Self::Coeff>, AlgebraError>;
    fn convert_lit(&self, lit: &ScalarLit) -> Result<Self::Coeff, AlgebraError>;
    fn lift_mat_z(&self, mat: &[Vec<BigInt>]) -> Vec<Vec<Self::Coeff>>;
}

pub(crate) struct QFieldAdapter;

impl FieldRingAdapter for QFieldAdapter {
    type Coeff = Rat;

    fn coeff_label(&self) -> String {
        "Q".to_owned()
    }

    fn zero(&self) -> Rat {
        Rat::zero()
    }

    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<Rat>, AlgebraError> {
        Poly::from_expr_q(expr, bindings)
    }

    fn convert_lit(&self, lit: &ScalarLit) -> Result<Rat, AlgebraError> {
        lit_to_q(lit)
    }

    fn lift_mat_z(&self, mat: &[Vec<BigInt>]) -> Vec<Vec<Rat>> {
        crate::solver::diagnostics::lift_mat_z_to_q(mat)
    }
}

pub(crate) struct FpFieldAdapter {
    pub(crate) p: BigUint,
    pub(crate) zero_fp: FpElem,
}

impl FieldRingAdapter for FpFieldAdapter {
    type Coeff = FpElem;

    fn coeff_label(&self) -> String {
        format!("F_{}", self.p)
    }

    fn zero(&self) -> FpElem {
        self.zero_fp.clone()
    }

    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<FpElem>, AlgebraError> {
        Poly::from_expr_fp(expr, bindings, &self.p)
    }

    fn convert_lit(&self, lit: &ScalarLit) -> Result<FpElem, AlgebraError> {
        lit_to_fp(lit, &self.p)
    }

    fn lift_mat_z(&self, mat: &[Vec<BigInt>]) -> Vec<Vec<FpElem>> {
        crate::solver::diagnostics::lift_mat_z_to_fp(mat, &self.p)
    }
}

pub(crate) struct FieldLiftBackend<A: FieldRingAdapter>(pub(crate) A);

impl<A: FieldRingAdapter> LiftRingBackend for FieldLiftBackend<A> {
    type Coeff = A::Coeff;

    fn coeff_label(&self) -> String {
        self.0.coeff_label()
    }

    fn zero(&self) -> A::Coeff {
        self.0.zero()
    }

    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<A::Coeff>, AlgebraError> {
        self.0.expand_expr(expr, bindings)
    }

    fn convert_lit(&self, lit: &ScalarLit) -> Result<A::Coeff, AlgebraError> {
        self.0.convert_lit(lit)
    }

    fn build_truncated_ext(
        &self,
        var_name: &str,
        base_degree: usize,
    ) -> Result<SquareZeroExtension<A::Coeff>, AlgebraError> {
        SquareZeroExtension::truncated_step_field(var_name, base_degree, self.zero())
    }

    fn build_explicit_ext(
        &self,
        r_prime: FiniteAlgebra<A::Coeff>,
        r_base: FiniteAlgebra<A::Coeff>,
        projection: Vec<Vec<A::Coeff>>,
    ) -> Result<SquareZeroExtension<A::Coeff>, AlgebraError> {
        SquareZeroExtension::new_field(r_prime, r_base, projection)
    }

    fn extract_kernel_coords(
        &self,
        ext: &SquareZeroExtension<A::Coeff>,
        elem: &[A::Coeff],
    ) -> Result<Vec<A::Coeff>, AlgebraError> {
        ext.extract_kernel_coords_field(elem)
    }

    fn solve_affine(
        &self,
        mat: &[Vec<A::Coeff>],
        rhs: &[A::Coeff],
        cols: usize,
    ) -> Result<AffineSolveOutput<A::Coeff>, AlgebraError> {
        match solve_affine_field(mat, rhs, cols, &self.zero())? {
            AffineSolutionField::Consistent {
                particular,
                kernel_basis,
                ..
            } => Ok(Some((particular, kernel_basis))),
            AffineSolutionField::Inconsistent { .. } => Ok(None),
        }
    }

    fn compute_syzygies(
        &self,
        law_polys: &[Poly<A::Coeff>],
        vars: VarOrder,
        max_pairs: usize,
    ) -> Result<SyzygyModule<A::Coeff>, SilenceReason> {
        let syz_res = compute_syzygies_field(law_polys, vars, MonomialOrder::Grevlex, max_pairs)
            .map_err(|e| SilenceReason::SyzygyOutOfScope {
                detail: e.to_string(),
            })?;
        if !syz_res.verified || !syz_res.generating_certified {
            return Err(SilenceReason::SyzygyOutOfScope {
                detail: "syzygy generating certification failed".to_owned(),
            });
        }
        Ok(syz_res)
    }

    fn cohomology_and_cocycle(
        &self,
        complex: &CochainComplex<A::Coeff>,
        cocycle: &[A::Coeff],
    ) -> Result<CohomologyAndCocycle<A::Coeff>, AlgebraError> {
        let coh = complex.cohomology_field()?;
        let coc = complex.check_h1_cocycle_field(&coh, cocycle)?;
        Ok(CohomologyAndCocycle {
            h0_dim: coh.h0_dim,
            h0_torsion: Vec::new(),
            h1_dim: coh.h1_dim,
            h1_torsion: Vec::new(),
            h0_basis: coh.h0_basis,
            is_cocycle: coc.is_cocycle,
            is_zero_class: coc.is_zero_class,
            class_coords: coc.class_coords.iter().map(ToString::to_string).collect(),
            coboundary_witness: coc.coboundary_witness,
        })
    }

    fn raw_cech_stats(
        &self,
        complex_d: &CochainComplex<A::Coeff>,
    ) -> Result<RawCechStats, AlgebraError> {
        let z = self.zero();
        let t_raw = CochainComplex::new(
            complex_d.dim0(),
            complex_d.dim1(),
            0,
            complex_d.d0().to_vec(),
            Vec::new(),
            z.clone(),
        )?;
        let raw_coh = t_raw.cohomology_field()?;
        let d1_rank = if complex_d.dim2() == 0 {
            0
        } else {
            rref_field(complex_d.d1(), complex_d.dim1(), &z)?.rank
        };
        Ok(RawCechStats {
            h0_t_raw_dim: raw_coh.h0_dim,
            h1_t_raw_dim: raw_coh.h1_dim,
            d1_rank,
        })
    }

    fn check_obs_laws_supported(&self, _has_obs_laws: bool) -> Result<(), SilenceReason> {
        Ok(())
    }

    fn ideal_membership(
        &self,
        poly: &Poly<A::Coeff>,
        gens: &[Poly<A::Coeff>],
        vars: &VarOrder,
        max_pairs: usize,
    ) -> Result<Option<Vec<Poly<A::Coeff>>>, AlgebraError> {
        ideal_membership_field(poly, gens, vars, MonomialOrder::Grevlex, max_pairs)
    }
}

pub(crate) struct ZLiftBackend;

impl LiftRingBackend for ZLiftBackend {
    type Coeff = BigInt;

    fn coeff_label(&self) -> String {
        "Z".to_owned()
    }

    fn zero(&self) -> BigInt {
        BigInt::zero()
    }

    fn expand_expr(
        &self,
        expr: &PolyExpr,
        bindings: &ExprBindings,
    ) -> Result<Poly<BigInt>, AlgebraError> {
        Poly::from_expr_z(expr, bindings)
    }

    fn convert_lit(&self, lit: &ScalarLit) -> Result<BigInt, AlgebraError> {
        lit_to_z(lit)
    }

    fn build_truncated_ext(
        &self,
        var_name: &str,
        base_degree: usize,
    ) -> Result<SquareZeroExtension<BigInt>, AlgebraError> {
        SquareZeroExtension::truncated_step_z(var_name, base_degree)
    }

    fn build_explicit_ext(
        &self,
        r_prime: FiniteAlgebra<BigInt>,
        r_base: FiniteAlgebra<BigInt>,
        projection: Vec<Vec<BigInt>>,
    ) -> Result<SquareZeroExtension<BigInt>, AlgebraError> {
        SquareZeroExtension::new_z(r_prime, r_base, projection)
    }

    fn extract_kernel_coords(
        &self,
        ext: &SquareZeroExtension<BigInt>,
        elem: &[BigInt],
    ) -> Result<Vec<BigInt>, AlgebraError> {
        ext.extract_kernel_coords_z(elem)
    }

    fn solve_affine(
        &self,
        mat: &[Vec<BigInt>],
        rhs: &[BigInt],
        cols: usize,
    ) -> Result<AffineSolveOutput<BigInt>, AlgebraError> {
        match solve_affine_z(mat, rhs, cols)? {
            AffineSolutionZ::Consistent {
                particular,
                kernel_basis,
                ..
            } => Ok(Some((particular, kernel_basis))),
            AffineSolutionZ::Inconsistent { .. } => Ok(None),
        }
    }

    fn compute_syzygies(
        &self,
        law_polys: &[Poly<BigInt>],
        vars: VarOrder,
        _max_pairs: usize,
    ) -> Result<SyzygyModule<BigInt>, SilenceReason> {
        let syz_res =
            compute_syzygies_z(law_polys, vars).map_err(|e| SilenceReason::SyzygyOutOfScope {
                detail: e.to_string(),
            })?;
        if !syz_res.verified || !syz_res.generating_certified {
            return Err(SilenceReason::SyzygyOutOfScope {
                detail: "Z syzygy generating certification failed".to_owned(),
            });
        }
        Ok(syz_res)
    }

    fn cohomology_and_cocycle(
        &self,
        complex: &CochainComplex<BigInt>,
        cocycle: &[BigInt],
    ) -> Result<CohomologyAndCocycle<BigInt>, AlgebraError> {
        let coh = complex.cohomology_z()?;
        let coc = complex.check_h1_cocycle_z(cocycle)?;
        let class_coords = if coc.is_zero_in_z {
            Vec::new()
        } else {
            cocycle.iter().map(ToString::to_string).collect()
        };
        Ok(CohomologyAndCocycle {
            h0_dim: coh.h0.free_rank,
            h0_torsion: coh.h0.torsion_invariants,
            h1_dim: coh.h1.free_rank,
            h1_torsion: coh.h1.torsion_invariants,
            h0_basis: coh.h0_basis,
            is_cocycle: coc.is_cocycle,
            is_zero_class: coc.is_zero_in_z,
            class_coords,
            coboundary_witness: coc.coboundary_witness_z,
        })
    }

    fn raw_cech_stats(
        &self,
        complex_d: &CochainComplex<BigInt>,
    ) -> Result<RawCechStats, AlgebraError> {
        let t_raw = CochainComplex::new(
            complex_d.dim0(),
            complex_d.dim1(),
            0,
            complex_d.d0().to_vec(),
            Vec::new(),
            BigInt::zero(),
        )?;
        let raw_coh = t_raw.cohomology_z()?;
        let d1_rank = if complex_d.dim2() == 0 {
            0
        } else {
            smith_normal_form_z(complex_d.d1(), complex_d.dim1())?.rank
        };
        Ok(RawCechStats {
            h0_t_raw_dim: raw_coh.h0.free_rank,
            h1_t_raw_dim: raw_coh.h1.free_rank,
            d1_rank,
        })
    }

    fn check_obs_laws_supported(&self, has_obs_laws: bool) -> Result<(), SilenceReason> {
        if has_obs_laws {
            return Err(SilenceReason::SyzygyOutOfScope {
                detail: "relative cone with non-empty obs_laws over Z is out of scope".to_owned(),
            });
        }
        Ok(())
    }

    fn ideal_membership(
        &self,
        _poly: &Poly<BigInt>,
        _gens: &[Poly<BigInt>],
        _vars: &VarOrder,
        _max_pairs: usize,
    ) -> Result<Option<Vec<Poly<BigInt>>>, AlgebraError> {
        Err(AlgebraError::OutOfScope {
            detail: "ideal membership over Z is out of scope".to_owned(),
        })
    }
}

/// `shigure_lift` の検証済み入力・延長環・基底点・周囲リフトを束ねる共有文脈。
pub(crate) struct LiftContext<'a, B: LiftRingBackend> {
    pub(crate) spec: &'a LiftTaskSpec,
    pub(crate) backend: &'a B,
    pub(crate) vars: VarOrder,
    pub(crate) bindings: ExprBindings,
    pub(crate) ext: SquareZeroExtension<B::Coeff>,
    pub(crate) law_polys: Vec<Poly<B::Coeff>>,
    pub(crate) base_pt_r: Vec<Vec<B::Coeff>>,
    pub(crate) param_vals_r: Vec<Vec<B::Coeff>>,
    pub(crate) ambient_lift_rp: Vec<Vec<B::Coeff>>,
    pub(crate) param_vals_rp: Vec<Vec<B::Coeff>>,
    pub(crate) max_pairs: usize,
}

impl<B: LiftRingBackend> LiftContext<'_, B> {
    pub(crate) fn expand_named(
        &self,
        items: &[crate::ir::change::NamedPoly],
        bindings: &ExprBindings,
    ) -> Result<Vec<Poly<B::Coeff>>, SilenceReason> {
        items
            .iter()
            .map(|item| self.backend.expand_expr(&item.expr, bindings))
            .collect::<Result<Vec<_>, _>>()
            .map_err(map_lift_algebra_error)
    }
}
