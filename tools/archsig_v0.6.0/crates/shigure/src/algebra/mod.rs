//! 多項式・ideal 計算核（Step 2 実装）。
//!
//! 責務:
//! - `scalar`: Z / Q / F_p の正確な係数演算（`Rat`, `FpElem`, `RingCoeff`）
//! - `poly`: 単項式・変数順序・多変数多項式 `Poly<C>` と `PolyExpr` 展開
//! - `groebner`: Q 上の cofactor 追跡付き Gröbner 基底、witness 付き ideal 所属、
//!   Rabinowitsch 可逆条件、商環上の ideal 所属層別（G-141 D5）
//! - `linear`: Q アフィン（RREF）、Z アフィン（Smith 標準形）、F_p 有限全列挙、
//!   および係数域・点集合域に応じた沈黙判定（G-141 D4–D6）
//! - `interaction`: 座標面支持による相互作用参加変数数 r と極小不成立部分族（G-141 F10–F12）

pub mod constructible;
pub mod constructible_image;
pub mod groebner;
pub mod interaction;
pub mod linear;
pub mod poly;
pub mod quotient;
pub mod scalar;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_constructible;

pub use constructible::{ConstructibleSet, DEFAULT_MAX_CONSTRUCTIBLE_STRATA, LocallyClosedStratum};
pub use constructible_image::{
    DEFAULT_MAX_IMAGE_BRANCHES, DEFAULT_MAX_IMAGE_Y_PAIRS, project_constructible_set,
    project_stratum_image,
};

pub use groebner::{
    DEFAULT_MAX_BUCHBERGER_PAIRS, GroebnerBasis, MembershipResult, RabinowitschResult, TrackedPoly,
    rabinowitsch_solve,
};
pub use interaction::{
    analyze_coordinate_interaction, analyze_interaction_on_face, require_closed_for_interaction,
};
pub use linear::{
    AffineSolutionQ, AffineSolutionZ, DEFAULT_MAX_FP_POINTS, FpEnumerationResult,
    SystemPointOutcome, solve_affine_q, solve_affine_z, solve_fp_enumeration,
    solve_polynomial_system_q,
};
pub use poly::{AlgebraError, ExprBindings, Monomial, Poly, VarOrder};
pub use quotient::{
    DEFAULT_MAX_QUOTIENT_BRANCHES, DEFAULT_MAX_QUOTIENT_Y_PAIRS, QuotientStratum,
    quotient_membership_locus,
};
pub use scalar::{FpElem, Rat, RingCoeff};

/// 単項式順序の種別。
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MonomialOrder {
    /// Graded reverse lexicographic order（既定の Gröbner 基底順序）。
    Grevlex,
    /// Lexicographic order（消去・逐次復元用）。
    Lex,
}
