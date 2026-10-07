import ResearchLean.AG.AtlasCoefficientFiber.DegenerateChain
import ResearchLean.AG.AtlasCoefficientFiber.QuotientDual

/-!
# G-135 A §4：元の支持chainの指定Lによる標準商

Implementation notes: 各次数は同じ原支持加群の指定部分空間によるliteral quotient。
微分も元の微分からmapQで生成され、商射は元の支持chainからのmkQである。
商双対の二微分と、この標準chainの二微分を同じquotientBoundaryへ接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 元のK′の同じLによる三次数の商と次数外の零加群。 -/
def quotientDegreeObject (n : ℤ) : ModuleCat.{u} ℚ :=
  if n = 0 then ModuleCat.of ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL0 M A)
  else if n = 1 then ModuleCat.of ℚ (K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A)
  else if n = 2 then ModuleCat.of ℚ (K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A)
  else ModuleCat.of ℚ PUnit.{u+1}

/-- 元のchain微分から生成した同じ商境界を全ℤ次数へ置く。 -/
def quotientDegreeDifferential (n : ℤ) :
    quotientDegreeObject M A (n + 1) ⟶ quotientDegreeObject M A n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (quotientBoundary1 M A)
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (quotientBoundary2 M A)
  else 0

/-- 元のsquare-zeroから標準商chainの全次数条件を放電する。 -/
theorem quotientDegreeDifferential_square (n : ℤ) :
    quotientDegreeDifferential M A (n + 1) ≫ quotientDegreeDifferential M A n = 0 := by
  by_cases h0 : n = 0
  · subst n
    exact ModuleCat.hom_ext (quotientBoundary_square M A)
  · by_cases h1 : n = 1
    · subst n; simp [quotientDegreeDifferential]
    · simp [quotientDegreeDifferential, h0, h1]

/-- 原始K′の指定Lによる標準ℤ chain商。 -/
def quotientChain : ChainComplex (ModuleCat.{u} ℚ) ℤ :=
  ChainComplex.of (quotientDegreeObject M A) (quotientDegreeDifferential M A)
    (quotientDegreeDifferential_square M A)

/-- 標準商chainの第一微分は商双対でも使用する同じ境界。 -/
@[simp] theorem quotientChain_d10 :
    (quotientChain M A).d (1 : ℤ) 0 = ModuleCat.ofHom (quotientBoundary1 M A) := rfl
/-- 標準商chainの第二微分は商双対でも使用する同じ境界。 -/
@[simp] theorem quotientChain_d21 :
    (quotientChain M A).d (2 : ℤ) 1 = ModuleCat.ofHom (quotientBoundary2 M A) := rfl

/-- 原支持chainから同じLによる商への次数別mkQ。 -/
def quotientDegreeProjection (n : ℤ) :
    chainDegreeObject Nf (comparisonFactor qc qf h ⁻¹' A) n ⟶ quotientDegreeObject M A n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (degenerateL0 M A).mkQ
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (degenerateL1 M A).mkQ
  else if h2 : n = 2 then by subst n; exact ModuleCat.ofHom (degenerateL2 M A).mkQ
  else 0

/-- 同じ原支持chainの商代表元式から全次数の商射可換性を得る。 -/
theorem quotientDegreeProjection_comm (n : ℤ) :
    quotientDegreeProjection M A (n + 1) ≫ quotientDegreeDifferential M A n =
      chainDegreeDifferential Nf _ n ≫ quotientDegreeProjection M A n := by
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact LinearMap.ext (quotientBoundary1_mk M A)
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact LinearMap.ext (quotientBoundary2_mk M A)
    · rw [chainDegreeDifferential_out Nf _ n h0 h1]
      simp [quotientDegreeDifferential, h0, h1]

/-- 元の同じK′から標準商chainへの実商射。 -/
def quotientChainProjection : supportedChain Nf (comparisonFactor qc qf h ⁻¹' A) ⟶
    quotientChain M A :=
  ChainComplex.ofHom _ _ _ _ _ _ (quotientDegreeProjection M A)
    (quotientDegreeProjection_comm M A)

/-- 標準商射の全次数成分は同じ次数別mkQ。 -/
@[simp] theorem quotientChainProjection_f (n : ℤ) :
    (quotientChainProjection M A).f n = quotientDegreeProjection M A n := rfl

/-- 元の指定Lは標準商射の全次数で零に送られる。 -/
theorem degenerateChainInclusion_quotient_zero :
    degenerateChainInclusion M A ≫ quotientChainProjection M A = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degenerateDegreeInclusion M A n ≫ quotientDegreeProjection M A n = 0
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero (degenerateL0 M A)).mpr x.2
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero (degenerateL1 M A)).mpr x.2
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (Submodule.Quotient.mk_eq_zero (degenerateL2 M A)).mpr x.2
      · rw [degenerateDegreeInclusion_out M A n h0 h1 h2]
        simp

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDegreeObject
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDegreeDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDegreeDifferential_square
#print axioms AAT.AG.AtlasCoefficientFiber.quotientChain
#print axioms AAT.AG.AtlasCoefficientFiber.quotientChain_d10
#print axioms AAT.AG.AtlasCoefficientFiber.quotientChain_d21
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDegreeProjection
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDegreeProjection_comm
#print axioms AAT.AG.AtlasCoefficientFiber.quotientChainProjection
#print axioms AAT.AG.AtlasCoefficientFiber.quotientChainProjection_f
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateChainInclusion_quotient_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
