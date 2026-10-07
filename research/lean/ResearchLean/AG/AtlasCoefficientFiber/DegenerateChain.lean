import ResearchLean.AG.AtlasCoefficientFiber.DegenerateSubcomplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# G-135 A §4：指定Lの標準chainと原支持chainへの包含

Implementation notes: Lの三部分空間と実制限微分をℤ添字へ零延長する。
包含先はG-134の同じsupportedChainであり、各成分は部分空間のsubtype。
H₀零性は原始境界の全射性から標準短複体の完全性を通して得る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 指定Lの三部分空間と次数外の零加群。 -/
def degenerateDegreeObject (n : ℤ) : ModuleCat.{u} ℚ :=
  if n = 0 then ModuleCat.of ℚ (degenerateL0 M A)
  else if n = 1 then ModuleCat.of ℚ (degenerateL1 M A)
  else if n = 2 then ModuleCat.of ℚ (degenerateL2 M A)
  else ModuleCat.of ℚ PUnit.{u+1}

/-- 次数外のL加群は明示零加群である。 -/
theorem degenerateDegreeObject_out (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    degenerateDegreeObject M A n = ModuleCat.of ℚ PUnit.{u+1} := by
  simp [degenerateDegreeObject, h0, h1, h2]

/-- 指定Lの制限微分を次数別に置く。 -/
def degenerateDegreeDifferential (n : ℤ) :
    degenerateDegreeObject M A (n + 1) ⟶ degenerateDegreeObject M A n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (degenerateBoundary1 M A)
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (degenerateBoundary2 M A)
  else 0

/-- 原支持chainのsquare-zeroから指定Lの全次数条件を放電する。 -/
theorem degenerateDegreeDifferential_square (n : ℤ) :
    degenerateDegreeDifferential M A (n + 1) ≫ degenerateDegreeDifferential M A n = 0 := by
  by_cases h0 : n = 0
  · subst n
    change ModuleCat.ofHom (degenerateBoundary2 M A) ≫
      ModuleCat.ofHom (degenerateBoundary1 M A) = 0
    exact ModuleCat.hom_ext (degenerateBoundary_square M A)
  · by_cases h1 : n = 1
    · subst n; simp [degenerateDegreeDifferential]
    · simp [degenerateDegreeDifferential, h0, h1]

/-- 原始退化セルから生成した同じLの標準ℤ chain。 -/
def degenerateChain : ChainComplex (ModuleCat.{u} ℚ) ℤ :=
  ChainComplex.of (degenerateDegreeObject M A) (degenerateDegreeDifferential M A)
    (degenerateDegreeDifferential_square M A)

/-- Lから元の支持chainへの次数別subtype包含。 -/
def degenerateDegreeInclusion (n : ℤ) :
    degenerateDegreeObject M A n ⟶ chainDegreeObject Nf (comparisonFactor qc qf h ⁻¹' A) n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (degenerateL0 M A).subtype
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (degenerateL1 M A).subtype
  else if h2 : n = 2 then by subst n; exact ModuleCat.ofHom (degenerateL2 M A).subtype
  else 0

/-- 部分空間の実制限式から原支持chainへの包含可換式を放電する。 -/
theorem degenerateDegreeInclusion_comm (n : ℤ) :
    degenerateDegreeInclusion M A (n + 1) ≫ chainDegreeDifferential Nf _ n =
      degenerateDegreeDifferential M A n ≫ degenerateDegreeInclusion M A n := by
  by_cases h0 : n = 0
  · subst n
    change ModuleCat.ofHom (degenerateL1 M A).subtype ≫ ModuleCat.ofHom (chainD1 Nf _) =
      ModuleCat.ofHom (degenerateBoundary1 M A) ≫ ModuleCat.ofHom (degenerateL0 M A).subtype
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => (degenerateBoundary1_val M A x).symm
  · by_cases h1 : n = 1
    · subst n
      change ModuleCat.ofHom (degenerateL2 M A).subtype ≫ ModuleCat.ofHom (chainD2 Nf _) =
        ModuleCat.ofHom (degenerateBoundary2 M A) ≫ ModuleCat.ofHom (degenerateL1 M A).subtype
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun x => (degenerateBoundary2_val M A x).symm
    · simp [chainDegreeDifferential, degenerateDegreeDifferential, h0, h1]

/-- 元の同じK′への標準chain包含。 -/
def degenerateChainInclusion : degenerateChain M A ⟶
    supportedChain Nf (comparisonFactor qc qf h ⁻¹' A) :=
  ChainComplex.ofHom _ _ _ _ _ _ (degenerateDegreeInclusion M A)
    (degenerateDegreeInclusion_comm M A)

/-- 標準包含の全次数成分を読む所有API。 -/
@[simp] theorem degenerateChainInclusion_f (n : ℤ) :
    (degenerateChainInclusion M A).f n = degenerateDegreeInclusion M A n := rfl

/-- 指定Lの標準包含も原始Mの同じchain比較により零に送られる。 -/
theorem degenerateChainInclusion_comparison_zero :
    degenerateChainInclusion M A ≫ M.supportedChainHom A
      (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degenerateDegreeInclusion M A n ≫
    M.supportedChainDegreeMap A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) n = 0
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => degenerateL0_le_ker M A x.2
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun x => degenerateL1_le_ker M A x.2
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => degenerateL2_le_ker M A x.2
      · simp [degenerateDegreeInclusion, h0, h1, h2]

/-- 各実部分空間の包含は標準chain圏でもmonoである。 -/
instance degenerateChainInclusion_mono : Mono (degenerateChainInclusion M A) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [degenerateChainInclusion_f]
  apply (ModuleCat.mono_iff_injective _).mpr
  by_cases h0 : n = 0
  · subst n; exact (degenerateL0 M A).injective_subtype
  · by_cases h1 : n = 1
    · subst n; exact (degenerateL1 M A).injective_subtype
    · by_cases h2 : n = 2
      · subst n; exact (degenerateL2 M A).injective_subtype
      · simp only [degenerateDegreeInclusion, dif_neg h0, dif_neg h1, dif_neg h2]
        change Function.Injective (0 : degenerateDegreeObject M A n →ₗ[ℚ] chainDegreeObject Nf _ n)
        haveI : Subsingleton (degenerateDegreeObject M A n) := by
          rw [degenerateDegreeObject_out M A n h0 h1 h2]
          infer_instance
        intro x y _
        exact Subsingleton.elim x y

/-- 指定Lの次数0端短複体。 -/
def degenerateZeroShort : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.moduleCatMk (degenerateBoundary1 M A)
    (0 : degenerateL0 M A →ₗ[ℚ] PUnit.{u+1}) (by simp)

/-- 標準chainの次数0短複体を同じ原始境界へ同定する。 -/
def degenerateZeroScIso : (degenerateChain M A).sc (0 : ℤ) ≅ degenerateZeroShort M A :=
  (degenerateChain M A).isoSc' (i := 1) (j := 0) (k := -1) (by simp) (by simp) ≪≫
    eqToIso (by rfl)

/-- 原始境界の全射性から標準短複体の完全性を導く。 -/
theorem degenerateZeroShort_exact : (degenerateZeroShort M A).Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  intro x
  constructor
  · intro _; exact degenerateBoundary1_surjective M A x
  · intro _; rfl

/-- 原始LのH₀は標準ℤ chainのhomologyとして零である。 -/
theorem degenerateChain_H0_isZero :
    Limits.IsZero ((degenerateChain M A).homology (0 : ℤ)) :=
  Limits.IsZero.of_iso
    ((ShortComplex.exact_iff_isZero_homology _).mp (degenerateZeroShort_exact M A))
    (ShortComplex.homologyMapIso (degenerateZeroScIso M A))

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateDegreeObject
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateDegreeObject_out
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateDegreeDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateDegreeDifferential_square
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateChain
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateDegreeInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateDegreeInclusion_comm
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateChainInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateChainInclusion_f
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateChainInclusion_comparison_zero
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateChainInclusion_mono
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateZeroShort
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateZeroScIso
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateZeroShort_exact
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateChain_H0_isZero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
