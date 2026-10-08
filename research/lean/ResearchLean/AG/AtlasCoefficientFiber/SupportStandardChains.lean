import ResearchLean.AG.AtlasCoefficientFiber.SupportDegenerate
import ResearchLean.AG.AtlasCoefficientFiber.DegenerateChain

/-!
# G-135 D：元細chainと原Lの全整数次数の台包含

## Implementation notes

元の三つの自由chain包含とL包含を次数外の零射で延長する。
原包含の可換正方形は同じ三つの部分空間値から証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 元細chainの三つの同じ台包含を整数次数へ延長する。 -/
def supportFineDegreeInclude (n : ℤ) :
    chainDegreeObject Nf (comparisonFactor qc qf h ⁻¹' A) n ⟶
      chainDegreeObject Nf (comparisonFactor qc qf h ⁻¹' B) n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (selectedInclude Nf.chartSupport (fun _ ht => hab ht))
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (selectedInclude Nf.edgeSupport (fun _ ht => hab ht))
  else if h2 : n = 2 then by subst n; exact ModuleCat.ofHom (selectedInclude Nf.faceSupport (fun _ ht => hab ht))
  else 0

/-- 元細chainの両微分の可換性は全整数次数でも成立する。 -/
theorem supportFineDegreeInclude_comm (n : ℤ) :
    supportFineDegreeInclude (Nf := Nf) (h := h) hab (n+1) ≫ chainDegreeDifferential Nf _ n =
      chainDegreeDifferential Nf _ n ≫ supportFineDegreeInclude (Nf := Nf) (h := h) hab n := by
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact (supportChainInclude_boundary1 Nf (fun _ ht => hab ht)).symm
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact (supportChainInclude_boundary2 Nf (fun _ ht => hab ht)).symm
    · rw [chainDegreeDifferential_out Nf _ n h0 h1,
        chainDegreeDifferential_out Nf _ n h0 h1]
      simp

/-- 元の同じ標準supportedChainの台包含。 -/
def supportFineChainInclude : supportedChain Nf (comparisonFactor qc qf h ⁻¹' A) ⟶
    supportedChain Nf (comparisonFactor qc qf h ⁻¹' B) :=
  ChainComplex.ofHom _ _ _ _ _ _ (supportFineDegreeInclude (Nf := Nf) (h := h) hab) (supportFineDegreeInclude_comm (Nf := Nf) (h := h) hab)

/-- 元細chain包含の全次数成分。 -/
@[simp] theorem supportFineChainInclude_f (n : ℤ) :
    (supportFineChainInclude (Nf := Nf) (h := h) hab).f n = supportFineDegreeInclude (Nf := Nf) (h := h) hab n := rfl

/-- 同じLの三つの台包含を整数次数へ延長する。 -/
def supportDegenerateDegreeInclude (n : ℤ) : degenerateDegreeObject M A n ⟶ degenerateDegreeObject M B n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (supportL0Include M hab)
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (supportL1Include M hab)
  else if h2 : n = 2 then by subst n; exact ModuleCat.ofHom (supportL2Include M hab)
  else 0

/-- 同じLの元制限微分は全整数次数で台包含と可換。 -/
theorem supportDegenerateDegreeInclude_comm (n : ℤ) :
    supportDegenerateDegreeInclude M hab (n+1) ≫ degenerateDegreeDifferential M B n =
      degenerateDegreeDifferential M A n ≫ supportDegenerateDegreeInclude M hab n := by
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (supportLInclude_boundary1 M hab x).symm
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (supportLInclude_boundary2 M hab x).symm
    · rw [degenerateDegreeDifferential_out M B n h0 h1,
        degenerateDegreeDifferential_out M A n h0 h1]
      simp

/-- 原Lの同じ標準chainの台包含。 -/
def supportDegenerateChainInclude : degenerateChain M A ⟶ degenerateChain M B :=
  ChainComplex.ofHom _ _ _ _ _ _ (supportDegenerateDegreeInclude M hab)
    (supportDegenerateDegreeInclude_comm M hab)

/-- 原Lの標準chain台包含の全次数値。 -/
@[simp] theorem supportDegenerateChainInclude_f (n : ℤ) :
    (supportDegenerateChainInclude M hab).f n = supportDegenerateDegreeInclude M hab n := rfl

/-- 原Lから元細chainへの包含は同じ全整数次数の台包含と可換。 -/
theorem supportDegenerateChainInclusion :
    supportDegenerateChainInclude M hab ≫ degenerateChainInclusion M B =
      degenerateChainInclusion M A ≫ supportFineChainInclude (Nf := Nf) (h := h) hab := by
  apply HomologicalComplex.Hom.ext
  funext n
  change supportDegenerateDegreeInclude M hab n ≫ degenerateDegreeInclusion M B n =
    degenerateDegreeInclusion M A n ≫ supportFineDegreeInclude (Nf := Nf) (h := h) hab n
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact LinearMap.ext (supportL0Include_val M hab)
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact LinearMap.ext (supportL1Include_val M hab)
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        exact LinearMap.ext (supportL2Include_val M hab)
      · rw [degenerateDegreeInclusion_out M B n h0 h1 h2,
          degenerateDegreeInclusion_out M A n h0 h1 h2]
        simp

/-- 原Lの全整数次数台包含の恒等則。 -/
theorem supportDegenerateChainInclude_refl (A : Set qc.Target) :
    supportDegenerateChainInclude M (Set.Subset.refl A) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change supportDegenerateDegreeInclude M (Set.Subset.refl A) n = 𝟙 _
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact supportL0Include_refl M A
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact supportL1Include_refl M A
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        exact supportL2Include_refl M A
      · letI : Subsingleton (degenerateDegreeObject M A n) := by
          rw [degenerateDegreeObject_out M A n h0 h1 h2]
          infer_instance
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _

/-- 原Lの全整数次数台包含の合成則。 -/
theorem supportDegenerateChainInclude_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    supportDegenerateChainInclude M hab ≫ supportDegenerateChainInclude M hbc =
      supportDegenerateChainInclude M (hab.trans hbc) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change supportDegenerateDegreeInclude M hab n ≫ supportDegenerateDegreeInclude M hbc n =
    supportDegenerateDegreeInclude M (hab.trans hbc) n
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact supportL0Include_comp M hab hbc
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact supportL1Include_comp M hab hbc
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        exact supportL2Include_comp M hab hbc
      · letI : Subsingleton (degenerateDegreeObject M C n) := by
          rw [degenerateDegreeObject_out M C n h0 h1 h2]
          infer_instance
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportFineDegreeInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportFineDegreeInclude_comm
#print axioms AAT.AG.AtlasCoefficientFiber.supportFineChainInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportFineChainInclude_f
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateDegreeInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateDegreeInclude_comm
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateChainInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateChainInclude_f
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateChainInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateChainInclude_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateChainInclude_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportFineDegreeInclude.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportDegenerateDegreeInclude.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
