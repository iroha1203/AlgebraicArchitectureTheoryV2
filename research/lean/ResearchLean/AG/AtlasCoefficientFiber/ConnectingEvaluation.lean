import ResearchLean.AG.AtlasCoefficientFiber.ChainConnecting
import ResearchLean.AG.AtlasCoefficientFiber.CochainRepresentatives

/-!
# G-135 B：原連結代表の双対評価

原関係をannihilateする垂直閉cochainを商へ降ろし、[-Dy]との評価をβHへ照合する。

## Implementation notes

閉cochainを元の垂直関係商へliftQで降ろし、原始VとD(ker B)を消す証明を渡す。
商の双対を別の供給係数として受け取る案は、原始評価zとの対応を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ原補正を持つ垂直cochainはVとD(ker B)の実関係に消える。 -/
theorem correctedCocycle_annihilates_relations (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (x : verticalCycles M A) (hx : x ∈ verticalRelations M A) : z.1 x.1 = 0 := by
  obtain ⟨v, y, he⟩ := (mem_verticalRelations M A x).mp hx
  rw [← he, map_add]
  have hz := LinearMap.congr_fun z.2 v
  have hy := (verticalCocycleClass_rawR_iff M A z).mp
    (verticalCocycleClass_rawR_of_correction M A z β hβ) y
  simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at hz
  rw [hz, hy, add_zero]

/-- 原垂直関係商上へ閉cochain評価を降ろす。 -/
def correctedRelationsFunctional (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    Module.Dual ℚ (verticalCycles M A ⧸ verticalRelations M A) :=
  (verticalRelations M A).liftQ ((verticalCycles M A).dualRestrict z.1)
    (correctedCocycle_annihilates_relations M A z β hβ)

/-- 原関係商での評価は元垂直閉路の値。 -/
@[simp] theorem correctedRelationsFunctional_mk (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (x : verticalCycles M A) :
    correctedRelationsFunctional M A z β hβ (Submodule.Quotient.mk x) = z.1 x.1 := rfl

/-- 原By=HxとβB=-zDから連結代表の双対評価がβHxに一致する。 -/
theorem correctedRelationsFunctional_horizontalLiftClass (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (x : HorizontalFace M A →₀ ℚ) (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) :
    correctedRelationsFunctional M A z β hβ (horizontalLiftClass M A x y hy) =
      β (horizontalFaceBoundary M A x) := by
  rw [horizontalLiftClass_mk, correctedRelationsFunctional_mk, horizontalLiftCycle_val, map_neg]
  have hh := LinearMap.congr_fun hβ y
  simp only [LinearMap.dualMap_apply, LinearMap.neg_apply] at hh
  rw [hy] at hh
  exact hh.symm

/-- 実連結写像への双対評価は選択に依らず同じβH。 -/
theorem correctedRelationsFunctional_horizontalChainConnecting (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (x : HorizontalFaceCycles M A) :
    correctedRelationsFunctional M A z β hβ (horizontalChainConnecting M A x) =
      β (horizontalFaceBoundary M A x.1) := by
  rw [horizontalChainConnecting_apply M A x (horizontalCycleLift M A x)
    (horizontalCycleLift_spec M A x)]
  exact correctedRelationsFunctional_horizontalLiftClass M A z β hβ _ _ _

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.correctedCocycle_annihilates_relations
#print axioms AAT.AG.AtlasCoefficientFiber.correctedRelationsFunctional
#print axioms AAT.AG.AtlasCoefficientFiber.correctedRelationsFunctional_mk
#print axioms AAT.AG.AtlasCoefficientFiber.correctedRelationsFunctional_horizontalLiftClass
#print axioms AAT.AG.AtlasCoefficientFiber.correctedRelationsFunctional_horizontalChainConnecting
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
