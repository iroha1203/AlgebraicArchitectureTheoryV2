import ResearchLean.AG.AtlasCoefficientFiber.QuotientHorizontalHomology
import ResearchLean.AG.AtlasCoefficientFiber.Kappa
import ResearchLean.AG.AtlasCoefficientFiber.DegenerateHomology

/-!
# G-135 B：原商鎖複体の連結代表

水平閉路の原式By=Hxから、同じ原Dによる[-Dy]を構成する。

## Implementation notes

水平閉性が生成したBy=Hxの解をClassical.chooseで選ぶ。解そのものの線形性は
要求せず、D(ker B)による商類の独立性から連結写像の線形性を導く。
線形sectionを入力として供給する案は、原始入力だけからの構成を変えるため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原By=Hxを満たす補正の負の垂直成分はa閉路である。 -/
theorem horizontalLift_vertical_closed (x : HorizontalFace M A →₀ ℚ)
    (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) :
    verticalEdgeBoundary M A (-mixedVerticalBoundary M A y) = 0 := by
  have hh := LinearMap.congr_fun (mixedBoundary_square M A) y
  have hhx := LinearMap.congr_fun (horizontalEdgeBoundary_comp_horizontalFaceBoundary M A) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hh
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hhx
  rw [hy, hhx, add_zero] at hh
  rw [map_neg, hh, neg_zero]

/-- 指定原代表から得る連結閉路。 -/
def horizontalLiftCycle (x : HorizontalFace M A →₀ ℚ) (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) : verticalCycles M A :=
  ⟨-mixedVerticalBoundary M A y, horizontalLift_vertical_closed M A x y hy⟩

/-- 原連結閉路の値は-Dy。 -/
@[simp] theorem horizontalLiftCycle_val (x : HorizontalFace M A →₀ ℚ)
    (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) :
    (horizontalLiftCycle M A x y hy).1 = -mixedVerticalBoundary M A y := rfl

/-- 同じ原関係商へ連結閉路を送る。 -/
def horizontalLiftClass (x : HorizontalFace M A →₀ ℚ) (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) :
    verticalCycles M A ⧸ verticalRelations M A :=
  Submodule.Quotient.mk (horizontalLiftCycle M A x y hy)

/-- 同じ原代表の商射による表示。 -/
@[simp] theorem horizontalLiftClass_mk (x : HorizontalFace M A →₀ ℚ)
    (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) :
    horizontalLiftClass M A x y hy =
      Submodule.Quotient.mk (horizontalLiftCycle M A x y hy) := rfl

/-- 水平持ち上げを選び直しても、差のD(ker B)は同じ原関係へ入る。 -/
theorem horizontalLiftClass_independent (x : HorizontalFace M A →₀ ℚ)
    (y y' : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x)
    (hy' : mixedHorizontalBoundary M A y' = horizontalFaceBoundary M A x) :
    horizontalLiftClass M A x y hy = horizontalLiftClass M A x y' hy' := by
  rw [horizontalLiftClass_mk, horizontalLiftClass_mk, Submodule.Quotient.eq]
  apply (mem_verticalRelations M A _).mpr
  have hb : mixedHorizontalBoundary M A (y' - y) = 0 := by
    rw [map_sub, hy, hy', sub_self]
  refine ⟨0, ⟨y' - y, hb⟩, ?_⟩
  simp only [map_zero, zero_add, map_sub, Submodule.coe_sub, horizontalLiftCycle_val]
  abel

/-- 原代表の連結類が零になる必要十分条件。 -/
theorem horizontalLiftClass_eq_zero_iff (x : HorizontalFace M A →₀ ℚ)
    (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) :
    horizontalLiftClass M A x y hy = 0 ↔
      horizontalLiftCycle M A x y hy ∈ verticalRelations M A := by
  rw [horizontalLiftClass_mk, Submodule.Quotient.mk_eq_zero]

/-- 水平商閉性が生成する補正の選択。 -/
def horizontalCycleLift (x : HorizontalFaceCycles M A) : MixedFace M A →₀ ℚ :=
  Classical.choose ((mem_horizontalFaceCycles_iff M A x.1).mp x.2)

/-- 選ばれた補正は原By=Hxを満たす。 -/
theorem horizontalCycleLift_spec (x : HorizontalFaceCycles M A) :
    mixedHorizontalBoundary M A (horizontalCycleLift M A x) = horizontalFaceBoundary M A x.1 :=
  Classical.choose_spec ((mem_horizontalFaceCycles_iff M A x.1).mp x.2)

/-- 原水平商閉路から原垂直関係商への連結写像。 -/
def horizontalChainConnecting : HorizontalFaceCycles M A →ₗ[ℚ]
    (verticalCycles M A ⧸ verticalRelations M A) where
  toFun x := horizontalLiftClass M A x.1 (horizontalCycleLift M A x)
    (horizontalCycleLift_spec M A x)
  map_add' x x' := by
    have hy : mixedHorizontalBoundary M A (horizontalCycleLift M A x + horizontalCycleLift M A x') =
        horizontalFaceBoundary M A (x + x').1 := by
      simp only [map_add, horizontalCycleLift_spec, Submodule.coe_add]
    rw [horizontalLiftClass_independent M A (x+x').1 _ _ (horizontalCycleLift_spec M A (x+x')) hy]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    simp only [horizontalLiftCycle_val, map_add, Submodule.coe_add]
    abel
  map_smul' r x := by
    have hy : mixedHorizontalBoundary M A (r • horizontalCycleLift M A x) =
        horizontalFaceBoundary M A (r • x).1 := by
      simp only [map_smul, horizontalCycleLift_spec, Submodule.coe_smul]
    rw [horizontalLiftClass_independent M A (r • x).1 _ _ (horizontalCycleLift_spec M A (r • x)) hy]
    change Submodule.Quotient.mk _ = r • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    simp only [horizontalLiftCycle_val, map_smul, Submodule.coe_smul, smul_neg]

/-- 生成された連結写像は任意の原By=Hx代表で評価できる。 -/
theorem horizontalChainConnecting_apply (x : HorizontalFaceCycles M A)
    (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x.1) :
    horizontalChainConnecting M A x = horizontalLiftClass M A x.1 y hy :=
  horizontalLiftClass_independent M A x.1 _ y (horizontalCycleLift_spec M A x) hy

/-- 連結写像の零性は全原By=Hx代表の同じ関係商零性と同値。 -/
theorem horizontalChainConnecting_eq_zero_iff :
    horizontalChainConnecting M A = 0 ↔
      ∀ (x : HorizontalFace M A →₀ ℚ) (y : MixedFace M A →₀ ℚ)
        (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x),
        horizontalLiftCycle M A x y hy ∈ verticalRelations M A := by
  constructor
  · intro hh x y hy
    have hx : x ∈ HorizontalFaceCycles M A :=
      (mem_horizontalFaceCycles_iff M A x).mpr ⟨y, hy⟩
    have he := LinearMap.congr_fun hh (⟨x, hx⟩ : HorizontalFaceCycles M A)
    rw [horizontalChainConnecting_apply M A ⟨x, hx⟩ y hy, LinearMap.zero_apply] at he
    exact (horizontalLiftClass_eq_zero_iff M A x y hy).mp he
  · intro hh
    apply LinearMap.ext
    intro x
    rw [horizontalChainConnecting_apply M A x (horizontalCycleLift M A x)
      (horizontalCycleLift_spec M A x), LinearMap.zero_apply]
    exact (horizontalLiftClass_eq_zero_iff M A x.1 _ _).mpr (hh _ _ _)

/-- 原quotient二次閉路の補正持ち上げを元K′で微分すると同じ-I_vDyとなる。 -/
theorem supportedBoundary_horizontalLift (x : HorizontalFace M A →₀ ℚ)
    (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x) :
    chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)
      (horizontalFaceInclusion M A x - mixedFaceInclusion M A y) =
        verticalEdgeInclusion M A (horizontalLiftCycle M A x y hy).1 := by
  have hx := LinearMap.congr_fun (horizontalFaceBoundary_inclusion M A) x
  simp only [LinearMap.comp_apply] at hx
  rw [map_sub, ← hx, ← mixedBoundary_recombination, hy, horizontalLiftCycle_val, map_neg]
  abel

/-- 補正持ち上げを商へ戻すと、同じ水平面代表を保つ。 -/
theorem quotient_horizontalLift (x : HorizontalFace M A →₀ ℚ)
    (y : MixedFace M A →₀ ℚ) :
    (degenerateL2 M A).mkQ (horizontalFaceInclusion M A x - mixedFaceInclusion M A y) =
      (quotientFaceEquiv M A).symm x := by
  rw [quotientFaceEquiv_symm_apply, map_sub]
  have hy : (degenerateL2 M A).mkQ (mixedFaceInclusion M A y) = 0 :=
    (Submodule.Quotient.mk_eq_zero (degenerateL2 M A)).mpr
      (mixedFaceInclusion_range_le_degenerate M A ⟨y, rfl⟩)
  rw [hy, sub_zero]
  rfl

/-- 原K′/Lの二次閉路から同じ実H₁Lへの鎖連結写像。 -/
def quotientChainConnecting : QuotientSecondCycles M A →ₗ[ℚ] DegenerateHomology M A :=
  (verticalRelationsHomologyEquiv M A).toLinearMap.comp
    ((horizontalChainConnecting M A).comp (quotientSecondCyclesEquiv M A).toLinearMap)

/-- 商閉路から実H₁Lへの連結写像は原[-Dy]のL内垂直包含類である。 -/
theorem quotientChainConnecting_apply (x : QuotientSecondCycles M A)
    (y : MixedFace M A →₀ ℚ)
    (hy : mixedHorizontalBoundary M A y = horizontalFaceBoundary M A
      (quotientSecondCyclesEquiv M A x).1) :
    quotientChainConnecting M A x = verticalCycleHomologyMap M A
      (horizontalLiftCycle M A (quotientSecondCyclesEquiv M A x).1 y hy) := by
  change verticalRelationsHomologyEquiv M A
    (horizontalChainConnecting M A (quotientSecondCyclesEquiv M A x)) = _
  rw [horizontalChainConnecting_apply M A _ y hy, horizontalLiftClass_mk,
    verticalRelationsHomologyEquiv_mk]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLift_vertical_closed
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLiftCycle
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLiftCycle_val
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLiftClass
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLiftClass_mk
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLiftClass_independent
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLiftClass_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCycleLift
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCycleLift_spec
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalChainConnecting
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalChainConnecting_apply
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalChainConnecting_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.supportedBoundary_horizontalLift
#print axioms AAT.AG.AtlasCoefficientFiber.quotient_horizontalLift
#print axioms AAT.AG.AtlasCoefficientFiber.quotientChainConnecting
#print axioms AAT.AG.AtlasCoefficientFiber.quotientChainConnecting_apply
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalLiftCycle.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
