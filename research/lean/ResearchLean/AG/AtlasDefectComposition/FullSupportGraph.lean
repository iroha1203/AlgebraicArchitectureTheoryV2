import ResearchLean.AG.AtlasDefectComposition.FullSupportBlocks
import Formal.Util.AssertStandardAxioms

/-! # 全台グラフの実Law block H¹

名付き辺への座標同定と既存微分の両方向像等号を使い、商を同定する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase Cohomology
universe u
variable {Source : Type u} [Fintype Source]
variable {q : Reading Source} (D : TargetSupportedNerve q)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (hs₀ : ∀ c, D.chartSupport c = Set.univ)
variable (hs₁ : ∀ e, D.edgeSupport e = Set.univ) (label : LawValueLabel laws)
variable [IsEmpty D.nerve.FaceComponent]

/-- 名付きグラフの元の端点から作る微分。 -/
def graphDifference (N : CoverNerve.{u}) :
    (N.Chart → ℚ) →ₗ[ℚ] (N.EdgeComponent → ℚ) where
  toFun c e := c (N.edgeRight e) - c (N.edgeLeft e)
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring

/-- 空面を持つ全台blockの実cocycleは名付き辺cochainに一致する。 -/
def fullBlockGraphCyclesEquiv :
    LinearMap.ker (D.lawValueBlockComplex laws ha label).d1 ≃ₗ[ℚ]
      (D.nerve.EdgeComponent → ℚ) where
  toFun z := fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label z.val
  invFun z := ⟨(fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label).symm z, by
    change D.lawValueBlockD1 laws ha label _ = 0
    funext c; exact isEmptyElim c.val.cell⟩
  left_inv z := by
    apply Subtype.ext
    exact (fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label).symm_apply_apply z.val
  right_inv z := (fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label).apply_symm_apply z
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

include hs₀ in
/-- 実degree-zero像と名付きグラフ微分の像の両方向一致。 -/
theorem fullBlockGraph_image :
    (LinearMap.range (D.lawValueBlockComplex laws ha label).boundaryToCycles).map
      (fullBlockGraphCyclesEquiv D laws ha hs₁ label).toLinearMap =
        LinearMap.range (graphDifference D.nerve) := by
  have hdiff (x : D.ChartBlockCoordinate laws ha label → ℚ) :
      fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label
        (D.lawValueBlockD0 laws ha label x) =
      graphDifference D.nerve (fullBlockCochainEquiv laws q ha D.chartSupport hs₀ label x) :=
    funext (fullBlock_d0 D laws ha hs₀ hs₁ label x)
  ext z
  constructor
  · rintro ⟨cycle, ⟨x, rfl⟩, rfl⟩
    exact ⟨fullBlockCochainEquiv laws q ha D.chartSupport hs₀ label x, (hdiff x).symm⟩
  · rintro ⟨x, rfl⟩
    let actual := (fullBlockCochainEquiv laws q ha D.chartSupport hs₀ label).symm x
    refine ⟨(D.lawValueBlockComplex laws ha label).boundaryToCycles actual, ⟨actual, rfl⟩, ?_⟩
    change fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label
      (D.lawValueBlockD0 laws ha label actual) = _
    rw [hdiff]
    simp only [actual, LinearEquiv.apply_symm_apply]

/-- 全台グラフの実Law block H¹と名付き辺cochain商の同型。 -/
def fullBlockGraphH1Equiv : (D.lawValueBlockComplex laws ha label).H1 ≃ₗ[ℚ]
    (D.nerve.EdgeComponent → ℚ) ⧸ LinearMap.range (graphDifference D.nerve) :=
  Submodule.Quotient.equiv _ _ (fullBlockGraphCyclesEquiv D laws ha hs₁ label)
    (fullBlockGraph_image D laws ha hs₀ hs₁ label)

/-- H¹同型は既存商のすべての代表cocycleで名付き辺座標を読む。 -/
@[simp] theorem fullBlockGraphH1Equiv_mk
    (z : LinearMap.ker (D.lawValueBlockComplex laws ha label).d1) :
    fullBlockGraphH1Equiv D laws ha hs₀ hs₁ label
      ((LinearMap.range (D.lawValueBlockComplex laws ha label).boundaryToCycles).mkQ z) =
      (LinearMap.range (graphDifference D.nerve)).mkQ
        (fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label z.val) := rfl

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
