import ResearchLean.AG.FaceRelationSubdivision.GeneratedComposition
import ResearchLean.AG.FaceRelationSubdivision.LawBlockComparison
import Formal.Util.AssertStandardAxioms

/-!
# 同じLawラベルを保つ原始比較の合成

G-134 A・D。ラベルの重複度を保持して、直接生成した成分Homと合成を照合する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u

variable {Source : Type u}
variable {q₀ q₁ q₂ : Reading Source}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}
variable (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂)
variable (laws : FiniteLawFamily Source)
variable (label : LawValueLabel laws)
variable (h₀ : laws.Adequate q₀) (h₁ : laws.Adequate q₁) (h₂ : laws.Adequate q₂)

/-- A の次数0座標の合成。Lawと値の同定を保持する。 -/
theorem chartBlockCoordinateMap_comp (c : N₂.ChartBlockCoordinate laws h₂ label) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).chartBlockCoordinateMap laws h₀ h₂ label c =
      M₀₁.chartBlockCoordinateMap laws h₀ h₁ label (M₁₂.chartBlockCoordinateMap laws h₁ h₂ label c) := by
  apply Subtype.ext
  apply CellCoordinate.ext <;> rfl

/-- A の edge 座標の部分合成。二つの退化経路とmapped経路を区別する。 -/
theorem edgeBlockCoordinateMapOption_comp (c : N₂.EdgeBlockCoordinate laws h₂ label) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeBlockCoordinateMapOption laws h₀ h₂ label c =
      (M₁₂.edgeBlockCoordinateMapOption laws h₁ h₂ label c).bind
        (M₀₁.edgeBlockCoordinateMapOption laws h₀ h₁ label) := by
  cases hb : M₁₂.edgeMap c.1.cell with
  | none =>
    have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.1.cell = none := by
      simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_none]
    rw [M₁₂.edgeBlockCoordinateMapOption_eq_none laws h₁ h₂ label c hb,
      (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeBlockCoordinateMapOption_eq_none laws h₀ h₂ label c hc]
    rfl
  | some b =>
    let cb := M₁₂.edgeBlockCoordinateMap laws h₁ h₂ label c b hb
    have hcb : cb.1.cell = b := rfl
    rw [M₁₂.edgeBlockCoordinateMapOption_eq_some laws h₁ h₂ label c b hb, Option.bind_some]
    cases ha : M₀₁.edgeMap b with
    | none =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.1.cell = none := by
        simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeBlockCoordinateMapOption_eq_none laws h₀ h₂ label c hc,
        M₀₁.edgeBlockCoordinateMapOption_eq_none laws h₀ h₁ label cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.1.cell = some a := by
        simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeBlockCoordinateMapOption_eq_some laws h₀ h₂ label c a hc,
        M₀₁.edgeBlockCoordinateMapOption_eq_some laws h₀ h₁ label cb a (by rw [hcb]; exact ha)]
      rfl

/-- A の face 座標の部分合成。二つの退化経路とmapped経路を区別する。 -/
theorem faceBlockCoordinateMapOption_comp (c : N₂.FaceBlockCoordinate laws h₂ label) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceBlockCoordinateMapOption laws h₀ h₂ label c =
      (M₁₂.faceBlockCoordinateMapOption laws h₁ h₂ label c).bind
        (M₀₁.faceBlockCoordinateMapOption laws h₀ h₁ label) := by
  cases hb : M₁₂.faceMap c.1.cell with
  | none =>
    have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.1.cell = none := by
      simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_none]
    rw [M₁₂.faceBlockCoordinateMapOption_eq_none laws h₁ h₂ label c hb,
      (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceBlockCoordinateMapOption_eq_none laws h₀ h₂ label c hc]
    rfl
  | some b =>
    let cb := M₁₂.faceBlockCoordinateMap laws h₁ h₂ label c b hb
    have hcb : cb.1.cell = b := rfl
    rw [M₁₂.faceBlockCoordinateMapOption_eq_some laws h₁ h₂ label c b hb, Option.bind_some]
    cases ha : M₀₁.faceMap b with
    | none =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.1.cell = none := by
        simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).faceBlockCoordinateMapOption_eq_none laws h₀ h₂ label c hc,
        M₀₁.faceBlockCoordinateMapOption_eq_none laws h₀ h₁ label cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.1.cell = some a := by
        simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).faceBlockCoordinateMapOption_eq_some laws h₀ h₂ label c a hc,
        M₀₁.faceBlockCoordinateMapOption_eq_some laws h₀ h₁ label cb a (by rw [hcb]; exact ha)]
      rfl

/-- A の次数0の直接生成pullbackと合成の一致。 -/
theorem generatedBlockPullback0_comp (x : N₀.ChartBlockCoordinate laws h₀ label → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedBlockPullback0 laws h₀ h₂ label x =
      M₁₂.generatedBlockPullback0 laws h₁ h₂ label (M₀₁.generatedBlockPullback0 laws h₀ h₁ label x) := by
  funext c
  simp only [IncidenceSupportedComparison.generatedBlockPullback0_apply,
    chartBlockCoordinateMap_comp M₀₁ M₁₂ laws label h₀ h₁ h₂]

/-- A の次数1の直接生成pullbackと合成の一致。 -/
theorem generatedBlockPullback1_comp (x : N₀.EdgeBlockCoordinate laws h₀ label → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedBlockPullback1 laws h₀ h₂ label x =
      M₁₂.generatedBlockPullback1 laws h₁ h₂ label (M₀₁.generatedBlockPullback1 laws h₀ h₁ label x) := by
  funext c
  rw [IncidenceSupportedComparison.generatedBlockPullback1_apply,
    IncidenceSupportedComparison.generatedBlockPullback1_apply,
    edgeBlockCoordinateMapOption_comp M₀₁ M₁₂ laws label h₀ h₁ h₂]
  cases M₁₂.edgeBlockCoordinateMapOption laws h₁ h₂ label c with
  | none => rfl
  | some b => exact (M₀₁.generatedBlockPullback1_apply laws h₀ h₁ label x b).symm

/-- A の次数2の直接生成pullbackと合成の一致。 -/
theorem generatedBlockPullback2_comp (x : N₀.FaceBlockCoordinate laws h₀ label → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedBlockPullback2 laws h₀ h₂ label x =
      M₁₂.generatedBlockPullback2 laws h₁ h₂ label (M₀₁.generatedBlockPullback2 laws h₀ h₁ label x) := by
  funext c
  rw [IncidenceSupportedComparison.generatedBlockPullback2_apply,
    IncidenceSupportedComparison.generatedBlockPullback2_apply,
    faceBlockCoordinateMapOption_comp M₀₁ M₁₂ laws label h₀ h₁ h₂]
  cases M₁₂.faceBlockCoordinateMapOption laws h₁ h₂ label c with
  | none => rfl
  | some b => exact (M₀₁.generatedBlockPullback2_apply laws h₀ h₁ label x b).symm

/-- A の全Law直接生成Homの一致。全三計算成分と可換性を含む等号。 -/
theorem generatedBlockComparisonHom_comp [Fintype Source] :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedBlockComparisonHom laws h₀ h₂ label =
      cochainComp (M₀₁.generatedBlockComparisonHom laws h₀ h₁ label)
        (M₁₂.generatedBlockComparisonHom laws h₁ h₂ label) := by
  apply cochain_ext
  · exact LinearMap.ext (generatedBlockPullback0_comp M₀₁ M₁₂ laws label h₀ h₁ h₂)
  · exact LinearMap.ext (generatedBlockPullback1_comp M₀₁ M₁₂ laws label h₀ h₁ h₂)
  · exact LinearMap.ext (generatedBlockPullback2_comp M₀₁ M₁₂ laws label h₀ h₁ h₂)

/-- A の全Law既存H¹商での直接生成比較の合成。 -/
theorem generatedBlockComparisonH1Map_comp [Fintype Source] :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedBlockComparisonH1Map laws h₀ h₂ label =
      (M₁₂.generatedBlockComparisonH1Map laws h₁ h₂ label).comp
        (M₀₁.generatedBlockComparisonH1Map laws h₀ h₁ label) := by
  change ((IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedBlockComparisonHom laws h₀ h₂ label).h1Map = _
  rw [generatedBlockComparisonHom_comp M₀₁ M₁₂ laws label h₀ h₁ h₂, cochainComp_h1Map]
  rfl


/-- 恒等の原始比較から生成した実Homは三次数の恒等。 -/
theorem identity_generatedBlockComparisonHom [Fintype Source]
    (q : Reading Source) (N : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (ha : laws.Adequate q) (label : LawValueLabel laws) :
    (IncidenceSupportedComparison.identity q N).generatedBlockComparisonHom laws ha ha label =
      cochainId (N.lawValueBlockComplex laws ha label) := by
  apply cochain_ext <;> rfl

/-- 原始恒等からの実H¹写像は既存商の恒等。 -/
theorem identity_generatedBlockComparisonH1Map [Fintype Source]
    (q : Reading Source) (N : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (ha : laws.Adequate q) (label : LawValueLabel laws) :
    (IncidenceSupportedComparison.identity q N).generatedBlockComparisonH1Map laws ha ha label =
      LinearMap.id := by
  change ((IncidenceSupportedComparison.identity q N).generatedBlockComparisonHom laws ha ha label).h1Map = _
  rw [identity_generatedBlockComparisonHom, cochainId_h1Map]


end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
