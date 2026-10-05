import ResearchLean.AG.AtlasDefectComposition.WitnessOnePeriods
import ResearchLean.AG.AtlasDefectComposition.FullSupportPullback
import Formal.Util.AssertStandardAxioms

/-! # W1の実生成比較とperiod

原始Option射から生成された二射が、実H¹のperiod同型を通して包含・射影になる。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase

/-- 原始前段射から得る実cochain比較の、名付き辺座標での作用。 -/
theorem forward_standard1 (label : LawValueLabel laws)
    (x : N₀.EdgeBlockCoordinate laws adequate₀ label → ℚ) :
    fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ label
      (M₀₁.generatedBlockPullback1 laws adequate₀ adequate₁ label x) =
    ![fullBlockCochainEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀ label x 0,
      fullBlockCochainEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀ label x 1,
      fullBlockCochainEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀ label x 2, 0, 0, 0] := by
  funext e
  fin_cases e
  · exact fullBlock_pullback1_some M₀₁ laws adequate₀ adequate₁ edgeSupport_univ₀ edgeSupport_univ₁ label x 0 0 rfl
  · exact fullBlock_pullback1_some M₀₁ laws adequate₀ adequate₁ edgeSupport_univ₀ edgeSupport_univ₁ label x 1 1 rfl
  · exact fullBlock_pullback1_some M₀₁ laws adequate₀ adequate₁ edgeSupport_univ₀ edgeSupport_univ₁ label x 2 2 rfl
  · exact fullBlock_pullback1_none M₀₁ laws adequate₀ adequate₁ edgeSupport_univ₁ label x 3 rfl
  · exact fullBlock_pullback1_none M₀₁ laws adequate₀ adequate₁ edgeSupport_univ₁ label x 4 rfl
  · exact fullBlock_pullback1_none M₀₁ laws adequate₀ adequate₁ edgeSupport_univ₁ label x 5 rfl

/-- 原始後段射から得る実cochain比較の、名付き辺座標での作用。 -/
theorem backward_standard1 (label : LawValueLabel laws)
    (x : N₁.EdgeBlockCoordinate laws adequate₁ label → ℚ) :
    fullBlockCochainEquiv laws q₂ adequate₂ N₂.edgeSupport edgeSupport_univ₂ label
      (M₁₂.generatedBlockPullback1 laws adequate₁ adequate₂ label x) =
    ![fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ label x 0,
      fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ label x 1,
      fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ label x 2] := by
  funext e
  fin_cases e
  · exact fullBlock_pullback1_some M₁₂ laws adequate₁ adequate₂ edgeSupport_univ₁ edgeSupport_univ₂ label x 0 0 rfl
  · exact fullBlock_pullback1_some M₁₂ laws adequate₁ adequate₂ edgeSupport_univ₁ edgeSupport_univ₂ label x 1 1 rfl
  · exact fullBlock_pullback1_some M₁₂ laws adequate₁ adequate₂ edgeSupport_univ₁ edgeSupport_univ₂ label x 2 2 rfl

/-- 直接原始射の実block cochain比較は同名辺を保持する。 -/
theorem direct_block_standard1 (label : LawValueLabel laws)
    (x : N₀.EdgeBlockCoordinate laws adequate₀ label → ℚ) :
    fullBlockCochainEquiv laws q₂ adequate₂ N₂.edgeSupport edgeSupport_univ₂ label
      (M₀₂.generatedBlockPullback1 laws adequate₀ adequate₂ label x) =
    fullBlockCochainEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀ label x := by
  funext e
  exact fullBlock_pullback1_some M₀₂ laws adequate₀ adequate₂ edgeSupport_univ₀ edgeSupport_univ₂ label x e e (direct_edge e)

/-- 既存商で生成した前段H¹比較は、periodで第一成分への包含になる。 -/
theorem forward_period (label : LawValueLabel laws)
    (x : (N₀.lawValueBlockComplex laws adequate₀ label).H1) :
    h1Periods₁ label (M₀₁.generatedBlockComparisonH1Map laws adequate₀ adequate₁ label x) =
      (h1Period₀ label x, 0) := by
  obtain ⟨z, rfl⟩ := (LinearMap.range (N₀.lawValueBlockComplex laws adequate₀ label).boundaryToCycles).mkQ_surjective x
  change h1Periods₁ label ((M₀₁.generatedBlockComparisonHom laws adequate₀ adequate₁ label).h1Map _) = _
  rw [ThreeCochainComplex.Hom.h1Map_mk, h1Periods₁_mk, h1Period₀_mk]
  change twoTrianglePeriods (fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ label
    (M₀₁.generatedBlockPullback1 laws adequate₀ adequate₁ label z.val)) = _
  rw [forward_standard1]
  simp [twoTrianglePeriods, trianglePeriod]

/-- 既存商で生成した後段H¹比較は、periodで第一成分への射影になる。 -/
theorem backward_period (label : LawValueLabel laws)
    (x : (N₁.lawValueBlockComplex laws adequate₁ label).H1) :
    h1Period₂ label (M₁₂.generatedBlockComparisonH1Map laws adequate₁ adequate₂ label x) =
      (h1Periods₁ label x).1 := by
  obtain ⟨z, rfl⟩ := (LinearMap.range (N₁.lawValueBlockComplex laws adequate₁ label).boundaryToCycles).mkQ_surjective x
  change h1Period₂ label ((M₁₂.generatedBlockComparisonHom laws adequate₁ adequate₂ label).h1Map _) = _
  rw [ThreeCochainComplex.Hom.h1Map_mk, h1Period₂_mk, h1Periods₁_mk]
  change trianglePeriod (fullBlockCochainEquiv laws q₂ adequate₂ N₂.edgeSupport edgeSupport_univ₂ label
    (M₁₂.generatedBlockPullback1 laws adequate₁ adequate₂ label z.val)) = _
  rw [backward_standard1]
  simp [trianglePeriod, twoTrianglePeriods]

/-- 既存商で直接生成したH¹比較は、同じperiodを保持する。 -/
theorem direct_block_period (label : LawValueLabel laws)
    (x : (N₀.lawValueBlockComplex laws adequate₀ label).H1) :
    h1Period₂ label (M₀₂.generatedBlockComparisonH1Map laws adequate₀ adequate₂ label x) =
      h1Period₀ label x := by
  obtain ⟨z, rfl⟩ := (LinearMap.range (N₀.lawValueBlockComplex laws adequate₀ label).boundaryToCycles).mkQ_surjective x
  change h1Period₂ label ((M₀₂.generatedBlockComparisonHom laws adequate₀ adequate₂ label).h1Map _) = _
  rw [ThreeCochainComplex.Hom.h1Map_mk, h1Period₂_mk, h1Period₀_mk]
  exact congrArg trianglePeriod (direct_block_standard1 label z.val)

end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
