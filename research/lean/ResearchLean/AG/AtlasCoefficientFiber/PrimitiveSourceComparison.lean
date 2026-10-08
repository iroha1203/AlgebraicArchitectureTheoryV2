import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveSourceBasis
import ResearchLean.AG.FaceRelationSubdivision.MixedLawFiniteCoordinates
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteOption
import ResearchLean.AG.FaceRelationSubdivision.RawLawHomotopy

/-!
# 同じSource原始有限和と独立生成比較

Implementation notes: 原始r表の等号は一般補題の方向仮定として扱う。
後続の正操作列では各constructorと有限合成からこの等号を生成する。
既存subset・Law射は独立に生成されたまま全三成分で照合する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.PrimitiveSource
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

/-- 原reading因子の逆像は同じSource台を選ぶ。 -/
theorem sourceSubset_eq (A : Set qc.Target) :
    qf.read ⁻¹' (comparisonFactor qc qf h ⁻¹' A) = qc.read ⁻¹' A := by
  ext x
  simp only [Set.mem_preimage, comparisonFactor_commutes]

/-- 原始chart基底の実台選択は同じ独立生成chain射。 -/
theorem basis0_selected (A : Set qc.Target) :
    (basis0 M).mixedSelected (comparisonFactor qc qf h ⁻¹' A) A (sourceSubset_eq (h := h) A) =
      M.supportedChainMap0 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) := by
  apply Finsupp.lhom_ext
  intro v a
  apply selectedEmbed_injective Nc.chartSupport A
  rw [SupportedBasisMap.mixedSelectedEmbed_apply, selectedEmbed_single,
    SupportedBasisMap.raw_single, basis0_image, M.supportedChainMap0_single, map_smul]
  rw [selectedEmbed_single, M.targetSubsetChartMap_val]

/-- 原始edge基底の実台選択は同じ独立生成chain射。 -/
theorem basis1_selected (A : Set qc.Target) :
    (basis1 M).mixedSelected (comparisonFactor qc qf h ⁻¹' A) A (sourceSubset_eq (h := h) A) =
      M.supportedChainMap1 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) := by
  apply Finsupp.lhom_ext
  intro v a
  apply selectedEmbed_injective Nc.edgeSupport A
  rw [SupportedBasisMap.mixedSelectedEmbed_apply, selectedEmbed_single,
    SupportedBasisMap.raw_single, basis1_image, M.supportedChainMap1_single, map_smul]
  cases hm : M.edgeMap v.1 with
  | none =>
    rw [M.targetSubsetEdgeMapOption_eq_none A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) v hm,
      rationalOptionCell_none, rationalOptionCell_none, map_zero]
  | some j =>
    rw [M.targetSubsetEdgeMapOption_eq_some A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) v j hm,
      rationalOptionCell_some, rationalOptionCell_some, selectedEmbed_single,
      M.targetSubsetEdgeMap_val]

/-- 原始face基底の実台選択は同じ独立生成chain射。 -/
theorem basis2_selected (A : Set qc.Target) :
    (basis2 M).mixedSelected (comparisonFactor qc qf h ⁻¹' A) A (sourceSubset_eq (h := h) A) =
      M.supportedChainMap2 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) := by
  apply Finsupp.lhom_ext
  intro v a
  apply selectedEmbed_injective Nc.faceSupport A
  rw [SupportedBasisMap.mixedSelectedEmbed_apply, selectedEmbed_single,
    SupportedBasisMap.raw_single, basis2_image, M.supportedChainMap2_single, map_smul]
  cases hm : M.faceMap v.1 with
  | none =>
    rw [M.targetSubsetFaceMapOption_eq_none A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) v hm,
      rationalOptionCell_none, rationalOptionCell_none, map_zero]
  | some j =>
    rw [M.targetSubsetFaceMapOption_eq_some A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) v j hm,
      rationalOptionCell_some, rationalOptionCell_some, selectedEmbed_single,
      M.targetSubsetFaceMap_val]

variable (E : RawChainEquivalence Nc Nf)
variable (h0 : E.r0 = basis0 M) (h1 : E.r1 = basis1 M) (h2 : E.r2 = basis2 M)

include h0 h1 h2 in
/-- 原始r表が一致すれば実subset有限和は独立生成した元aSubnerve全Hom。 -/
theorem rawR_eq_generated (A : Set qc.Target) :
    E.targetRHom A (comparisonFactor qc qf h ⁻¹' A) (sourceSubset_eq (h := h) A) =
      M.aSubnerveComparisonHom A := by
  apply cochain_ext
  · change (E.targetRHom A (comparisonFactor qc qf h ⁻¹' A) (sourceSubset_eq (h := h) A)).f0 =
      M.targetSubsetPullback0 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)
    rw [RawChainEquivalence.targetRHom_f0, h0]
    apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    rw [dualCellMap_dual, basis0_selected M A, M.supportedChainMap0_dual]
  · change (E.targetRHom A (comparisonFactor qc qf h ⁻¹' A) (sourceSubset_eq (h := h) A)).f1 =
      M.targetSubsetPullback1 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)
    rw [RawChainEquivalence.targetRHom_f1, h1]
    apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    rw [dualCellMap_dual, basis1_selected M A, M.supportedChainMap1_dual]
  · change (E.targetRHom A (comparisonFactor qc qf h ⁻¹' A) (sourceSubset_eq (h := h) A)).f2 =
      M.targetSubsetPullback2 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)
    rw [RawChainEquivalence.targetRHom_f2, h2]
    apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    rw [dualCellMap_dual, basis2_selected M A, M.supportedChainMap2_dual]

variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- Source原始chart双対は同じ元Law/label生成座標の全値。 -/
theorem basis0_law : (basis0 M).mixedLawDual laws (adequate_of_coarser laws h ha) ha =
    M.generatedPullback0 laws ha (adequate_of_coarser laws h ha) := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.generatedPullback0_apply]
  rw [SupportedBasisMap.mixedLawDual_apply_single _ laws _ _ z x (M.chartMap x.cell)
    (basis0_image M x.cell)]
  apply congrArg z
  apply coordinate_eq_of_cell_label laws ha
  · rw [SupportedBasisMap.mixedLawCoordinate_cell, M.chartCoordinateMap_cell]
  · exact (SupportedBasisMap.mixedLawCoordinate_label _ laws _ _ x _ _).trans
      (M.chartCoordinateMap_lawValueLabel laws ha _ x).symm

/-- Source原始edge双対は同じ元Law/value生成座標の全値。 -/
theorem basis1_law : (basis1 M).mixedLawDual laws (adequate_of_coarser laws h ha) ha =
    M.generatedPullback1 laws ha (adequate_of_coarser laws h ha) := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.generatedPullback1_apply]
  cases hm : M.edgeMap x.cell with
  | none =>
    rw [M.edgeCoordinateMapOption_eq_none laws ha _ x hm, Option.elim_none]
    exact SupportedBasisMap.mixedLawDual_apply_zero _ laws _ _ z x
      (by rw [basis1_image, hm, rationalOptionCell_none])
  | some j =>
    rw [M.edgeCoordinateMapOption_eq_some laws ha _ x j hm, Option.elim_some,
      SupportedBasisMap.mixedLawDual_apply_single _ laws _ _ z x j
        (by rw [basis1_image, hm, rationalOptionCell_some])]
    apply congrArg z
    apply coordinate_eq_of_cell_label laws ha
    · rw [SupportedBasisMap.mixedLawCoordinate_cell, M.edgeCoordinateMap_cell]
    · exact (SupportedBasisMap.mixedLawCoordinate_label _ laws _ _ x _ _).trans
        (M.edgeCoordinateMap_lawValueLabel laws ha _ x j hm).symm

/-- Source原始face双対は同じ元Law/value生成座標の全値。 -/
theorem basis2_law : (basis2 M).mixedLawDual laws (adequate_of_coarser laws h ha) ha =
    M.generatedPullback2 laws ha (adequate_of_coarser laws h ha) := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.generatedPullback2_apply]
  cases hm : M.faceMap x.cell with
  | none =>
    rw [M.faceCoordinateMapOption_eq_none laws ha _ x hm, Option.elim_none]
    exact SupportedBasisMap.mixedLawDual_apply_zero _ laws _ _ z x
      (by rw [basis2_image, hm, rationalOptionCell_none])
  | some j =>
    rw [M.faceCoordinateMapOption_eq_some laws ha _ x j hm, Option.elim_some,
      SupportedBasisMap.mixedLawDual_apply_single _ laws _ _ z x j
        (by rw [basis2_image, hm, rationalOptionCell_some])]
    apply congrArg z
    apply coordinate_eq_of_cell_label laws ha
    · rw [SupportedBasisMap.mixedLawCoordinate_cell, M.faceCoordinateMap_cell]
    · exact (SupportedBasisMap.mixedLawCoordinate_label _ laws _ _ x _ _).trans
        (M.faceCoordinateMap_lawValueLabel laws ha _ x j hm).symm

variable [Fintype Source]

include h0 h1 h2 in
/-- 原始r表一致は全Lawの元独立generatedComparisonHomの全三成分一致を与える。 -/
theorem rawLawR_eq_generated :
    E.lawR laws ha (adequate_of_coarser laws h ha) =
      M.generatedComparisonHom laws ha (adequate_of_coarser laws h ha) := by
  apply cochain_ext
  · rw [RawChainEquivalence.lawR_f0, h0, M.generatedComparisonHom_f0]
    exact basis0_law M laws ha
  · rw [RawChainEquivalence.lawR_f1, h1, M.generatedComparisonHom_f1]
    exact basis1_law M laws ha
  · rw [RawChainEquivalence.lawR_f2, h2, M.generatedComparisonHom_f2]
    exact basis2_law M laws ha

end AAT.AG.AtlasCoefficientFiber.PrimitiveSource
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.sourceSubset_eq
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis0_selected
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis1_selected
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis2_selected
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.rawR_eq_generated
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis0_law
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis1_law
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis2_law
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.rawLawR_eq_generated
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.PrimitiveSource
