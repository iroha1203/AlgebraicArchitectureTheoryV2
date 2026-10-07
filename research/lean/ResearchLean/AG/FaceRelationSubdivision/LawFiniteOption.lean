import ResearchLean.AG.FaceRelationSubdivision.LawFiniteBlockHom
import ResearchLean.AG.FaceRelationSubdivision.IncidenceBasis
import ResearchLean.AG.FaceRelationSubdivision.LawBlockComparison
import Formal.Util.AssertStandardAxioms

/-!
# 有限和Law生成と同じ原始Option比較

## Implementation notes

単一・零の原始像の評価から既存生成式へ接続する。射の一致を対象の同値から
推測せず、同じセル名・発生ラベルによる座標等号を証明する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source I : Type u} {q : Reading Source}
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- セル名と発生ラベルの一致は同じK0座標の等号を与える。 -/
theorem coordinate_eq_of_cell_label (si : I → Set q.Target)
    (x y : CellCoordinate laws q ha I si)
    (hc : x.cell = y.cell)
    (hl : x.lawValueLabel laws q ha I si = y.lawValueLabel laws q ha I si) : x = y := by
  let l := x.lawValueLabel laws q ha I si
  have h := CellCoordinate.block_cell_injective laws q ha I si l
    (a₁ := ⟨x, rfl⟩) (a₂ := ⟨y, hl.symm⟩) hc
  exact congrArg (fun b : CellCoordinate.Block laws q ha I si l => b.1) h

namespace IncidenceSupportedComparison
variable {Nc Nf : ResolutionInvariance.TargetSupportedNerve q}
variable (M : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) Nc Nf)

/-- 原始頂点基底有限和のLaw射は同じ生成pullback0。 -/
theorem basisLaw0_eq_generated : M.basis0.lawDual laws ha = M.generatedPullback0 laws ha ha := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.basis0.lawDual_apply_single laws ha z x (M.chartMap x.cell) (M.basis0_image x.cell),
    M.generatedPullback0_apply]
  apply congrArg z
  apply coordinate_eq_of_cell_label laws ha
  · rw [SupportedBasisMap.lawCoordinate_cell, M.chartCoordinateMap_cell]
  · exact (M.basis0.lawCoordinate_label laws ha x _ _).trans
      (M.chartCoordinateMap_lawValueLabel laws ha ha x).symm

/-- 原始辺の零/単一有限和は同じOption生成pullback1。 -/
theorem basisLaw1_eq_generated : M.basis1.lawDual laws ha = M.generatedPullback1 laws ha ha := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.generatedPullback1_apply]
  cases hm : M.edgeMap x.cell with
  | none =>
    rw [M.edgeCoordinateMapOption_eq_none laws ha ha x hm, Option.elim_none]
    exact M.basis1.lawDual_apply_zero laws ha z x
      (by rw [M.basis1_image, hm, rationalOptionCell_none])
  | some j =>
    rw [M.edgeCoordinateMapOption_eq_some laws ha ha x j hm, Option.elim_some,
      M.basis1.lawDual_apply_single laws ha z x j
        (by rw [M.basis1_image, hm, rationalOptionCell_some])]
    apply congrArg z
    apply coordinate_eq_of_cell_label laws ha
    · rw [SupportedBasisMap.lawCoordinate_cell, M.edgeCoordinateMap_cell]
    · exact (M.basis1.lawCoordinate_label laws ha x _ _).trans
        (M.edgeCoordinateMap_lawValueLabel laws ha ha x j hm).symm

/-- 原始面の零/単一有限和は同じOption生成pullback2。 -/
theorem basisLaw2_eq_generated : M.basis2.lawDual laws ha = M.generatedPullback2 laws ha ha := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.generatedPullback2_apply]
  cases hm : M.faceMap x.cell with
  | none =>
    rw [M.faceCoordinateMapOption_eq_none laws ha ha x hm, Option.elim_none]
    exact M.basis2.lawDual_apply_zero laws ha z x
      (by rw [M.basis2_image, hm, rationalOptionCell_none])
  | some j =>
    rw [M.faceCoordinateMapOption_eq_some laws ha ha x j hm, Option.elim_some,
      M.basis2.lawDual_apply_single laws ha z x j
        (by rw [M.basis2_image, hm, rationalOptionCell_some])]
    apply congrArg z
    apply coordinate_eq_of_cell_label laws ha
    · rw [SupportedBasisMap.lawCoordinate_cell, M.faceCoordinateMap_cell]
    · exact (M.basis2.lawCoordinate_label laws ha x _ _).trans
        (M.faceCoordinateMap_lawValueLabel laws ha ha x j hm).symm

/-- 原始finite-map chain式から作ったLaw Homは同じ生成Homに全三成分一致。 -/
theorem basisLawHom_eq_generated [Fintype Source]
    (h0 : (TargetSupportedNerve.rawD1 Nc).raw.comp M.basis1.raw =
      M.basis0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
    (h1 : (TargetSupportedNerve.rawD2 Nc).raw.comp M.basis2.raw =
      M.basis1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw) :
    lawFiniteHom M.basis0 M.basis1 M.basis2 h0 h1 laws ha = M.generatedComparisonHom laws ha ha := by
  apply cochain_ext
  · exact M.basisLaw0_eq_generated laws ha
  · exact M.basisLaw1_eq_generated laws ha
  · exact M.basisLaw2_eq_generated laws ha

/-- 原始頂点基底像の独立 block 双対は同じ生成 pullback0。 -/
theorem basisBlock0_eq_generated (l : LawValueLabel laws) :
    M.basis0.lawBlockDual laws ha l=M.generatedBlockPullback0 laws ha ha l := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.basis0.lawBlockDual_apply_single laws ha l z x (M.chartMap x.val.cell) (M.basis0_image x.val.cell),
    M.generatedBlockPullback0_apply]
  apply congrArg z
  apply CellCoordinate.block_cell_injective laws q ha _ _ l
  exact (M.basis0.lawBlockCoordinate_cell laws ha l x _ _).trans
    (M.chartBlockCoordinateMap_cell laws ha ha l x).symm
/-- 原始辺の零/単一基底像の独立 block 双対は同じ生成 pullback1。 -/
theorem basisBlock1_eq_generated (l : LawValueLabel laws) :
    M.basis1.lawBlockDual laws ha l=M.generatedBlockPullback1 laws ha ha l := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.generatedBlockPullback1_apply]
  cases hm : M.edgeMap x.val.cell with
  | none =>
    rw [M.edgeBlockCoordinateMapOption_eq_none laws ha ha l x hm,Option.elim_none]
    exact M.basis1.lawBlockDual_apply_zero laws ha l z x
      (by rw [M.basis1_image,hm,rationalOptionCell_none])
  | some j =>
    rw [M.edgeBlockCoordinateMapOption_eq_some laws ha ha l x j hm,Option.elim_some,
      M.basis1.lawBlockDual_apply_single laws ha l z x j
        (by rw [M.basis1_image,hm,rationalOptionCell_some])]
    apply congrArg z
    apply CellCoordinate.block_cell_injective laws q ha _ _ l
    exact (M.basis1.lawBlockCoordinate_cell laws ha l x _ _).trans
      (M.edgeBlockCoordinateMap_cell laws ha ha l x j hm).symm
/-- 原始面の零/単一基底像の独立 block 双対は同じ生成 pullback2。 -/
theorem basisBlock2_eq_generated (l : LawValueLabel laws) :
    M.basis2.lawBlockDual laws ha l=M.generatedBlockPullback2 laws ha ha l := by
  apply LinearMap.ext
  intro z
  funext x
  rw [M.generatedBlockPullback2_apply]
  cases hm : M.faceMap x.val.cell with
  | none =>
    rw [M.faceBlockCoordinateMapOption_eq_none laws ha ha l x hm,Option.elim_none]
    exact M.basis2.lawBlockDual_apply_zero laws ha l z x
      (by rw [M.basis2_image,hm,rationalOptionCell_none])
  | some j =>
    rw [M.faceBlockCoordinateMapOption_eq_some laws ha ha l x j hm,Option.elim_some,
      M.basis2.lawBlockDual_apply_single laws ha l z x j
        (by rw [M.basis2_image,hm,rationalOptionCell_some])]
    apply congrArg z
    apply CellCoordinate.block_cell_injective laws q ha _ _ l
    exact (M.basis2.lawBlockCoordinate_cell laws ha l x _ _).trans
      (M.faceBlockCoordinateMap_cell laws ha ha l x j hm).symm
/-- 独立 block 有限和 Hom は原始 Option 比較の生成 Hom と全三成分で一致する。 -/
theorem basisBlockHom_eq_generated [Fintype Source] (l : LawValueLabel laws)
    (h0 : (TargetSupportedNerve.rawD1 Nc).raw.comp M.basis1.raw=M.basis0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
    (h1 : (TargetSupportedNerve.rawD2 Nc).raw.comp M.basis2.raw=M.basis1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw) :
    blockFiniteHom laws ha M.basis0 M.basis1 M.basis2 h0 h1 l=M.generatedBlockComparisonHom laws ha ha l := by
  apply cochain_ext
  · exact M.basisBlock0_eq_generated laws ha l
  · exact M.basisBlock1_eq_generated laws ha l
  · exact M.basisBlock2_eq_generated laws ha l

end IncidenceSupportedComparison
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
