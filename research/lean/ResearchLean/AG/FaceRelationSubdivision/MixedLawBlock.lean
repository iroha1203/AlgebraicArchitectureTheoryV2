import ResearchLean.AG.FaceRelationSubdivision.MixedLawFiniteCoordinates
import ResearchLean.AG.FaceRelationSubdivision.MixedSelectedBasis
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteBlock

/-!
# 混在reading原始有限和の独立Law block生成

## Implementation notes

非零原始係数と同じLaw名・値から実block座標を生成し、別に生成した
実支持fiber射と項ごとに照合する。射の定義を座標同型の共役にはしない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance AtlasDefectComposition
universe u
variable {Source I J : Type u} {qi qj : Reading Source}
variable {si : I → Set qi.Target} {sj : J → Set qj.Target}
variable (laws : FiniteLawFamily Source) (hi : laws.Adequate qi) (hj : laws.Adequate qj)

/-- adequate readingで同じ発生ラベルを読むSource逆像は一致する。 -/
theorem labelFiber_source_preimage (l : LawValueLabel laws) :
    qi.read ⁻¹' labelValueFiber laws qi hi l = qj.read ⁻¹' labelValueFiber laws qj hj l := by
  have hqi : qi.CoarserThan (sourceReading Source) := by
    intro x y h
    exact congrArg qi.read h
  have hqj : qj.CoarserThan (sourceReading Source) := by
    intro x y h
    exact congrArg qj.read h
  have fi : comparisonFactor qi (sourceReading Source) hqi = qi.read := by
    funext x
    simpa only [sourceReading_read] using comparisonFactor_commutes qi (sourceReading Source) hqi x
  have fj : comparisonFactor qj (sourceReading Source) hqj = qj.read := by
    funext x
    simpa only [sourceReading_read] using comparisonFactor_commutes qj (sourceReading Source) hqj x
  have ei := labelValueFiber_eq_preimage laws qi (sourceReading Source) hi (sourceAdequate laws) hqi l
  have ej := labelValueFiber_eq_preimage laws qj (sourceReading Source) hj (sourceAdequate laws) hqj l
  rw [fi] at ei
  rw [fj] at ej
  exact ei.symm.trans ej

namespace SupportedBasisMap
variable (M : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj))

/-- 同じ発生ラベルを保つ独立block出力座標。 -/
def mixedLawBlockCoordinate (l : LawValueLabel laws)
    (x : CellCoordinate.Block laws qi hi I si l) (j : J)
    (hne : M.basisImage x.1.cell j ≠ 0) : CellCoordinate.Block laws qj hj J sj l :=
  ⟨M.mixedLawCoordinate laws hi hj x.1 j hne,
    (M.mixedLawCoordinate_label laws hi hj x.1 j hne).trans x.2⟩
/-- 独立block像の同じ原始セル名。 -/
@[simp] theorem mixedLawBlockCoordinate_cell (l) (x) (j) (hne) :
    (M.mixedLawBlockCoordinate laws hi hj l x j hne).1.cell = j := rfl
/-- 独立block像の全Law座標。 -/
@[simp] theorem mixedLawBlockCoordinate_val (l) (x) (j) (hne) :
    (M.mixedLawBlockCoordinate laws hi hj l x j hne).1 =
      M.mixedLawCoordinate laws hi hj x.1 j hne := rfl

/-- 同じ非零原始係数から独立生成するblock基底有限和。 -/
def mixedLawBlockBasis (l : LawValueLabel laws) (x : CellCoordinate.Block laws qi hi I si l) :
    CellCoordinate.Block laws qj hj J sj l →₀ ℚ :=
  ∑ j ∈ (M.basisImage x.1.cell).support.attach,
    Finsupp.single (M.mixedLawBlockCoordinate laws hi hj l x j.1 (Finsupp.mem_support_iff.mp j.2))
      (M.basisImage x.1.cell j.1)
/-- 独立block基底有限和の自由線形延長。 -/
def mixedLawBlockRaw (l : LawValueLabel laws) := freeMap (M.mixedLawBlockBasis laws hi hj l)
/-- 独立block自由射の同じ実双対。 -/
def mixedLawBlockDual (l : LawValueLabel laws) := dualCellMap (M.mixedLawBlockRaw laws hi hj l)
/-- 独立block自由射の基底評価。 -/
@[simp] theorem mixedLawBlockRaw_single (l) (x) (a : ℚ) :
    M.mixedLawBlockRaw laws hi hj l (Finsupp.single x a) = a • M.mixedLawBlockBasis laws hi hj l x :=
  freeMap_single _ _ _
/-- 同じ原始係数の独立block双対有限和。 -/
theorem mixedLawBlockDual_apply (l) (z) (x) :
    M.mixedLawBlockDual laws hi hj l z x =
      ∑ j ∈ (M.basisImage x.1.cell).support.attach,
        M.basisImage x.1.cell j.1 *
          z (M.mixedLawBlockCoordinate laws hi hj l x j.1 (Finsupp.mem_support_iff.mp j.2)) := by
  rw [mixedLawBlockDual, dualCellMap_apply, mixedLawBlockRaw_single, one_smul,
    mixedLawBlockBasis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact freeDualEquiv_single _ _ _

/-- 独立全Law有限和と独立block有限和の同じ座標正方形。 -/
theorem mixedLawDual_block (l) (z) :
    lawBlockRead laws hi si l (M.mixedLawDual laws hi hj z) =
      M.mixedLawBlockDual laws hi hj l (lawBlockRead laws hj sj l z) := by
  funext x
  rw [lawBlockRead_apply, mixedLawDual_apply, mixedLawBlockDual_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lawBlockRead_apply, mixedLawBlockCoordinate_val]

/-- 独立block有限和と独立実fiber射は同じ原始項で可換。 -/
theorem mixedLawBlockDual_fiber (l) (z) :
    blockFiberEquiv laws hi si l (M.mixedLawBlockDual laws hi hj l z) =
      dualCellMap (M.mixedSelected (labelValueFiber laws qi hi l) (labelValueFiber laws qj hj l)
        (labelFiber_source_preimage laws hi hj l)) (blockFiberEquiv laws hj sj l z) := by
  funext i
  rw [blockFiberEquiv_apply, mixedLawBlockDual_apply, mixedSelectedDual_apply]
  simp only [CellCoordinate.targetSubsetEquivBlock_cell]
  apply Finset.sum_congr rfl
  intro j hmem
  congr 1
  rw [blockFiberEquiv_apply]
  congr 1
  apply CellCoordinate.block_cell_injective laws qj hj J sj l
  exact (M.mixedLawBlockCoordinate_cell laws hi hj l _ _ (Finsupp.mem_support_iff.mp j.2)).trans
    (CellCoordinate.targetSubsetEquivBlock_cell laws qj hj J sj l
      (M.mixedSelectedCell (labelValueFiber laws qi hi l) (labelValueFiber laws qj hj l)
        (labelFiber_source_preimage laws hi hj l) i j.1 (Finsupp.mem_support_iff.mp j.2))).symm

/-- 同じ独立全Law射と実ラベルfiber射も可換。 -/
theorem mixedLawDual_fiber (l) (z) :
    lawFiberRead laws hi si l (M.mixedLawDual laws hi hj z) =
      dualCellMap (M.mixedSelected (labelValueFiber laws qi hi l) (labelValueFiber laws qj hj l)
        (labelFiber_source_preimage laws hi hj l)) (lawFiberRead laws hj sj l z) := by
  rw [← blockFiberEquiv_read, mixedLawDual_block, mixedLawBlockDual_fiber, blockFiberEquiv_read]

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
