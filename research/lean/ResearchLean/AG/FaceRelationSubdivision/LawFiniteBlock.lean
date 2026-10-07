import ResearchLean.AG.FaceRelationSubdivision.LawFiniteHom
import Formal.Util.AssertStandardAxioms

/-!
# 同じ原始有限和のLaw block生成

## Implementation notes

各非零像のラベル保存証明でblock基底像を生成する。全Law射の値から
block射を定義する方法は用いず、同じ原始セル有限和をもう一度評価する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {q : Reading Source}
variable {si : I → Set q.Target} {sj : J → Set q.Target}
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 全Law座標から同じラベルblockを読む実projection。 -/
def lawBlockRead (si : I → Set q.Target) (l : LawValueLabel laws) :
    (CellCoordinate laws q ha I si → ℚ) →ₗ[ℚ] (CellCoordinate.Block laws q ha I si l → ℚ) where
  toFun z x := z x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- block projectionの同じ座標評価。 -/
@[simp] theorem lawBlockRead_apply (si : I → Set q.Target) (l) (z) (x) :
    lawBlockRead laws ha si l z x = z x.1 := rfl

/-- 同じlabel blockとfiberのセルcochainを同定する。 -/
def blockFiberEquiv (si : I → Set q.Target) (l : LawValueLabel laws) :
    (CellCoordinate.Block laws q ha I si l → ℚ) ≃ₗ[ℚ]
      (Selected si (labelValueFiber laws q ha l) → ℚ) :=
  cochainEquivOfIndexEquiv (CellCoordinate.targetSubsetEquivBlock laws q ha I si l)
/-- 同じセル名によるblock/fiber評価。 -/
@[simp] theorem blockFiberEquiv_apply (si : I → Set q.Target) (l) (z) (i) :
    blockFiberEquiv laws ha si l z i =
      z (CellCoordinate.targetSubsetEquivBlock laws q ha I si l i) :=
  cochainEquivOfIndexEquiv_apply _ _ _
/-- block読み取りとfiber同定は全Lawの同じfiber読み取り。 -/
theorem blockFiberEquiv_read (si : I → Set q.Target) (l) (z) :
    blockFiberEquiv laws ha si l (lawBlockRead laws ha si l z) =
      lawFiberRead laws ha si l z := by
  funext i
  rw [blockFiberEquiv_apply, lawBlockRead_apply, lawFiberRead_apply]

namespace SupportedBasisMap
variable (M : SupportedBasisMap si sj)
/-- 非零原始セル像の同じ発生label block座標。 -/
def lawBlockCoordinate (l : LawValueLabel laws)
    (x : CellCoordinate.Block laws q ha I si l) (j : J)
    (hj : M.basisImage x.1.cell j ≠ 0) : CellCoordinate.Block laws q ha J sj l :=
  ⟨M.lawCoordinate laws ha x.1 j hj, (M.lawCoordinate_label laws ha x.1 j hj).trans x.2⟩
/-- 原始block像の基底セル名。 -/
@[simp] theorem lawBlockCoordinate_cell (l) (x) (j) (hj) :
    (M.lawBlockCoordinate laws ha l x j hj).1.cell = j :=
  M.lawCoordinate_cell laws ha x.1 j hj
/-- 同じblock像の全Law座標。 -/
@[simp] theorem lawBlockCoordinate_val (l) (x) (j) (hj) :
    (M.lawBlockCoordinate laws ha l x j hj).1 = M.lawCoordinate laws ha x.1 j hj := rfl

/-- block座標の原始有限基底像。 -/
def lawBlockBasis (l : LawValueLabel laws) (x : CellCoordinate.Block laws q ha I si l) :
    CellCoordinate.Block laws q ha J sj l →₀ ℚ :=
  ∑ j ∈ (M.basisImage x.1.cell).support.attach,
    Finsupp.single (M.lawBlockCoordinate laws ha l x j.1 (Finsupp.mem_support_iff.mp j.2))
      (M.basisImage x.1.cell j.1)
/-- 同じblock有限和の自由線形延長。 -/
def lawBlockRaw (l : LawValueLabel laws) := freeMap (M.lawBlockBasis laws ha l)
/-- 独立生成されたblock基底射の実双対。 -/
def lawBlockDual (l : LawValueLabel laws) := dualCellMap (M.lawBlockRaw laws ha l)
/-- 原始block射の基底評価。 -/
@[simp] theorem lawBlockRaw_single (l) (x) (a : ℚ) :
    M.lawBlockRaw laws ha l (Finsupp.single x a) = a • M.lawBlockBasis laws ha l x :=
  freeMap_single _ _ _
/-- 同じ原始係数で生成する実block有限和の評価。 -/
theorem lawBlockDual_apply (l) (z) (x) :
    M.lawBlockDual laws ha l z x =
      ∑ j ∈ (M.basisImage x.1.cell).support.attach,
        M.basisImage x.1.cell j.1 *
          z (M.lawBlockCoordinate laws ha l x j.1 (Finsupp.mem_support_iff.mp j.2)) := by
  rw [lawBlockDual, dualCellMap_apply, lawBlockRaw_single, one_smul, lawBlockBasis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact freeDualEquiv_single _ _ _

/-- 零の原始基底像は同じ独立 block 双対でも零。 -/
theorem lawBlockDual_apply_zero (l) (z) (x) (h : M.basisImage x.1.cell=0) :
    M.lawBlockDual laws ha l z x=0 := by
  rw [lawBlockDual_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [h,Finsupp.zero_apply,zero_mul]
/-- 単一原始基底像は同じ生成 block 座標を評価する。 -/
theorem lawBlockDual_apply_single (l) (z) (x) (j : J)
    (h : M.basisImage x.1.cell=Finsupp.single j 1) :
    M.lawBlockDual laws ha l z x=
      z (M.lawBlockCoordinate laws ha l x j (by rw [h]; simp)) := by
  classical
  rw [lawBlockDual_apply]
  let j' : {j // j∈(M.basisImage x.1.cell).support} :=
    ⟨j,Finsupp.mem_support_iff.mpr (by rw [h]; simp)⟩
  rw [Finset.sum_eq_single j']
  · simp only [j',h,Finsupp.single_eq_same,one_mul]
  · intro k hk hkj
    have hne : k.1≠j := by
      intro he
      exact hkj (Subtype.ext he)
    simp [h,hne]
  · intro hn
    exact False.elim (hn (Finset.mem_attach _ j'))

/-- 全Law座標生成と同じ原始block座標生成は射そのものが可換。 -/
theorem lawDual_block (l) (z) :
    lawBlockRead laws ha si l (M.lawDual laws ha z) =
      M.lawBlockDual laws ha l (lawBlockRead laws ha sj l z) := by
  funext x
  rw [lawBlockRead_apply, lawDual_apply, lawBlockDual_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lawBlockRead_apply, lawBlockCoordinate_val]

/-- 独立block有限和も同じfiberの原始選択双対と可換。 -/
theorem lawBlockDual_fiber (l) (z) :
    blockFiberEquiv laws ha si l (M.lawBlockDual laws ha l z) =
      dualCellMap (M.selected (labelValueFiber laws q ha l))
        (blockFiberEquiv laws ha sj l z) := by
  funext i
  rw [blockFiberEquiv_apply, lawBlockDual_apply, dual_selected_apply]
  simp only [CellCoordinate.targetSubsetEquivBlock_cell]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [blockFiberEquiv_apply]
  congr 1
  apply CellCoordinate.block_cell_injective laws q ha J sj l
  exact (M.lawBlockCoordinate_cell laws ha l _ _ (Finsupp.mem_support_iff.mp j.2)).trans
    (CellCoordinate.targetSubsetEquivBlock_cell laws q ha J sj l
      ⟨j.1, M.basis_support_selected (labelValueFiber laws q ha l) i j.1 j.2⟩).symm

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
