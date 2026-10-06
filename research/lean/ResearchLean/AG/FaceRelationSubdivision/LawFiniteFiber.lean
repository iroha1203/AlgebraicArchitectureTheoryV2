import ResearchLean.AG.FaceRelationSubdivision.LawFiniteCoordinates
import Formal.Util.AssertStandardAxioms

/-!
# 独立生成したLaw有限和と同じラベルfiberの射

## Implementation notes

非零セル像を同じfiber内へ移す式を証明し、全ラベルの座標読み取りで射を検査する。
fiber射の共役をLaw射の定義にせず、原始有限和の項ごとのセル・ラベル等号を使う。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {q : Reading Source}
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 全Law座標cochainを同じラベルfiberのセルへ読む。 -/
def lawFiberRead (si : I → Set q.Target) (l : LawValueLabel laws) :
    (CellCoordinate laws q ha I si → ℚ) →ₗ[ℚ]
      (Selected si (labelValueFiber laws q ha l) → ℚ) where
  toFun z i := z (CellCoordinate.targetSubsetEquivBlock laws q ha I si l i).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 同じセル名・ラベル座標を読む基本評価API。 -/
@[simp] theorem lawFiberRead_apply (si : I → Set q.Target) (l) (z) (i) :
    lawFiberRead laws ha si l z i =
      z (CellCoordinate.targetSubsetEquivBlock laws q ha I si l i).1 := rfl

/-- 全発生ラベルの読み取りは全座標cochainの等号を反映する。 -/
theorem lawFiberRead_joint_injective (si : I → Set q.Target)
    {z w : CellCoordinate laws q ha I si → ℚ}
    (h : ∀ l, lawFiberRead laws ha si l z = lawFiberRead laws ha si l w) : z = w := by
  funext x
  let l := x.lawValueLabel laws q ha I si
  let b : CellCoordinate.Block laws q ha I si l := ⟨x, rfl⟩
  let i := (CellCoordinate.targetSubsetEquivBlock laws q ha I si l).symm b
  have hx := congrFun (h l) i
  simp only [lawFiberRead_apply] at hx
  change z ((CellCoordinate.targetSubsetEquivBlock laws q ha I si l)
      ((CellCoordinate.targetSubsetEquivBlock laws q ha I si l).symm b)).1 =
    w ((CellCoordinate.targetSubsetEquivBlock laws q ha I si l)
      ((CellCoordinate.targetSubsetEquivBlock laws q ha I si l).symm b)).1 at hx
  rw [Equiv.apply_symm_apply] at hx
  exact hx

variable {si : I → Set q.Target} {sj : J → Set q.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap si sj)

/-- 選択基底像は原始有限supportの全非零項を同じセルへ制限した和。 -/
theorem selected_single_attached (A : Set q.Target) (i : Selected si A) :
    M.selected A (Finsupp.single i 1) =
      ∑ j ∈ (M.basisImage i.1).support.attach,
        Finsupp.single (⟨j.1, M.basis_support_selected A i j.1 j.2⟩ : Selected sj A)
          (M.basisImage i.1 j.1) := by
  classical
  rw [selected_single, one_smul]
  have hs : (∑ j ∈ (M.basisImage i.1).support.attach,
      Finsupp.single j.1 (M.basisImage i.1 j.1)) = M.basisImage i.1 := by
    exact (Finset.sum_attach (M.basisImage i.1).support
      (fun j : J => Finsupp.single j (M.basisImage i.1 j))).trans
        (Finsupp.sum_single (M.basisImage i.1))
  calc
    _ = (∑ j ∈ (M.basisImage i.1).support.attach,
        Finsupp.single j.1 (M.basisImage i.1 j.1)).subtypeDomain
          (fun j => ∃ t, t ∈ sj j ∧ t ∈ A) := congrArg _ hs.symm
    _ = _ := by
      rw [Finsupp.subtypeDomain_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact subtypeDomain_single_selected sj A
        ⟨j.1, M.basis_support_selected A i j.1 j.2⟩ _

/-- 実選択双対射も同じ原始非零係数で有限和評価する。 -/
theorem dual_selected_apply (A : Set q.Target) (z) (i : Selected si A) :
    dualCellMap (M.selected A) z i =
      ∑ j ∈ (M.basisImage i.1).support.attach,
        M.basisImage i.1 j.1 *
          z ⟨j.1, M.basis_support_selected A i j.1 j.2⟩ := by
  rw [dualCellMap_apply, selected_single_attached, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact freeDualEquiv_single _ _ _

/-- 独立生成のLaw有限和は同じラベルfiberの原始双対射と可換。 -/
theorem lawDual_fiber (l : LawValueLabel laws) (z) :
    lawFiberRead laws ha si l (M.lawDual laws ha z) =
      dualCellMap (M.selected (labelValueFiber laws q ha l))
        (lawFiberRead laws ha sj l z) := by
  funext i
  rw [lawFiberRead_apply, lawDual_apply, dual_selected_apply]
  simp only [CellCoordinate.targetSubsetEquivBlock_cell]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [lawFiberRead_apply]
  congr 1
  let x := (CellCoordinate.targetSubsetEquivBlock laws q ha I si l i).1
  have hl : (M.lawCoordinate laws ha x j.1 (Finsupp.mem_support_iff.mp j.2)).lawValueLabel
      laws q ha J sj = l := (M.lawCoordinate_label laws ha x _ _).trans
        (CellCoordinate.targetSubsetEquivBlock laws q ha I si l i).2
  have hb := CellCoordinate.block_cell_injective laws q ha J sj l
    (a₁ := ⟨M.lawCoordinate laws ha x j.1 (Finsupp.mem_support_iff.mp j.2), hl⟩)
    (a₂ := CellCoordinate.targetSubsetEquivBlock laws q ha J sj l
      ⟨j.1, M.basis_support_selected (labelValueFiber laws q ha l) i j.1 j.2⟩)
  exact congrArg (fun b : CellCoordinate.Block laws q ha J sj l => b.1)
    (hb ((M.lawCoordinate_cell laws ha x j.1 (Finsupp.mem_support_iff.mp j.2)).trans
      (CellCoordinate.targetSubsetEquivBlock_cell laws q ha J sj l
        ⟨j.1, M.basis_support_selected (labelValueFiber laws q ha l) i j.1 j.2⟩).symm))

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
