import Formal.SHIGURE.Part2.Descent.TensorLaws
import Formal.SHIGURE.Part2.Descent.Examples

/-! # Tensor and operation descent on a split cover

These examples use the faithfully flat algebra `ℚ × ℚ`. They evaluate
a tensor comparison and a compatible binary operation, and detect
both a noncommuting square and an incompatible chosen element.
-/

namespace SHIGURE.CoefficientDescent.Examples

open TensorProduct CategoryTheory TensorRealization

noncomputable section

private abbrev K := ℚ
private abbrev B := ℚ × ℚ
private abbrev lineModule := ModuleCat.of K K

private def lineDatum : DescentModule K B :=
  (DescentModule.extend (A := K) (B := B)).obj lineModule

private def fixed (r : K) : lineDatum.datum.toCoaction.descended :=
  standardUnit (A := K) (B := B) (M := K) r

/-- The tensor comparison sends two fixed scalars to their actual tensor in the cover. -/
theorem split_tensor_fixed_three_five :
    (lineDatum.datum.tensorDescendedEquiv lineDatum.datum
      (fixed 3 ⊗ₜ[K] fixed 5)).val =
      ((1 : B) ⊗ₜ[K] (3 : K)) ⊗ₜ[B] ((1 : B) ⊗ₜ[K] (5 : K)) :=
  lineDatum.datum.tensorDescendedEquiv_tmul lineDatum.datum (fixed 3) (fixed 5)

private def family (_ : Unit) : DescentModule K B := lineDatum
private abbrev arguments : List Unit := [(), ()]

private local instance : Fintype (TensorPosition arguments) := Fintype.ofFinite _

private def readFixed : lineDatum.datum.toCoaction.descended ≃ₗ[K] K :=
  (standardUnitEquiv (A := K) (B := B) (M := K)).symm

private def binaryProduct :
    MultilinearMap K (fun i : TensorPosition arguments => fixedFamily family i.1)
      lineDatum.datum.toCoaction.descended :=
  readFixed.symm.toLinearMap.compMultilinearMap
    ((MultilinearMap.mkPiAlgebra K (TensorPosition arguments) K).compLinearMap
      (fun _ => readFixed.toLinearMap))

private def bothThree (_ : TensorPosition arguments) : lineDatum.datum.toCoaction.descended :=
  fixed 3

/-- The compatible binary operation corresponding to multiplication gives nine on two fixed threes. -/
theorem split_binary_product :
    let op := (operationEquiv family arguments lineDatum).symm binaryProduct
    op.val (fun i => (bothThree i).val) = ((1 : B) ⊗ₜ[K] (9 : K)) := by
  dsimp only
  let e := operationEquiv family arguments lineDatum
  have eq := operationEquiv_apply family arguments lineDatum
    (e.symm binaryProduct).val (e.symm binaryProduct).property bothThree
  change (e (e.symm binaryProduct) bothThree).val = _ at eq
  rw [e.apply_symm_apply] at eq
  rw [← eq]
  change (readFixed.symm (∏ _i : TensorPosition arguments, readFixed (fixed 3))).val = _
  have scalarRead : readFixed (fixed 3) = 3 :=
    (standardUnitEquiv (A := K) (B := B) (M := K)).symm_apply_apply 3
  have size : Fintype.card (TensorPosition arguments) = 2 := by
    classical
    let positions : TensorPosition arguments ≃ Bool := {
      toFun
        | ⟨_, .here⟩ => false
        | ⟨_, .there .here⟩ => true
      invFun
        | false => ⟨(), .here⟩
        | true => ⟨(), .there .here⟩
      left_inv
        | ⟨_, .here⟩ => rfl
        | ⟨_, .there .here⟩ => rfl
      right_inv x := by cases x <;> rfl }
    exact (Fintype.card_congr positions).trans (by decide)
  rw [scalarRead, Finset.prod_const, Finset.card_univ, size]
  norm_num
  rfl

private theorem unitZeroCompatible :
    (unitDatum K B).Compatible (unitDatum K B) (0 : B →ₗ[B] B) := by
  apply ((unitDatum K B).compatible_iff_coaction _ _).2
  intro x
  simp

/-- The identity and zero routes remain distinct on the descended scalar module. -/
theorem split_descended_square_distinguishes_zero :
    let D := unitDatum K B
    let i : B →ₗ[B] B := LinearMap.id
    (D.descendMap D i D.compatible_id).comp (D.descendMap D i D.compatible_id) ≠
      (D.descendMap D 0 unitZeroCompatible).comp (D.descendMap D i D.compatible_id) := by
  dsimp only
  intro equal
  let D := unitDatum K B
  let i : B →ₗ[B] B := LinearMap.id
  have native := (D.descend_square_iff D D D i 0 i i
    D.compatible_id unitZeroCompatible D.compatible_id D.compatible_id).1 equal
  have atOne := LinearMap.congr_fun native (1 : B)
  change (1 : B) = 0 at atOne
  exact one_ne_zero atOne

set_option maxHeartbeats 800000 in
/-- A chosen first idempotent cannot descend through the standard split scalar overlap. -/
theorem split_first_idempotent_element_incompatible :
    ¬ (unitDatum K B).Compatible lineDatum.datum
        (LinearMap.toSpanSingleton B lineDatum.carrier (((1, 0) : B) ⊗ₜ[K] (1 : K))) := by
  intro compatible
  have fixedFirst := (element_compatible_iff lineDatum.datum _).1 compatible
  let x : lineDatum.datum.toCoaction.descended := ⟨_, fixedFirst⟩
  let r := readFixed x
  have val := congrArg Subtype.val (readFixed.symm_apply_apply x)
  change ((1 : B) ⊗ₜ[K] r) = ((1, 0) : B) ⊗ₜ[K] (1 : K) at val
  have components := congrArg (AlgebraTensorModule.rid K B B) val
  simp only [AlgebraTensorModule.rid_tmul] at components
  have left := congrArg Prod.fst components
  have right := congrArg Prod.snd components
  change r * 1 = 1 * 1 at left
  change r * 1 = 1 * 0 at right
  linarith

private def badNullary :
    MultilinearMap B (fun i : TensorPosition ([] : List Unit) => nativeFamily family i.1) lineDatum.carrier :=
  PiTensorProduct.lift.symm ((LinearMap.toSpanSingleton B lineDatum.carrier (((1, 0) : B) ⊗ₜ[K] (1 : K))).comp
    (inputTensorUnit B (nativeFamily family)).toLinearMap)

/-- The constant operation given by a single idempotent fails the finite-operation compatibility. -/
theorem split_bad_nullary_incompatible : ¬ CompatibleOperation family [] lineDatum badNullary := by
  intro compatible
  let x : ∀ i : TensorPosition ([] : List Unit), fixedFamily family i.1 := fun i => nomatch i.2
  let z := operationEquiv family [] lineDatum ⟨badNullary, compatible⟩ x
  have native := operationEquiv_apply family [] lineDatum badNullary compatible x
  have value : badNullary (fun i => (x i).val) = ((1, 0) : B) ⊗ₜ[K] (1 : K) := by
    change (LinearMap.toSpanSingleton B lineDatum.carrier (((1, 0) : B) ⊗ₜ[K] (1 : K)))
      (inputTensorUnit B (nativeFamily family) (PiTensorProduct.tprod B (fun i => (x i).val))) = _
    rw [inputTensorUnit_tprod B (nativeFamily family) (fun i => (x i).val), LinearMap.toSpanSingleton_apply_one]
  change z.val = badNullary _ at native
  have fixed := z.property
  rw [native, value] at fixed
  exact split_first_idempotent_element_incompatible ((element_compatible_iff lineDatum.datum _).2 fixed)

private def multiplicationSignature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨arguments, ()⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

private def multiplicationDatum : TensorDatum K B multiplicationSignature where
  sort := family
  total _ := (operationEquiv family arguments lineDatum).symm binaryProduct
  quantity q := nomatch q

private def doubleProductLaw : TensorLaw K multiplicationSignature :=
  ⟨.arguments arguments, .sort (), .add (.total ()) (.total ()), .smul 2 (.total ())⟩

/-- Adding two copies of the written binary operation agrees with scaling it, before and after descent. -/
theorem split_binary_law :
    (doubleProductLaw.mapScalars (algebraMap K B)).holds multiplicationDatum.native ∧
      doubleProductLaw.holds multiplicationDatum.descended := by
  have descended : doubleProductLaw.holds multiplicationDatum.descended := by
    change (PiTensorProduct.lift (multiplicationDatum.descended.total ()) +
      PiTensorProduct.lift (multiplicationDatum.descended.total ())) =
      (2 : K) • PiTensorProduct.lift (multiplicationDatum.descended.total ())
    exact (two_smul _ _).symm
  exact ⟨(multiplicationDatum.tensorLaw_holds_iff doubleProductLaw).2 descended, descended⟩

end

end SHIGURE.CoefficientDescent.Examples
