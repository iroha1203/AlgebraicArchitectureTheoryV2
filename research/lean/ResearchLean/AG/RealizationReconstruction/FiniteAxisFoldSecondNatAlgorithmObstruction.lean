import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldExactSupportCarrierUnion
import Formal.Util.AssertStandardAxioms

/-!
# A second finite Nat algorithm outside the first enlarged presentation

The fixed algorithm `n ↦ n xor 2` is source-owned and independent of the
existing `xor 1` normal-form syntax.  It moves every natural number, while its
product with `xor 1` also moves every natural number.  Hence it belongs to
neither the finite-support branch nor the `xor 1` left coset classified by the
Nat algorithm normal form.

Transporting `xor 2` through the same fixed section gives an actual residual
witness.  Canonical Nat probes separate it from every exact-support carrier
image, and faithfulness of the full Nat backward action separates it from the
entire `xor 1` normal-form image.  Thus the Cycle 107 enlarged image is still
not full.  The new algorithm is a fixed recipe used to construct the witness;
it is not stored as a completed permutation field in presentation syntax.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- A second source-owned finite Nat algorithm, distinct from the fixed
`xor 1` algorithm used in the existing normal-form family. -/
def finiteAxisFoldNatSecondXorAlgorithm : Equiv.Perm Nat where
  toFun value := value ^^^ 2
  invFun value := value ^^^ 2
  left_inv value := Nat.xor_xor_cancel_right value 2
  right_inv value := Nat.xor_xor_cancel_right value 2

@[simp] theorem finiteAxisFoldNatSecondXorAlgorithm_apply (value : Nat) :
    finiteAxisFoldNatSecondXorAlgorithm value = value ^^^ 2 := rfl

@[simp] theorem finiteAxisFoldNatSecondXorAlgorithm_inv :
    finiteAxisFoldNatSecondXorAlgorithm⁻¹ =
      finiteAxisFoldNatSecondXorAlgorithm := by
  apply Equiv.ext
  intro value
  rfl

/-- Xor by a nonzero fixed mask cannot fix a natural number. -/
private theorem nat_xor_ne_self_of_ne_zero
    (mask : Nat) (mask_ne : mask ≠ 0) (value : Nat) :
    value ^^^ mask ≠ value := by
  intro equality
  have xorEquality : value ^^^ mask = value ^^^ 0 := by
    simpa using equality
  exact mask_ne (Nat.xor_right_inj.mp xorEquality)

/-- The second algorithm moves every primitive value. -/
theorem finiteAxisFoldNatSecondXorAlgorithm_ne (value : Nat) :
    finiteAxisFoldNatSecondXorAlgorithm value ≠ value := by
  exact nat_xor_ne_self_of_ne_zero 2 (by omega) value

/-- Composing the fixed `xor 1` algorithm with `xor 2` is xor by `3`. -/
theorem finiteAxisFoldNatAdjacent_mul_secondXor_apply (value : Nat) :
    (finiteAxisFoldNatAdjacentSwap *
        finiteAxisFoldNatSecondXorAlgorithm) value = value ^^^ 3 := by
  change (value ^^^ 2) ^^^ 1 = value ^^^ 3
  rw [Nat.xor_assoc]
  norm_num

/-- The second algorithm itself is not finite-support. -/
theorem finiteAxisFoldNatSecondXorAlgorithm_not_finiteSupport :
    ¬ (fixedBy Nat finiteAxisFoldNatSecondXorAlgorithm)ᶜ.Finite := by
  intro finiteSupport
  have moved_eq_univ :
      (fixedBy Nat finiteAxisFoldNatSecondXorAlgorithm)ᶜ = Set.univ := by
    ext value
    simp only [Set.mem_compl_iff, mem_fixedBy, Set.mem_univ, iff_true]
    exact finiteAxisFoldNatSecondXorAlgorithm_ne value
  have univFinite : (Set.univ : Set Nat).Finite := by
    rw [← moved_eq_univ]
    exact finiteSupport
  exact Set.infinite_univ univFinite

/-- The second algorithm also does not enter the adjacent coset branch: left
multiplication by xor `1` is xor `3` and still moves every value. -/
theorem finiteAxisFoldNatAdjacent_mul_secondXor_not_finiteSupport :
    ¬ (fixedBy Nat
      (finiteAxisFoldNatAdjacentSwap *
        finiteAxisFoldNatSecondXorAlgorithm))ᶜ.Finite := by
  intro finiteSupport
  have moved_eq_univ :
      (fixedBy Nat
        (finiteAxisFoldNatAdjacentSwap *
          finiteAxisFoldNatSecondXorAlgorithm))ᶜ = Set.univ := by
    ext value
    simp only [Set.mem_compl_iff, mem_fixedBy, Set.mem_univ, iff_true]
    change
      (finiteAxisFoldNatAdjacentSwap *
          finiteAxisFoldNatSecondXorAlgorithm) value ≠ value
    rw [finiteAxisFoldNatAdjacent_mul_secondXor_apply]
    exact nat_xor_ne_self_of_ne_zero 3 (by omega) value
  have univFinite : (Set.univ : Set Nat).Finite := by
    rw [← moved_eq_univ]
    exact finiteSupport
  exact Set.infinite_univ univFinite

/-- The fixed xor `2` recipe lies outside the complete source subgroup
presented by finite support plus the xor `1` normal-form coset. -/
theorem finiteAxisFoldNatSecondXorAlgorithm_not_mem_algorithmSubgroup :
    finiteAxisFoldNatSecondXorAlgorithm ∉
      finiteAxisFoldNatAlgorithmPermutationSubgroup := by
  rw [finiteAxisFoldNatAlgorithmPermutationSubgroup_mem_iff_coset]
  rintro (finite | adjacentFinite)
  · exact finiteAxisFoldNatSecondXorAlgorithm_not_finiteSupport finite
  · exact finiteAxisFoldNatAdjacent_mul_secondXor_not_finiteSupport
      adjacentFinite

/-- The actual residual witness obtained from the same fixed section used by
all preceding carrier presentations. -/
noncomputable def finiteAxisFoldNatSecondXorLocalFiberKernel :
    FiniteAxisFoldResidualLocalFiberKernel :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
    finiteAxisFoldNatSecondXorAlgorithm

/-- A transported xor `2` action differs from every transported
finite-support action, on any decidable primitive carrier. -/
theorem finiteAxisFoldNatSecondXor_transported_ne_finiteSupport
    (E : Type) [DecidableEq E] (permutation : Equiv.Perm E)
    (finiteSupport : (fixedBy E permutation)ᶜ.Finite) :
    finiteAxisFoldTransportedSourceContextPermutation
        finiteAxisFoldNatSecondXorAlgorithm ≠
      finiteAxisFoldTransportedSourceContextPermutation permutation := by
  obtain ⟨value, fixedProbe⟩ :=
    finiteAxisFoldFiniteSupportSourceAction_exists_fixed_natProbe
      E permutation finiteSupport
  intro equality
  have evaluated := congrArg
    (fun actualPermutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      actualPermutation
        (finiteAxisFoldSourceToActualContextEquiv
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject)))
    equality
  simp only [finiteAxisFoldTransportedSourceContextPermutation,
    Equiv.trans_apply, Equiv.symm_apply_apply] at evaluated
  have sourceEquality :=
    finiteAxisFoldSourceToActualContextEquiv.injective evaluated
  have sourceEquality' := sourceEquality.trans fixedProbe
  have extensionSigmaEquality := congrArg
    (fun W : FiniteAxisFoldSourceContextObject =>
      (⟨W.ctx.Extension, W.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier))
    sourceEquality'
  have movedEqualsFixed : finiteAxisFoldNatSecondXorAlgorithm value = value := by
    simpa [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] using extensionSigmaEquality
  exact finiteAxisFoldNatSecondXorAlgorithm_ne value movedEqualsFixed

/-- The xor `2` actual witness is outside the exact-support union over all
decidable carriers. -/
theorem finiteAxisFoldNatSecondXor_not_mem_exactSupportCarrierUnion :
    finiteAxisFoldNatSecondXorLocalFiberKernel ∉
      FiniteAxisFoldExactSupportCarrierUnion := by
  intro membership
  obtain ⟨descriptor, intrinsicMembership⟩ :=
    (finiteAxisFoldExactSupportCarrierUnion_mem_iff _).1 membership
  letI : DecidableEq descriptor.Carrier := descriptor.decidableEq
  obtain ⟨permutation, finiteSupport, actionEquality⟩ :=
    (finiteAxisFoldFiniteSwapWordIntrinsicImage_mem_iff
      finiteAxisFoldNatSecondXorLocalFiberKernel).1 intrinsicMembership
  have inverseFiniteSupport :
      (fixedBy descriptor.Carrier permutation⁻¹)ᶜ.Finite := by
    apply (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).mp
    exact (finiteAxisFoldFiniteSupportPermutationSubgroup
      descriptor.Carrier).inv_mem
        ((finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff permutation).mpr
          finiteSupport)
  have projectedSecond :=
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
      finiteAxisFoldNatSecondXorAlgorithm
  rw [finiteAxisFoldNatSecondXorAlgorithm_inv] at projectedSecond
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation
          finiteAxisFoldNatSecondXorAlgorithm =
        finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹ := by
    apply MulOpposite.op_injective
    calc
      MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation
            finiteAxisFoldNatSecondXorAlgorithm) =
        finiteAxisFoldResidualLocalFiberKernelBackwardProjection
          finiteAxisFoldNatSecondXorLocalFiberKernel := projectedSecond.symm
      _ = finiteAxisFoldArbitraryCarrierBackwardAction
          descriptor.Carrier permutation := actionEquality
      _ = MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹) := rfl
  exact finiteAxisFoldNatSecondXor_transported_ne_finiteSupport
    descriptor.Carrier permutation⁻¹ inverseFiniteSupport transportedEquality

/-- The xor `2` actual witness is outside the complete actual range of the
faithful xor `1` Nat normal form. -/
theorem finiteAxisFoldNatSecondXor_not_mem_natAlgorithmNormalFormRange :
    finiteAxisFoldNatSecondXorLocalFiberKernel ∉
      Set.range FiniteAxisFoldNatAlgorithmNormalForm.actualEvaluate := by
  rintro ⟨normal, equality⟩
  apply finiteAxisFoldNatSecondXorAlgorithm_not_mem_algorithmSubgroup
  have projectionEquality :=
    congrArg finiteAxisFoldResidualLocalFiberKernelBackwardProjection equality
  have actionEquality :
      finiteAxisFoldArbitraryCarrierBackwardAction Nat normal.evaluate =
        finiteAxisFoldArbitraryCarrierBackwardAction Nat
          finiteAxisFoldNatSecondXorAlgorithm := by
    calc
      _ = finiteAxisFoldResidualLocalFiberKernelBackwardProjection
          normal.actualEvaluate := normal.actualEvaluate_backwardProjection.symm
      _ = finiteAxisFoldResidualLocalFiberKernelBackwardProjection
          finiteAxisFoldNatSecondXorLocalFiberKernel := projectionEquality
      _ = _ := by
        simpa [finiteAxisFoldNatSecondXorLocalFiberKernel,
          finiteAxisFoldArbitraryCarrierBackwardAction] using
          finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
            finiteAxisFoldNatSecondXorAlgorithm
  have sourceEquality :
      normal.evaluate = finiteAxisFoldNatSecondXorAlgorithm := by
    apply finiteAxisFoldArbitraryCarrierBackwardAction_injective_forCarrier Nat
    exact actionEquality
  rw [← sourceEquality]
  exact normal.evaluate_mem

/-- The second finite Nat algorithm gives an actual residual witness outside
the Cycle 107 enlarged presented image. -/
theorem finiteAxisFoldNatSecondXor_not_mem_enlargedPresentedCarrierImage :
    finiteAxisFoldNatSecondXorLocalFiberKernel ∉
      FiniteAxisFoldEnlargedPresentedCarrierImage := by
  rintro (exactSupport | natNormalForm)
  · exact finiteAxisFoldNatSecondXor_not_mem_exactSupportCarrierUnion
      exactSupport
  · exact finiteAxisFoldNatSecondXor_not_mem_natAlgorithmNormalFormRange
      natNormalForm

/-- Consequently the first enlarged presentation is not the full actual
local-fiber kernel.  No stronger coverage claim is inferred. -/
theorem finiteAxisFoldEnlargedPresentedCarrierImage_ne_univ :
    FiniteAxisFoldEnlargedPresentedCarrierImage ≠ Set.univ := by
  intro equality
  apply finiteAxisFoldNatSecondXor_not_mem_enlargedPresentedCarrierImage
  rw [equality]
  exact Set.mem_univ _

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
