import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldArbitraryCarrierNormalForm
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNatAlgorithmNormalForm
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldFiniteSupportUnionObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Literal carrier union of exact-support presentations

For every decidable primitive Extension carrier, Cycle 106 gives an
independent exact-support finite code and its actual evaluation.  This file
forms the literal union of those actual code images and proves, rather than
defines, that it equals the previously fixed intrinsic finite-support carrier
image.

The presentation family is then enlarged by the actual image of the faithful
`Nat` algorithm normal form.  The fixed adjacent algorithm supplies a member
of the enlarged image outside the exact-support union, so the inclusion is
strict.  No claim that the enlarged image covers the full residual kernel is
made here.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- Literal union, over every decidable primitive carrier, of the actual
images of independently authored exact-support finite codes. -/
def FiniteAxisFoldExactSupportCarrierUnion :
    Set FiniteAxisFoldResidualLocalFiberKernel :=
  { remainder |
    ∃ descriptor : FiniteAxisFoldDecidableExtensionCarrier,
      letI := descriptor.decidableEq
      ∃ code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode
          descriptor.Carrier,
        code.actualEvaluate = remainder }

/-- Literal exact-support code membership is equivalent to the already fixed
intrinsic finite-support carrier condition.  The reverse implication uses the
Cycle 106 equivalence; it is not a decoder-range definition of the target. -/
theorem finiteAxisFoldExactSupportCarrierUnion_mem_iff
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) :
    remainder ∈ FiniteAxisFoldExactSupportCarrierUnion ↔
      FiniteAxisFoldFiniteSupportCarrierImage remainder := by
  constructor
  · rintro ⟨descriptor, code, rfl⟩
    refine ⟨descriptor, ?_⟩
    letI : DecidableEq descriptor.Carrier := descriptor.decidableEq
    exact code.intrinsicDecode.2
  · rintro ⟨descriptor, membership⟩
    letI : DecidableEq descriptor.Carrier := descriptor.decidableEq
    let intrinsic : FiniteAxisFoldFiniteSwapWordIntrinsicImage
        descriptor.Carrier :=
      ⟨remainder, membership⟩
    obtain ⟨code, equality⟩ :=
      (FiniteAxisFoldArbitraryCarrierFiniteSupportCode.equivIntrinsicImage
        (E := descriptor.Carrier)).surjective intrinsic
    exact ⟨descriptor, code, congrArg Subtype.val equality⟩

/-- Set-level equality between the literal code-image union and the intrinsic
carrier image established in Cycle 101. -/
theorem finiteAxisFoldExactSupportCarrierUnion_eq_finiteSupportCarrierImage :
    FiniteAxisFoldExactSupportCarrierUnion =
      { remainder | FiniteAxisFoldFiniteSupportCarrierImage remainder } := by
  ext remainder
  exact finiteAxisFoldExactSupportCarrierUnion_mem_iff remainder

/-- A canonical faithful normal form for the fixed adjacent `Nat` algorithm.
Its finite component is constructed by exact-support encoding of the identity,
not by storing the adjacent permutation as an input field. -/
noncomputable def finiteAxisFoldNatAdjacentAlgorithmNormalForm :
    FiniteAxisFoldNatAlgorithmNormalForm :=
  ⟨true, FiniteAxisFoldNatFiniteSupportCode.encode
    (1 : finiteAxisFoldFiniteSupportPermutationSubgroup Nat)⟩

/-- The canonical adjacent normal form evaluates to the fixed finite
algorithm. -/
theorem finiteAxisFoldNatAdjacentAlgorithmNormalForm_evaluate :
    finiteAxisFoldNatAdjacentAlgorithmNormalForm.evaluate =
      finiteAxisFoldNatAdjacentSwap := by
  have decoded := congrArg Subtype.val
    (FiniteAxisFoldNatFiniteSupportCode.decode_encode
      (1 : finiteAxisFoldFiniteSupportPermutationSubgroup Nat))
  change
    (FiniteAxisFoldNatFiniteSupportCode.encode
      (1 : finiteAxisFoldFiniteSupportPermutationSubgroup Nat)).evaluate =
        (1 : Equiv.Perm Nat) at decoded
  simp [finiteAxisFoldNatAdjacentAlgorithmNormalForm,
    FiniteAxisFoldNatAlgorithmNormalForm.evaluate, decoded]

/-- Its actual evaluation is the fixed adjacent local-fiber-kernel witness. -/
theorem finiteAxisFoldNatAdjacentAlgorithmNormalForm_actualEvaluate :
    finiteAxisFoldNatAdjacentAlgorithmNormalForm.actualEvaluate =
      finiteAxisFoldNatAdjacentSwapLocalFiberKernel := by
  change finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
      finiteAxisFoldNatAdjacentAlgorithmNormalForm.evaluate =
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
      finiteAxisFoldNatAdjacentSwap
  rw [finiteAxisFoldNatAdjacentAlgorithmNormalForm_evaluate]

/-- The enlarged presented image adds the actual image of the faithful `Nat`
algorithm normal form to the exact-support carrier union. -/
def FiniteAxisFoldEnlargedPresentedCarrierImage :
    Set FiniteAxisFoldResidualLocalFiberKernel :=
  FiniteAxisFoldExactSupportCarrierUnion ∪
    Set.range FiniteAxisFoldNatAlgorithmNormalForm.actualEvaluate

/-- Every exact-support presentation remains in the enlarged image. -/
theorem finiteAxisFoldExactSupportCarrierUnion_subset_enlarged :
    FiniteAxisFoldExactSupportCarrierUnion ⊆
      FiniteAxisFoldEnlargedPresentedCarrierImage := by
  intro remainder membership
  exact Set.mem_union_left _ membership

/-- The adjacent algorithm belongs to the enlarged presented image. -/
theorem finiteAxisFoldNatAdjacentSwap_mem_enlargedPresentedCarrierImage :
    finiteAxisFoldNatAdjacentSwapLocalFiberKernel ∈
      FiniteAxisFoldEnlargedPresentedCarrierImage := by
  apply Set.mem_union_right
  exact ⟨finiteAxisFoldNatAdjacentAlgorithmNormalForm,
    finiteAxisFoldNatAdjacentAlgorithmNormalForm_actualEvaluate⟩

/-- The same adjacent witness is not in the exact-support carrier union. -/
theorem finiteAxisFoldNatAdjacentSwap_not_mem_exactSupportCarrierUnion :
    finiteAxisFoldNatAdjacentSwapLocalFiberKernel ∉
      FiniteAxisFoldExactSupportCarrierUnion := by
  intro membership
  exact finiteAxisFoldNatAdjacentSwap_not_finiteSupportCarrierImage
    ((finiteAxisFoldExactSupportCarrierUnion_mem_iff _).1 membership)

/-- Adding the faithful `Nat` algorithm image is a strict enlargement of the
literal exact-support carrier union. -/
theorem finiteAxisFoldExactSupportCarrierUnion_ssubset_enlarged :
    FiniteAxisFoldExactSupportCarrierUnion ⊂
      FiniteAxisFoldEnlargedPresentedCarrierImage := by
  constructor
  · exact finiteAxisFoldExactSupportCarrierUnion_subset_enlarged
  · intro reverseInclusion
    exact finiteAxisFoldNatAdjacentSwap_not_mem_exactSupportCarrierUnion
      (reverseInclusion
        finiteAxisFoldNatAdjacentSwap_mem_enlargedPresentedCarrierImage)

/-- Exact-support presentations over all decidable carriers still do not
cover the full actual local-fiber kernel. -/
theorem finiteAxisFoldExactSupportCarrierUnion_ne_univ :
    FiniteAxisFoldExactSupportCarrierUnion ≠ Set.univ := by
  intro equality
  apply finiteAxisFoldNatAdjacentSwap_not_mem_exactSupportCarrierUnion
  rw [equality]
  exact Set.mem_univ _

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
