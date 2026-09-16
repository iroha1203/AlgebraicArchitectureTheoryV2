import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldSecondNatAlgorithmObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Faithful finite xor-mask normal forms on Nat

A natural-number mask is itself finite source data and determines the fixed
algorithm `n ↦ n xor mask`.  Pairing that mask with the existing exact-support
finite code gives a uniform source-owned family containing the earlier xor
`1` normal forms and the xor `2` witness.  No completed permutation or actual
residual element is stored in the syntax.

Faithfulness is proved at a Nat probe outside the union of the two authored
finite supports.  Both finite tables fix that probe, so equality of evaluated
permutations recovers the masks by xor cancellation.  Group cancellation then
recovers the finite-table evaluations, and exact-support faithfulness recovers
the source codes themselves.

The actual image is characterized independently by the existence of a mask
and a finite-support source permutation inducing the complete backward
action.  The same fixed section gives an equivalence from normal forms to this
intrinsic image.  No full residual-kernel coverage claim is made.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- The fixed source algorithm attached to a finite Nat mask. -/
def finiteAxisFoldNatXorMask (mask : Nat) : Equiv.Perm Nat where
  toFun value := value ^^^ mask
  invFun value := value ^^^ mask
  left_inv value := Nat.xor_xor_cancel_right value mask
  right_inv value := Nat.xor_xor_cancel_right value mask

@[simp] theorem finiteAxisFoldNatXorMask_apply (mask value : Nat) :
    finiteAxisFoldNatXorMask mask value = value ^^^ mask := rfl

@[simp] theorem finiteAxisFoldNatXorMask_zero :
    finiteAxisFoldNatXorMask 0 = 1 := by
  apply Equiv.ext
  intro value
  simp

@[simp] theorem finiteAxisFoldNatXorMask_one :
    finiteAxisFoldNatXorMask 1 = finiteAxisFoldNatAdjacentSwap := by
  apply Equiv.ext
  intro value
  rfl

@[simp] theorem finiteAxisFoldNatXorMask_two :
    finiteAxisFoldNatXorMask 2 = finiteAxisFoldNatSecondXorAlgorithm := by
  apply Equiv.ext
  intro value
  rfl

/-- Independent uniform source syntax: a finite algorithm parameter and an
exact-support finite table. -/
structure FiniteAxisFoldNatXorMaskNormalForm where
  mask : Nat
  finite : FiniteAxisFoldNatFiniteSupportCode

namespace FiniteAxisFoldNatXorMaskNormalForm

/-- Evaluate a mask followed by the exact-support finite permutation. -/
def evaluate (normal : FiniteAxisFoldNatXorMaskNormalForm) : Equiv.Perm Nat :=
  finiteAxisFoldNatXorMask normal.mask * normal.finite.evaluate

/-- Equality of evaluations recovers both the finite mask and the exact finite
table. -/
theorem evaluate_injective : Function.Injective evaluate := by
  intro first second equality
  obtain ⟨probe, outside⟩ := Infinite.exists_notMem_finset
    (first.finite.support ∪ second.finite.support)
  have outsideFirst : probe ∉ first.finite.support := by
    intro inside
    exact outside (Finset.mem_union_left _ inside)
  have outsideSecond : probe ∉ second.finite.support := by
    intro inside
    exact outside (Finset.mem_union_right _ inside)
  have firstFixed : first.finite.evaluate probe = probe := by
    by_contra moved
    exact outsideFirst ((first.finite.evaluate_ne_iff_mem probe).1 moved)
  have secondFixed : second.finite.evaluate probe = probe := by
    by_contra moved
    exact outsideSecond ((second.finite.evaluate_ne_iff_mem probe).1 moved)
  have evaluatedAtProbe := congrArg
    (fun permutation : Equiv.Perm Nat => permutation probe) equality
  have maskEquality : first.mask = second.mask := by
    change
      (first.finite.evaluate probe) ^^^ first.mask =
        (second.finite.evaluate probe) ^^^ second.mask at evaluatedAtProbe
    rw [firstFixed, secondFixed] at evaluatedAtProbe
    exact Nat.xor_right_inj.mp evaluatedAtProbe
  have finiteEvaluationEquality :
      first.finite.evaluate = second.finite.evaluate := by
    have cancelled := congrArg
      (fun permutation : Equiv.Perm Nat =>
        (finiteAxisFoldNatXorMask first.mask)⁻¹ * permutation)
      equality
    rw [evaluate, evaluate, ← maskEquality] at cancelled
    simpa [mul_assoc] using cancelled
  have finiteEquality : first.finite = second.finite :=
    FiniteAxisFoldNatFiniteSupportCode.evaluate_injective
      finiteEvaluationEquality
  cases first with
  | mk firstMask firstFinite =>
      cases second with
      | mk secondMask secondFinite =>
          dsimp only at maskEquality finiteEquality
          cases maskEquality
          cases finiteEquality
          rfl

/-- Evaluate the uniform source form through the same fixed actual section. -/
noncomputable def actualEvaluate
    (normal : FiniteAxisFoldNatXorMaskNormalForm) :
    FiniteAxisFoldResidualLocalFiberKernel :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
    normal.evaluate

/-- The actual projection is the independently defined complete backward
action of the source evaluation. -/
theorem actualEvaluate_backwardProjection
    (normal : FiniteAxisFoldNatXorMaskNormalForm) :
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        normal.actualEvaluate =
      finiteAxisFoldArbitraryCarrierBackwardAction Nat normal.evaluate :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
    normal.evaluate

/-- Actual evaluation remains faithful because its complete backward action
recovers the source permutation. -/
theorem actualEvaluate_injective : Function.Injective actualEvaluate := by
  intro first second equality
  apply evaluate_injective
  apply finiteAxisFoldArbitraryCarrierBackwardAction_injective_forCarrier Nat
  rw [← first.actualEvaluate_backwardProjection,
    ← second.actualEvaluate_backwardProjection]
  exact congrArg finiteAxisFoldResidualLocalFiberKernelBackwardProjection
    equality

/-- Embed the earlier Bool-parity xor `1` normal form into the uniform
mask family. -/
def ofAdjacentNormalForm
    (normal : FiniteAxisFoldNatAlgorithmNormalForm) :
    FiniteAxisFoldNatXorMaskNormalForm :=
  ⟨if normal.adjacent then 1 else 0, normal.finite⟩

/-- The embedding preserves the source evaluation exactly. -/
theorem ofAdjacentNormalForm_evaluate
    (normal : FiniteAxisFoldNatAlgorithmNormalForm) :
    (ofAdjacentNormalForm normal).evaluate = normal.evaluate := by
  cases adjacent : normal.adjacent <;>
    simp [ofAdjacentNormalForm, evaluate,
      FiniteAxisFoldNatAlgorithmNormalForm.evaluate, adjacent]

/-- The embedding also preserves evaluation through the fixed actual
section. -/
theorem ofAdjacentNormalForm_actualEvaluate
    (normal : FiniteAxisFoldNatAlgorithmNormalForm) :
    (ofAdjacentNormalForm normal).actualEvaluate = normal.actualEvaluate := by
  change finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
      (ofAdjacentNormalForm normal).evaluate =
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
      normal.evaluate
  rw [ofAdjacentNormalForm_evaluate]

/-- The earlier faithful normal-form family embeds faithfully into the
uniform xor-mask family. -/
theorem ofAdjacentNormalForm_injective :
    Function.Injective ofAdjacentNormalForm := by
  intro first second equality
  apply FiniteAxisFoldNatAlgorithmNormalForm.evaluate_injective
  rw [← ofAdjacentNormalForm_evaluate first,
    ← ofAdjacentNormalForm_evaluate second, equality]

/-- Canonical uniform normal form for the xor `2` witness. -/
noncomputable def secondXorNormalForm :
    FiniteAxisFoldNatXorMaskNormalForm :=
  ⟨2, FiniteAxisFoldNatFiniteSupportCode.encode
    (1 : finiteAxisFoldFiniteSupportPermutationSubgroup Nat)⟩

/-- The canonical mask-2 normal form evaluates to the Cycle 108 source
algorithm. -/
theorem secondXorNormalForm_evaluate :
    secondXorNormalForm.evaluate = finiteAxisFoldNatSecondXorAlgorithm := by
  have decoded := congrArg Subtype.val
    (FiniteAxisFoldNatFiniteSupportCode.decode_encode
      (1 : finiteAxisFoldFiniteSupportPermutationSubgroup Nat))
  change
    (FiniteAxisFoldNatFiniteSupportCode.encode
      (1 : finiteAxisFoldFiniteSupportPermutationSubgroup Nat)).evaluate =
        (1 : Equiv.Perm Nat) at decoded
  simp [secondXorNormalForm, evaluate, decoded]

/-- The same-section actual evaluation recovers the Cycle 108 residual
witness. -/
theorem secondXorNormalForm_actualEvaluate :
    secondXorNormalForm.actualEvaluate =
      finiteAxisFoldNatSecondXorLocalFiberKernel := by
  change finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
      secondXorNormalForm.evaluate =
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
      finiteAxisFoldNatSecondXorAlgorithm
  rw [secondXorNormalForm_evaluate]

end FiniteAxisFoldNatXorMaskNormalForm

/-- Decoder-independent actual image: a residual element belongs when its
complete backward action is induced by a xor-mask algorithm followed by an
arbitrary finite-support Nat permutation. -/
def FiniteAxisFoldNatXorMaskIntrinsicImage :
    Set FiniteAxisFoldResidualLocalFiberKernel :=
  { remainder |
    ∃ mask : Nat, ∃ permutation : Equiv.Perm Nat,
      (fixedBy Nat permutation)ᶜ.Finite ∧
      finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder =
        finiteAxisFoldArbitraryCarrierBackwardAction Nat
          (finiteAxisFoldNatXorMask mask * permutation) }

namespace FiniteAxisFoldNatXorMaskNormalForm

/-- Decode into the independently characterized actual image. -/
noncomputable def intrinsicDecode
    (normal : FiniteAxisFoldNatXorMaskNormalForm) :
    FiniteAxisFoldNatXorMaskIntrinsicImage :=
  ⟨normal.actualEvaluate, normal.mask, normal.finite.evaluate,
    normal.finite.evaluate_finite,
    normal.actualEvaluate_backwardProjection⟩

/-- Intrinsic decoding is faithful. -/
theorem intrinsicDecode_injective : Function.Injective intrinsicDecode := by
  intro first second equality
  apply actualEvaluate_injective
  exact congrArg Subtype.val equality

/-- Every intrinsically characterized actual element has an exact-support
uniform normal form. -/
theorem intrinsicDecode_surjective : Function.Surjective intrinsicDecode := by
  intro remainder
  obtain ⟨mask, permutation, finiteSupport, actionEquality⟩ := remainder.2
  let finitePermutation :
      finiteAxisFoldFiniteSupportPermutationSubgroup Nat :=
    ⟨permutation,
      (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).2
        finiteSupport⟩
  let normal : FiniteAxisFoldNatXorMaskNormalForm :=
    ⟨mask, FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation⟩
  refine ⟨normal, ?_⟩
  apply Subtype.ext
  apply finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      normal.actualEvaluate =
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder.1
  rw [normal.actualEvaluate_backwardProjection]
  have decoded := congrArg Subtype.val
    (FiniteAxisFoldNatFiniteSupportCode.decode_encode finitePermutation)
  change
    (FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation).evaluate =
      permutation at decoded
  change finiteAxisFoldArbitraryCarrierBackwardAction Nat
      (finiteAxisFoldNatXorMask mask *
        (FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation).evaluate) =
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder.1
  rw [decoded]
  exact actionEquality.symm

/-- Exact recovery equivalence for the uniform xor-mask presentation. -/
noncomputable def equivIntrinsicImage :
    FiniteAxisFoldNatXorMaskNormalForm ≃
      FiniteAxisFoldNatXorMaskIntrinsicImage :=
  Equiv.ofBijective intrinsicDecode
    ⟨intrinsicDecode_injective, intrinsicDecode_surjective⟩

end FiniteAxisFoldNatXorMaskNormalForm

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
