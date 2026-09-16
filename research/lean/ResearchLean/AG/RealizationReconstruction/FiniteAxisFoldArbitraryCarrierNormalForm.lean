import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldFiniteSwapWordImage
import Mathlib.GroupTheory.Perm.Support
import Formal.Util.AssertStandardAxioms

/-!
# Exact-support normal forms on arbitrary Extension carriers

The finite-support component is represented by a finite set of values of an
arbitrary carrier `E` and explicit forward/backward lookup tables on that
finite subtype.  Every table point is required to move.  Thus the authored
finite set is exactly the semantic moved set, and fixed-point padding cannot
destroy faithfulness.  The ambient carrier itself need not be finite.

The source action remains faithful for arbitrary `E`: equality is read at the
canonical source Extension probe attached to each `e : E`.  Transport through
the fixed source-to-actual context equivalence therefore remains faithful as
well.  This proves an equivalence from the independent exact-support syntax to
the already defined, decoder-independent actual intrinsic image.

No completed permutation of `E`, actual residual-kernel element, decoder
range witness, or image-membership certificate is stored in the syntax.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- Independent exact-support finite data on an arbitrary carrier.  Only the
finite subtype is tabulated; no ambient permutation is a field. -/
structure FiniteAxisFoldArbitraryCarrierFiniteSupportCode
    (E : Type) [DecidableEq E] where
  support : Finset E
  table : FiniteAxisFoldExtensionPermutationCode support
  table_moves : ∀ value, table.forward value ≠ value

namespace FiniteAxisFoldArbitraryCarrierFiniteSupportCode

variable {E : Type} [DecidableEq E]

/-- Extend the explicit table by the identity outside its finite support. -/
def evaluate (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E) :
    Equiv.Perm E :=
  Equiv.Perm.ofSubtype code.table.toPerm

/-- The authored support is exactly the moved set of the evaluation. -/
theorem evaluate_ne_iff_mem
    (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E)
    (value : E) :
    code.evaluate value ≠ value ↔ value ∈ code.support := by
  constructor
  · intro moved
    by_contra outside
    exact moved
      (Equiv.Perm.ofSubtype_apply_of_not_mem code.table.toPerm outside)
  · intro inside fixed
    apply code.table_moves ⟨value, inside⟩
    apply Subtype.ext
    change (↑(code.table.toPerm ⟨value, inside⟩) : E) = value
    rw [← Equiv.Perm.ofSubtype_apply_of_mem code.table.toPerm inside]
    exact fixed

/-- Finite support is derived from the finite code. -/
theorem evaluate_finite
    (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E) :
    (fixedBy E code.evaluate)ᶜ.Finite := by
  have moved_eq : (fixedBy E code.evaluate)ᶜ =
      (code.support : Set E) := by
    ext value
    simp only [Set.mem_compl_iff, mem_fixedBy, Finset.mem_coe]
    exact code.evaluate_ne_iff_mem value
  rw [moved_eq]
  exact code.support.finite_toSet

/-- Evaluation lands in the independently characterized finite-support
subgroup. -/
def decode (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E) :
    finiteAxisFoldFiniteSupportPermutationSubgroup E :=
  ⟨code.evaluate,
    (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).2
      code.evaluate_finite⟩

/-- Equality of ambient evaluations recovers the complete exact-support
finite code. -/
theorem evaluate_injective :
    Function.Injective
      (evaluate (E := E)) := by
  intro first second equality
  have supportEquality : first.support = second.support := by
    ext value
    rw [← first.evaluate_ne_iff_mem, ← second.evaluate_ne_iff_mem, equality]
  cases first with
  | mk firstSupport firstTable firstMoves =>
      cases second with
      | mk secondSupport secondTable secondMoves =>
          dsimp only at supportEquality
          subst secondSupport
          congr
          apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
          apply Equiv.Perm.ofSubtype_injective
          exact equality

/-- Membership in the moved set is invariant under a permutation. -/
private theorem moved_invariant (permutation : Equiv.Perm E) (value : E) :
    permutation (permutation value) ≠ permutation value ↔
      permutation value ≠ value := by
  rw [permutation.injective.ne_iff]

/-- The exact finite moved set of a finite-support permutation. -/
private noncomputable def exactSupport
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup E) :
    Finset E :=
  ((finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff permutation.1).1
    permutation.2).toFinset

private theorem mem_exactSupport_iff
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup E)
    (value : E) :
    value ∈ exactSupport permutation ↔ permutation.1 value ≠ value := by
  rw [exactSupport, Set.Finite.mem_toFinset]
  simp [fixedBy]

private theorem exactSupport_invariant
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup E)
    (value : E) :
    permutation.1 value ∈ exactSupport permutation ↔
      value ∈ exactSupport permutation := by
  rw [mem_exactSupport_iff, mem_exactSupport_iff]
  exact moved_invariant permutation.1 value

/-- Extract the exact moved set and restrict the already given source
permutation to it.  This is the inverse construction in the coverage theorem,
not an additional syntax field. -/
noncomputable def encode
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup E) :
    FiniteAxisFoldArbitraryCarrierFiniteSupportCode E :=
  { support := exactSupport permutation
    table := FiniteAxisFoldExtensionPermutationCode.ofPerm
      (permutation.1.subtypePerm (exactSupport_invariant permutation))
    table_moves := fun value fixed => by
      have movedValue : permutation.1 value.1 ≠ value.1 :=
        (mem_exactSupport_iff permutation value.1).1 value.2
      apply movedValue
      exact congrArg Subtype.val fixed }

/-- Exact-support extraction decodes to the original source permutation. -/
theorem decode_encode
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup E) :
    (encode permutation).decode = permutation := by
  apply Subtype.ext
  apply Equiv.Perm.ofSubtype_subtypePerm
    (exactSupport_invariant permutation)
  intro value moved
  exact (mem_exactSupport_iff permutation value).2 moved

/-- Re-encoding a decoded exact-support table introduces no padding. -/
theorem encode_decode
    (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E) :
    encode code.decode = code := by
  apply evaluate_injective
  change (encode code.decode).decode.1 = code.decode.1
  exact congrArg Subtype.val (decode_encode code.decode)

/-- Canonical equivalence between exact finite source data and all
finite-support permutations of the arbitrary carrier. -/
noncomputable def equivFiniteSupport :
    FiniteAxisFoldArbitraryCarrierFiniteSupportCode E ≃
      finiteAxisFoldFiniteSupportPermutationSubgroup E where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

end FiniteAxisFoldArbitraryCarrierFiniteSupportCode

/-- The transported full-context action is faithful for every carrier.  The
proof evaluates equality at the canonical source probe for each `value : E`;
no finite enumeration or represented subfamily is supplied. -/
theorem finiteAxisFoldTransportedArbitraryCarrierSourceContextPermutation_injective
    (E : Type) :
    Function.Injective
      (finiteAxisFoldTransportedSourceContextPermutationHom E) := by
  intro first second equality
  apply Equiv.ext
  intro value
  have evaluated := congrArg
    (fun actualPermutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      actualPermutation
        (finiteAxisFoldSourceToActualContextEquiv
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject)))
    equality
  simp only [finiteAxisFoldTransportedSourceContextPermutationHom,
    MonoidHom.coe_mk, OneHom.coe_mk,
    finiteAxisFoldTransportedSourceContextPermutation,
    Equiv.trans_apply, Equiv.symm_apply_apply] at evaluated
  have sourceEquality :=
    finiteAxisFoldSourceToActualContextEquiv.injective evaluated
  have extensionSigmaEquality := congrArg
    (fun W : FiniteAxisFoldSourceContextObject =>
      (⟨W.ctx.Extension, W.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier))
    sourceEquality
  have probeEquality :
      (⟨E, first value⟩ : Sigma fun carrier : Type => carrier) =
        ⟨E, second value⟩ := by
    simpa [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] using extensionSigmaEquality
  exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2

/-- The independently defined expected backward action is faithful for every
carrier, without `Fintype E` or a completed semantic action as input. -/
theorem finiteAxisFoldArbitraryCarrierBackwardAction_injective_forCarrier
    (E : Type) :
    Function.Injective (finiteAxisFoldArbitraryCarrierBackwardAction E) := by
  intro first second equality
  have transportedInverseEquality :
      finiteAxisFoldTransportedSourceContextPermutation first⁻¹ =
        finiteAxisFoldTransportedSourceContextPermutation second⁻¹ :=
    MulOpposite.op_injective equality
  have inverseEquality :=
    finiteAxisFoldTransportedArbitraryCarrierSourceContextPermutation_injective
      E transportedInverseEquality
  exact inv_injective inverseEquality

namespace FiniteAxisFoldArbitraryCarrierFiniteSupportCode

variable {E : Type} [DecidableEq E]

/-- Evaluate exact finite source data through the fixed actual section. -/
noncomputable def actualEvaluate
    (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E) :
    FiniteAxisFoldResidualLocalFiberKernel :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E code.evaluate

/-- The actual projection is the independently defined expected backward
action of the source evaluation. -/
theorem actualEvaluate_backwardProjection
    (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E) :
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        code.actualEvaluate =
      finiteAxisFoldArbitraryCarrierBackwardAction E code.evaluate :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
    code.evaluate

/-- Decode into the pre-existing intrinsic image characterized only by finite
support and the expected full backward action. -/
noncomputable def intrinsicDecode
    (code : FiniteAxisFoldArbitraryCarrierFiniteSupportCode E) :
    FiniteAxisFoldFiniteSwapWordIntrinsicImage E :=
  ⟨code.actualEvaluate, by
    rw [finiteAxisFoldFiniteSwapWordIntrinsicImage_mem_iff]
    exact ⟨code.evaluate, code.evaluate_finite,
      code.actualEvaluate_backwardProjection⟩⟩

/-- Actual decoding is faithful because the complete backward action reads
back the ambient source permutation and exact support reads back the code. -/
theorem intrinsicDecode_injective :
    Function.Injective (intrinsicDecode (E := E)) := by
  intro first second equality
  apply evaluate_injective
  apply finiteAxisFoldArbitraryCarrierBackwardAction_injective_forCarrier E
  rw [← first.actualEvaluate_backwardProjection,
    ← second.actualEvaluate_backwardProjection]
  exact congrArg finiteAxisFoldResidualLocalFiberKernelBackwardProjection
    (congrArg Subtype.val equality)

/-- Every member of the independently characterized actual intrinsic image
has an exact-support finite code. -/
theorem intrinsicDecode_surjective :
    Function.Surjective (intrinsicDecode (E := E)) := by
  intro remainder
  obtain ⟨permutation, finiteSupport, actionEquality⟩ :=
    (finiteAxisFoldFiniteSwapWordIntrinsicImage_mem_iff remainder.1).mp
      remainder.2
  let source : finiteAxisFoldFiniteSupportPermutationSubgroup E :=
    ⟨permutation,
      (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).2
        finiteSupport⟩
  refine ⟨encode source, ?_⟩
  apply Subtype.ext
  apply finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      (encode source).actualEvaluate =
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder.1
  rw [actualEvaluate_backwardProjection]
  have decoded := congrArg Subtype.val (decode_encode source)
  change (encode source).evaluate = permutation at decoded
  rw [decoded]
  exact actionEquality.symm

/-- Exact recovery equivalence on the decoder-independent actual intrinsic
image for arbitrary, possibly infinite, primitive carriers. -/
noncomputable def equivIntrinsicImage :
    FiniteAxisFoldArbitraryCarrierFiniteSupportCode E ≃
      FiniteAxisFoldFiniteSwapWordIntrinsicImage E :=
  Equiv.ofBijective intrinsicDecode
    ⟨intrinsicDecode_injective, intrinsicDecode_surjective⟩

end FiniteAxisFoldArbitraryCarrierFiniteSupportCode

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
