import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldFiniteSwapWordImage
import Mathlib.Data.Nat.Bitwise
import Formal.Util.AssertStandardAxioms

/-!
# An infinite-support source recipe outside every finite swap-word image

Cycle 100 supplies finite words of explicit swaps on every primitive carrier
and identifies their image with finite-support permutations.  This file forms
the literal carrier-indexed union of those intrinsic images and proves that it
still does not cover the actual local-fiber kernel.

The separating element is not an arbitrary completed permutation supplied as
presentation data.  It is the fixed finite algorithm `n ↦ n xor 1` on the
primitive `Nat` carrier.  The algorithm is an involution and moves every
natural number.  Thus it differs from every finite-support action on `Nat` at
a fixed point, while actions attached to another carrier fix every `Nat`
probe.  The same source-to-actual equivalence and faithful backward projection
then preserve the distinction.

This refutes only coverage by the current finite-swap-word recipe class.  It
does not refute the fixed G-123 target and does not yet provide the enlarged
faithful presentation required by B and D.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- A primitive carrier equipped only with the decidable equality needed by
the independent finite-swap-word syntax. -/
structure FiniteAxisFoldDecidableExtensionCarrier where
  Carrier : Type
  decidableEq : DecidableEq Carrier

/-- Literal carrier-indexed union of all Cycle 100 finite-support intrinsic
images.  The carrier is chosen before membership is tested. -/
def FiniteAxisFoldFiniteSupportCarrierImage
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) : Prop :=
  ∃ descriptor : FiniteAxisFoldDecidableExtensionCarrier,
    letI := descriptor.decidableEq
    remainder ∈ FiniteAxisFoldFiniteSwapWordIntrinsicImage descriptor.Carrier

/-- Adjacent-pair exchange on the primitive `Nat` carrier, given by a fixed
finite algorithm rather than an all-domain lookup table. -/
def finiteAxisFoldNatAdjacentSwap : Equiv.Perm Nat where
  toFun atom := atom ^^^ 1
  invFun atom := atom ^^^ 1
  left_inv atom := Nat.xor_xor_cancel_right atom 1
  right_inv atom := Nat.xor_xor_cancel_right atom 1

@[simp] theorem finiteAxisFoldNatAdjacentSwap_apply (atom : Nat) :
    finiteAxisFoldNatAdjacentSwap atom = atom ^^^ 1 := rfl

@[simp] theorem finiteAxisFoldNatAdjacentSwap_inv :
    finiteAxisFoldNatAdjacentSwap⁻¹ = finiteAxisFoldNatAdjacentSwap := by
  apply Equiv.ext
  intro atom
  rfl

/-- Every primitive value is moved by the adjacent-pair algorithm. -/
theorem finiteAxisFoldNatAdjacentSwap_ne (atom : Nat) :
    finiteAxisFoldNatAdjacentSwap atom ≠ atom := by
  intro equality
  have xorEquality : atom ^^^ 1 = atom ^^^ 0 := by
    simpa using equality
  have : (1 : Nat) = 0 := Nat.xor_right_inj.mp xorEquality
  omega

/-- The adjacent-pair algorithm transported through the same fixed actual
route as Cycles 92--100. -/
noncomputable def finiteAxisFoldNatAdjacentSwapLocalFiberKernel :
    FiniteAxisFoldResidualLocalFiberKernel :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
    finiteAxisFoldNatAdjacentSwap

private theorem finiteAxisFoldFiniteSupportUnionContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- A finite-support action attached to any primitive carrier fixes at least
one canonical `Nat` probe.  On the `Nat` carrier this follows from infinite
cardinality; on every other carrier all `Nat` probes are fixed by construction.
-/
theorem finiteAxisFoldFiniteSupportSourceAction_exists_fixed_natProbe
    (E : Type) [DecidableEq E] (permutation : Equiv.Perm E)
    (finiteSupport : (fixedBy E permutation)ᶜ.Finite) :
    ∃ atom : Nat,
      (finiteAxisFoldSourceContextObjectPermHom E permutation)
          (⟨finiteAxisFoldSourceExtensionProbe atom⟩ :
            FiniteAxisFoldSourceContextObject) =
        (⟨finiteAxisFoldSourceExtensionProbe atom⟩ :
          FiniteAxisFoldSourceContextObject) := by
  classical
  by_cases carrierEquality : Nat = E
  · subst E
    have fixedPoint : ∃ atom : Nat, permutation atom = atom := by
      by_contra noFixedPoint
      push_neg at noFixedPoint
      have moved_eq_univ : (fixedBy Nat permutation)ᶜ = Set.univ := by
        ext atom
        simp [fixedBy, noFixedPoint atom]
      have univFinite : (Set.univ : Set Nat).Finite := by
        rw [← moved_eq_univ]
        exact finiteSupport
      exact Set.infinite_univ univFinite
    obtain ⟨atom, fixed⟩ := fixedPoint
    refine ⟨atom, ?_⟩
    apply finiteAxisFoldFiniteSupportUnionContextObject_eq_of_ctx_eq
    simp [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe, fixed]
  · refine ⟨0, ?_⟩
    apply finiteAxisFoldFiniteSupportUnionContextObject_eq_of_ctx_eq
    simp [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe,
      finiteAxisFoldExtensionValuePermutation, carrierEquality]

/-- The transported adjacent-pair action differs from every transported
finite-support action, including those on the same primitive carrier. -/
theorem finiteAxisFoldNatAdjacentSwap_transported_ne_finiteSupport
    (E : Type) [DecidableEq E] (permutation : Equiv.Perm E)
    (finiteSupport : (fixedBy E permutation)ᶜ.Finite) :
    finiteAxisFoldTransportedSourceContextPermutation
        finiteAxisFoldNatAdjacentSwap ≠
      finiteAxisFoldTransportedSourceContextPermutation permutation := by
  obtain ⟨atom, fixedProbe⟩ :=
    finiteAxisFoldFiniteSupportSourceAction_exists_fixed_natProbe
      E permutation finiteSupport
  intro equality
  have evaluated := congrArg
    (fun actualPermutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      actualPermutation
        (finiteAxisFoldSourceToActualContextEquiv
          (⟨finiteAxisFoldSourceExtensionProbe atom⟩ :
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
  have movedEqualsFixed : finiteAxisFoldNatAdjacentSwap atom = atom := by
    simpa [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] using extensionSigmaEquality
  exact finiteAxisFoldNatAdjacentSwap_ne atom movedEqualsFixed

/-- The fixed adjacent-pair source recipe is outside the carrier-indexed union
of all finite-swap-word intrinsic images. -/
theorem finiteAxisFoldNatAdjacentSwap_not_finiteSupportCarrierImage :
    ¬ FiniteAxisFoldFiniteSupportCarrierImage
      finiteAxisFoldNatAdjacentSwapLocalFiberKernel := by
  rintro ⟨descriptor, membership⟩
  letI : DecidableEq descriptor.Carrier := descriptor.decidableEq
  obtain ⟨permutation, finiteSupport, actionEquality⟩ :=
    (finiteAxisFoldFiniteSwapWordIntrinsicImage_mem_iff
      finiteAxisFoldNatAdjacentSwapLocalFiberKernel).1 membership
  have inverseFiniteSupport :
      (fixedBy descriptor.Carrier permutation⁻¹)ᶜ.Finite := by
    apply (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).mp
    exact (finiteAxisFoldFiniteSupportPermutationSubgroup descriptor.Carrier).inv_mem
      ((finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff permutation).mpr
        finiteSupport)
  have projectedAdjacent :=
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
      finiteAxisFoldNatAdjacentSwap
  rw [finiteAxisFoldNatAdjacentSwap_inv] at projectedAdjacent
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation
          finiteAxisFoldNatAdjacentSwap =
        finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹ := by
    apply MulOpposite.op_injective
    calc
      MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation
            finiteAxisFoldNatAdjacentSwap) =
        finiteAxisFoldResidualLocalFiberKernelBackwardProjection
          finiteAxisFoldNatAdjacentSwapLocalFiberKernel := projectedAdjacent.symm
      _ = finiteAxisFoldArbitraryCarrierBackwardAction
          descriptor.Carrier permutation := actionEquality
      _ = MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹) := rfl
  exact finiteAxisFoldNatAdjacentSwap_transported_ne_finiteSupport
    descriptor.Carrier permutation⁻¹ inverseFiniteSupport transportedEquality

/-- Therefore the carrier-indexed finite-support recipe class does not cover
the full actual local-fiber kernel. -/
theorem finiteAxisFoldFiniteSupportCarrierImage_not_all :
    ¬ ∀ remainder : FiniteAxisFoldResidualLocalFiberKernel,
      FiniteAxisFoldFiniteSupportCarrierImage remainder := by
  intro coverage
  exact finiteAxisFoldNatAdjacentSwap_not_finiteSupportCarrierImage
    (coverage finiteAxisFoldNatAdjacentSwapLocalFiberKernel)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
