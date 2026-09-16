import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationIntrinsicImage
import Formal.Util.AssertStandardAxioms

/-!
# A source-owned direction outside every finite-carrier Extension image

Cycle 98 characterized the image attached to each fixed finite Extension
carrier.  This file forms their literal carrier-indexed union and proves that
it does not cover the full actual local-fiber kernel.

The outside element is not supplied as a semantic residual witness.  It is the
primitive source action which swaps `0` and `1` on the `Nat` Extension carrier,
transported through the same complete-geometry route as the finite-carrier
family.  Every finite-carrier action fixes the canonical `Nat` probe because a
finite type cannot equal `Nat`; the `Nat` swap moves that probe.  The fixed
route equivalence and the faithful actual backward projection preserve this
distinction.

This is a strict noncoverage result for the literal union of the Cycle 98
subgroups.  It does not yet construct the enlarged parameter-relative syntax
or recover the remaining G-122 classification data.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- A carrier together with the finite structure required by the Cycle 98
lookup-table code. -/
structure FiniteAxisFoldFiniteExtensionCarrier where
  Carrier : Type
  finite : Fintype Carrier

/-- Literal carrier-indexed union of all Cycle 98 intrinsic subgroups. -/
def FiniteAxisFoldFiniteCarrierExtensionImage
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) : Prop :=
  ∃ descriptor : FiniteAxisFoldFiniteExtensionCarrier,
    letI := descriptor.finite
    remainder ∈
      FiniteAxisFoldExtensionPermutationIntrinsicImage descriptor.Carrier

/-- The fixed source-owned permutation which exchanges `0` and `1` on the
infinite Extension carrier `Nat`. -/
def finiteAxisFoldNatZeroOneSwap : Equiv.Perm Nat :=
  Equiv.swap 0 1

@[simp] theorem finiteAxisFoldNatZeroOneSwap_zero :
    finiteAxisFoldNatZeroOneSwap 0 = 1 := by
  simp [finiteAxisFoldNatZeroOneSwap]

@[simp] theorem finiteAxisFoldNatZeroOneSwap_inv :
    finiteAxisFoldNatZeroOneSwap⁻¹ = finiteAxisFoldNatZeroOneSwap := by
  simp [finiteAxisFoldNatZeroOneSwap]

/-- The actual backward projection of every primitive Extension permutation
is its independently transported source-context action.  No finiteness of the
carrier is used by this route computation. -/
theorem finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
    {E : Type} (permutation : Equiv.Perm E) :
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E
          permutation) =
      MulOpposite.op
        (finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹) := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro context
  change contextBackward
      ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E)
        permutation).hom.1.base context =
    finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹ context
  rw [finiteAxisFoldActualPermutation_contextBackward,
    finiteAxisFoldExactLeftPermutation_contextBackward,
    finiteAxisFoldSouthwestPermutation_contextBackward]
  rfl

/-- The `Nat` swap carried through the same source-to-actual construction. -/
noncomputable def finiteAxisFoldNatZeroOneSwapLocalFiberKernel :
    FiniteAxisFoldResidualLocalFiberKernel :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
    finiteAxisFoldNatZeroOneSwap

private theorem finiteAxisFoldNat_ne_finiteCarrier
    (descriptor : FiniteAxisFoldFiniteExtensionCarrier) :
    Nat ≠ descriptor.Carrier := by
  rcases descriptor with ⟨E, finite⟩
  dsimp
  intro equality
  subst E
  exact Fintype.false finite

private theorem finiteAxisFoldFiniteCarrierUnionContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- Every finite-carrier primitive action fixes the canonical zero-valued
`Nat` source probe. -/
theorem finiteAxisFoldFiniteCarrierSourceAction_fixes_natZeroProbe
    (descriptor : FiniteAxisFoldFiniteExtensionCarrier)
    (permutation : Equiv.Perm descriptor.Carrier) :
    (finiteAxisFoldSourceContextObjectPermHom descriptor.Carrier permutation)
        (⟨finiteAxisFoldSourceExtensionProbe (0 : Nat)⟩ :
          FiniteAxisFoldSourceContextObject) =
      (⟨finiteAxisFoldSourceExtensionProbe (0 : Nat)⟩ :
        FiniteAxisFoldSourceContextObject) := by
  apply finiteAxisFoldFiniteCarrierUnionContextObject_eq_of_ctx_eq
  simp [finiteAxisFoldSourceContextObjectPermHom,
    finiteAxisFoldSourceContextObjectPerm,
    finiteAxisFoldSourceContextObjectPermutation,
    finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldSourceExtensionProbe,
    finiteAxisFoldExtensionValuePermutation,
    finiteAxisFoldNat_ne_finiteCarrier descriptor]

/-- The transported `Nat` swap and every transported finite-carrier action
remain distinct on the actual image of the canonical `Nat` probe. -/
theorem finiteAxisFoldNatZeroOneSwap_transported_ne_finiteCarrier
    (descriptor : FiniteAxisFoldFiniteExtensionCarrier)
    (permutation : Equiv.Perm descriptor.Carrier) :
    finiteAxisFoldTransportedSourceContextPermutation
        finiteAxisFoldNatZeroOneSwap ≠
      finiteAxisFoldTransportedSourceContextPermutation permutation := by
  intro equality
  have evaluated := congrArg
    (fun actualPermutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      actualPermutation
        (finiteAxisFoldSourceToActualContextEquiv
          (⟨finiteAxisFoldSourceExtensionProbe (0 : Nat)⟩ :
            FiniteAxisFoldSourceContextObject)))
    equality
  simp only [finiteAxisFoldTransportedSourceContextPermutation,
    Equiv.trans_apply, Equiv.symm_apply_apply] at evaluated
  have sourceEquality := finiteAxisFoldSourceToActualContextEquiv.injective evaluated
  have sourceEquality' := sourceEquality.trans
    (finiteAxisFoldFiniteCarrierSourceAction_fixes_natZeroProbe
      descriptor permutation)
  have extensionSigmaEquality := congrArg
    (fun W : FiniteAxisFoldSourceContextObject =>
      (⟨W.ctx.Extension, W.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier))
    sourceEquality'
  have zeroEqualsOne : (1 : Nat) = 0 := by
    simp [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] at extensionSigmaEquality
  omega

/-- The source-owned `Nat` swap lies outside the literal union of all
fixed-finite-carrier intrinsic images. -/
theorem finiteAxisFoldNatZeroOneSwap_not_finiteCarrierExtensionImage :
    ¬ FiniteAxisFoldFiniteCarrierExtensionImage
      finiteAxisFoldNatZeroOneSwapLocalFiberKernel := by
  rintro ⟨descriptor, membership⟩
  letI : Fintype descriptor.Carrier := descriptor.finite
  obtain ⟨code, actionEquality⟩ :=
    (finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff
      finiteAxisFoldNatZeroOneSwapLocalFiberKernel).1 membership
  have projectedNat :=
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
      finiteAxisFoldNatZeroOneSwap
  rw [finiteAxisFoldNatZeroOneSwap_inv] at projectedNat
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation
          finiteAxisFoldNatZeroOneSwap =
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm code)⁻¹ := by
    apply MulOpposite.op_injective
    calc
      MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation
            finiteAxisFoldNatZeroOneSwap) =
        finiteAxisFoldResidualLocalFiberKernelBackwardProjection
          finiteAxisFoldNatZeroOneSwapLocalFiberKernel := projectedNat.symm
      _ = finiteAxisFoldExtensionPermutationBackwardAction
          descriptor.Carrier code := actionEquality
      _ = MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation
            (FiniteAxisFoldExtensionPermutationCode.toPerm code)⁻¹) := rfl
  exact finiteAxisFoldNatZeroOneSwap_transported_ne_finiteCarrier
    descriptor
    (FiniteAxisFoldExtensionPermutationCode.toPerm code)⁻¹
    transportedEquality

/-- Consequently the literal finite-carrier union does not cover the full
actual local-fiber kernel. -/
theorem finiteAxisFoldFiniteCarrierExtensionImage_not_all :
    ¬ ∀ remainder : FiniteAxisFoldResidualLocalFiberKernel,
      FiniteAxisFoldFiniteCarrierExtensionImage remainder := by
  intro coverage
  exact finiteAxisFoldNatZeroOneSwap_not_finiteCarrierExtensionImage
    (coverage finiteAxisFoldNatZeroOneSwapLocalFiberKernel)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
