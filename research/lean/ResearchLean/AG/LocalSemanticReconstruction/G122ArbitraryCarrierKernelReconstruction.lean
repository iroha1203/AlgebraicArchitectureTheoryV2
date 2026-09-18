import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPowerSetComplementObstruction
import ResearchLean.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle
import Formal.Util.AssertStandardAxioms

/-!
# Arbitrary-carrier reconstruction inside the G-122 local-fiber kernel

The primitive Extension-permutation section does not require a finite carrier.
This module proves its faithfulness for every carrier, reconstructs its actual
local-fiber-kernel image multiplicatively from source permutations, and then
reconstructs that image again from the actual stored-backward observation.

The resulting carrier-indexed family strictly exceeds the union of all finite
carrier lookup-table images.  It also contains the powerset-complement witness
which is outside the stronger union of all exact-support images.  These are
source-owned recipes transported through the accepted actual route; no actual
kernel value, semantic membership witness, or completed observation is stored
in the source syntax.

This is not a presentation of the full local-fiber kernel.  Each theorem keeps
the carrier parameter explicit, and the strictness statements only compare the
accepted represented families.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

namespace G122ArbitraryCarrierKernelReconstruction

/-- Canonical primitive probes separate source permutations without a
finiteness assumption on the carrier. -/
theorem sourceContextObjectPermHom_injective (E : Type) :
    Function.Injective (finiteAxisFoldSourceContextObjectPermHom E) := by
  intro first second equality
  apply Equiv.ext
  intro value
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
      permutation
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject))
    equality
  have extensionSigmaEquality := congrArg
    (fun W : FiniteAxisFoldSourceContextObject =>
      (⟨W.ctx.Extension, W.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier))
    evaluated
  have probeEquality :
      (⟨E, first value⟩ : Sigma fun carrier : Type => carrier) =
        ⟨E, second value⟩ := by
    simpa [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] using extensionSigmaEquality
  exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2

/-- The arbitrary-carrier section into the actual joint local-fiber kernel is
faithful. -/
theorem localFiberKernelSection_injective (E : Type) :
    Function.Injective
      (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E) := by
  intro first second equality
  have projected := congrArg
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection equality
  rw [finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection,
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection]
      at projected
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation first⁻¹ =
        finiteAxisFoldTransportedSourceContextPermutation second⁻¹ :=
    MulOpposite.op_injective projected
  have sourceEquality :
      finiteAxisFoldSourceContextObjectPermHom E first⁻¹ =
        finiteAxisFoldSourceContextObjectPermHom E second⁻¹ := by
    apply G122ParametricCarrierDisplayedBundle.transportSourceActionHom_injective
    simpa only [
      G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier]
      using transportedEquality
  have inverseEquality : first⁻¹ = second⁻¹ :=
    sourceContextObjectPermHom_injective E sourceEquality
  exact inv_injective inverseEquality

/-- The actual subgroup represented by permutations of one arbitrary carrier.
The source syntax remains `Equiv.Perm E`. -/
noncomputable def ActualImage (E : Type) :
    Subgroup FiniteAxisFoldResidualLocalFiberKernel :=
  MonoidHom.range
    (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E)

/-- Assemble a source permutation into its actual kernel image. -/
noncomputable def assemble (E : Type) (permutation : Equiv.Perm E) :
    ActualImage E :=
  ⟨finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E permutation,
    ⟨permutation, rfl⟩⟩

/-- Every represented actual kernel value has exactly one source permutation. -/
theorem source_existsUnique (E : Type) (value : ActualImage E) :
    ∃! permutation : Equiv.Perm E, assemble E permutation = value := by
  rcases value with ⟨value, permutation, rfl⟩
  refine ⟨permutation, rfl, ?_⟩
  intro candidate equality
  apply localFiberKernelSection_injective E
  exact congrArg Subtype.val equality

/-- Read the unique source permutation from a represented actual value. -/
noncomputable def read (E : Type) (value : ActualImage E) : Equiv.Perm E :=
  Classical.choose (source_existsUnique E value)

/-- Reading after assembly is identity. -/
@[simp] theorem read_assemble (E : Type) (permutation : Equiv.Perm E) :
    read E (assemble E permutation) = permutation := by
  exact ((Classical.choose_spec (source_existsUnique E (assemble E permutation))).2
    permutation rfl).symm

/-- Assembly after reading is identity on every represented actual value. -/
@[simp] theorem assemble_read (E : Type) (value : ActualImage E) :
    assemble E (read E value) = value :=
  (Classical.choose_spec (source_existsUnique E value)).1

/-- Source permutations and the actual arbitrary-carrier image are
multiplicatively equivalent. -/
noncomputable def sourceActualMulEquiv (E : Type) :
    Equiv.Perm E ≃* ActualImage E where
  toFun := assemble E
  invFun := read E
  left_inv := read_assemble E
  right_inv := assemble_read E
  map_mul' first second := by
    apply Subtype.ext
    change
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E
          (first * second) =
        finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E first *
          finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E second
    exact
      (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E).map_mul
        first second

/-- Actual stored-backward observation restricted to the represented image. -/
noncomputable def backwardObservationHom (E : Type) :
    ActualImage E →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldResidualLocalFiberKernelBackwardProjection.comp
    (ActualImage E).subtype

/-- Stored-backward observation of an assembled source permutation is the
independently transported inverse source action. -/
theorem backwardObservation_assemble (E : Type)
    (permutation : Equiv.Perm E) :
    backwardObservationHom E (assemble E permutation) =
      MulOpposite.op
        (finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹) :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
    permutation

/-- Stored-backward observation separates every represented actual value. -/
theorem backwardObservationHom_injective (E : Type) :
    Function.Injective (backwardObservationHom E) := by
  intro first second equality
  apply Subtype.ext
  exact finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
    equality

/-- The actually observed action image for one arbitrary carrier. -/
noncomputable def ObservedImage (E : Type) :
    Subgroup (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  MonoidHom.range (backwardObservationHom E)

/-- Every represented actual kernel value is recovered uniquely from its
stored-backward observation, multiplicatively and in both directions. -/
noncomputable def actualObservedMulEquiv (E : Type) :
    ActualImage E ≃* ObservedImage E :=
  MulEquiv.ofBijective
    (MonoidHom.rangeRestrict (backwardObservationHom E))
    ⟨(by
        intro first second equality
        apply backwardObservationHom_injective E
        exact congrArg Subtype.val equality),
      MonoidHom.rangeRestrict_surjective _⟩

/-- Reading an observed action back after observation recovers the actual value. -/
@[simp] theorem observedRead_observe (E : Type) (value : ActualImage E) :
    (actualObservedMulEquiv E).symm (actualObservedMulEquiv E value) = value :=
  (actualObservedMulEquiv E).symm_apply_apply value

/-- Observing the reconstructed actual value recovers the observed action. -/
@[simp] theorem observe_observedRead (E : Type) (value : ObservedImage E) :
    actualObservedMulEquiv E ((actualObservedMulEquiv E).symm value) = value :=
  (actualObservedMulEquiv E).apply_symm_apply value

/-- Carrier-indexed union of all arbitrary-permutation images. -/
def ArbitraryCarrierImage
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) : Prop :=
  ∃ E : Type, ∃ permutation : Equiv.Perm E,
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E
      permutation = remainder

/-- Every accepted finite-carrier lookup-table image belongs to the new
arbitrary-carrier family. -/
theorem finiteCarrierImage_subset_arbitraryCarrierImage :
    {remainder | FiniteAxisFoldFiniteCarrierExtensionImage remainder} ⊆
      {remainder | ArbitraryCarrierImage remainder} := by
  intro remainder membership
  rcases membership with ⟨descriptor, membership⟩
  letI : Fintype descriptor.Carrier := descriptor.finite
  obtain ⟨code, equality⟩ :=
    (finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff_decoder
      remainder).1 membership
  refine ⟨descriptor.Carrier,
    FiniteAxisFoldExtensionPermutationCode.toPerm code, ?_⟩
  exact equality

/-- The source-owned Nat swap belongs to the arbitrary-carrier family. -/
theorem natZeroOneSwap_mem_arbitraryCarrierImage :
    ArbitraryCarrierImage finiteAxisFoldNatZeroOneSwapLocalFiberKernel :=
  ⟨Nat, finiteAxisFoldNatZeroOneSwap, rfl⟩

/-- The new arbitrary-carrier family is a proper enlargement of the whole
finite-carrier lookup-table union. -/
theorem finiteCarrierImage_ssubset_arbitraryCarrierImage :
    {remainder | FiniteAxisFoldFiniteCarrierExtensionImage remainder} ⊂
      {remainder | ArbitraryCarrierImage remainder} := by
  refine ⟨finiteCarrierImage_subset_arbitraryCarrierImage, ?_⟩
  intro reverseInclusion
  exact finiteAxisFoldNatZeroOneSwap_not_finiteCarrierExtensionImage
    (reverseInclusion natZeroOneSwap_mem_arbitraryCarrierImage)

/-- The powerset complement is represented on its primitive carrier. -/
theorem powerSetComplement_mem_arbitraryCarrierImage :
    ArbitraryCarrierImage
      finiteAxisFoldNatPowerSetComplementLocalFiberKernel :=
  ⟨Set Nat, finiteAxisFoldNatPowerSetComplement, rfl⟩

/-- The represented powerset complement remains outside the accepted union of
all exact-support carrier images. -/
theorem powerSetComplement_not_mem_exactSupportCarrierUnion :
    finiteAxisFoldNatPowerSetComplementLocalFiberKernel ∉
      FiniteAxisFoldExactSupportCarrierUnion :=
  finiteAxisFoldNatPowerSetComplement_not_mem_exactSupportCarrierUnion

/-- Unrestricted source/actual reconstruction, observation recovery, and both
strict noncoverage witnesses hold on one theorem surface. -/
theorem reconstruction_and_strict_noncoverage (E : Type) :
    Function.Injective
        (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E) ∧
      (∀ permutation : Equiv.Perm E,
        read E (assemble E permutation) = permutation) ∧
      (∀ value : ActualImage E,
        assemble E (read E value) = value) ∧
      Function.Injective (backwardObservationHom E) ∧
      (∀ value : ActualImage E,
        (actualObservedMulEquiv E).symm
          (actualObservedMulEquiv E value) = value) ∧
      (∀ value : ObservedImage E,
        actualObservedMulEquiv E
          ((actualObservedMulEquiv E).symm value) = value) ∧
      ArbitraryCarrierImage finiteAxisFoldNatZeroOneSwapLocalFiberKernel ∧
      ¬ FiniteAxisFoldFiniteCarrierExtensionImage
        finiteAxisFoldNatZeroOneSwapLocalFiberKernel ∧
      ArbitraryCarrierImage
        finiteAxisFoldNatPowerSetComplementLocalFiberKernel ∧
      finiteAxisFoldNatPowerSetComplementLocalFiberKernel ∉
        FiniteAxisFoldExactSupportCarrierUnion :=
  ⟨localFiberKernelSection_injective E,
    read_assemble E,
    assemble_read E,
    backwardObservationHom_injective E,
    observedRead_observe E,
    observe_observedRead E,
    natZeroOneSwap_mem_arbitraryCarrierImage,
    finiteAxisFoldNatZeroOneSwap_not_finiteCarrierExtensionImage,
    powerSetComplement_mem_arbitraryCarrierImage,
    powerSetComplement_not_mem_exactSupportCarrierUnion⟩

end G122ArbitraryCarrierKernelReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction

end

end AAT.AG.LocalSemanticReconstruction
