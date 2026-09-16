import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNatXorMaskNormalForm
import Mathlib.SetTheory.Cardinal.Order
import Formal.Util.AssertStandardAxioms

/-!
# A different infinite carrier outside the Nat xor-mask image

The source-owned complement algorithm on `Set Nat` is a fixed finite formula
and moves every primitive value.  Its carrier is provably distinct from
`Nat` by Cantor's theorem.  This cardinal distinction is important because
the source action is indexed by actual carrier equality, not by a chosen
equivalence between carriers.

Transporting complement through the same fixed section gives an actual
residual witness.  A finite-support action on `Set Nat` has a fixed point; an
action on any other carrier fixes a canonical `Set Nat` probe.  Thus the
witness lies outside the all-carrier exact-support union.  Every Nat xor-mask
source action fixes the empty-set probe, whereas complement moves it, so the
witness also lies outside the Cycle 109 intrinsic Nat xor-mask image.

No completed permutation or actual residual element is added to presentation
syntax, and no full-kernel presentation claim is made.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- The fixed complement algorithm on the different infinite primitive
carrier `Set Nat`. -/
def finiteAxisFoldNatPowerSetComplement : Equiv.Perm (Set Nat) where
  toFun subset := subsetᶜ
  invFun subset := subsetᶜ
  left_inv subset := by simp
  right_inv subset := by simp

@[simp] theorem finiteAxisFoldNatPowerSetComplement_apply
    (subset : Set Nat) :
    finiteAxisFoldNatPowerSetComplement subset = subsetᶜ := rfl

@[simp] theorem finiteAxisFoldNatPowerSetComplement_inv :
    finiteAxisFoldNatPowerSetComplement⁻¹ =
      finiteAxisFoldNatPowerSetComplement := by
  apply Equiv.ext
  intro subset
  rfl

/-- No subset of Nat equals its own complement. -/
theorem finiteAxisFoldNatPowerSetComplement_ne (subset : Set Nat) :
    finiteAxisFoldNatPowerSetComplement subset ≠ subset := by
  intro equality
  have pointEquality := Set.ext_iff.mp equality 0
  simp only [finiteAxisFoldNatPowerSetComplement_apply,
    Set.mem_compl_iff] at pointEquality
  tauto

/-- Cantor's theorem makes the powerset carrier provably different from Nat,
not merely differently named. -/
theorem finiteAxisFoldNatPowerSet_ne_nat : Set Nat ≠ Nat := by
  intro equality
  have cardinalEquality : Cardinal.mk (Set Nat) = Cardinal.mk Nat :=
    congrArg Cardinal.mk equality
  have cantorStrict : Cardinal.mk Nat < Cardinal.mk (Set Nat) := by
    simpa only [Cardinal.mk_set] using
      Cardinal.cantor (Cardinal.mk Nat)
  rw [cardinalEquality] at cantorStrict
  exact (lt_irrefl (Cardinal.mk Nat)) cantorStrict

/-- The actual residual witness obtained from the same fixed section. -/
noncomputable def finiteAxisFoldNatPowerSetComplementLocalFiberKernel :
    FiniteAxisFoldResidualLocalFiberKernel :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom (Set Nat)
    finiteAxisFoldNatPowerSetComplement

private theorem finiteAxisFoldPowerSetContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- A finite-support action on any primitive carrier fixes some canonical
`Set Nat` probe.  On the same carrier this follows from infinitude; on a
different carrier the source action is definitionally inactive. -/
theorem finiteAxisFoldFiniteSupportSourceAction_exists_fixed_powerSetProbe
    (E : Type) [DecidableEq E] (permutation : Equiv.Perm E)
    (finiteSupport : (fixedBy E permutation)ᶜ.Finite) :
    ∃ subset : Set Nat,
      (finiteAxisFoldSourceContextObjectPermHom E permutation)
          (⟨finiteAxisFoldSourceExtensionProbe subset⟩ :
            FiniteAxisFoldSourceContextObject) =
        (⟨finiteAxisFoldSourceExtensionProbe subset⟩ :
          FiniteAxisFoldSourceContextObject) := by
  classical
  by_cases carrierEquality : Set Nat = E
  · subst E
    have fixedPoint : ∃ subset : Set Nat, permutation subset = subset := by
      by_contra noFixedPoint
      push_neg at noFixedPoint
      have moved_eq_univ : (fixedBy (Set Nat) permutation)ᶜ = Set.univ := by
        ext subset
        simp [fixedBy, noFixedPoint subset]
      have univFinite : (Set.univ : Set (Set Nat)).Finite := by
        rw [← moved_eq_univ]
        exact finiteSupport
      exact Set.infinite_univ univFinite
    obtain ⟨subset, fixed⟩ := fixedPoint
    refine ⟨subset, ?_⟩
    apply finiteAxisFoldPowerSetContextObject_eq_of_ctx_eq
    simp [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe, fixed]
  · refine ⟨∅, ?_⟩
    apply finiteAxisFoldPowerSetContextObject_eq_of_ctx_eq
    simp [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe,
      finiteAxisFoldExtensionValuePermutation, carrierEquality]

/-- The transported complement action differs from every transported
finite-support action on every decidable carrier. -/
theorem finiteAxisFoldNatPowerSetComplement_transported_ne_finiteSupport
    (E : Type) [DecidableEq E] (permutation : Equiv.Perm E)
    (finiteSupport : (fixedBy E permutation)ᶜ.Finite) :
    finiteAxisFoldTransportedSourceContextPermutation
        finiteAxisFoldNatPowerSetComplement ≠
      finiteAxisFoldTransportedSourceContextPermutation permutation := by
  obtain ⟨subset, fixedProbe⟩ :=
    finiteAxisFoldFiniteSupportSourceAction_exists_fixed_powerSetProbe
      E permutation finiteSupport
  intro equality
  have evaluated := congrArg
    (fun actualPermutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      actualPermutation
        (finiteAxisFoldSourceToActualContextEquiv
          (⟨finiteAxisFoldSourceExtensionProbe subset⟩ :
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
  have movedEqualsFixed : finiteAxisFoldNatPowerSetComplement subset = subset := by
    simpa [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] using extensionSigmaEquality
  exact finiteAxisFoldNatPowerSetComplement_ne subset movedEqualsFixed

/-- Every Nat source action fixes the canonical empty-set probe. -/
theorem finiteAxisFoldNatSourceAction_fixes_powerSetEmptyProbe
    (permutation : Equiv.Perm Nat) :
    (finiteAxisFoldSourceContextObjectPermHom Nat permutation)
        (⟨finiteAxisFoldSourceExtensionProbe (∅ : Set Nat)⟩ :
          FiniteAxisFoldSourceContextObject) =
      (⟨finiteAxisFoldSourceExtensionProbe (∅ : Set Nat)⟩ :
        FiniteAxisFoldSourceContextObject) := by
  apply finiteAxisFoldPowerSetContextObject_eq_of_ctx_eq
  simp [finiteAxisFoldSourceContextObjectPermHom,
    finiteAxisFoldSourceContextObjectPerm,
    finiteAxisFoldSourceContextObjectPermutation,
    finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldSourceExtensionProbe,
    finiteAxisFoldExtensionValuePermutation,
    finiteAxisFoldNatPowerSet_ne_nat]

/-- The transported complement action differs from every transported Nat
action, not only from the xor-mask formulas themselves. -/
theorem finiteAxisFoldNatPowerSetComplement_transported_ne_natAction
    (permutation : Equiv.Perm Nat) :
    finiteAxisFoldTransportedSourceContextPermutation
        finiteAxisFoldNatPowerSetComplement ≠
      finiteAxisFoldTransportedSourceContextPermutation permutation := by
  intro equality
  have evaluated := congrArg
    (fun actualPermutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      actualPermutation
        (finiteAxisFoldSourceToActualContextEquiv
          (⟨finiteAxisFoldSourceExtensionProbe (∅ : Set Nat)⟩ :
            FiniteAxisFoldSourceContextObject)))
    equality
  simp only [finiteAxisFoldTransportedSourceContextPermutation,
    Equiv.trans_apply, Equiv.symm_apply_apply] at evaluated
  have sourceEquality :=
    finiteAxisFoldSourceToActualContextEquiv.injective evaluated
  have sourceEquality' := sourceEquality.trans
    (finiteAxisFoldNatSourceAction_fixes_powerSetEmptyProbe permutation)
  have extensionSigmaEquality := congrArg
    (fun W : FiniteAxisFoldSourceContextObject =>
      (⟨W.ctx.Extension, W.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier))
    sourceEquality'
  have complementEmptyFixed :
      finiteAxisFoldNatPowerSetComplement (∅ : Set Nat) = ∅ := by
    simpa [finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe] using extensionSigmaEquality
  exact finiteAxisFoldNatPowerSetComplement_ne ∅ complementEmptyFixed

/-- The actual complement witness lies outside the exact-support union over
all decidable primitive carriers. -/
theorem finiteAxisFoldNatPowerSetComplement_not_mem_exactSupportCarrierUnion :
    finiteAxisFoldNatPowerSetComplementLocalFiberKernel ∉
      FiniteAxisFoldExactSupportCarrierUnion := by
  intro membership
  obtain ⟨descriptor, intrinsicMembership⟩ :=
    (finiteAxisFoldExactSupportCarrierUnion_mem_iff _).1 membership
  letI : DecidableEq descriptor.Carrier := descriptor.decidableEq
  obtain ⟨permutation, finiteSupport, actionEquality⟩ :=
    (finiteAxisFoldFiniteSwapWordIntrinsicImage_mem_iff
      finiteAxisFoldNatPowerSetComplementLocalFiberKernel).1
        intrinsicMembership
  have inverseFiniteSupport :
      (fixedBy descriptor.Carrier permutation⁻¹)ᶜ.Finite := by
    apply (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).mp
    exact (finiteAxisFoldFiniteSupportPermutationSubgroup
      descriptor.Carrier).inv_mem
        ((finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff permutation).mpr
          finiteSupport)
  have projectedComplement :=
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
      finiteAxisFoldNatPowerSetComplement
  rw [finiteAxisFoldNatPowerSetComplement_inv] at projectedComplement
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation
          finiteAxisFoldNatPowerSetComplement =
        finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹ := by
    apply MulOpposite.op_injective
    calc
      MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation
            finiteAxisFoldNatPowerSetComplement) =
        finiteAxisFoldResidualLocalFiberKernelBackwardProjection
          finiteAxisFoldNatPowerSetComplementLocalFiberKernel :=
            projectedComplement.symm
      _ = finiteAxisFoldArbitraryCarrierBackwardAction
          descriptor.Carrier permutation := actionEquality
      _ = MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation permutation⁻¹) := rfl
  exact finiteAxisFoldNatPowerSetComplement_transported_ne_finiteSupport
    descriptor.Carrier permutation⁻¹ inverseFiniteSupport transportedEquality

/-- The actual complement witness also lies outside the independently
characterized Nat xor-mask intrinsic image. -/
theorem finiteAxisFoldNatPowerSetComplement_not_mem_natXorMaskIntrinsicImage :
    finiteAxisFoldNatPowerSetComplementLocalFiberKernel ∉
      FiniteAxisFoldNatXorMaskIntrinsicImage := by
  rintro ⟨mask, permutation, finiteSupport, actionEquality⟩
  have projectedComplement :=
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
      finiteAxisFoldNatPowerSetComplement
  rw [finiteAxisFoldNatPowerSetComplement_inv] at projectedComplement
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation
          finiteAxisFoldNatPowerSetComplement =
        finiteAxisFoldTransportedSourceContextPermutation
          (finiteAxisFoldNatXorMask mask * permutation)⁻¹ := by
    apply MulOpposite.op_injective
    calc
      MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation
            finiteAxisFoldNatPowerSetComplement) =
        finiteAxisFoldResidualLocalFiberKernelBackwardProjection
          finiteAxisFoldNatPowerSetComplementLocalFiberKernel :=
            projectedComplement.symm
      _ = finiteAxisFoldArbitraryCarrierBackwardAction Nat
          (finiteAxisFoldNatXorMask mask * permutation) := actionEquality
      _ = MulOpposite.op
          (finiteAxisFoldTransportedSourceContextPermutation
            (finiteAxisFoldNatXorMask mask * permutation)⁻¹) := rfl
  exact finiteAxisFoldNatPowerSetComplement_transported_ne_natAction
    (finiteAxisFoldNatXorMask mask * permutation)⁻¹ transportedEquality

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
