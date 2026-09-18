import ResearchLean.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction
import Mathlib.Data.Finset.NoncommProd
import Formal.Util.AssertStandardAxioms

/-!
# Finite multi-carrier reconstruction across the G-122 actual surfaces

A finite family of pairwise unequal primitive Extension carriers acts by a
well-defined commuting product.  This module proves that the product is
faithful and reconstructs it multiplicatively from the actual local-fiber
kernel, stored-backward observations, the canonical expanded direct endpoint,
and the normalized `barAlpha` comparison image.

The finite-family image strictly contains the complete two-carrier image.  A
fixed witness acts simultaneously on `Nat`, `Set Nat`, and `Set (Set Nat)`.

This is not a presentation of the full local-fiber kernel or of every expanded
G-122 Hom.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000

namespace G122FiniteMultiCarrierExpandedReconstruction

universe u w

/-- A finite indexed family of pairwise unequal primitive carriers. -/
structure CarrierFamily where
  Index : Type
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  Carrier : Index → Type
  pairwise_ne : ∀ {i j : Index}, i ≠ j → Carrier i ≠ Carrier j

attribute [instance] CarrierFamily.indexFintype CarrierFamily.indexDecidableEq

/-- Source codes assign one permutation to every carrier in the family. -/
abbrev CarrierFamily.Code (family : CarrierFamily) :=
  ∀ i, Equiv.Perm (family.Carrier i)

/-- Distinct members of a carrier family have commuting source actions. -/
theorem sourceCarrier_commute (family : CarrierFamily)
    {i j : family.Index} (different : i ≠ j)
    (first : Equiv.Perm (family.Carrier i))
    (second : Equiv.Perm (family.Carrier j)) :
    Commute
      (finiteAxisFoldSourceContextObjectPermHom (family.Carrier i) first)
      (finiteAxisFoldSourceContextObjectPermHom (family.Carrier j) second) := by
  exact G122TwoCarrierExpandedReconstruction.sourceContextObjectPerm_commute
    (family.pairwise_ne different) first second

/-- The commuting source product for a finite carrier family. -/
noncomputable def sourceFamilyHom (family : CarrierFamily) :
    family.Code →* Equiv.Perm FiniteAxisFoldSourceContextObject where
  toFun code := Finset.univ.noncommProd
    (fun i => finiteAxisFoldSourceContextObjectPermHom
      (family.Carrier i) (code i))
    (fun i _ j _ different =>
      sourceCarrier_commute family different (code i) (code j))
  map_one' := by
    classical
    rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
    · simp
    · simp
  map_mul' first second := by
    classical
    let firstAction := fun i => finiteAxisFoldSourceContextObjectPermHom
      (family.Carrier i) (first i)
    let secondAction := fun i => finiteAxisFoldSourceContextObjectPermHom
      (family.Carrier i) (second i)
    have firstComm : (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
        (Function.onFun Commute firstAction) := by
      intro i _ j _ different
      exact sourceCarrier_commute family different (first i) (first j)
    have secondComm : (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
        (Function.onFun Commute secondAction) := by
      intro i _ j _ different
      exact sourceCarrier_commute family different (second i) (second j)
    have crossComm : (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
        (fun i j => Commute (secondAction i) (firstAction j)) := by
      intro i _ j _ different
      exact sourceCarrier_commute family different (second i) (first j)
    simpa [firstAction, secondAction, Pi.mul_apply, map_mul] using
      Finset.noncommProd_mul_distrib firstAction secondAction
        firstComm secondComm crossComm

/-- On the canonical probe for one member, the finite source product reads
exactly that member's permutation. -/
theorem sourceFamilyHom_probe (family : CarrierFamily)
    (code : family.Code) (i : family.Index) (value : family.Carrier i) :
    (sourceFamilyHom family code)
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) =
      ⟨finiteAxisFoldSourceExtensionProbe (code i value)⟩ := by
  classical
  let action := fun j => finiteAxisFoldSourceContextObjectPermHom
    (family.Carrier j) (code j)
  have comm : (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
      (Function.onFun Commute action) := by
    intro j _ k _ different
    exact sourceCarrier_commute family different (code j) (code k)
  change
    (Finset.univ.noncommProd action comm)
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) = _
  have erasedFix (probeValue : family.Carrier i) :
      ((Finset.univ.erase i).noncommProd action
        (comm.mono (Finset.coe_subset.2 (Finset.erase_subset i Finset.univ))))
          (⟨finiteAxisFoldSourceExtensionProbe probeValue⟩ :
            FiniteAxisFoldSourceContextObject) =
        ⟨finiteAxisFoldSourceExtensionProbe probeValue⟩ := by
    apply Finset.noncommProd_induction
      (Finset.univ.erase i) action
      (comm.mono (Finset.coe_subset.2 (Finset.erase_subset i Finset.univ)))
      (fun permutation =>
        permutation
            (⟨finiteAxisFoldSourceExtensionProbe probeValue⟩ :
              FiniteAxisFoldSourceContextObject) =
          ⟨finiteAxisFoldSourceExtensionProbe probeValue⟩)
    · intro first second firstFix secondFix
      simp only [Equiv.Perm.mul_apply, secondFix, firstFix]
    · rfl
    · intro j membership
      rw [Finset.mem_erase] at membership
      simp [action, finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation,
        (family.pairwise_ne membership.1).symm]
  rw [← Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i)
    action comm]
  simp only [Equiv.Perm.mul_apply]
  have actionApply :
      action i
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject) =
        ⟨finiteAxisFoldSourceExtensionProbe (code i value)⟩ := by
    simp [action, finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe,
      finiteAxisFoldExtensionValuePermutation]
  rw [actionApply, erasedFix]

/-- Canonical primitive probes separate every finite family code. -/
theorem sourceFamilyHom_injective (family : CarrierFamily) :
    Function.Injective (sourceFamilyHom family) := by
  intro first second equality
  funext i
  apply Equiv.ext
  intro value
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
      permutation
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject)) equality
  change
    sourceFamilyHom family first
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) =
      sourceFamilyHom family second
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) at evaluated
  rw [sourceFamilyHom_probe, sourceFamilyHom_probe] at evaluated
  have extensionSigmaEquality := congrArg
    (fun context : FiniteAxisFoldSourceContextObject =>
      (⟨context.ctx.Extension, context.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier)) evaluated
  exact eq_of_heq (Sigma.mk.inj_iff.mp extensionSigmaEquality).2

/-- Distinct carrier sections commute in the actual local-fiber kernel. -/
theorem kernelCarrier_commute (family : CarrierFamily)
    {i j : family.Index} (different : i ≠ j)
    (first : Equiv.Perm (family.Carrier i))
    (second : Equiv.Perm (family.Carrier j)) :
    Commute
      (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom
        (family.Carrier i) first)
      (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom
        (family.Carrier j) second) := by
  exact G122TwoCarrierExpandedReconstruction.localFiberKernelSection_commute
    (family.pairwise_ne different) first second

/-- The commuting actual-kernel product of a finite carrier family. -/
noncomputable def familyKernelHom (family : CarrierFamily) :
    family.Code →* FiniteAxisFoldResidualLocalFiberKernel where
  toFun code := Finset.univ.noncommProd
    (fun i => finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom
      (family.Carrier i) (code i))
    (fun i _ j _ different =>
      kernelCarrier_commute family different (code i) (code j))
  map_one' := by
    classical
    rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
    · simp
    · simp
  map_mul' first second := by
    classical
    let firstAction := fun i =>
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom
        (family.Carrier i) (first i)
    let secondAction := fun i =>
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom
        (family.Carrier i) (second i)
    have firstComm :
        (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
          (Function.onFun Commute firstAction) := by
      intro i _ j _ different
      exact kernelCarrier_commute family different (first i) (first j)
    have secondComm :
        (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
          (Function.onFun Commute secondAction) := by
      intro i _ j _ different
      exact kernelCarrier_commute family different (second i) (second j)
    have crossComm :
        (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
          (fun i j => Commute (secondAction i) (firstAction j)) := by
      intro i _ j _ different
      exact kernelCarrier_commute family different (second i) (first j)
    simpa [firstAction, secondAction, Pi.mul_apply, map_mul] using
      Finset.noncommProd_mul_distrib firstAction secondAction
        firstComm secondComm crossComm

/-- The opposite stored-backward convention is turned back into the forward
transported action by unop and inversion. -/
noncomputable def oppositeInverseHom (G : Type w) [Group G] : Gᵐᵒᵖ →* G where
  toFun value := value.unop⁻¹
  map_one' := by simp
  map_mul' first second := by simp [mul_inv_rev]

/-- Read an actual local-fiber kernel element back as its forward residual
context action. -/
noncomputable def kernelSourceRecoveryHom :
    FiniteAxisFoldResidualLocalFiberKernel →*
      Equiv.Perm FiniteAxisFoldResidualContextObject :=
  (oppositeInverseHom
    (Equiv.Perm FiniteAxisFoldResidualContextObject)).comp
      finiteAxisFoldResidualLocalFiberKernelBackwardProjection

/-- Recovery of the finite actual product is exactly fixed transport of the
finite source product. -/
theorem familyKernelHom_recovery (family : CarrierFamily)
    (code : family.Code) :
    kernelSourceRecoveryHom (familyKernelHom family code) =
      G122ParametricCarrierDisplayedBundle.transportSourceActionHom
        (sourceFamilyHom family code) := by
  classical
  let kernelAction := fun i =>
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom
      (family.Carrier i) (code i)
  have kernelComm :
      (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
        (Function.onFun Commute kernelAction) := by
    intro i _ j _ different
    exact kernelCarrier_commute family different (code i) (code j)
  let sourceAction := fun i =>
    finiteAxisFoldSourceContextObjectPermHom (family.Carrier i) (code i)
  have sourceComm :
      (↑(Finset.univ : Finset family.Index) : Set family.Index).Pairwise
        (Function.onFun Commute sourceAction) := by
    intro i _ j _ different
    exact sourceCarrier_commute family different (code i) (code j)
  change
    kernelSourceRecoveryHom
        (Finset.univ.noncommProd kernelAction kernelComm) =
      G122ParametricCarrierDisplayedBundle.transportSourceActionHom
        (Finset.univ.noncommProd sourceAction sourceComm)
  rw [Finset.map_noncommProd, Finset.map_noncommProd]
  apply Finset.noncommProd_congr rfl
  intro i _
  dsimp [kernelAction, sourceAction, kernelSourceRecoveryHom,
    oppositeInverseHom]
  rw [finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection]
  rw [G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier]
  apply Equiv.ext
  intro context
  rfl

/-- The actual finite-family kernel representation is faithful. -/
theorem familyKernelHom_injective (family : CarrierFamily) :
    Function.Injective (familyKernelHom family) := by
  intro first second equality
  apply sourceFamilyHom_injective family
  apply G122ParametricCarrierDisplayedBundle.transportSourceActionHom_injective
  rw [← familyKernelHom_recovery, ← familyKernelHom_recovery, equality]

/-- The actual finite-family kernel image. -/
noncomputable def FamilyKernelImage (family : CarrierFamily) :
    Subgroup FiniteAxisFoldResidualLocalFiberKernel :=
  MonoidHom.range (familyKernelHom family)

/-- Finite source families reconstruct their actual kernel range
multiplicatively. -/
noncomputable def sourceFamilyKernelMulEquiv (family : CarrierFamily) :
    family.Code ≃* FamilyKernelImage family :=
  G122TwoCarrierExpandedReconstruction.rangeMulEquivOfInjective
    (familyKernelHom family) (familyKernelHom_injective family)

/-- Stored-backward observation restricted to a finite-family image. -/
noncomputable def familyBackwardObservationHom (family : CarrierFamily) :
    FamilyKernelImage family →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldResidualLocalFiberKernelBackwardProjection.comp
    (FamilyKernelImage family).subtype

/-- Stored-backward observations separate the actual finite-family image. -/
theorem familyBackwardObservationHom_injective (family : CarrierFamily) :
    Function.Injective (familyBackwardObservationHom family) := by
  intro first second equality
  apply Subtype.ext
  exact finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
    equality

/-- Stored-backward observation range of a finite-family image. -/
noncomputable def FamilyObservedImage (family : CarrierFamily) :
    Subgroup (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  MonoidHom.range (familyBackwardObservationHom family)

/-- The actual finite-family image reconstructs from stored-backward
observations multiplicatively. -/
noncomputable def familyKernelObservedMulEquiv (family : CarrierFamily) :
    FamilyKernelImage family ≃* FamilyObservedImage family :=
  G122TwoCarrierExpandedReconstruction.rangeMulEquivOfInjective
    (familyBackwardObservationHom family)
    (familyBackwardObservationHom_injective family)

/-- Source families reconstruct the stored-backward observation range. -/
noncomputable def sourceFamilyObservedMulEquiv (family : CarrierFamily) :
    family.Code ≃* FamilyObservedImage family :=
  (sourceFamilyKernelMulEquiv family).trans
    (familyKernelObservedMulEquiv family)

/-- Forget the kernel predicates and retain the normalized direct
automorphism. -/
noncomputable def familyNormalizedDirectHom (family : CarrierFamily) :
    family.Code →* Aut FiniteAxisFoldNormalizedDirectGeometry where
  toFun code := (familyKernelHom family code).1.1.1.1
  map_one' := congrArg
    (fun value : FiniteAxisFoldResidualLocalFiberKernel => value.1.1.1.1)
    (map_one (familyKernelHom family))
  map_mul' first second := congrArg
    (fun value : FiniteAxisFoldResidualLocalFiberKernel => value.1.1.1.1)
    (map_mul (familyKernelHom family) first second)

/-- Forgetting the kernel predicates preserves finite-family separation. -/
theorem familyNormalizedDirectHom_injective (family : CarrierFamily) :
    Function.Injective (familyNormalizedDirectHom family) := by
  intro first second equality
  apply familyKernelHom_injective family
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact equality

/-- Carry a finite-family image through the canonical normalization section. -/
noncomputable def familyExpandedDirectHom (family : CarrierFamily) :
    family.Code →* Aut finiteAxisFoldActualDirectAdmissibleGeometry :=
  (canonicalNormalizationAutomorphismSectionHom
      finiteAxisFoldActualDirectAdmissibleGeometry).comp
    (familyNormalizedDirectHom family)

/-- The canonical expanded lift preserves finite-family separation. -/
theorem familyExpandedDirectHom_injective (family : CarrierFamily) :
    Function.Injective (familyExpandedDirectHom family) := by
  intro first second equality
  apply familyNormalizedDirectHom_injective family
  have normalized := congrArg
    (RealizationComparisonIdempotents.functorAutomorphismHom
      (geometryNormalizationFunctor FiniteModel.carrier)
      finiteAxisFoldActualDirectAdmissibleGeometry) equality
  change
    RealizationComparisonIdempotents.functorAutomorphismHom
        (geometryNormalizationFunctor FiniteModel.carrier)
        finiteAxisFoldActualDirectAdmissibleGeometry
        (canonicalNormalizationAutomorphismSectionHom
          finiteAxisFoldActualDirectAdmissibleGeometry
          (familyNormalizedDirectHom family first)) =
      RealizationComparisonIdempotents.functorAutomorphismHom
        (geometryNormalizationFunctor FiniteModel.carrier)
        finiteAxisFoldActualDirectAdmissibleGeometry
        (canonicalNormalizationAutomorphismSectionHom
          finiteAxisFoldActualDirectAdmissibleGeometry
          (familyNormalizedDirectHom family second)) at normalized
  rw [canonicalNormalizationAutomorphismSection_rightInverse,
    canonicalNormalizationAutomorphismSection_rightInverse] at normalized
  exact normalized

/-- Expanded direct-endpoint range of a finite-family image. -/
noncomputable def FamilyExpandedDirectImage (family : CarrierFamily) :
    Subgroup (Aut finiteAxisFoldActualDirectAdmissibleGeometry) :=
  MonoidHom.range (familyExpandedDirectHom family)

/-- Source families reconstruct the canonical expanded direct range. -/
noncomputable def sourceFamilyExpandedDirectMulEquiv (family : CarrierFamily) :
    family.Code ≃* FamilyExpandedDirectImage family :=
  G122TwoCarrierExpandedReconstruction.rangeMulEquivOfInjective
    (familyExpandedDirectHom family)
    (familyExpandedDirectHom_injective family)

/-- Carry the same finite source family through the normalized `barAlpha`
comparison section. -/
noncomputable def familyComparisonHom (family : CarrierFamily) :
    family.Code →*
      GeneratedArrowComparisonSubgroup finiteAxisFoldNormalizedBarAlphaIso.hom :=
  (generatedArrowComparisonSectionHom
      finiteAxisFoldNormalizedBarAlphaIso).comp
    (familyNormalizedDirectHom family)

/-- The comparison source projection preserves finite-family separation. -/
theorem familyComparisonHom_injective (family : CarrierFamily) :
    Function.Injective (familyComparisonHom family) := by
  intro first second equality
  apply familyNormalizedDirectHom_injective family
  exact congrArg
    (generatedArrowComparisonSourceHom
      finiteAxisFoldNormalizedBarAlphaIso.hom) equality

/-- Normalized comparison range of a finite-family image. -/
noncomputable def FamilyComparisonImage (family : CarrierFamily) :
    Subgroup
      (GeneratedArrowComparisonSubgroup
        finiteAxisFoldNormalizedBarAlphaIso.hom) :=
  MonoidHom.range (familyComparisonHom family)

/-- Source families reconstruct the normalized comparison range. -/
noncomputable def sourceFamilyComparisonMulEquiv (family : CarrierFamily) :
    family.Code ≃* FamilyComparisonImage family :=
  G122TwoCarrierExpandedReconstruction.rangeMulEquivOfInjective
    (familyComparisonHom family)
    (familyComparisonHom_injective family)

/-- Recovery through the stored-backward projection is faithful on the whole
actual kernel. -/
theorem kernelSourceRecoveryHom_injective :
    Function.Injective kernelSourceRecoveryHom := by
  intro first second equality
  apply finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
  apply MulOpposite.unop_injective
  apply inv_injective
  exact equality

/-- The recovery map sends a two-carrier product to fixed transport of its
source product. -/
theorem pairKernelHom_recovery
    {E F : Type} (different : E ≠ F)
    (code : Equiv.Perm E × Equiv.Perm F) :
    kernelSourceRecoveryHom
        (G122TwoCarrierExpandedReconstruction.pairKernelHom
          E F different code) =
      G122ParametricCarrierDisplayedBundle.transportSourceActionHom
        (G122TwoCarrierExpandedReconstruction.sourcePairHom
          E F different code) := by
  dsimp [kernelSourceRecoveryHom, oppositeInverseHom]
  rw [G122TwoCarrierExpandedReconstruction.pairKernelHom_backwardProjection]
  change
    (finiteAxisFoldTransportedSourceContextPermutation code.2⁻¹ *
      finiteAxisFoldTransportedSourceContextPermutation code.1⁻¹)⁻¹ = _
  rw [mul_inv_rev]
  change
    (finiteAxisFoldTransportedSourceContextPermutation code.1⁻¹)⁻¹ *
        (finiteAxisFoldTransportedSourceContextPermutation code.2⁻¹)⁻¹ =
      G122ParametricCarrierDisplayedBundle.transportSourceActionHom
        (finiteAxisFoldSourceContextObjectPermHom E code.1 *
          finiteAxisFoldSourceContextObjectPermHom F code.2)
  rw [map_mul,
    G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier,
    G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier]
  rfl

/-- The two-member family used to embed every accepted two-carrier product. -/
def binaryFamily (E F : Type) (different : E ≠ F) : CarrierFamily where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Carrier
    | false => E
    | true => F
  pairwise_ne := by
    intro i j inequality
    cases i <;> cases j
    · exact (inequality rfl).elim
    · exact different
    · exact different.symm
    · exact (inequality rfl).elim

/-- Regard a pair code as a code for its two-member family. -/
def binaryCode {E F : Type} (different : E ≠ F)
    (code : Equiv.Perm E × Equiv.Perm F) :
    (binaryFamily E F different).Code
  | false => code.1
  | true => code.2

/-- The finite-family source product specializes to the accepted pair source
product. -/
theorem binary_sourceFamilyHom
    {E F : Type} (different : E ≠ F)
    (code : Equiv.Perm E × Equiv.Perm F) :
    sourceFamilyHom (binaryFamily E F different) (binaryCode different code) =
      G122TwoCarrierExpandedReconstruction.sourcePairHom
        E F different code := by
  classical
  let action := fun i : Bool => finiteAxisFoldSourceContextObjectPermHom
    ((binaryFamily E F different).Carrier i) (binaryCode different code i)
  have comm :
      (↑(Finset.univ : Finset Bool) : Set Bool).Pairwise
        (Function.onFun Commute action) := by
    intro i _ j _ inequality
    exact sourceCarrier_commute (binaryFamily E F different) inequality
      (binaryCode different code i) (binaryCode different code j)
  change Finset.univ.noncommProd action comm = _
  let pairSet : Finset Bool := insert false {true}
  have univEquality : (Finset.univ : Finset Bool) = pairSet := by
    ext i
    cases i <;> simp [pairSet]
  calc
    Finset.univ.noncommProd action comm =
        pairSet.noncommProd action
          (fun i hi j hj inequality => by
            exact comm (by simpa [univEquality] using hi)
              (by simpa [univEquality] using hj) inequality) :=
      Finset.noncommProd_congr univEquality
        (fun _ _ => rfl) comm
    _ = _ := by
      dsimp [pairSet]
      rw [Finset.noncommProd_insert_of_notMem {true} false action _ (by simp)]
      simp [action, binaryFamily, binaryCode,
        G122TwoCarrierExpandedReconstruction.sourcePairHom]

/-- The finite-family actual product specializes to the accepted pair actual
product. -/
theorem binary_familyKernelHom
    {E F : Type} (different : E ≠ F)
    (code : Equiv.Perm E × Equiv.Perm F) :
    familyKernelHom (binaryFamily E F different) (binaryCode different code) =
      G122TwoCarrierExpandedReconstruction.pairKernelHom
        E F different code := by
  apply kernelSourceRecoveryHom_injective
  rw [familyKernelHom_recovery, pairKernelHom_recovery,
    binary_sourceFamilyHom]

/-- Union of all actual images represented by finite pairwise unequal carrier
families. -/
def FiniteCarrierImage
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) : Prop :=
  ∃ family : CarrierFamily, ∃ code : family.Code,
    familyKernelHom family code = remainder

/-- Every two-carrier image belongs to the coherent finite-family image. -/
theorem twoCarrierImage_subset_finiteCarrierImage :
    {remainder |
      G122TwoCarrierExpandedReconstruction.TwoCarrierImage remainder} ⊆
      {remainder | FiniteCarrierImage remainder} := by
  intro remainder membership
  rcases membership with ⟨E, F, different, code, rfl⟩
  exact ⟨binaryFamily E F different, binaryCode different code,
    binary_familyKernelHom different code⟩

/-- Two powerset iterations cannot return to the original type. -/
theorem type_ne_powerSet_powerSet (E : Type) : E ≠ Set (Set E) := by
  intro equality
  have cardinalEquality : Cardinal.mk E = Cardinal.mk (Set (Set E)) :=
    congrArg Cardinal.mk equality
  have firstStrict : Cardinal.mk E < Cardinal.mk (Set E) := by
    simpa only [Cardinal.mk_set] using Cardinal.cantor (Cardinal.mk E)
  have secondStrict : Cardinal.mk (Set E) < Cardinal.mk (Set (Set E)) := by
    simpa only [Cardinal.mk_set] using Cardinal.cantor (Cardinal.mk (Set E))
  have totalStrict := firstStrict.trans secondStrict
  rw [← cardinalEquality] at totalStrict
  exact (lt_irrefl (Cardinal.mk E)) totalStrict

/-- Three fixed pairwise unequal carrier types. -/
def tripleFamily : CarrierFamily where
  Index := Fin 1 ⊕ Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Carrier
    | Sum.inl _ => Nat
    | Sum.inr false => Set Nat
    | Sum.inr true => Set (Set Nat)
  pairwise_ne := by
    intro i j inequality
    rcases i with i | i <;> rcases j with j | j
    · exact (inequality
        (congrArg Sum.inl (Subsingleton.elim i j))).elim
    · cases i
      cases j
      · exact G122TwoCarrierExpandedReconstruction.type_ne_powerSet Nat
      · exact type_ne_powerSet_powerSet Nat
    · cases j
      cases i
      · exact (G122TwoCarrierExpandedReconstruction.type_ne_powerSet Nat).symm
      · exact (type_ne_powerSet_powerSet Nat).symm
    · cases i
      · cases j
        · exact (inequality rfl).elim
        · exact G122TwoCarrierExpandedReconstruction.type_ne_powerSet (Set Nat)
      · cases j
        · exact (G122TwoCarrierExpandedReconstruction.type_ne_powerSet
            (Set Nat)).symm
        · exact (inequality rfl).elim

/-- Complement on an arbitrary powerset carrier. -/
def powerSetComplement (E : Type) : Equiv.Perm (Set E) where
  toFun subset := subsetᶜ
  invFun subset := subsetᶜ
  left_inv subset := by simp
  right_inv subset := by simp

/-- The fixed three-carrier source code: Nat swap and complements on the first
and second powersets. -/
noncomputable def tripleCode : tripleFamily.Code
  | Sum.inl _ => finiteAxisFoldNatZeroOneSwap
  | Sum.inr false => finiteAxisFoldNatPowerSetComplement
  | Sum.inr true => powerSetComplement (Set Nat)

/-- The fixed simultaneous three-carrier actual-kernel witness. -/
noncomputable def tripleKernel :
    FiniteAxisFoldResidualLocalFiberKernel :=
  familyKernelHom tripleFamily tripleCode

/-- A fresh moved carrier in a finite family prevents equality with any
two-carrier source product. -/
theorem sourceFamilyHom_ne_pair_of_fresh
    (family : CarrierFamily) (code : family.Code)
    (i : family.Index) (value : family.Carrier i)
    (moves : code i value ≠ value)
    {E F : Type} (different : E ≠ F)
    (pair : Equiv.Perm E × Equiv.Perm F)
    (freshE : family.Carrier i ≠ E)
    (freshF : family.Carrier i ≠ F) :
    sourceFamilyHom family code ≠
      G122TwoCarrierExpandedReconstruction.sourcePairHom
        E F different pair := by
  intro equality
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
      permutation
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject)) equality
  change
    sourceFamilyHom family code
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) = _ at evaluated
  rw [sourceFamilyHom_probe] at evaluated
  have extensionSigmaEquality := congrArg
    (fun context : FiniteAxisFoldSourceContextObject =>
      (⟨context.ctx.Extension, context.ctx.extension⟩ :
        Sigma fun carrier : Type => carrier)) evaluated
  have fixed : code i value = value := by
    simpa [G122TwoCarrierExpandedReconstruction.sourcePairHom,
      finiteAxisFoldSourceContextObjectPermHom,
      finiteAxisFoldSourceContextObjectPerm,
      finiteAxisFoldSourceContextObjectPermutation,
      finiteAxisFoldSourceContextPermutation,
      finiteAxisFoldSourceExtensionProbe,
      finiteAxisFoldExtensionValuePermutation, freshE, freshF,
      Ne.symm freshE, Ne.symm freshF] using extensionSigmaEquality
  exact moves fixed

/-- Complement moves the empty subset whenever the underlying carrier is
inhabited. -/
theorem powerSetComplement_empty_ne (E : Type) [Nonempty E] :
    powerSetComplement E (∅ : Set E) ≠ ∅ := by
  intro equality
  let point : E := Classical.choice (inferInstance : Nonempty E)
  have pointEquality := Set.ext_iff.mp equality point
  simp [powerSetComplement] at pointEquality

/-- The fixed three-carrier source product cannot be represented by any
two-carrier source product. -/
theorem triple_sourceFamilyHom_ne_pair
    {E F : Type} (different : E ≠ F)
    (pair : Equiv.Perm E × Equiv.Perm F) :
    sourceFamilyHom tripleFamily tripleCode ≠
      G122TwoCarrierExpandedReconstruction.sourcePairHom
        E F different pair := by
  classical
  by_cases eNat : E = Nat
  · subst E
    by_cases fSet : F = Set Nat
    · subst F
      exact sourceFamilyHom_ne_pair_of_fresh
        tripleFamily tripleCode (Sum.inr true) (∅ : Set (Set Nat))
        (powerSetComplement_empty_ne (Set Nat)) different pair
        (type_ne_powerSet_powerSet Nat).symm
        (G122TwoCarrierExpandedReconstruction.type_ne_powerSet
          (Set Nat)).symm
    · exact sourceFamilyHom_ne_pair_of_fresh
        tripleFamily tripleCode (Sum.inr false) (∅ : Set Nat)
        (finiteAxisFoldNatPowerSetComplement_ne ∅) different pair
        (G122TwoCarrierExpandedReconstruction.type_ne_powerSet Nat).symm
        (fun equality => fSet equality.symm)
  · by_cases fNat : F = Nat
    · subst F
      by_cases eSet : E = Set Nat
      · subst E
        exact sourceFamilyHom_ne_pair_of_fresh
          tripleFamily tripleCode (Sum.inr true) (∅ : Set (Set Nat))
          (powerSetComplement_empty_ne (Set Nat)) different pair
          (G122TwoCarrierExpandedReconstruction.type_ne_powerSet
            (Set Nat)).symm
          (type_ne_powerSet_powerSet Nat).symm
      · exact sourceFamilyHom_ne_pair_of_fresh
          tripleFamily tripleCode (Sum.inr false) (∅ : Set Nat)
          (finiteAxisFoldNatPowerSetComplement_ne ∅) different pair
          (fun equality : Set Nat = E => eSet equality.symm)
          (G122TwoCarrierExpandedReconstruction.type_ne_powerSet Nat).symm
    · exact sourceFamilyHom_ne_pair_of_fresh
        tripleFamily tripleCode (Sum.inl (0 : Fin 1))
        (show tripleFamily.Carrier (Sum.inl (0 : Fin 1)) from (0 : Nat))
        (by simp [tripleFamily, tripleCode, finiteAxisFoldNatZeroOneSwap])
        different pair
        (fun equality : Nat = E => eNat equality.symm)
        (fun equality : Nat = F => fNat equality.symm)

/-- The fixed triple witness belongs to the finite-family image. -/
theorem tripleKernel_mem_finiteCarrierImage :
    FiniteCarrierImage tripleKernel :=
  ⟨tripleFamily, tripleCode, rfl⟩

/-- The fixed triple witness lies outside every two-carrier image. -/
theorem tripleKernel_not_twoCarrierImage :
    ¬ G122TwoCarrierExpandedReconstruction.TwoCarrierImage tripleKernel := by
  rintro ⟨E, F, different, pair, equality⟩
  apply triple_sourceFamilyHom_ne_pair different pair
  apply G122ParametricCarrierDisplayedBundle.transportSourceActionHom_injective
  rw [← familyKernelHom_recovery tripleFamily tripleCode,
    ← pairKernelHom_recovery different pair]
  exact congrArg kernelSourceRecoveryHom equality.symm

/-- Coherent finite-family products strictly enlarge the complete two-carrier
family. -/
theorem twoCarrierImage_ssubset_finiteCarrierImage :
    {remainder |
      G122TwoCarrierExpandedReconstruction.TwoCarrierImage remainder} ⊂
      {remainder | FiniteCarrierImage remainder} := by
  refine ⟨twoCarrierImage_subset_finiteCarrierImage, ?_⟩
  intro reverseInclusion
  exact tripleKernel_not_twoCarrierImage
    (reverseInclusion tripleKernel_mem_finiteCarrierImage)

/-- One theorem packages the substantive finite-family result: source
separation, actual recovery, four multiplicative surfaces, and strict progress
beyond all pairs. -/
theorem finite_family_reconstruction_and_strict_progress :
    (∀ family : CarrierFamily,
      Function.Injective (familyKernelHom family)) ∧
    (∀ family : CarrierFamily,
      Nonempty (family.Code ≃* FamilyKernelImage family)) ∧
    (∀ family : CarrierFamily,
      Nonempty (family.Code ≃* FamilyObservedImage family)) ∧
    (∀ family : CarrierFamily,
      Nonempty (family.Code ≃* FamilyExpandedDirectImage family)) ∧
    (∀ family : CarrierFamily,
      Nonempty (family.Code ≃* FamilyComparisonImage family)) ∧
    {remainder |
      G122TwoCarrierExpandedReconstruction.TwoCarrierImage remainder} ⊂
      {remainder | FiniteCarrierImage remainder} := by
  exact ⟨familyKernelHom_injective,
    fun family => ⟨sourceFamilyKernelMulEquiv family⟩,
    fun family => ⟨sourceFamilyObservedMulEquiv family⟩,
    fun family => ⟨sourceFamilyExpandedDirectMulEquiv family⟩,
    fun family => ⟨sourceFamilyComparisonMulEquiv family⟩,
    twoCarrierImage_ssubset_finiteCarrierImage⟩

end G122FiniteMultiCarrierExpandedReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction

end

end AAT.AG.LocalSemanticReconstruction
