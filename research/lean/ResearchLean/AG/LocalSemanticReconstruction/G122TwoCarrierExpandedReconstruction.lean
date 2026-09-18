import ResearchLean.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Two-carrier reconstruction across the G-122 actual surfaces

Two distinct primitive Extension carriers act independently.  This module
proves that their actions commute before transport, after transport, and in
the actual local-fiber kernel.  Their product is faithful and is reconstructed
multiplicatively from its kernel image, stored-backward observation, canonical
expanded direct-endpoint lift, and normalized `barAlpha` comparison image.

The existential two-carrier family properly contains the complete
single-carrier family.  The strict witness acts simultaneously by the Nat
zero-one swap and the `Set Nat` complement, so no action supported on one
primitive carrier can represent it.

This is not a presentation of the full local-fiber kernel or of all expanded
G-122 Homs.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000

namespace G122TwoCarrierExpandedReconstruction

universe u v

/-- Actions supported on unequal Extension carriers commute pointwise. -/
theorem extensionValuePermutation_commute
    {E F alpha : Type} (different : E ≠ F)
    (first : Equiv.Perm E) (second : Equiv.Perm F) (value : alpha) :
    finiteAxisFoldExtensionValuePermutation first
        (finiteAxisFoldExtensionValuePermutation second value) =
      finiteAxisFoldExtensionValuePermutation second
        (finiteAxisFoldExtensionValuePermutation first value) := by
  classical
  by_cases alphaE : alpha = E
  · subst alpha
    simp [finiteAxisFoldExtensionValuePermutation, different]
  · by_cases alphaF : alpha = F
    · subst alpha
      simp [finiteAxisFoldExtensionValuePermutation, alphaE]
    · simp [finiteAxisFoldExtensionValuePermutation, alphaE, alphaF]

/-- Unequal-carrier actions commute on complete source contexts. -/
theorem sourceContextPermutation_commute
    {E F : Type} (different : E ≠ F)
    (first : Equiv.Perm E) (second : Equiv.Perm F)
    (context : Site.ArchCtx finiteAxisFoldSourceGeometryPackage.core.object) :
    finiteAxisFoldSourceContextPermutation first
        (finiteAxisFoldSourceContextPermutation second context) =
      finiteAxisFoldSourceContextPermutation second
        (finiteAxisFoldSourceContextPermutation first context) := by
  rcases context with ⟨minimal, Extension, extension⟩
  simp only [finiteAxisFoldSourceContextPermutation]
  congr 1
  exact extensionValuePermutation_commute different first second extension

/-- Unequal-carrier actions commute on the full source context-object type. -/
theorem sourceContextObjectPerm_commute
    {E F : Type} (different : E ≠ F)
    (first : Equiv.Perm E) (second : Equiv.Perm F) :
    finiteAxisFoldSourceContextObjectPermHom E first *
        finiteAxisFoldSourceContextObjectPermHom F second =
      finiteAxisFoldSourceContextObjectPermHom F second *
        finiteAxisFoldSourceContextObjectPermHom E first := by
  apply Equiv.ext
  intro context
  change finiteAxisFoldSourceContextObjectPermutation first
      (finiteAxisFoldSourceContextObjectPermutation second context) =
    finiteAxisFoldSourceContextObjectPermutation second
      (finiteAxisFoldSourceContextObjectPermutation first context)
  rcases context with ⟨context⟩
  change (⟨finiteAxisFoldSourceContextPermutation first
      (finiteAxisFoldSourceContextPermutation second context)⟩ :
        FiniteAxisFoldSourceContextObject) =
    (⟨finiteAxisFoldSourceContextPermutation second
      (finiteAxisFoldSourceContextPermutation first context)⟩ :
        FiniteAxisFoldSourceContextObject)
  exact context_object_eq_of_ctx_eq
    (sourceContextPermutation_commute different first second context)

/-- Fixed-route transport preserves unequal-carrier commutativity. -/
theorem transportedSourceContextPermutation_commute
    {E F : Type} (different : E ≠ F)
    (first : Equiv.Perm E) (second : Equiv.Perm F) :
    finiteAxisFoldTransportedSourceContextPermutation first *
        finiteAxisFoldTransportedSourceContextPermutation second =
      finiteAxisFoldTransportedSourceContextPermutation second *
        finiteAxisFoldTransportedSourceContextPermutation first := by
  calc
    _ = G122ParametricCarrierDisplayedBundle.transportSourceActionHom
          (finiteAxisFoldSourceContextObjectPermHom E first) *
        G122ParametricCarrierDisplayedBundle.transportSourceActionHom
          (finiteAxisFoldSourceContextObjectPermHom F second) := by
            rw [G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier,
              G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier]
    _ = G122ParametricCarrierDisplayedBundle.transportSourceActionHom
          (finiteAxisFoldSourceContextObjectPermHom E first *
            finiteAxisFoldSourceContextObjectPermHom F second) := by
          rw [map_mul]
    _ = G122ParametricCarrierDisplayedBundle.transportSourceActionHom
          (finiteAxisFoldSourceContextObjectPermHom F second *
            finiteAxisFoldSourceContextObjectPermHom E first) :=
          congrArg G122ParametricCarrierDisplayedBundle.transportSourceActionHom
            (sourceContextObjectPerm_commute different first second)
    _ = G122ParametricCarrierDisplayedBundle.transportSourceActionHom
          (finiteAxisFoldSourceContextObjectPermHom F second) *
        G122ParametricCarrierDisplayedBundle.transportSourceActionHom
          (finiteAxisFoldSourceContextObjectPermHom E first) := by
          rw [map_mul]
    _ = _ := by
      rw [G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier,
        G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier]

/-- Unequal-carrier sections commute inside the actual local-fiber kernel. -/
theorem localFiberKernelSection_commute
    {E F : Type} (different : E ≠ F)
    (first : Equiv.Perm E) (second : Equiv.Perm F) :
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E first *
        finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F second =
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F second *
        finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E first := by
  apply finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
  rw [map_mul, map_mul,
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection,
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection]
  change MulOpposite.op
      (finiteAxisFoldTransportedSourceContextPermutation second⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation first⁻¹) =
    MulOpposite.op
      (finiteAxisFoldTransportedSourceContextPermutation first⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation second⁻¹)
  exact congrArg MulOpposite.op
    (transportedSourceContextPermutation_commute different first⁻¹ second⁻¹).symm

/-- Product of two independent carrier-permutation groups in the actual
local-fiber kernel. -/
noncomputable def pairKernelHom (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) →*
      FiniteAxisFoldResidualLocalFiberKernel where
  toFun code :=
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E code.1 *
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F code.2
  map_one' := by simp
  map_mul' first second := by
    change
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E
            (first.1 * second.1) *
          finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F
            (first.2 * second.2) =
        (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E first.1 *
            finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F first.2) *
          (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E second.1 *
            finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F second.2)
    rw [map_mul, map_mul]
    calc
      _ = finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E first.1 *
          (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E second.1 *
            finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F first.2) *
          finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F second.2 := by
            simp only [mul_assoc]
      _ = finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E first.1 *
          (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F first.2 *
            finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E second.1) *
          finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F second.2 := by
            rw [localFiberKernelSection_commute different second.1 first.2]
      _ = _ := by simp only [mul_assoc]

/-- Backward observation of the pair is the product of the two independently
transported inverse actions. -/
theorem pairKernelHom_backwardProjection
    {E F : Type} (different : E ≠ F)
    (code : Equiv.Perm E × Equiv.Perm F) :
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        (pairKernelHom E F different code) =
      MulOpposite.op
        (finiteAxisFoldTransportedSourceContextPermutation code.2⁻¹ *
          finiteAxisFoldTransportedSourceContextPermutation code.1⁻¹) := by
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E code.1 *
        finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom F code.2) = _
  rw [map_mul,
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection,
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection]
  rfl

/-- The product action on the primitive source context-object carrier. -/
noncomputable def sourcePairHom (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) →*
      Equiv.Perm FiniteAxisFoldSourceContextObject where
  toFun code :=
    finiteAxisFoldSourceContextObjectPermHom E code.1 *
      finiteAxisFoldSourceContextObjectPermHom F code.2
  map_one' := by simp
  map_mul' first second := by
    change
      finiteAxisFoldSourceContextObjectPermHom E (first.1 * second.1) *
          finiteAxisFoldSourceContextObjectPermHom F (first.2 * second.2) =
        (finiteAxisFoldSourceContextObjectPermHom E first.1 *
            finiteAxisFoldSourceContextObjectPermHom F first.2) *
          (finiteAxisFoldSourceContextObjectPermHom E second.1 *
            finiteAxisFoldSourceContextObjectPermHom F second.2)
    rw [map_mul, map_mul]
    calc
      _ = finiteAxisFoldSourceContextObjectPermHom E first.1 *
          (finiteAxisFoldSourceContextObjectPermHom E second.1 *
            finiteAxisFoldSourceContextObjectPermHom F first.2) *
          finiteAxisFoldSourceContextObjectPermHom F second.2 := by
            simp only [mul_assoc]
      _ = finiteAxisFoldSourceContextObjectPermHom E first.1 *
          (finiteAxisFoldSourceContextObjectPermHom F first.2 *
            finiteAxisFoldSourceContextObjectPermHom E second.1) *
          finiteAxisFoldSourceContextObjectPermHom F second.2 := by
            rw [sourceContextObjectPerm_commute different second.1 first.2]
      _ = _ := by simp only [mul_assoc]

/-- Primitive probes on the two carrier types separate every pair code. -/
theorem sourcePairHom_injective
    {E F : Type} (different : E ≠ F) :
    Function.Injective (sourcePairHom E F different) := by
  intro first second equality
  apply Prod.ext
  · apply Equiv.ext
    intro value
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
        permutation
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject)) equality
    have extensionSigmaEquality := congrArg
      (fun context : FiniteAxisFoldSourceContextObject =>
        (⟨context.ctx.Extension, context.ctx.extension⟩ :
          Sigma fun carrier : Type => carrier)) evaluated
    have probeEquality :
        (⟨E, first.1 value⟩ : Sigma fun carrier : Type => carrier) =
          ⟨E, second.1 value⟩ := by
      simpa [sourcePairHom, finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation, different, different.symm] using
          extensionSigmaEquality
    exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2
  · apply Equiv.ext
    intro value
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
        permutation
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject)) equality
    have extensionSigmaEquality := congrArg
      (fun context : FiniteAxisFoldSourceContextObject =>
        (⟨context.ctx.Extension, context.ctx.extension⟩ :
          Sigma fun carrier : Type => carrier)) evaluated
    have probeEquality :
        (⟨F, first.2 value⟩ : Sigma fun carrier : Type => carrier) =
          ⟨F, second.2 value⟩ := by
      simpa [sourcePairHom, finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation, different, different.symm] using
          extensionSigmaEquality
    exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2

/-- The two-carrier actual kernel representation is faithful. -/
theorem pairKernelHom_injective
    {E F : Type} (different : E ≠ F) :
    Function.Injective (pairKernelHom E F different) := by
  intro first second equality
  have projected := congrArg
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection equality
  rw [pairKernelHom_backwardProjection, pairKernelHom_backwardProjection]
      at projected
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation first.2⁻¹ *
          finiteAxisFoldTransportedSourceContextPermutation first.1⁻¹ =
        finiteAxisFoldTransportedSourceContextPermutation second.2⁻¹ *
          finiteAxisFoldTransportedSourceContextPermutation second.1⁻¹ :=
    MulOpposite.op_injective projected
  have sourceEquality :
      finiteAxisFoldSourceContextObjectPermHom F first.2⁻¹ *
          finiteAxisFoldSourceContextObjectPermHom E first.1⁻¹ =
        finiteAxisFoldSourceContextObjectPermHom F second.2⁻¹ *
          finiteAxisFoldSourceContextObjectPermHom E second.1⁻¹ := by
    apply G122ParametricCarrierDisplayedBundle.transportSourceActionHom_injective
    simpa only [map_mul,
      G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier]
      using transportedEquality
  have orderedSourceEquality :
      sourcePairHom E F different (first.1⁻¹, first.2⁻¹) =
        sourcePairHom E F different (second.1⁻¹, second.2⁻¹) := by
    change
      finiteAxisFoldSourceContextObjectPermHom E first.1⁻¹ *
          finiteAxisFoldSourceContextObjectPermHom F first.2⁻¹ =
        finiteAxisFoldSourceContextObjectPermHom E second.1⁻¹ *
          finiteAxisFoldSourceContextObjectPermHom F second.2⁻¹
    rw [sourceContextObjectPerm_commute different first.1⁻¹ first.2⁻¹,
      sourceContextObjectPerm_commute different second.1⁻¹ second.2⁻¹]
    exact sourceEquality
  have inversePairEquality := sourcePairHom_injective different orderedSourceEquality
  apply Prod.ext
  · exact inv_injective (congrArg Prod.fst inversePairEquality)
  · exact inv_injective (congrArg Prod.snd inversePairEquality)

/-- Canonical multiplicative equivalence from any injective hom to its actual
range. -/
noncomputable def rangeMulEquivOfInjective
    {G : Type u} {H : Type v} [Group G] [Group H]
    (hom : G →* H) (injective : Function.Injective hom) :
    G ≃* MonoidHom.range hom :=
  MulEquiv.ofBijective (MonoidHom.rangeRestrict hom)
    ⟨(fun _ _ equality => injective (congrArg Subtype.val equality)),
      MonoidHom.rangeRestrict_surjective hom⟩

/-- The actual two-carrier kernel image. -/
noncomputable def PairKernelImage (E F : Type) (different : E ≠ F) :
    Subgroup FiniteAxisFoldResidualLocalFiberKernel :=
  MonoidHom.range (pairKernelHom E F different)

/-- Source pairs reconstruct their actual kernel image multiplicatively. -/
noncomputable def sourcePairKernelMulEquiv
    (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) ≃* PairKernelImage E F different :=
  rangeMulEquivOfInjective (pairKernelHom E F different)
    (pairKernelHom_injective different)

/-- Stored-backward observation restricted to the actual pair image. -/
noncomputable def pairBackwardObservationHom
    (E F : Type) (different : E ≠ F) :
    PairKernelImage E F different →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldResidualLocalFiberKernelBackwardProjection.comp
    (PairKernelImage E F different).subtype

/-- Stored-backward observation remains faithful on the pair image. -/
theorem pairBackwardObservationHom_injective
    {E F : Type} (different : E ≠ F) :
    Function.Injective (pairBackwardObservationHom E F different) := by
  intro first second equality
  apply Subtype.ext
  exact finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
    equality

/-- Actual stored-backward observations of the pair image. -/
noncomputable def PairObservedImage
    (E F : Type) (different : E ≠ F) :
    Subgroup (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  MonoidHom.range (pairBackwardObservationHom E F different)

/-- The actual pair image is reconstructed multiplicatively from its
stored-backward observations. -/
noncomputable def pairKernelObservedMulEquiv
    (E F : Type) (different : E ≠ F) :
    PairKernelImage E F different ≃* PairObservedImage E F different :=
  rangeMulEquivOfInjective (pairBackwardObservationHom E F different)
    (pairBackwardObservationHom_injective different)

/-- Source pairs reconstruct the observed range without losing the actual
kernel stage. -/
noncomputable def sourcePairObservedMulEquiv
    (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) ≃* PairObservedImage E F different :=
  (sourcePairKernelMulEquiv E F different).trans
    (pairKernelObservedMulEquiv E F different)

/-- Forget the successive kernel predicates and retain the actual normalized
direct-endpoint automorphism. -/
noncomputable def pairNormalizedDirectHom
    (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) →*
      Aut FiniteAxisFoldNormalizedDirectGeometry where
  toFun code := (pairKernelHom E F different code).1.1.1.1
  map_one' := congrArg
    (fun value : FiniteAxisFoldResidualLocalFiberKernel => value.1.1.1.1)
    (map_one (pairKernelHom E F different))
  map_mul' first second := congrArg
    (fun value : FiniteAxisFoldResidualLocalFiberKernel => value.1.1.1.1)
    (map_mul (pairKernelHom E F different) first second)

/-- Forgetting the kernel predicates does not identify source pairs. -/
theorem pairNormalizedDirectHom_injective
    {E F : Type} (different : E ≠ F) :
    Function.Injective (pairNormalizedDirectHom E F different) := by
  intro first second equality
  apply pairKernelHom_injective different
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact equality

/-- Carry the pair image through the canonical normalization section to the
expanded actual direct endpoint. -/
noncomputable def pairExpandedDirectHom
    (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) →*
      Aut finiteAxisFoldActualDirectAdmissibleGeometry :=
  (canonicalNormalizationAutomorphismSectionHom
      finiteAxisFoldActualDirectAdmissibleGeometry).comp
    (pairNormalizedDirectHom E F different)

/-- The canonical expanded lift preserves the pair separation. -/
theorem pairExpandedDirectHom_injective
    {E F : Type} (different : E ≠ F) :
    Function.Injective (pairExpandedDirectHom E F different) := by
  intro first second equality
  apply pairNormalizedDirectHom_injective different
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
          (pairNormalizedDirectHom E F different first)) =
      RealizationComparisonIdempotents.functorAutomorphismHom
        (geometryNormalizationFunctor FiniteModel.carrier)
        finiteAxisFoldActualDirectAdmissibleGeometry
        (canonicalNormalizationAutomorphismSectionHom
          finiteAxisFoldActualDirectAdmissibleGeometry
          (pairNormalizedDirectHom E F different second)) at normalized
  rw [canonicalNormalizationAutomorphismSection_rightInverse,
    canonicalNormalizationAutomorphismSection_rightInverse] at normalized
  exact normalized

/-- Expanded direct-endpoint image of the source pair. -/
noncomputable def PairExpandedDirectImage
    (E F : Type) (different : E ≠ F) :
    Subgroup (Aut finiteAxisFoldActualDirectAdmissibleGeometry) :=
  MonoidHom.range (pairExpandedDirectHom E F different)

/-- Source pairs reconstruct their expanded direct-endpoint image. -/
noncomputable def sourcePairExpandedDirectMulEquiv
    (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) ≃*
      PairExpandedDirectImage E F different :=
  rangeMulEquivOfInjective (pairExpandedDirectHom E F different)
    (pairExpandedDirectHom_injective different)

/-- Carry the same pair through the normalized `barAlpha` comparison section. -/
noncomputable def pairComparisonHom
    (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) →*
      GeneratedArrowComparisonSubgroup finiteAxisFoldNormalizedBarAlphaIso.hom :=
  (generatedArrowComparisonSectionHom
      finiteAxisFoldNormalizedBarAlphaIso).comp
    (pairNormalizedDirectHom E F different)

/-- The displayed comparison source projection preserves pair separation. -/
theorem pairComparisonHom_injective
    {E F : Type} (different : E ≠ F) :
    Function.Injective (pairComparisonHom E F different) := by
  intro first second equality
  apply pairNormalizedDirectHom_injective different
  exact congrArg
    (generatedArrowComparisonSourceHom
      finiteAxisFoldNormalizedBarAlphaIso.hom) equality

/-- Normalized `barAlpha` comparison image of the source pair. -/
noncomputable def PairComparisonImage
    (E F : Type) (different : E ≠ F) :
    Subgroup
      (GeneratedArrowComparisonSubgroup
        finiteAxisFoldNormalizedBarAlphaIso.hom) :=
  MonoidHom.range (pairComparisonHom E F different)

/-- Source pairs reconstruct their actual normalized comparison image. -/
noncomputable def sourcePairComparisonMulEquiv
    (E F : Type) (different : E ≠ F) :
    (Equiv.Perm E × Equiv.Perm F) ≃*
      PairComparisonImage E F different :=
  rangeMulEquivOfInjective (pairComparisonHom E F different)
    (pairComparisonHom_injective different)

/-- No type is equal to its powerset type. -/
theorem type_ne_powerSet (E : Type) : E ≠ Set E := by
  intro equality
  have cardinalEquality : Cardinal.mk E = Cardinal.mk (Set E) :=
    congrArg Cardinal.mk equality
  have cantorStrict : Cardinal.mk E < Cardinal.mk (Set E) := by
    simpa only [Cardinal.mk_set] using Cardinal.cantor (Cardinal.mk E)
  rw [← cardinalEquality] at cantorStrict
  exact (lt_irrefl (Cardinal.mk E)) cantorStrict

/-- A pair moving a chosen value on each unequal carrier cannot be represented
by an action supported on a single primitive carrier. -/
theorem sourcePairHom_ne_singleCarrier
    {E F G : Type} (different : E ≠ F)
    (first : Equiv.Perm E) (second : Equiv.Perm F)
    (firstValue : E) (secondValue : F)
    (firstMoves : first firstValue ≠ firstValue)
    (secondMoves : second secondValue ≠ secondValue)
    (single : Equiv.Perm G) :
    sourcePairHom E F different (first, second) ≠
      finiteAxisFoldSourceContextObjectPermHom G single := by
  intro equality
  by_cases carrierEquality : G = E
  · subst G
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
        permutation
          (⟨finiteAxisFoldSourceExtensionProbe secondValue⟩ :
            FiniteAxisFoldSourceContextObject)) equality
    have extensionSigmaEquality := congrArg
      (fun context : FiniteAxisFoldSourceContextObject =>
        (⟨context.ctx.Extension, context.ctx.extension⟩ :
          Sigma fun carrier : Type => carrier)) evaluated
    have fixed : second secondValue = secondValue := by
      simpa [sourcePairHom, finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation, different, different.symm]
        using extensionSigmaEquality
    exact secondMoves fixed
  · have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
        permutation
          (⟨finiteAxisFoldSourceExtensionProbe firstValue⟩ :
            FiniteAxisFoldSourceContextObject)) equality
    have extensionSigmaEquality := congrArg
      (fun context : FiniteAxisFoldSourceContextObject =>
        (⟨context.ctx.Extension, context.ctx.extension⟩ :
          Sigma fun carrier : Type => carrier)) evaluated
    have fixed : first firstValue = firstValue := by
      simpa [sourcePairHom, finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation, different, different.symm,
        carrierEquality, Ne.symm carrierEquality] using extensionSigmaEquality
    exact firstMoves fixed

/-- Carrier-indexed family generated by two unequal primitive carriers. -/
def TwoCarrierImage
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) : Prop :=
  ∃ E F : Type, ∃ different : E ≠ F,
    ∃ code : Equiv.Perm E × Equiv.Perm F,
      pairKernelHom E F different code = remainder

/-- Every single-carrier image belongs to the two-carrier family by adjoining
the identity action on its powerset carrier. -/
theorem arbitraryCarrierImage_subset_twoCarrierImage :
    {remainder | G122ArbitraryCarrierKernelReconstruction.ArbitraryCarrierImage
      remainder} ⊆ {remainder | TwoCarrierImage remainder} := by
  intro remainder membership
  rcases membership with ⟨E, permutation, rfl⟩
  refine ⟨E, Set E, type_ne_powerSet E, (permutation, 1), ?_⟩
  change
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E permutation *
        finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom (Set E) 1 =
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E permutation
  simp

/-- The simultaneous Nat swap and powerset complement is represented by the
two-carrier hom. -/
noncomputable def natPowerSetPairKernel :
    FiniteAxisFoldResidualLocalFiberKernel :=
  pairKernelHom Nat (Set Nat) finiteAxisFoldNatPowerSet_ne_nat.symm
    (finiteAxisFoldNatZeroOneSwap, finiteAxisFoldNatPowerSetComplement)

/-- The simultaneous Nat and powerset action belongs to the two-carrier family. -/
theorem natPowerSetPairKernel_mem_twoCarrierImage :
    TwoCarrierImage natPowerSetPairKernel :=
  ⟨Nat, Set Nat, finiteAxisFoldNatPowerSet_ne_nat.symm,
    (finiteAxisFoldNatZeroOneSwap, finiteAxisFoldNatPowerSetComplement), rfl⟩

/-- The simultaneous action cannot be represented on any single primitive
carrier. -/
theorem natPowerSetPairKernel_not_arbitraryCarrierImage :
    ¬ G122ArbitraryCarrierKernelReconstruction.ArbitraryCarrierImage
      natPowerSetPairKernel := by
  rintro ⟨G, single, equality⟩
  have projected := congrArg
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection equality.symm
  change
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        (pairKernelHom Nat (Set Nat)
          finiteAxisFoldNatPowerSet_ne_nat.symm
          (finiteAxisFoldNatZeroOneSwap,
            finiteAxisFoldNatPowerSetComplement)) =
      finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom G single)
      at projected
  rw [pairKernelHom_backwardProjection,
    finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection,
    finiteAxisFoldNatZeroOneSwap_inv,
    finiteAxisFoldNatPowerSetComplement_inv] at projected
  have transportedEquality :
      finiteAxisFoldTransportedSourceContextPermutation
            finiteAxisFoldNatPowerSetComplement *
          finiteAxisFoldTransportedSourceContextPermutation
            finiteAxisFoldNatZeroOneSwap =
        finiteAxisFoldTransportedSourceContextPermutation single⁻¹ :=
    MulOpposite.op_injective projected
  have sourceEquality :
      finiteAxisFoldSourceContextObjectPermHom (Set Nat)
            finiteAxisFoldNatPowerSetComplement *
          finiteAxisFoldSourceContextObjectPermHom Nat
            finiteAxisFoldNatZeroOneSwap =
        finiteAxisFoldSourceContextObjectPermHom G single⁻¹ := by
    apply G122ParametricCarrierDisplayedBundle.transportSourceActionHom_injective
    simpa only [map_mul,
      G122ParametricCarrierDisplayedBundle.transportSourceActionHom_sourceCarrier]
      using transportedEquality
  have orderedSourceEquality :
      sourcePairHom Nat (Set Nat) finiteAxisFoldNatPowerSet_ne_nat.symm
          (finiteAxisFoldNatZeroOneSwap,
            finiteAxisFoldNatPowerSetComplement) =
        finiteAxisFoldSourceContextObjectPermHom G single⁻¹ := by
    change
      finiteAxisFoldSourceContextObjectPermHom Nat
            finiteAxisFoldNatZeroOneSwap *
          finiteAxisFoldSourceContextObjectPermHom (Set Nat)
            finiteAxisFoldNatPowerSetComplement =
        finiteAxisFoldSourceContextObjectPermHom G single⁻¹
    rw [sourceContextObjectPerm_commute
      finiteAxisFoldNatPowerSet_ne_nat.symm
      finiteAxisFoldNatZeroOneSwap finiteAxisFoldNatPowerSetComplement]
    exact sourceEquality
  exact sourcePairHom_ne_singleCarrier
    finiteAxisFoldNatPowerSet_ne_nat.symm
    finiteAxisFoldNatZeroOneSwap finiteAxisFoldNatPowerSetComplement
    0 (∅ : Set Nat)
    (by simp) (finiteAxisFoldNatPowerSetComplement_ne ∅) single⁻¹
    orderedSourceEquality

/-- The two-carrier family is a proper enlargement of the complete
single-carrier family. -/
theorem arbitraryCarrierImage_ssubset_twoCarrierImage :
    {remainder | G122ArbitraryCarrierKernelReconstruction.ArbitraryCarrierImage
      remainder} ⊂ {remainder | TwoCarrierImage remainder} := by
  refine ⟨arbitraryCarrierImage_subset_twoCarrierImage, ?_⟩
  intro reverseInclusion
  exact natPowerSetPairKernel_not_arbitraryCarrierImage
    (reverseInclusion natPowerSetPairKernel_mem_twoCarrierImage)

end G122TwoCarrierExpandedReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction

end

end AAT.AG.LocalSemanticReconstruction
