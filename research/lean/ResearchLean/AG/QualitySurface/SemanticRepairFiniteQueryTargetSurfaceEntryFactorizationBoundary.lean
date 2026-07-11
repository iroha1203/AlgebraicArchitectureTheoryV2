import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceEntryExactnessBoundary

/-!
Cycle 57 evidence for `G-aat-quality-surface-04`.

Cycle 56 identified represented assignment entry, semantic-reading adequacy,
no post-fiber separation, and explicit coordinate certificates as one exact
finite-query boundary under visible recovery.  This file connects the entry
face to the target-surface universal factorization API.

The direct entry-to-factorization direction is recovery-free: assignment entry
already contains visible shadow extensionality.  The package theorem then keeps
the recovery and decidable-output premises visible when it lists the four exact
boundary routes.  It does not turn any route into target-level semantic
soundness, arbitrary representation adequacy, global coherence, obstruction
vanishing, or target theorem completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceEntryFactorizationBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
open SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary
open SemanticRepairFiniteQueryTargetSurfaceEntryExactnessBoundary
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r s

/-! ## Assignment entry as a target-surface factorization route -/

/--
Represented assignment entry makes the observation read the target surface
through the finite shadow of `Obs(A)`.  This direction is recovery-free because
the entry witness already carries visible shadow extensionality.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_entry
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hentry :
      ∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates) := by
  have hext : ShadowExtensionalTowerObservation observe :=
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
      (Atom := Atom) repr).1 hentry
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_shadowExtensional
      (Atom := Atom) repr hext A certificates

/--
Represented assignment entry gives the full target-surface finite-shadow
factorization and uniqueness package.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_entry
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hentry :
      ∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    (observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe U = factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor observe
            (targetSurfaceLayerShadow A certificates)) := by
  have hext : ShadowExtensionalTowerObservation observe :=
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
      (Atom := Atom) repr).1 hentry
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_shadowExtensional
      (Atom := Atom) repr hext A certificates

/--
With visible recovery and decidable output equality, each face of the exact
entry boundary is an explicit route into target-surface universal
factorization.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_entryExactBoundary_universalFactorization_routes_of_observationRecoversQueryReadings
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    [DecidableEq Out]
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    let UF : Prop :=
      (observe (Obs_A_ofFiniteCertificates A certificates) =
        canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe U = factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor observe
            (targetSurfaceLayerShadow A certificates))
    (((∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
          (Atom := Atom) reading repr.package.query repr.package.post)) ∧
    ((∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) ∧
    ((¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
      (Atom := Atom) repr.package.query repr.package.post) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) ∧
    ((∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) ∧
    ((∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)) ∧
    (((∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) -> UF) ∧
    (((∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) -> UF) ∧
    ((¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
      (Atom := Atom) repr.package.query repr.package.post) -> UF) ∧
    (QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      repr.package.query -> UF))) := by
  dsimp
  have hexact :=
    representedFiniteTraceQueryObservation_entry_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover
  refine ⟨hexact, ?_⟩
  exact
    ⟨fun hentry =>
      targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_entry
        (Atom := Atom) repr hentry A certificates,
      fun hadequacy =>
        targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_exists_semanticReadingAdequacy
          (Atom := Atom) repr hadequacy A certificates,
      fun hno =>
        targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_no_queryPostFiberSeparation
          (Atom := Atom) repr hno A certificates,
      fun cert =>
        targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_queryCurrentShadowCoordinateCertificate
          (Atom := Atom) repr cert A certificates⟩

end SemanticRepairFiniteQueryTargetSurfaceEntryFactorizationBoundary
end QualitySurface
end ResearchLean.AG
