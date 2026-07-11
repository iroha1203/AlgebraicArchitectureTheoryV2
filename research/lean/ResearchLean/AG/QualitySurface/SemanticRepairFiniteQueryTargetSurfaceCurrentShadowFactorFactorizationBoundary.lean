import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceEntryFactorizationBoundary
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorBoundary

/-!
Cycle 59 evidence for `G-aat-quality-surface-04`.

Cycle 58 made raw current-shadow factorization exact with represented
assignment entry and the surrounding finite-query boundary.  This file records
the target-surface consequence: raw current-shadow factorization is a
recovery-free route into target-surface universal factorization.

The exact-boundary route package keeps `ObservationRecoversQueryReadings` and
`[DecidableEq Out]` visible when it exchanges raw factorization with
semantic-reading adequacy, no-separation, or coordinate certificates.  It does
not promote finite-query factorization to target-level semantic soundness,
arbitrary representation adequacy, global coherence, obstruction vanishing, or
target theorem completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorFactorizationBoundary

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
open SemanticRepairFiniteQueryTargetSurfaceEntryFactorizationBoundary
open SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorBoundary
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r s

/-! ## Raw current-shadow factorization as a target-surface route -/

/--
Raw current-shadow factorization makes the represented observation read the
target surface through the finite shadow of `Obs(A)`.  This direction is
recovery-free.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_currentShadowFactor
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
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> Out,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe T = factor (canonicalTowerLayerShadow T))
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
  have hentry :
      ∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe :=
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_entry
      (Atom := Atom) repr).1 hfactor
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_entry
      (Atom := Atom) repr hentry A certificates

/--
Raw current-shadow factorization gives the full target-surface finite-shadow
factorization and uniqueness package.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_currentShadowFactor
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
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> Out,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe T = factor (canonicalTowerLayerShadow T))
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
  have hentry :
      ∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe :=
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_entry
      (Atom := Atom) repr).1 hfactor
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_entry
      (Atom := Atom) repr hentry A certificates

/--
With visible recovery and decidable output equality, every face of the raw
current-shadow factor exact boundary gives the same target-surface universal
factorization route.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_currentShadowFactorExactBoundary_universalFactorization_routes_of_observationRecoversQueryReadings
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
    (((∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      (∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe)) ∧
    ((∃ assignment :
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
    ((∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) ∧
    ((∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)) ∧
    (((∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) -> UF) ∧
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
      repr.package.query -> UF)))) := by
  dsimp
  have hexact :=
    representedFiniteTraceQueryObservation_currentShadowFactor_entry_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover
  refine ⟨hexact, ?_⟩
  exact
    ⟨fun hfactor =>
      targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_currentShadowFactor
        (Atom := Atom) repr hfactor A certificates,
      fun hentry =>
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

end SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorFactorizationBoundary
end QualitySurface
end ResearchLean.AG
