import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessRoute
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateRoute

/-!
Cycle 70 evidence for `G-aat-quality-surface-04`.

Cycles 68 and 69 isolated the current-shadow-reading faithfulness premise for
the canonical support-shadow route and showed that support-shadow recovery does
not discharge it.  This file identifies that faithfulness premise with the
explicit support-coordinate current-shadow certificate surface.

The certificate remains visible theorem data.  The route does not claim
arbitrary semantic observation adequacy, target-level representation adequacy,
global coherence, tower vanishing, or target theorem completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessCertificateRoute

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessRoute
open SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateRoute
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r

/-! ## Faithfulness/certificate exact support boundary -/

/--
For the canonical support-shadow observation, current-shadow-reading
faithfulness is exactly the explicit support-coordinate current-shadow
certificate.
-/
theorem supportTraceShadowObservation_currentShadowSemanticReading_faithful_iff_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    (support : List Atom) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support := by
  exact
    (currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful
      (Atom := Atom) support).symm.trans
      (currentShadowDeterminesSupportTraceShadow_iff_supportCoordinateCurrentShadowFactors
        (Atom := Atom) support)

/--
Current-shadow-reading faithfulness of the canonical support-shadow observation
extracts the explicit support-coordinate certificate.
-/
theorem queryCurrentShadowCoordinateCertificate_of_supportTraceShadowObservation_currentShadowSemanticReading_faithful
    {Atom : Type u}
    (support : List Atom)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      support := by
  exact
    (supportTraceShadowObservation_currentShadowSemanticReading_faithful_iff_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) support).1 hfaithful

/--
The explicit support-coordinate certificate supplies current-shadow-reading
faithfulness for the canonical support-shadow observation.
-/
theorem supportTraceShadowObservation_currentShadowSemanticReading_faithful_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    (support : List Atom)
    (hcert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (supportTraceShadowFiniteTraceQueryObservation support).post := by
  exact
    (supportTraceShadowObservation_currentShadowSemanticReading_faithful_iff_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) support).2 hcert

/-! ## Certificate-visible target route packages -/

/--
Faithfulness first extracts the explicit coordinate certificate, and that
certificate then routes the canonical support-shadow representation through
recovery, semantic adequacy, current-shadow factorization, and target-surface
universal factorization.
-/
theorem supportTraceShadowRepresentation_certificate_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_currentShadowSemanticReading_faithful
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support ∧
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T) ∧
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) ∧
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        (supportTraceShadowFiniteTraceQueryObservation support).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    (((fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor
        (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          (supportTraceShadowFiniteTraceQueryObservation support).observe U =
            factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor
            (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
              (supportTraceShadowFiniteTraceQueryObservation support).observe T)
            (targetSurfaceLayerShadow A certificates))) := by
  have hcert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support :=
    queryCurrentShadowCoordinateCertificate_of_supportTraceShadowObservation_currentShadowSemanticReading_faithful
      (Atom := Atom) support hfaithful
  exact
    ⟨hcert,
      supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support hcert A certificates⟩

/--
Conversely, the explicit coordinate certificate gives both current-shadow
reading faithfulness and the certificate-driven target-surface route.
-/
theorem supportTraceShadowRepresentation_currentShadowFaithfulness_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (hcert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post ∧
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T) ∧
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) ∧
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        (supportTraceShadowFiniteTraceQueryObservation support).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    (((fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor
        (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          (supportTraceShadowFiniteTraceQueryObservation support).observe U =
            factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor
            (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
              (supportTraceShadowFiniteTraceQueryObservation support).observe T)
            (targetSurfaceLayerShadow A certificates))) := by
  exact
    ⟨supportTraceShadowObservation_currentShadowSemanticReading_faithful_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support hcert,
      supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support hcert A certificates⟩

end SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessCertificateRoute
end QualitySurface
end ResearchLean.AG
