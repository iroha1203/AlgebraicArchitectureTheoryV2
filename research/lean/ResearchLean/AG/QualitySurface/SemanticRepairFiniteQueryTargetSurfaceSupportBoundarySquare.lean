import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessCertificateRoute

/-!
Cycle 71 evidence for `G-aat-quality-surface-04`.

Cycle 70 identified support-shadow current-shadow-reading faithfulness with
the explicit support-coordinate certificate surface.  This file closes the
adjacent square by adding the raw current-shadow factorization face: for the
canonical support-shadow representation, raw factorization, support-control,
current-shadow-reading faithfulness, and the coordinate certificate are the
same visible finite support boundary.

The factorization / certificate boundary remains theorem data.  This is not
arbitrary semantic observation adequacy, target-level representation adequacy,
global coherence, tower vanishing, or target theorem completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportBoundarySquare

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairCurrentShadowCoordinateObligations
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQuerySupportedCurrentShadowFactorization
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessCertificateRoute
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r

/-! ## Support boundary square -/

/--
For the canonical support-shadow representation, raw current-shadow
factorization is exactly current-shadow-reading faithfulness.
-/
theorem supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowSemanticReading_faithful
    {Atom : Type u}
    (support : List Atom) :
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) ↔
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post := by
  exact
    (supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowDeterminesSupportTraceShadow
      (Atom := Atom) support).trans
      (currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful
        (Atom := Atom) support)

/--
For the canonical support-shadow representation, raw current-shadow
factorization is exactly the explicit support-coordinate certificate.
-/
theorem supportTraceShadowRepresentation_currentShadowFactor_iff_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    (support : List Atom) :
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support := by
  exact
    (supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowDeterminesSupportTraceShadow
      (Atom := Atom) support).trans
      (currentShadowDeterminesSupportTraceShadow_iff_supportCoordinateCurrentShadowFactors
        (Atom := Atom) support)

/--
Canonical support-shadow factorization, support-control, current-shadow-reading
faithfulness, and explicit coordinate certification form one exact boundary.
-/
theorem supportTraceShadowRepresentation_factor_control_faithfulness_certificate_boundary
    {Atom : Type u}
    (support : List Atom) :
    ((∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) ↔
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
        (Atom := Atom) support) ∧
    (CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
        (Atom := Atom) support ↔
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) ∧
    (SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support) ∧
    ((∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support) := by
  exact
    ⟨supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowDeterminesSupportTraceShadow
      (Atom := Atom) support,
      currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful
        (Atom := Atom) support,
      supportTraceShadowObservation_currentShadowSemanticReading_faithful_iff_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support,
      supportTraceShadowRepresentation_currentShadowFactor_iff_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support⟩

/-! ## Raw-factorization route into the certificate-visible target package -/

/--
Raw current-shadow factorization of the canonical support-shadow representation
extracts the coordinate certificate and current-shadow-reading faithfulness,
then enters the certificate-visible target-surface route.
-/
theorem supportTraceShadowRepresentation_certificate_faithfulness_recovery_semanticAdequacy_targetSurfaceRoute_of_currentShadowFactor
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          canonicalSupportTraceProbeTowerLayerShadow support T =
            factor (canonicalTowerLayerShadow T))
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
    (supportTraceShadowRepresentation_currentShadowFactor_iff_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) support).1 hfactor
  have hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post :=
    (supportTraceShadowObservation_currentShadowSemanticReading_faithful_iff_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) support).2 hcert
  have hroute :=
    supportTraceShadowRepresentation_currentShadowFaithfulness_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) support hcert A certificates
  exact
    ⟨hcert,
      hfaithful,
      hroute.2.1,
      hroute.2.2.1,
      hroute.2.2.2.2⟩

end SemanticRepairFiniteQueryTargetSurfaceSupportBoundarySquare
end QualitySurface
end ResearchLean.AG
