import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryRecoveryGap

/-!
Cycle 74 evidence for `G-aat-quality-surface-04`.

Cycle 73 showed that support-shadow self-recovery cannot be promoted to the
whole support-boundary square.  This file decomposes that blocker into each
visible support-boundary face.  Even for the canonical complete Bool
support-shadow observation, self-recovery does not yield raw current-shadow
factorization, support-control, current-shadow-reading faithfulness, or the
explicit coordinate certificate.

The result is blocker evidence against a non-circular representation-adequacy
bridge that tries to discharge support-boundary membership from recovery alone.
It is not target theorem completion and not a target theorem refutation.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryCertificateGap

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryObstruction
open SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryRecoveryGap

/-! ## Self-recovery does not discharge individual support-boundary faces -/

/--
Self-recovery of the complete Bool support-shadow observation does not imply
raw factorization through the canonical current shadow.
-/
theorem not_boolCompleteSupportTraceShadow_selfRecovery_to_currentShadowFactor :
    ¬ (ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ->
      ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
          canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
            factor (canonicalTowerLayerShadow T)) := by
  intro himp
  have hw :=
    boolCompleteSupportTraceShadow_selfRecovery_noSupportBoundarySquare
  exact hw.2.1 (himp hw.1)

/--
Self-recovery of the complete Bool support-shadow observation does not imply
support-control by the canonical current shadow.
-/
theorem not_boolCompleteSupportTraceShadow_selfRecovery_to_supportControl :
    ¬ (ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ->
      CurrentShadowDeterminesSupportTraceShadow.{0, 0, 0, 0, 0}
        (Atom := Bool) boolCompleteTraceSupport) := by
  intro himp
  have hw :=
    boolCompleteSupportTraceShadow_selfRecovery_noSupportBoundarySquare
  exact hw.2.2.1 (himp hw.1)

/--
Self-recovery of the complete Bool support-shadow observation does not imply
current-shadow-reading faithfulness for its query/post pair.
-/
theorem not_boolCompleteSupportTraceShadow_selfRecovery_to_currentShadowFaithfulness :
    ¬ (ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ->
      SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).post) := by
  intro himp
  have hw :=
    boolCompleteSupportTraceShadow_selfRecovery_noSupportBoundarySquare
  exact hw.2.2.2.1 (himp hw.1)

/--
Self-recovery of the complete Bool support-shadow observation does not imply
the explicit coordinate certificate needed by the support-boundary square.
-/
theorem not_boolCompleteSupportTraceShadow_selfRecovery_to_coordinateCertificate :
    ¬ (ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ->
      QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
        boolCompleteTraceSupport) := by
  intro himp
  have hw :=
    boolCompleteSupportTraceShadow_selfRecovery_noSupportBoundarySquare
  exact hw.2.2.2.2 (himp hw.1)

/--
The complete Bool self-recovery witness packages all four support-boundary
gaps at once.  It records exactly which extra visible data a future
representation-adequacy bridge must produce.
-/
theorem boolCompleteSupportTraceShadow_selfRecovery_individualBoundaryGaps :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    (¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
          factor (canonicalTowerLayerShadow T)) ∧
    (¬ CurrentShadowDeterminesSupportTraceShadow.{0, 0, 0, 0, 0}
      (Atom := Bool) boolCompleteTraceSupport) ∧
    (¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).post) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolCompleteTraceSupport := by
  exact boolCompleteSupportTraceShadow_selfRecovery_noSupportBoundarySquare

end SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryCertificateGap
end QualitySurface
end ResearchLean.AG
