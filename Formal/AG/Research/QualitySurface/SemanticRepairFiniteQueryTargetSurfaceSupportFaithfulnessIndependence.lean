import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessRoute
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportControlIndependence

/-!
Cycle 69 evidence for `G-aat-quality-surface-04`.

Cycle 68 added the positive target-surface route from visible current-shadow
reading faithfulness of the canonical support-shadow observation.  This file
records the adjacent anti-weakening boundary: complete support-shadow recovery
does not produce that current-shadow reading faithfulness, and it still does not
produce support-control, raw current-shadow factorization, or an explicit
coordinate certificate.

The Bool witness keeps the Cycle 68 premise visible.  Recovery of finite query
readings is not current-shadow reading faithfulness and is not target theorem
completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessIndependence

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization
open SemanticRepairFiniteQueryTargetSurfaceSupportControlIndependence

/-! ## Complete support recovery does not discharge reading faithfulness -/

/--
The complete Bool support shadow recovers Bool `[true]` readings, but the
canonical current-shadow reading is not faithful for its support-shadow
observation.
-/
theorem boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_not_currentShadowSemanticReading_faithful :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    ¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).post := by
  exact
    ⟨boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_no_currentShadowFactor.1,
      not_boolCompleteSupportTraceShadowObservation_currentShadowSemanticReading_faithful⟩

/--
Complete Bool support-shadow recovery, no current-shadow reading faithfulness,
no support-control, no current-shadow factorization, and no coordinate
certificate hold together.
-/
theorem boolCompleteSupportTraceShadow_recovery_noFaithfulness_noSupportControl_noCurrentFactor_noCoordinateCertificate :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    (¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).post) ∧
    (¬ CurrentShadowDeterminesSupportTraceShadow.{0, 0, 0, 0, 0}
      (Atom := Bool)
      boolCompleteTraceSupport) ∧
    (¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
          factor (canonicalTowerLayerShadow T)) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolCompleteTraceSupport := by
  exact
    ⟨boolCompleteSupportTraceShadow_recovery_noSupportControl_noCurrentFactor_noCoordinateCertificate.1,
      not_boolCompleteSupportTraceShadowObservation_currentShadowSemanticReading_faithful,
      boolCompleteSupportTraceShadow_recovery_noSupportControl_noCurrentFactor_noCoordinateCertificate.2.1,
      boolCompleteSupportTraceShadow_recovery_noSupportControl_noCurrentFactor_noCoordinateCertificate.2.2.1,
      boolCompleteSupportTraceShadow_recovery_noSupportControl_noCurrentFactor_noCoordinateCertificate.2.2.2⟩

end SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessIndependence
end QualitySurface
end Formal.AG.Research
