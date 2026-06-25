import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportControlRoute
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateIndependence

/-!
Cycle 67 evidence for `G-aat-quality-surface-04`.

Cycle 66 added the positive target-surface route from the visible
support-control premise `CurrentShadowDeterminesSupportTraceShadow`.  This file
records the adjacent anti-weakening boundary: complete support-shadow recovery
does not produce support-control, raw current-shadow factorization, or an
explicit coordinate certificate.

The Bool witness keeps the Cycle 66 premise visible.  Recovery of finite query
readings is not current-shadow determinacy and is not target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportControlIndependence

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization
open SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateIndependence

/-! ## Complete support recovery does not discharge support-control -/

/--
The complete Bool support shadow recovers Bool `[true]` readings, but it does
not satisfy the support-control premise required by the Cycle 66 target route.
-/
theorem boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_not_currentShadowDeterminesSupportTraceShadow :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    ¬ CurrentShadowDeterminesSupportTraceShadow.{0, 0, 0, 0, 0}
      (Atom := Bool)
      boolCompleteTraceSupport := by
  exact
    ⟨boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_no_currentShadowFactor.1,
      not_currentShadowDetermines_boolCompleteSupportTraceShadow⟩

/--
Complete Bool support-shadow recovery, no support-control, no current-shadow
factorization, and no coordinate certificate hold together.
-/
theorem boolCompleteSupportTraceShadow_recovery_noSupportControl_noCurrentFactor_noCoordinateCertificate :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
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
    ⟨boolCompleteSupportTraceShadow_recovery_noCurrentFactor_noCoordinateCertificate.1,
      not_currentShadowDetermines_boolCompleteSupportTraceShadow,
      boolCompleteSupportTraceShadow_recovery_noCurrentFactor_noCoordinateCertificate.2.1,
      boolCompleteSupportTraceShadow_recovery_noCurrentFactor_noCoordinateCertificate.2.2⟩

end SemanticRepairFiniteQueryTargetSurfaceSupportControlIndependence
end QualitySurface
end Formal.AG.Research
