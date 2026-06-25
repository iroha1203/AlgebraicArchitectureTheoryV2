import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryObstruction
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationSupportRecovery

/-!
Cycle 73 evidence for `G-aat-quality-surface-04`.

Cycle 72 separated support-shadow recovery from support-boundary membership
using the Bool `[true]` query.  This file records the sharper self-recovery
gap: even the canonical support-shadow observation's own query readings are
recoverable from the support shadow, but that recovery does not put the
complete Bool support shadow into the support-boundary square.

The theorem remains a finite support-shadow anti-weakening witness.  It is not
target theorem completion and not a target theorem refutation.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryRecoveryGap

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
open SemanticRepairFiniteQueryRepresentationSupportRecovery
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryObstruction

/-! ## Self-recovery still does not imply the support boundary -/

/--
The complete Bool support shadow recovers its own support query readings, but
it still misses every face of the support-boundary square.
-/
theorem boolCompleteSupportTraceShadow_selfRecovery_noSupportBoundarySquare :
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
  have hblocked :=
    boolCompleteSupportTraceShadow_recovery_noSupportBoundarySquare
  exact
    ⟨supportTraceShadowObservation_recoversSupportedQueryReadings
        (Atom := Bool)
        (support := boolCompleteTraceSupport)
        (query := (supportTraceShadowFiniteTraceQueryObservation
          boolCompleteTraceSupport).query)
        (supportSelfQuerySupportedBy boolCompleteTraceSupport),
      hblocked.2.1,
      hblocked.2.2.1,
      hblocked.2.2.2.1,
      hblocked.2.2.2.2⟩

/--
Therefore self-recovery of the complete Bool support-shadow observation cannot
be promoted into support-boundary membership.
-/
theorem not_boolCompleteSupportTraceShadow_selfRecovery_to_supportBoundarySquare :
    ¬ (ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ->
      (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
          canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
            factor (canonicalTowerLayerShadow T)) ∧
      CurrentShadowDeterminesSupportTraceShadow.{0, 0, 0, 0, 0}
        (Atom := Bool) boolCompleteTraceSupport ∧
      SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
        (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).post ∧
      QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
        boolCompleteTraceSupport) := by
  intro himp
  have hw :=
    boolCompleteSupportTraceShadow_selfRecovery_noSupportBoundarySquare
  have hboundary := himp hw.1
  exact hw.2.1 hboundary.1

end SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryRecoveryGap
end QualitySurface
end Formal.AG.Research
