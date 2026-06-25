import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportBoundarySquare
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessIndependence

/-!
Cycle 72 evidence for `G-aat-quality-surface-04`.

Cycle 71 packaged the exact support boundary square for canonical support-shadow
representations.  This file records the obstruction side of that square: if the
canonical support-shadow representation has no raw current-shadow factorization,
then support-control, current-shadow-reading faithfulness, and the explicit
coordinate certificate all fail.

The obstruction is still a finite support-shadow boundary result.  It does not
claim arbitrary semantic observation inadequacy, target-level representation
failure, global coherence failure, tower nonvanishing, or target theorem
refutation.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryObstruction

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
open SemanticRepairFiniteQuerySupportedCurrentShadowFactorization
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization
open SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessIndependence
open SemanticRepairFiniteQueryTargetSurfaceSupportBoundarySquare

universe u v w x y

/-! ## Obstruction side of the support boundary square -/

/--
If the canonical support-shadow representation has no raw current-shadow
factorization, then none of the equivalent support-boundary faces can hold:
support-control, current-shadow-reading faithfulness, and the explicit
coordinate certificate all fail.
-/
theorem no_supportTraceShadowBoundary_of_no_currentShadowFactor
    {Atom : Type u}
    (support : List Atom)
    (hnofactor :
      ¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          canonicalSupportTraceProbeTowerLayerShadow support T =
            factor (canonicalTowerLayerShadow T)) :
    (¬ CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
      (Atom := Atom) support) ∧
    (¬ SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (supportTraceShadowFiniteTraceQueryObservation support).post) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      support := by
  exact
    ⟨fun hcontrol =>
        hnofactor
          ((supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowDeterminesSupportTraceShadow
            (Atom := Atom) support).2 hcontrol),
      fun hfaithful =>
        hnofactor
          ((supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowSemanticReading_faithful
            (Atom := Atom) support).2 hfaithful),
      fun hcert =>
        hnofactor
          ((supportTraceShadowRepresentation_currentShadowFactor_iff_queryCurrentShadowCoordinateCertificate
            (Atom := Atom) support).2 hcert)⟩

/--
The complete Bool support-shadow witness recovers Bool `[true]` readings but
misses every face of the support boundary square: no raw current-shadow
factorization, no support-control, no current-shadow-reading faithfulness, and
no explicit coordinate certificate.
-/
theorem boolCompleteSupportTraceShadow_recovery_noSupportBoundarySquare :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
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
  have hbase :=
    boolCompleteSupportTraceShadow_recovery_noFaithfulness_noSupportControl_noCurrentFactor_noCoordinateCertificate
  have hblocked :=
    no_supportTraceShadowBoundary_of_no_currentShadowFactor
      (Atom := Bool)
      boolCompleteTraceSupport
      hbase.2.2.2.1
  exact
    ⟨hbase.1,
      hbase.2.2.2.1,
      hblocked.1,
      hblocked.2.1,
      hblocked.2.2⟩

end SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryObstruction
end QualitySurface
end Formal.AG.Research
