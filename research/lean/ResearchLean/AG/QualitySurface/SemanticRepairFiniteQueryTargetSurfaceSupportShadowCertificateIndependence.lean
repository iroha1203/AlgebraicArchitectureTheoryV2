import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateRoute
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationRecoveredFactorization

/-!
Cycle 65 evidence for `G-aat-quality-surface-04`.

Cycle 64 gave a positive route from an explicit support-coordinate certificate
to support-shadow recovery, semantic adequacy, current-shadow factorization, and
target-surface universal factorization.  This file records the adjacent
anti-weakening boundary: complete support-shadow recovery itself does not
produce that explicit coordinate certificate.

For the complete Bool support shadow, the support shadow recovers Bool `[true]`
readings, but the support shadow still has no current-shadow factor.  If an
explicit coordinate certificate for the complete support existed, Cycle 64 would
produce such a factor.  Therefore the certificate premise remains visible.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateIndependence

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization
open SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateRoute

/-! ## Complete support recovery is not a coordinate certificate -/

/--
The complete Bool support list has no explicit current-shadow coordinate
certificate.

If it had one, the Cycle 64 certificate route would give a current-shadow factor
for the complete Bool support-shadow observation, contradicting the Cycle 42
anti-weakening witness.
-/
theorem not_boolCompleteTraceSupport_queryCurrentShadowCoordinateCertificate :
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolCompleteTraceSupport := by
  intro hcert
  have hroute :=
    supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
      (Atom := Bool) boolCompleteTraceSupport hcert
  rcases hroute.2.2 with ⟨factor, hfactor⟩
  exact
    boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_no_currentShadowFactor.2
      ⟨factor, by
        intro T
        simpa [supportTraceShadowFiniteTraceQueryObservation_observe_eq] using
          hfactor T⟩

/--
The complete Bool support shadow recovers Bool `[true]` readings, but still has
no explicit current-shadow coordinate certificate for the full support list.
-/
theorem boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_not_queryCurrentShadowCoordinateCertificate :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolCompleteTraceSupport := by
  exact
    ⟨boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_no_currentShadowFactor.1,
      not_boolCompleteTraceSupport_queryCurrentShadowCoordinateCertificate⟩

/--
Complete Bool support-shadow recovery, lack of current-shadow factorization,
and lack of an explicit coordinate certificate hold together.
-/
theorem boolCompleteSupportTraceShadow_recovery_noCurrentFactor_noCoordinateCertificate :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    (¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
          factor (canonicalTowerLayerShadow T)) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolCompleteTraceSupport := by
  exact
    ⟨boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_no_currentShadowFactor.1,
      boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_no_currentShadowFactor.2,
      not_boolCompleteTraceSupport_queryCurrentShadowCoordinateCertificate⟩

end SemanticRepairFiniteQueryTargetSurfaceSupportShadowCertificateIndependence
end QualitySurface
end ResearchLean.AG
