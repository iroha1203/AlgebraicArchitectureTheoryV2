import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorFactorizationBoundary
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceNoSeparationIndependence

/-!
Cycle 60 evidence for `G-aat-quality-surface-04`.

Cycle 58 made raw current-shadow factorization exact with assignment entry, and
Cycle 59 routed that factorization into target-surface universal factorization.
This file records the anti-weakening boundary: raw current-shadow factorization
still does not imply query-reading recovery or an explicit query-coordinate
current-shadow certificate.

The Bool constant post-map has raw current-shadow factorization and
no-separation, and it enters target-surface universal factorization; its
`[true]` query still has no coordinate certificate and no realized recovery.
Thus recovery and coordinate certificates remain visible theorem data, not
hidden consequences of factorization, entry, or target-surface certificates.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorIndependence

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceRecoveryIndependence
open SemanticRepairFiniteQueryTargetSurfaceCoordinateIndependence
open SemanticRepairFiniteQueryTargetSurfaceNoSeparationIndependence
open SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorBoundary
open SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorFactorizationBoundary
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe z r

/-! ## Raw factorization does not recover coordinates -/

/--
The Bool constant represented observation has raw current-shadow factorization,
but its query has no explicit current-shadow coordinate certificate.
-/
theorem boolTrueConstantPost_currentShadowFactor_but_not_queryCurrentShadowCoordinateCertificate :
    (∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  have hentry :
      ∃ assignment :
        ShadowExtensionalObstructionAssignment (Atom := Bool) Bool,
        assignment.observe =
          (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
            (boolTrueFiniteTraceQueryObservation
              (fun _shadow _readings => false)).observe T) :=
    boolTrueConstantPost_shadowExtensionalAssignment_but_not_queryCurrentShadowCoordinateCertificate.1
  exact
    ⟨(representedFiniteTraceQueryObservation_currentShadowFactor_iff_entry
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservationRepresentation
        (fun _shadow _readings => false))).2 hentry,
      not_boolTrueTraceQueryCurrentShadowCoordinateCertificate⟩

/--
Raw current-shadow factorization also does not imply realized-tower
query-reading recovery.
-/
theorem boolTrueConstantPost_currentShadowFactor_but_not_observationRecoversQueryReadings :
    (∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    ¬ ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T) := by
  exact
    ⟨boolTrueConstantPost_currentShadowFactor_but_not_queryCurrentShadowCoordinateCertificate.1,
      not_boolTrueConstantFiniteTraceQueryObservation_observationRecoversQueryReadings⟩

/--
Even raw current-shadow factorization plus no-separation does not imply an
explicit coordinate certificate.
-/
theorem boolTrueConstantPost_currentShadowFactor_noSeparation_but_not_queryCurrentShadowCoordinateCertificate :
    (∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    (¬ QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false)) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  exact
    ⟨boolTrueConstantPost_currentShadowFactor_but_not_queryCurrentShadowCoordinateCertificate.1,
      boolTrueConstantPost_no_queryPostFiberSeparation,
      not_boolTrueTraceQueryCurrentShadowCoordinateCertificate⟩

/--
Raw current-shadow factorization and target-surface universal factorization
together still do not imply an explicit coordinate certificate.
-/
theorem boolTrueConstantPost_currentShadowFactor_targetSurfaceUniversalFactorization_but_not_queryCurrentShadowCoordinateCertificate
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface.{0, 0, 0, 0, 0, z, r}
        Bool Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    (∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    (((fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T)
        (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          (boolTrueFiniteTraceQueryObservation
            (fun _shadow _readings => false)).observe T)
        (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Bool,
        (∀ U : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
          (boolTrueFiniteTraceQueryObservation
            (fun _shadow _readings => false)).observe U =
            factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor
            (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
              (boolTrueFiniteTraceQueryObservation
                (fun _shadow _readings => false)).observe T)
            (targetSurfaceLayerShadow A certificates))) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  exact
    ⟨boolTrueConstantPost_currentShadowFactor_but_not_queryCurrentShadowCoordinateCertificate.1,
      boolTrueConstantPost_targetSurfaceUniversalFactorization_but_not_queryCurrentShadowCoordinateCertificate
        A certificates⟩

end SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorIndependence
end QualitySurface
end ResearchLean.AG
