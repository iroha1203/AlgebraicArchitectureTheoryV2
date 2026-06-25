import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationRealizedRecovery

/-!
Cycle 50 evidence for `G-aat-quality-surface-04`.

Cycle 47 showed that represented finite-query observations enter the
target-surface finite-shadow factorization API when their post-map is
current-shadow invariant.  Cycle 48/49 related that entry surface to explicit
coordinate certificates and post-fiber separation.  This file records the
missing anti-weakening boundary: target-surface entry is not query-reading
recovery.

The Bool constant post-map is represented, shadow-extensional, and factors
through the target-surface finite shadow.  It still cannot recover Bool
`[true]` query readings on realized towers.  Recovery therefore remains a
visible theorem premise; it is not hidden in assignment entry, target-surface
certificates, typeclass assumptions, or representation certificates.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceRecoveryIndependence

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe z r

/-! ## Recovery-independent entry witness -/

/--
The Bool constant represented observation has no decoder recovering the Bool
`[true]` query readings on realized towers.
-/
theorem not_boolTrueConstantFiniteTraceQueryObservation_observationRecoversQueryReadings :
    ¬ ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T) := by
  intro hrecover
  exact
    not_boolTrueConstantPost_queryReadingsRecoveringPostOnRealizedTowers
      (queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
        (Atom := Bool)
        (boolTrueFiniteTraceQueryObservationRepresentation
          (fun _shadow _readings => false))
        hrecover)

/--
The Bool constant represented observation enters the shadow-extensional
assignment surface, but it still has no realized-tower query-reading decoder.
-/
theorem boolTrueConstantPost_shadowExtensionalAssignment_but_not_observationRecoversQueryReadings :
    (∃ assignment :
      ShadowExtensionalObstructionAssignment (Atom := Bool) Bool,
      assignment.observe =
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          (boolTrueFiniteTraceQueryObservation
            (fun _shadow _readings => false)).observe T)) ∧
    ¬ ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T) := by
  refine
    ⟨?_,
      not_boolTrueConstantFiniteTraceQueryObservation_observationRecoversQueryReadings⟩
  refine
    ⟨representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_postInvariant
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservationRepresentation
        (fun _shadow _readings => false))
      ?_,
      rfl⟩
  intro _shadow _leftReadings _rightReadings _hleft _hright
  rfl

/--
Even target-surface pointwise finite-shadow factorization does not imply
realized-tower query-reading recovery.
-/
theorem boolTrueConstantPost_targetSurfaceFactorization_but_not_observationRecoversQueryReadings
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
    ((fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T)
        (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          (boolTrueFiniteTraceQueryObservation
            (fun _shadow _readings => false)).observe T)
        (targetSurfaceLayerShadow A certificates)) ∧
    ¬ ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T) := by
  refine
    ⟨?_,
      not_boolTrueConstantFiniteTraceQueryObservation_observationRecoversQueryReadings⟩
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_postInvariant
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservationRepresentation
        (fun _shadow _readings => false))
      (by
        intro _shadow _leftReadings _rightReadings _hleft _hright
        rfl)
      A certificates

/--
The full target-surface factorization-and-uniqueness package is also
independent of realized-tower query-reading recovery.
-/
theorem boolTrueConstantPost_targetSurfaceUniversalFactorization_but_not_observationRecoversQueryReadings
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
    ¬ ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T) := by
  refine
    ⟨?_,
      not_boolTrueConstantFiniteTraceQueryObservation_observationRecoversQueryReadings⟩
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_postInvariant
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservationRepresentation
        (fun _shadow _readings => false))
      (by
        intro _shadow _leftReadings _rightReadings _hleft _hright
        rfl)
      A certificates

end SemanticRepairFiniteQueryTargetSurfaceRecoveryIndependence
end QualitySurface
end Formal.AG.Research
