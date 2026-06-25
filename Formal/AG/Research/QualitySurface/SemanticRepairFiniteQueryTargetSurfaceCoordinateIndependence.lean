import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceRecoveryIndependence
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryExplicitCurrentShadowCertificates

/-!
Cycle 51 evidence for `G-aat-quality-surface-04`.

Cycle 50 showed that target-surface entry does not imply realized
query-reading recovery.  This file fixes the adjacent anti-weakening boundary:
target-surface entry does not imply an explicit query-coordinate current-shadow
certificate either.

The Bool constant post-map enters the assignment and target-surface
factorization APIs by post-invariance.  Its represented query is still the Bool
`[true]` query, whose coordinate is not current-shadow certified.  Theorem
statements therefore keep `QueryCurrentShadowCoordinateCertificate` as visible
data; it is not hidden inside assignment entry, factorization, target-surface
certificates, or representation certificates.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceCoordinateIndependence

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceRecoveryIndependence
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe z r

/-! ## Coordinate-certificate-independent entry witness -/

/--
The Bool `[true]` query has no explicit current-shadow coordinate
certificate.
-/
theorem not_boolTrueTraceQueryCurrentShadowCoordinateCertificate :
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  intro cert
  exact
    not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional
      ((queryCoordinateCurrentShadowExtensional_iff_certificate
        (Atom := Bool) boolTrueTraceQuery).2 cert)

/--
The Bool constant represented observation enters the assignment surface, but
its query has no current-shadow coordinate certificate.
-/
theorem boolTrueConstantPost_shadowExtensionalAssignment_but_not_queryCurrentShadowCoordinateCertificate :
    (∃ assignment :
      ShadowExtensionalObstructionAssignment (Atom := Bool) Bool,
      assignment.observe =
        (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
          (boolTrueFiniteTraceQueryObservation
            (fun _shadow _readings => false)).observe T)) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  exact
    ⟨boolTrueConstantPost_shadowExtensionalAssignment_but_not_observationRecoversQueryReadings.1,
      not_boolTrueTraceQueryCurrentShadowCoordinateCertificate⟩

/--
Even target-surface pointwise finite-shadow factorization does not imply a
query-coordinate current-shadow certificate.
-/
theorem boolTrueConstantPost_targetSurfaceFactorization_but_not_queryCurrentShadowCoordinateCertificate
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
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  exact
    ⟨(boolTrueConstantPost_targetSurfaceFactorization_but_not_observationRecoversQueryReadings
        A certificates).1,
      not_boolTrueTraceQueryCurrentShadowCoordinateCertificate⟩

/--
The full target-surface factorization-and-uniqueness package is also
independent of query-coordinate current-shadow certificates.
-/
theorem boolTrueConstantPost_targetSurfaceUniversalFactorization_but_not_queryCurrentShadowCoordinateCertificate
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
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  exact
    ⟨(boolTrueConstantPost_targetSurfaceUniversalFactorization_but_not_observationRecoversQueryReadings
        A certificates).1,
      not_boolTrueTraceQueryCurrentShadowCoordinateCertificate⟩

end SemanticRepairFiniteQueryTargetSurfaceCoordinateIndependence
end QualitySurface
end Formal.AG.Research
