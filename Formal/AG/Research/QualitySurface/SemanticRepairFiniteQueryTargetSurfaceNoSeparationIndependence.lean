import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceCoordinateIndependence
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryPostFiberObstruction

/-!
Cycle 52 evidence for `G-aat-quality-surface-04`.

Cycle 49 connected post-fiber separation to coordinate-certificate obstruction,
with the exact no-separation / coordinate-certificate equivalence stated only
under visible recovery.  This file records why that recovery premise is
essential: no post-fiber separation alone does not recover query readings and
does not produce a query-coordinate current-shadow certificate.

The Bool constant post-map has no separated post-fiber, enters target-surface
factorization by the Cycle 50/51 entry witnesses, and still fails both recovery
and coordinate certification.  Thus no-separation remains an obstruction
boundary, not semantic soundness or target completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceNoSeparationIndependence

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceRecoveryIndependence
open SemanticRepairFiniteQueryTargetSurfaceCoordinateIndependence
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe z r

/-! ## No-separation is not recovery or coordinate certification -/

/--
The Bool constant post-map has no separated current-shadow post-fiber.
-/
theorem boolTrueConstantPost_no_queryPostFiberSeparation :
    ¬ QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false) := by
  intro hsep
  rcases hsep with
    ⟨_shadow, _leftReadings, _rightReadings, _hleft, _hright, hne⟩
  exact hne rfl

/--
No separated post-fiber does not imply realized-tower query-reading recovery.
-/
theorem boolTrueConstantPost_noSeparation_but_not_queryReadingsRecoveringPostOnRealizedTowers :
    (¬ QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false)) ∧
    ¬ QueryReadingsRecoveringPostOnRealizedTowers.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false) := by
  exact
    ⟨boolTrueConstantPost_no_queryPostFiberSeparation,
      not_boolTrueConstantPost_queryReadingsRecoveringPostOnRealizedTowers⟩

/--
No separated post-fiber does not imply an explicit query-coordinate
current-shadow certificate.
-/
theorem boolTrueConstantPost_noSeparation_but_not_queryCurrentShadowCoordinateCertificate :
    (¬ QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false)) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{0, 0, 0, 0, 0}
      boolTrueTraceQuery := by
  exact
    ⟨boolTrueConstantPost_no_queryPostFiberSeparation,
      not_boolTrueTraceQueryCurrentShadowCoordinateCertificate⟩

/--
Even no-separation plus target-surface universal factorization does not imply
an explicit query-coordinate current-shadow certificate.
-/
theorem boolTrueConstantPost_noSeparation_targetSurfaceUniversalFactorization_but_not_queryCurrentShadowCoordinateCertificate
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
    (¬ QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false)) ∧
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
    ⟨boolTrueConstantPost_no_queryPostFiberSeparation,
      boolTrueConstantPost_targetSurfaceUniversalFactorization_but_not_queryCurrentShadowCoordinateCertificate
        A certificates⟩

end SemanticRepairFiniteQueryTargetSurfaceNoSeparationIndependence
end QualitySurface
end Formal.AG.Research
