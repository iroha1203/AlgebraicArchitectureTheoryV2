import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationRecoveredFactorization
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorFactorizationBoundary

/-!
Cycle 63 evidence for `G-aat-quality-surface-04`.

The previous cycles protected the recovery boundary against hidden weakening.
This file records the adjacent positive route for canonical finite support
shadows: when the visible support coordinates are current-shadow extensional,
the canonical support-shadow representation recovers its readings, has
semantic-reading adequacy, factors through the current shadow, and therefore
enters target-surface universal factorization.

The coordinate-extensionality premise remains visible.  This is a finite-query
support-shadow route, not arbitrary semantic observation adequacy or target
theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportShadowRoute

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationSupportRecovery
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization
open SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorFactorizationBoundary
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r

/-! ## Support-shadow recovery and current-shadow route -/

/--
For the canonical support-shadow representation, visible current-shadow
extensionality of the support coordinates simultaneously gives recovery,
semantic-reading adequacy, and raw current-shadow factorization.
-/
theorem supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (support : List Atom)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support) :
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T) ∧
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) ∧
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        (supportTraceShadowFiniteTraceQueryObservation support).observe T =
          factor (canonicalTowerLayerShadow T)) := by
  exact
    ⟨supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings
        (Atom := Atom) support,
      (supportTraceShadowRepresentation_semanticReadingAdequacy_iff_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) support).2 hcoords,
      (supportTraceShadowRepresentation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) support).2 hcoords⟩

/--
The same visible support-coordinate current-shadow extensionality routes the
canonical support-shadow representation into target-surface universal
factorization.
-/
theorem targetSurfaceSupportTraceShadowRepresentation_universalFactorization_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    ((fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor
        (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          (supportTraceShadowFiniteTraceQueryObservation support).observe U =
            factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor
            (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
              (supportTraceShadowFiniteTraceQueryObservation support).observe T)
            (targetSurfaceLayerShadow A certificates)) := by
  have hfactor :
      ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          (supportTraceShadowFiniteTraceQueryObservation support).observe T =
            factor (canonicalTowerLayerShadow T) :=
    (supportTraceShadowRepresentation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) support).2 hcoords
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_currentShadowFactor
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation support)
      hfactor
      A certificates

/--
Combined support-shadow route package: visible coordinate extensionality gives
recovery, semantic adequacy, current-shadow factorization, and target-surface
universal factorization.
-/
theorem supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T) ∧
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) ∧
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        (supportTraceShadowFiniteTraceQueryObservation support).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    (((fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor
        (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          (supportTraceShadowFiniteTraceQueryObservation support).observe U =
            factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor
            (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
              (supportTraceShadowFiniteTraceQueryObservation support).observe T)
            (targetSurfaceLayerShadow A certificates))) := by
  have hlocal :=
    supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) support hcoords
  exact
    ⟨hlocal.1,
      hlocal.2.1,
      hlocal.2.2,
      targetSurfaceSupportTraceShadowRepresentation_universalFactorization_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) support hcoords A certificates⟩

end SemanticRepairFiniteQueryTargetSurfaceSupportShadowRoute
end QualitySurface
end Formal.AG.Research
