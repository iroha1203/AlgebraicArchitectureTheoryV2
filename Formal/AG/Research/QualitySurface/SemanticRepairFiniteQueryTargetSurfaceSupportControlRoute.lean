import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportShadowRoute
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQuerySupportedCurrentShadowFactorization

/-!
Cycle 66 evidence for `G-aat-quality-surface-04`.

Cycle 63 routed canonical support-shadow representations from visible
support-coordinate current-shadow extensionality into recovery, semantic
adequacy, current-shadow factorization, and target-surface universal
factorization.  This file packages the same route under the operational
support-control premise that the current shadow determines the chosen support
trace shadow.

The support-control premise remains visible theorem data.  This is a finite
support-shadow route, not arbitrary semantic observation adequacy or target
theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSupportControlRoute

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairCurrentShadowCoordinateObligations
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQuerySupportedCurrentShadowFactorization
open SemanticRepairFiniteQueryTargetSurfaceSupportShadowRoute
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r

/-! ## Support-control route to target-surface factorization -/

/--
If the current shadow determines the chosen support trace shadow, the canonical
support-shadow representation recovers its readings, has semantic-reading
adequacy, and factors through the current shadow.
-/
theorem supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    (support : List Atom)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
        (Atom := Atom) support) :
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
    supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      support
      ((currentShadowDeterminesSupportTraceShadow_iff_coordinateCurrentShadowExtensional
        (Atom := Atom) support).1 hcurrent)

/--
The same visible support-control premise routes the canonical support-shadow
representation into target-surface universal factorization.
-/
theorem targetSurfaceSupportTraceShadowRepresentation_universalFactorization_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
        (Atom := Atom) support)
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
  exact
    targetSurfaceSupportTraceShadowRepresentation_universalFactorization_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      support
      ((currentShadowDeterminesSupportTraceShadow_iff_coordinateCurrentShadowExtensional
        (Atom := Atom) support).1 hcurrent)
      A certificates

/--
Combined support-control route package: current-shadow determinacy of the
support trace shadow gives recovery, semantic adequacy, current-shadow
factorization, and target-surface universal factorization.
-/
theorem supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
        (Atom := Atom) support)
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
  exact
    supportTraceShadowRepresentation_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      support
      ((currentShadowDeterminesSupportTraceShadow_iff_coordinateCurrentShadowExtensional
        (Atom := Atom) support).1 hcurrent)
      A certificates

end SemanticRepairFiniteQueryTargetSurfaceSupportControlRoute
end QualitySurface
end Formal.AG.Research
