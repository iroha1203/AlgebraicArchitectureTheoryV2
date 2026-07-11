import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationCurrentShadowReading

/-!
Cycle 37 evidence for `G-aat-quality-surface-04`.

Cycle 36 exposed canonical current-shadow reading faithfulness as an exact
criterion for represented finite-query observations.  This file identifies the
support-level certificate that discharges that criterion: the current canonical
shadow must determine the finite support trace shadow.

The result remains a support node.  `CurrentShadowDeterminesSupportTraceShadow`
is a visible theorem argument / concrete certificate, not a hidden field in the
representation package and not a target-completion premise discharge.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationSupportControl

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryRepresentationCurrentShadowReading

universe u v w x y z

/-! ## The support-shadow observation -/

/-- A support list is always supported by itself as a finite query. -/
theorem supportSelfQuerySupportedBy
    {Atom : Type u}
    (support : List Atom) :
    QuerySupportedBy support support := by
  intro atom hmem
  exact hmem

/--
The post-map that reconstructs a support trace shadow from the current layer
and the support trace readings.
-/
def supportTraceShadowPost :
    FiniteTowerLayerShadow -> List Bool -> TraceProbeFiniteTowerLayerShadow :=
  fun shadow readings =>
    { layer := shadow
      sourceTraceReadings := readings }

/--
The canonical finite-query package whose generated observation is exactly the
finite support trace shadow.
-/
def supportTraceShadowFiniteTraceQueryObservation
    {Atom : Type u}
    (support : List Atom) :
    FiniteTraceQueryObservation support TraceProbeFiniteTowerLayerShadow where
  query := support
  query_supported := supportSelfQuerySupportedBy support
  post := supportTraceShadowPost

/-- The support-shadow package observes the canonical support trace shadow. -/
theorem supportTraceShadowFiniteTraceQueryObservation_observe_eq
    {Atom : Type u}
    (support : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (supportTraceShadowFiniteTraceQueryObservation support).observe T =
      canonicalSupportTraceProbeTowerLayerShadow support T := by
  rfl

/--
A visible representation certificate for the canonical support trace shadow
observation.
-/
def supportTraceShadowFiniteTraceQueryObservationRepresentation
    {Atom : Type u}
    (support : List Atom) :
    FiniteTraceQueryObservationRepresentation support
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        canonicalSupportTraceProbeTowerLayerShadow support T) where
  package := supportTraceShadowFiniteTraceQueryObservation support
  represents := by
    intro T
    rfl

/-! ## Support control is the exact faithfulness criterion -/

/--
If the current shadow determines the concrete query trace shadow, every post-map
is invariant on realized current-shadow query fibers.
-/
theorem postInvariantOnCurrentShadowFibers_of_currentShadowDeterminesTraceQuery
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hcurrent :
      CurrentShadowDeterminesTraceQuery.{u, v, w, x, y} query) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  intro shadow leftReadings rightReadings hleft hright
  rcases hleft with ⟨left, hleftShadow, hleftReadings⟩
  rcases hright with ⟨right, hrightShadow, hrightReadings⟩
  have hsameShadow :
      canonicalTowerLayerShadow left =
        canonicalTowerLayerShadow right := by
    rw [hleftShadow, hrightShadow]
  have hsupport :
      canonicalSupportTraceProbeTowerLayerShadow query left =
        canonicalSupportTraceProbeTowerLayerShadow query right :=
    hcurrent left right hsameShadow
  have hreadings :
      supportTraceVector query left.sourceTraceToken =
        supportTraceVector query right.sourceTraceToken :=
    congrArg TraceProbeFiniteTowerLayerShadow.sourceTraceReadings hsupport
  calc
    post shadow leftReadings =
        post (canonicalTowerLayerShadow left)
          (supportTraceVector query left.sourceTraceToken) := by
      rw [hleftShadow, hleftReadings]
    _ = post (canonicalTowerLayerShadow right)
          (supportTraceVector query right.sourceTraceToken) := by
      rw [hsameShadow, hreadings]
    _ = post shadow rightReadings := by
      rw [hrightShadow, hrightReadings]

/--
Query-trace determinacy discharges canonical current-shadow reading faithfulness
for any post-map on that query.
-/
theorem currentShadowSemanticReading_faithfulToQueryPost_of_currentShadowDeterminesTraceQuery
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hcurrent :
      CurrentShadowDeterminesTraceQuery.{u, v, w, x, y} query) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      query post := by
  exact
    (currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) query post).2
      (postInvariantOnCurrentShadowFibers_of_currentShadowDeterminesTraceQuery
        (Atom := Atom) hcurrent)

/--
Package version: query-trace determinacy discharges current-shadow reading
faithfulness for a finite query observation.
-/
theorem finiteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesTraceQuery
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hcurrent :
      CurrentShadowDeterminesTraceQuery.{u, v, w, x, y} obs.query) :
    SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      obs := by
  exact
    currentShadowSemanticReading_faithfulToQueryPost_of_currentShadowDeterminesTraceQuery
      (Atom := Atom) hcurrent

/--
Represented-observation version: query-trace determinacy discharges canonical
current-shadow reading faithfulness for the representing package.
-/
theorem representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesTraceQuery
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesTraceQuery.{u, v, w, x, y}
        repr.package.query) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post := by
  exact
    currentShadowSemanticReading_faithfulToQueryPost_of_currentShadowDeterminesTraceQuery
      (Atom := Atom) hcurrent

/--
Query-trace determinacy gives raw current-shadow factorization for a represented
finite-query observation.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowDeterminesTraceQuery
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesTraceQuery.{u, v, w, x, y}
        repr.package.query) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  exact
    representedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowSemanticReading_faithful
      (Atom := Atom)
      repr
      (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesTraceQuery
        (Atom := Atom) repr hcurrent)

/--
Query-trace determinacy rules out separated post-fibers for a represented
finite-query observation.
-/
theorem no_queryPostFiberSeparation_of_representedFiniteTraceQueryObservation_currentShadowDeterminesTraceQuery
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesTraceQuery.{u, v, w, x, y}
        repr.package.query) :
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) repr.package.query repr.package.post := by
  exact
    no_queryPostFiberSeparation_of_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful
      (Atom := Atom)
      repr
      (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesTraceQuery
        (Atom := Atom) repr hcurrent)

/--
If the current shadow determines the support trace shadow, every represented
finite-query observation over that support is faithful for the canonical
current-shadow reading.
-/
theorem representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post := by
  exact
    representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_currentShadowDeterminesSupportTraceShadow
        (Atom := Atom) repr hcurrent)

/--
The support trace shadow is determined by the current shadow exactly when the
canonical support-shadow observation is faithful for the current-shadow reading.
-/
theorem currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful
    {Atom : Type u}
    (support : List Atom) :
    CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support ↔
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post := by
  constructor
  · intro hcurrent
    exact
      representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesSupportTraceShadow
        (Atom := Atom)
        (supportTraceShadowFiniteTraceQueryObservationRepresentation support)
        hcurrent
  · intro hfaithful left right hshadow
    have hext :
        ShadowExtensionalTowerObservation
          (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
            canonicalSupportTraceProbeTowerLayerShadow support T) :=
      representedFiniteTraceQueryObservation_shadowExtensional_of_currentShadowSemanticReading_faithful
        (Atom := Atom)
        (supportTraceShadowFiniteTraceQueryObservationRepresentation support)
        hfaithful
    exact hext left right hshadow

/-! ## Concrete positive and obstruction boundaries -/

/--
The empty support discharges current-shadow reading faithfulness for every
represented finite-query observation over that support.
-/
theorem nilSupport_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful
    {Atom : Type u}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation ([] : List Atom) observe) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post := by
  exact
    representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_currentShadowDeterminesSupportTraceShadow
      (Atom := Atom)
      repr
      nilCurrentShadowDeterminesSupportTraceShadow

/--
The complete Bool support cannot satisfy the support-control criterion, so the
support-shadow observation cannot be faithful for the current-shadow reading.
-/
theorem not_boolCompleteSupportTraceShadowObservation_currentShadowSemanticReading_faithful :
    ¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (supportTraceShadowFiniteTraceQueryObservation
        SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport).query
      (supportTraceShadowFiniteTraceQueryObservation
        SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport).post := by
  intro hfaithful
  have hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{0, 0, 0, 0, 0}
        (Atom := Bool)
        SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport :=
    (currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful
      (Atom := Bool)
      SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport).2
      hfaithful
  exact
    not_currentShadowDetermines_boolCompleteSupportTraceShadow hcurrent

end SemanticRepairFiniteQueryRepresentationSupportControl
end QualitySurface
end ResearchLean.AG
