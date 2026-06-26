import Formal.AG.Research.QualitySurface.SemanticRepairTraceAwareShadow

/-!
Cycle 15 evidence for `G-aat-quality-surface-04`.

This file extends the one-coordinate trace-aware shadow from Cycle 14 to a
finite list of supplied source-trace probes.  The probes are input geometry:
they are not asserted to be complete, runtime-extracted, or sufficient for all
semantic observations.

The result remains a support node.  It proves factorization only for the
listed probe vector and observations generated from the current four-bit layer
plus that vector.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairTraceProbeShadow

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteShadowSeparation
open SemanticRepairTraceAwareShadow

universe u v w x y z

/-! ## Finite trace-probe shadow -/

/-- A supplied Boolean source-trace probe. -/
abbrev SourceTraceProbe (Atom : Type u) :=
  (Atom -> Bool) -> Bool

/--
A finite trace-probe enrichment of the current four-bit finite shadow.

The list of readings records exactly the supplied probe family.  No completeness
or extraction-correctness claim is stored in this structure.
-/
structure TraceProbeFiniteTowerLayerShadow where
  layer : FiniteTowerLayerShadow
  sourceTraceReadings : List Bool

/-- Read all supplied trace probes from a source-trace token. -/
def traceProbeReadings
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (traceToken : Atom -> Bool) : List Bool :=
  probes.map (fun probe => probe traceToken)

/-- The canonical finite trace-probe shadow for a supplied probe family. -/
def canonicalTraceProbeTowerLayerShadow
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    TraceProbeFiniteTowerLayerShadow where
  layer := canonicalTowerLayerShadow T
  sourceTraceReadings := traceProbeReadings probes T.sourceTraceToken

/-- The trace-probe shadow projects back to the current four-bit shadow. -/
theorem traceProbeShadow_projects_to_currentShadow
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (canonicalTraceProbeTowerLayerShadow probes T).layer =
      canonicalTowerLayerShadow T := by
  rfl

/-- The trace-probe shadow records the supplied probe readings definitionally. -/
theorem traceProbeShadow_sourceTraceReadings_eq
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (canonicalTraceProbeTowerLayerShadow probes T).sourceTraceReadings =
      traceProbeReadings probes T.sourceTraceToken := by
  rfl

/-- Read the entire supplied probe vector from a trace-probe shadow. -/
def traceProbeVectorFactor
    (shadow : TraceProbeFiniteTowerLayerShadow) : List Bool :=
  shadow.sourceTraceReadings

/-- The entire supplied probe vector factors through the trace-probe shadow. -/
theorem traceProbeVectorObservation_factors_through_traceProbeShadow
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom)) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> List Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        traceProbeReadings probes T.sourceTraceToken =
          factor (canonicalTraceProbeTowerLayerShadow probes T) := by
  exact ⟨traceProbeVectorFactor, by intro T; rfl⟩

/-- Equal trace-probe shadows have equal supplied probe vectors. -/
theorem traceProbeVectorObservation_same_of_same_traceProbeShadow
    {Atom : Type u}
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {probes : List (SourceTraceProbe Atom)}
    (hshadow :
      canonicalTraceProbeTowerLayerShadow probes left =
        canonicalTraceProbeTowerLayerShadow probes right) :
    traceProbeReadings probes left.sourceTraceToken =
      traceProbeReadings probes right.sourceTraceToken := by
  exact congrArg TraceProbeFiniteTowerLayerShadow.sourceTraceReadings hshadow

/-- Read the layer and supplied probe vector through a post-processing map. -/
def traceProbeGeneratedFactor
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out)
    (shadow : TraceProbeFiniteTowerLayerShadow) : Out :=
  post shadow.layer shadow.sourceTraceReadings

/--
Extensionality relative to the finite trace-probe shadow.

This is a necessary property for factorization through the enriched shadow; it
is not a completeness or semantic-soundness assertion.
-/
def TraceProbeShadowExtensional
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    {Out : Type z}
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out) :
    Prop :=
  ∀ left right : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
    canonicalTraceProbeTowerLayerShadow probes left =
      canonicalTraceProbeTowerLayerShadow probes right ->
    observe left = observe right

/--
Any observation generated from the current four-bit layer and the supplied
probe vector factors through the trace-probe shadow.
-/
theorem traceProbeGeneratedObservation_factors_through_traceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    (probes : List (SourceTraceProbe Atom))
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (traceProbeReadings probes T.sourceTraceToken) =
          factor (canonicalTraceProbeTowerLayerShadow probes T) := by
  exact ⟨traceProbeGeneratedFactor post, by intro T; rfl⟩

/--
Observations generated from the four-bit layer and supplied probe vector are
extensional for the trace-probe shadow.
-/
theorem traceProbeGeneratedObservation_same_of_same_traceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {probes : List (SourceTraceProbe Atom)}
    (post : FiniteTowerLayerShadow -> List Bool -> Out)
    (hshadow :
      canonicalTraceProbeTowerLayerShadow probes left =
        canonicalTraceProbeTowerLayerShadow probes right) :
    post (canonicalTowerLayerShadow left)
        (traceProbeReadings probes left.sourceTraceToken) =
      post (canonicalTowerLayerShadow right)
        (traceProbeReadings probes right.sourceTraceToken) := by
  exact congrArg (traceProbeGeneratedFactor post) hshadow

/-! ## Probe-aware finite assignment interface -/

/--
A finite probe-aware semantic repair obstruction assignment.

The assignment is visibly generated from a supplied finite source-trace probe
family and a post-map from the current finite layer shadow plus the probe
reading vector.  The probes are input geometry; this structure does not store
trace completeness, extraction correctness, semantic faithfulness, global
coherence, obstruction vanishing, descent effectiveness, or an arbitrary
extensionality premise.
-/
structure TraceProbeSemanticRepairObstructionAssignment
    {Atom : Type u}
    (Out : Type z) where
  probes : List (SourceTraceProbe Atom)
  post : FiniteTowerLayerShadow -> List Bool -> Out

/-- The tower observation generated by a probe-aware assignment. -/
def traceProbeAssignmentObserve
    {Atom : Type u}
    {Out : Type z}
    (assignment : TraceProbeSemanticRepairObstructionAssignment
      (Atom := Atom) Out)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    Out :=
  assignment.post (canonicalTowerLayerShadow T)
    (traceProbeReadings assignment.probes T.sourceTraceToken)

/-- The induced factor on the enriched trace-probe shadow. -/
def traceProbeAssignmentFactor
    {Atom : Type u}
    {Out : Type z}
    (assignment : TraceProbeSemanticRepairObstructionAssignment
      (Atom := Atom) Out)
    (shadow : TraceProbeFiniteTowerLayerShadow) :
    Out :=
  assignment.post shadow.layer shadow.sourceTraceReadings

/--
Every finite probe-aware assignment factors through the trace-probe enriched
tower shadow generated by its supplied probe family.
-/
theorem traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    (assignment : TraceProbeSemanticRepairObstructionAssignment
      (Atom := Atom) Out) :
    ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      traceProbeAssignmentObserve assignment T =
        traceProbeAssignmentFactor assignment
          (canonicalTraceProbeTowerLayerShadow assignment.probes T) := by
  intro T
  rfl

/--
Finite probe-aware assignments are extensional for equality of the enriched
trace-probe shadow.
-/
theorem traceProbeSemanticRepairObstructionAssignment_extensional_on_traceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    (assignment : TraceProbeSemanticRepairObstructionAssignment
      (Atom := Atom) Out) :
    TraceProbeShadowExtensional
      (Atom := Atom)
      assignment.probes
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        traceProbeAssignmentObserve assignment T) := by
  intro left right hshadow
  calc
    traceProbeAssignmentObserve assignment left =
        traceProbeAssignmentFactor assignment
          (canonicalTraceProbeTowerLayerShadow assignment.probes left) :=
      traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeShadow
        assignment left
    _ = traceProbeAssignmentFactor assignment
          (canonicalTraceProbeTowerLayerShadow assignment.probes right) := by
      rw [hshadow]
    _ = traceProbeAssignmentObserve assignment right :=
      (traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeShadow
        assignment right).symm

/--
Any observation that factors through the trace-probe shadow is trace-probe
extensional.
-/
theorem traceProbeShadowExtensional_of_factorization
    {Atom : Type u}
    {Out : Type z}
    {probes : List (SourceTraceProbe Atom)}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (factor : TraceProbeFiniteTowerLayerShadow -> Out)
    (hfactor :
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T =
          factor (canonicalTraceProbeTowerLayerShadow probes T)) :
    TraceProbeShadowExtensional probes observe := by
  intro left right hshadow
  calc
    observe left = factor (canonicalTraceProbeTowerLayerShadow probes left) :=
      hfactor left
    _ = factor (canonicalTraceProbeTowerLayerShadow probes right) := by
      rw [hshadow]
    _ = observe right := (hfactor right).symm

/--
An observation extensional for the current four-bit shadow is also extensional
for any trace-probe enrichment, because equality of enriched shadows includes
equality of their four-bit layer.
-/
theorem traceProbeShadowExtensional_of_currentShadowExtensional
    {Atom : Type u}
    {Out : Type z}
    {probes : List (SourceTraceProbe Atom)}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (extensional : ShadowExtensionalTowerObservation observe) :
    TraceProbeShadowExtensional probes observe := by
  intro left right hshadow
  exact
    extensional left right
      (congrArg TraceProbeFiniteTowerLayerShadow.layer hshadow)

/--
Four-bit shadow-extensional observations factor through every trace-probe
enrichment by forgetting the trace readings.
-/
theorem currentShadowExtensionalObservation_factors_through_traceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    (probes : List (SourceTraceProbe Atom))
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (factor : FiniteTowerLayerShadow -> Out)
    (hfactor :
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) :
    ∃ traceFactor : TraceProbeFiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T =
          traceFactor (canonicalTraceProbeTowerLayerShadow probes T) := by
  exact ⟨fun shadow => factor shadow.layer, by intro T; exact hfactor T⟩

/-- Convert a singleton probe shadow to the one-coordinate trace-aware shadow. -/
def singletonTraceProbeAsTraceAware
    (shadow : TraceProbeFiniteTowerLayerShadow) :
    TraceAwareFiniteTowerLayerShadow where
  layer := shadow.layer
  sourceTrace := shadow.sourceTraceReadings.headD false

/-- Cycle 14's trace-aware shadow is the singleton case of trace-probe shadow. -/
theorem singletonTraceProbeShadow_is_traceAwareShadow
    {Atom : Type u}
    (traceCoordinate : SourceTraceProbe Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    singletonTraceProbeAsTraceAware
        (canonicalTraceProbeTowerLayerShadow [traceCoordinate] T) =
      canonicalTraceAwareTowerLayerShadow traceCoordinate T := by
  rfl

/-! ## Cycle 13 witness through the finite probe family -/

/-- The singleton family containing the Cycle 13 source-trace coordinate. -/
def selectedSourceTraceProbeFamily :
    List (SourceTraceProbe PUnit.{u + 1}) :=
  [punitSourceTraceCoordinate]

/-- The Cycle 13 source-trace observation factors through the singleton probe shadow. -/
theorem sourceTraceObservation_factors_through_traceProbeShadow :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T :
        FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0} PUnit.{u + 1},
        sourceTraceObservation T =
          factor
            (canonicalTraceProbeTowerLayerShadow
              selectedSourceTraceProbeFamily T) := by
  exact
    ⟨fun shadow => shadow.sourceTraceReadings.headD false,
      by intro T; rfl⟩

/--
The Cycle 13 pair that the current four-bit shadow identifies is separated by
the singleton trace-probe readings.
-/
theorem selected_traceTrue_traceProbeShadow_readings_ne :
    (canonicalTraceProbeTowerLayerShadow selectedSourceTraceProbeFamily
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1})).sourceTraceReadings ≠
      (canonicalTraceProbeTowerLayerShadow selectedSourceTraceProbeFamily
        selectedFiniteSemanticRepairObstructionTower_traceTrue).sourceTraceReadings := by
  decide

/--
The same pair still agrees after forgetting the trace-probe readings back to
the current four-bit shadow.
-/
theorem selected_traceTrue_traceProbeShadow_layer_agrees :
    (canonicalTraceProbeTowerLayerShadow selectedSourceTraceProbeFamily
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1})).layer =
      (canonicalTraceProbeTowerLayerShadow selectedSourceTraceProbeFamily
        selectedFiniteSemanticRepairObstructionTower_traceTrue).layer := by
  exact selected_traceTrue_same_canonicalShadow.{u}

end SemanticRepairTraceProbeShadow
end QualitySurface
end Formal.AG.Research
