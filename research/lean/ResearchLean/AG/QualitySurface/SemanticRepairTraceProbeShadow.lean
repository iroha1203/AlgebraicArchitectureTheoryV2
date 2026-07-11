import ResearchLean.AG.QualitySurface.SemanticRepairTraceAwareShadow

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

namespace ResearchLean.AG
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

/-! ## Probe-generated admissible observations -/

/--
A non-circular admissible observation surface for supplied trace probes.

This is only an alias for the generated assignment syntax above.  It stores the
supplied probes and a post-map from the current four-bit layer plus the supplied
probe-reading vector.  It does not store factorization, extensionality,
faithfulness, completeness, or runtime extraction correctness as fields.
-/
abbrev TraceProbeGeneratedAdmissibleObservation
    {Atom : Type u}
    (Out : Type z) :=
  TraceProbeSemanticRepairObstructionAssignment (Atom := Atom) Out

/--
Every probe-generated admissible observation factors through its trace-probe
shadow.  The factorization is derived from the generated syntax, not assumed as
the admissibility definition.
-/
theorem traceProbeGeneratedAdmissibleObservation_factors_through_traceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    (obs : TraceProbeGeneratedAdmissibleObservation (Atom := Atom) Out) :
    ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      traceProbeAssignmentObserve obs T =
        traceProbeAssignmentFactor obs
          (canonicalTraceProbeTowerLayerShadow obs.probes T) := by
  exact traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeShadow obs

/--
Every probe-generated admissible observation is extensional for equality of its
trace-probe shadow.
-/
theorem traceProbeGeneratedAdmissibleObservation_extensional_on_traceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    (obs : TraceProbeGeneratedAdmissibleObservation (Atom := Atom) Out) :
    TraceProbeShadowExtensional
      (Atom := Atom)
      obs.probes
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        traceProbeAssignmentObserve obs T) := by
  exact traceProbeSemanticRepairObstructionAssignment_extensional_on_traceProbeShadow obs

/-! ## Trace-probe ArchSig-style bounded artifact surface -/

/--
A bounded ArchSig-style finite artifact enriched with supplied trace-probe
readings.

This is a Lean-side finite artifact shape.  The probe readings are supplied
input geometry; the structure does not assert ArchMap / ArchSig runtime
extraction correctness, trace completeness, semantic faithfulness, global
coherence, obstruction vanishing, descent effectiveness, or target completion.
-/
structure TraceProbeArchSigStyleFiniteShadowArtifact where
  measuredH1 : Bool
  measuredTorsor : Bool
  measuredHigher : Bool
  measuredStack : Bool
  sourceTraceReadings : List Bool
  recordsBoundedEvidence : Bool
  recordsNonConclusions : Bool

/-- Read a trace-probe ArchSig-style artifact as an enriched finite shadow. -/
def traceProbeArchSigStyleArtifactShadow
    (artifact : TraceProbeArchSigStyleFiniteShadowArtifact) :
    TraceProbeFiniteTowerLayerShadow where
  layer :=
    { h1 := artifact.measuredH1
      torsor := artifact.measuredTorsor
      higher := artifact.measuredHigher
      stack := artifact.measuredStack }
  sourceTraceReadings := artifact.sourceTraceReadings

/-- Forget trace-probe readings back to the four-layer ArchSig-style artifact. -/
def traceProbeArchSigStyleArtifact_project
    (artifact : TraceProbeArchSigStyleFiniteShadowArtifact) :
    ArchSigStyleFiniteShadowArtifact where
  measuredH1 := artifact.measuredH1
  measuredTorsor := artifact.measuredTorsor
  measuredHigher := artifact.measuredHigher
  measuredStack := artifact.measuredStack
  recordsBoundedEvidence := artifact.recordsBoundedEvidence
  recordsNonConclusions := artifact.recordsNonConclusions

/-- Build the bounded trace-probe artifact associated to an enriched shadow. -/
def traceProbeArchSigStyleArtifactOfShadow
    (shadow : TraceProbeFiniteTowerLayerShadow) :
    TraceProbeArchSigStyleFiniteShadowArtifact where
  measuredH1 := shadow.layer.h1
  measuredTorsor := shadow.layer.torsor
  measuredHigher := shadow.layer.higher
  measuredStack := shadow.layer.stack
  sourceTraceReadings := shadow.sourceTraceReadings
  recordsBoundedEvidence := true
  recordsNonConclusions := true

/-- Build the bounded trace-probe artifact associated to a finite tower. -/
def traceProbeArchSigStyleArtifactOfTower
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    TraceProbeArchSigStyleFiniteShadowArtifact :=
  traceProbeArchSigStyleArtifactOfShadow
    (canonicalTraceProbeTowerLayerShadow probes T)

/--
The bounded trace-probe artifact of a tower factors through the enriched
trace-probe shadow.
-/
theorem traceProbeArchSigStyleArtifactOfTower_factors_through_traceProbeShadow
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    traceProbeArchSigStyleArtifactShadow
        (traceProbeArchSigStyleArtifactOfTower probes T) =
      canonicalTraceProbeTowerLayerShadow probes T := by
  rfl

/--
Forgetting probe readings recovers the existing four-layer ArchSig-style
artifact of the same tower.
-/
theorem traceProbeArchSigStyleArtifact_projects_to_archSigStyleArtifactShadow
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    archSigStyleArtifactShadow
        (traceProbeArchSigStyleArtifact_project
          (traceProbeArchSigStyleArtifactOfTower probes T)) =
      archSigStyleArtifactShadow (archSigStyleArtifactOfTower T) := by
  rfl

/-- The bounded trace-probe artifact records evidence and non-conclusion flags. -/
theorem traceProbeArchSigStyleArtifact_records_boundary
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (traceProbeArchSigStyleArtifactOfTower probes T).recordsBoundedEvidence =
        true /\
      (traceProbeArchSigStyleArtifactOfTower probes T).recordsNonConclusions =
        true := by
  exact ⟨rfl, rfl⟩

/-- The bounded trace-probe artifact stores exactly the supplied probe readings. -/
theorem traceProbeArchSigStyleArtifact_probeReadings_eq
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (traceProbeArchSigStyleArtifactOfTower probes T).sourceTraceReadings =
      traceProbeReadings probes T.sourceTraceToken := by
  rfl

/--
Every probe-generated admissible observation factors through the bounded
trace-probe artifact surface.
-/
theorem traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeArtifact
    {Atom : Type u}
    {Out : Type z}
    (assignment : TraceProbeSemanticRepairObstructionAssignment
      (Atom := Atom) Out) :
    ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      traceProbeAssignmentObserve assignment T =
        traceProbeAssignmentFactor assignment
          (traceProbeArchSigStyleArtifactShadow
            (traceProbeArchSigStyleArtifactOfTower assignment.probes T)) := by
  intro T
  calc
    traceProbeAssignmentObserve assignment T =
        traceProbeAssignmentFactor assignment
          (canonicalTraceProbeTowerLayerShadow assignment.probes T) :=
      traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeShadow
        assignment T
    _ =
        traceProbeAssignmentFactor assignment
          (traceProbeArchSigStyleArtifactShadow
            (traceProbeArchSigStyleArtifactOfTower assignment.probes T)) := by
      rw [traceProbeArchSigStyleArtifactOfTower_factors_through_traceProbeShadow]

/--
Equal bounded trace-probe artifacts give the same value for every
probe-generated admissible observation.
-/
theorem traceProbeSemanticRepairObstructionAssignment_same_of_same_traceProbeArtifact
    {Atom : Type u}
    {Out : Type z}
    (assignment : TraceProbeSemanticRepairObstructionAssignment
      (Atom := Atom) Out)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hartifact :
      traceProbeArchSigStyleArtifactOfTower assignment.probes left =
        traceProbeArchSigStyleArtifactOfTower assignment.probes right) :
    traceProbeAssignmentObserve assignment left =
      traceProbeAssignmentObserve assignment right := by
  calc
    traceProbeAssignmentObserve assignment left =
        traceProbeAssignmentFactor assignment
          (traceProbeArchSigStyleArtifactShadow
            (traceProbeArchSigStyleArtifactOfTower assignment.probes left)) :=
      traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeArtifact
        assignment left
    _ =
        traceProbeAssignmentFactor assignment
          (traceProbeArchSigStyleArtifactShadow
            (traceProbeArchSigStyleArtifactOfTower assignment.probes right)) := by
      rw [hartifact]
    _ = traceProbeAssignmentObserve assignment right :=
      (traceProbeSemanticRepairObstructionAssignment_factors_through_traceProbeArtifact
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
end ResearchLean.AG
