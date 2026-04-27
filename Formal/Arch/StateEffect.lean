import Formal.Arch.Lawfulness

namespace Formal.Arch

universe u v w

/--
Minimal expression language for state-transition history laws.

The constructors distinguish the syntactic origin of an observation while
leaving interpretation to `Semantics`.
-/
inductive StateTransitionExpr (State : Type u) (Event : Type v) : Type (max u v) where
  | state : State -> StateTransitionExpr State Event
  | history : State -> List Event -> StateTransitionExpr State Event
  | replay : State -> List Event -> StateTransitionExpr State Event
  | roundtrip : State -> List Event -> List Event -> StateTransitionExpr State Event
  | compensated :
      State -> List Event -> List Event -> StateTransitionExpr State Event

/--
Minimal expression language for effect-boundary laws.

This keeps runtime effects and boundary policies in the diagram layer without
claiming that a concrete extractor is complete.
-/
inductive EffectBoundaryExpr (Effect : Type u) (Boundary : Type v) : Type (max u v) where
  | effect : Effect -> EffectBoundaryExpr Effect Boundary
  | through : Boundary -> Effect -> EffectBoundaryExpr Effect Boundary
  | trace : Boundary -> List Effect -> EffectBoundaryExpr Effect Boundary
  | replay : Boundary -> List Effect -> EffectBoundaryExpr Effect Boundary
  | roundtrip : Boundary -> Effect -> EffectBoundaryExpr Effect Boundary
  | compensated :
      Boundary -> Effect -> Effect -> EffectBoundaryExpr Effect Boundary

/-- A required diagram is lawful when every required equality commutes. -/
def DiagramLawful {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) (required : RequiredDiagram Expr -> Prop) :
    Prop :=
  ∀ d, required d -> DiagramCommutes sem d

/-- No required diagram obstruction witness exists. -/
def NoDiagramObstruction {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) (required : RequiredDiagram Expr -> Prop) :
    Prop :=
  ∀ d, required d -> ¬ DiagramBad sem d

/--
Diagram lawfulness is equivalent to the absence of required diagram
obstruction witnesses.
-/
theorem diagramLawful_iff_noDiagramObstruction
    {Expr : Type u} {Obs : Type v}
    {sem : Semantics Expr Obs}
    {required : RequiredDiagram Expr -> Prop} :
    DiagramLawful sem required ↔ NoDiagramObstruction sem required := by
  classical
  constructor
  · intro hLawful d hRequired hBad
    exact hBad (hLawful d hRequired)
  · intro hNoBad d hRequired
    exact Classical.byContradiction (fun hNotCommutes =>
      hNoBad d hRequired hNotCommutes)

/-- A finite list of required diagrams is lawful when every listed diagram commutes. -/
def DiagramLawfulByList {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) (required : List (RequiredDiagram Expr)) :
    Prop :=
  DiagramLawful sem (RequiredDiagramsByList required)

/-- No obstruction witness exists in a finite required diagram list. -/
def NoDiagramObstructionByList {Expr : Type u} {Obs : Type v}
    (sem : Semantics Expr Obs) (required : List (RequiredDiagram Expr)) :
    Prop :=
  NoDiagramObstruction sem (RequiredDiagramsByList required)

/--
Finite-list diagram lawfulness is equivalent to absence of listed diagram
obstruction witnesses.
-/
theorem diagramLawfulByList_iff_noDiagramObstructionByList
    {Expr : Type u} {Obs : Type v}
    {sem : Semantics Expr Obs}
    {required : List (RequiredDiagram Expr)} :
    DiagramLawfulByList sem required ↔ NoDiagramObstructionByList sem required := by
  exact diagramLawful_iff_noDiagramObstruction

/-- One replay law case for a state-transition history. -/
structure StateReplayCase (State : Type u) (Event : Type v) : Type (max u v) where
  start : State
  events : List Event

/-- One roundtrip law case for a state-transition history. -/
structure StateRoundtripCase (State : Type u) (Event : Type v) : Type (max u v) where
  start : State
  forward : List Event
  backward : List Event

/-- One compensation law case for a state-transition history. -/
structure StateCompensationCase (State : Type u) (Event : Type v) : Type (max u v) where
  start : State
  events : List Event
  compensation : List Event

/-- Replay requires a recorded history and its replay to have the same observation. -/
def stateReplayDiagram {State : Type u} {Event : Type v}
    (c : StateReplayCase State Event) :
    RequiredDiagram (StateTransitionExpr State Event) where
  lhs := StateTransitionExpr.history c.start c.events
  rhs := StateTransitionExpr.replay c.start c.events

/-- Roundtrip requires a forward/backward transition sequence to return to the baseline. -/
def stateRoundtripDiagram {State : Type u} {Event : Type v}
    (c : StateRoundtripCase State Event) :
    RequiredDiagram (StateTransitionExpr State Event) where
  lhs := StateTransitionExpr.state c.start
  rhs := StateTransitionExpr.roundtrip c.start c.forward c.backward

/-- Compensation requires a transition sequence plus compensation to match the baseline. -/
def stateCompensationDiagram {State : Type u} {Event : Type v}
    (c : StateCompensationCase State Event) :
    RequiredDiagram (StateTransitionExpr State Event) where
  lhs := StateTransitionExpr.state c.start
  rhs := StateTransitionExpr.compensated c.start c.events c.compensation

/-- Required replay diagrams for finite state-transition cases. -/
def stateReplayDiagrams {State : Type u} {Event : Type v}
    (cases : List (StateReplayCase State Event)) :
    List (RequiredDiagram (StateTransitionExpr State Event)) :=
  cases.map stateReplayDiagram

/-- Required roundtrip diagrams for finite state-transition cases. -/
def stateRoundtripDiagrams {State : Type u} {Event : Type v}
    (cases : List (StateRoundtripCase State Event)) :
    List (RequiredDiagram (StateTransitionExpr State Event)) :=
  cases.map stateRoundtripDiagram

/-- Required compensation diagrams for finite state-transition cases. -/
def stateCompensationDiagrams {State : Type u} {Event : Type v}
    (cases : List (StateCompensationCase State Event)) :
    List (RequiredDiagram (StateTransitionExpr State Event)) :=
  cases.map stateCompensationDiagram

/-- Replay lawfulness for finite state-transition cases. -/
def StateReplayLawful {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (cases : List (StateReplayCase State Event)) : Prop :=
  DiagramLawfulByList sem (stateReplayDiagrams cases)

/-- No replay obstruction witness exists for finite state-transition cases. -/
def NoStateReplayObstruction {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (cases : List (StateReplayCase State Event)) : Prop :=
  NoDiagramObstructionByList sem (stateReplayDiagrams cases)

/-- State replay lawfulness is exactly absence of replay obstruction witnesses. -/
theorem stateReplayLawful_iff_noStateReplayObstruction
    {State : Type u} {Event : Type v} {Obs : Type w}
    {sem : Semantics (StateTransitionExpr State Event) Obs}
    {cases : List (StateReplayCase State Event)} :
    StateReplayLawful sem cases ↔ NoStateReplayObstruction sem cases := by
  exact diagramLawfulByList_iff_noDiagramObstructionByList

/-- Roundtrip lawfulness for finite state-transition cases. -/
def StateRoundtripLawful {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (cases : List (StateRoundtripCase State Event)) : Prop :=
  DiagramLawfulByList sem (stateRoundtripDiagrams cases)

/-- No roundtrip obstruction witness exists for finite state-transition cases. -/
def NoStateRoundtripObstruction {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (cases : List (StateRoundtripCase State Event)) : Prop :=
  NoDiagramObstructionByList sem (stateRoundtripDiagrams cases)

/-- State roundtrip lawfulness is exactly absence of roundtrip obstruction witnesses. -/
theorem stateRoundtripLawful_iff_noStateRoundtripObstruction
    {State : Type u} {Event : Type v} {Obs : Type w}
    {sem : Semantics (StateTransitionExpr State Event) Obs}
    {cases : List (StateRoundtripCase State Event)} :
    StateRoundtripLawful sem cases ↔ NoStateRoundtripObstruction sem cases := by
  exact diagramLawfulByList_iff_noDiagramObstructionByList

/-- Compensation lawfulness for finite state-transition cases. -/
def StateCompensationLawful {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (cases : List (StateCompensationCase State Event)) : Prop :=
  DiagramLawfulByList sem (stateCompensationDiagrams cases)

/-- No compensation obstruction witness exists for finite state-transition cases. -/
def NoStateCompensationObstruction {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (cases : List (StateCompensationCase State Event)) : Prop :=
  NoDiagramObstructionByList sem (stateCompensationDiagrams cases)

/-- State compensation lawfulness is exactly absence of compensation obstruction witnesses. -/
theorem stateCompensationLawful_iff_noStateCompensationObstruction
    {State : Type u} {Event : Type v} {Obs : Type w}
    {sem : Semantics (StateTransitionExpr State Event) Obs}
    {cases : List (StateCompensationCase State Event)} :
    StateCompensationLawful sem cases ↔ NoStateCompensationObstruction sem cases := by
  exact diagramLawfulByList_iff_noDiagramObstructionByList

/-- One replay law case for effects crossing a boundary. -/
structure EffectReplayCase (Effect : Type u) (Boundary : Type v) : Type (max u v) where
  boundary : Boundary
  trace : List Effect

/-- One roundtrip law case for an effect crossing a boundary. -/
structure EffectRoundtripCase (Effect : Type u) (Boundary : Type v) : Type (max u v) where
  boundary : Boundary
  effect : Effect

/-- One compensation law case for an effect crossing a boundary. -/
structure EffectCompensationCase (Effect : Type u) (Boundary : Type v) : Type (max u v) where
  boundary : Boundary
  effect : Effect
  compensation : Effect

/-- Boundary replay requires replayed effects to match the boundary observation. -/
def effectReplayDiagram {Effect : Type u} {Boundary : Type v}
    (c : EffectReplayCase Effect Boundary) :
    RequiredDiagram (EffectBoundaryExpr Effect Boundary) where
  lhs := EffectBoundaryExpr.trace c.boundary c.trace
  rhs := EffectBoundaryExpr.replay c.boundary c.trace

/-- Boundary roundtrip requires crossing out and back to match the direct effect. -/
def effectRoundtripDiagram {Effect : Type u} {Boundary : Type v}
    (c : EffectRoundtripCase Effect Boundary) :
    RequiredDiagram (EffectBoundaryExpr Effect Boundary) where
  lhs := EffectBoundaryExpr.effect c.effect
  rhs := EffectBoundaryExpr.roundtrip c.boundary c.effect

/-- Boundary compensation requires a compensated effect to match its boundary form. -/
def effectCompensationDiagram {Effect : Type u} {Boundary : Type v}
    (c : EffectCompensationCase Effect Boundary) :
    RequiredDiagram (EffectBoundaryExpr Effect Boundary) where
  lhs := EffectBoundaryExpr.through c.boundary c.effect
  rhs := EffectBoundaryExpr.compensated c.boundary c.effect c.compensation

/-- Required replay diagrams for finite effect-boundary cases. -/
def effectReplayDiagrams {Effect : Type u} {Boundary : Type v}
    (cases : List (EffectReplayCase Effect Boundary)) :
    List (RequiredDiagram (EffectBoundaryExpr Effect Boundary)) :=
  cases.map effectReplayDiagram

/-- Required roundtrip diagrams for finite effect-boundary cases. -/
def effectRoundtripDiagrams {Effect : Type u} {Boundary : Type v}
    (cases : List (EffectRoundtripCase Effect Boundary)) :
    List (RequiredDiagram (EffectBoundaryExpr Effect Boundary)) :=
  cases.map effectRoundtripDiagram

/-- Required compensation diagrams for finite effect-boundary cases. -/
def effectCompensationDiagrams {Effect : Type u} {Boundary : Type v}
    (cases : List (EffectCompensationCase Effect Boundary)) :
    List (RequiredDiagram (EffectBoundaryExpr Effect Boundary)) :=
  cases.map effectCompensationDiagram

/-- Replay lawfulness for finite effect-boundary cases. -/
def EffectReplayLawful {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (cases : List (EffectReplayCase Effect Boundary)) : Prop :=
  DiagramLawfulByList sem (effectReplayDiagrams cases)

/-- No replay obstruction witness exists for finite effect-boundary cases. -/
def NoEffectReplayObstruction {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (cases : List (EffectReplayCase Effect Boundary)) : Prop :=
  NoDiagramObstructionByList sem (effectReplayDiagrams cases)

/-- Effect replay lawfulness is exactly absence of replay obstruction witnesses. -/
theorem effectReplayLawful_iff_noEffectReplayObstruction
    {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    {sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs}
    {cases : List (EffectReplayCase Effect Boundary)} :
    EffectReplayLawful sem cases ↔ NoEffectReplayObstruction sem cases := by
  exact diagramLawfulByList_iff_noDiagramObstructionByList

/-- Roundtrip lawfulness for finite effect-boundary cases. -/
def EffectRoundtripLawful {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (cases : List (EffectRoundtripCase Effect Boundary)) : Prop :=
  DiagramLawfulByList sem (effectRoundtripDiagrams cases)

/-- No roundtrip obstruction witness exists for finite effect-boundary cases. -/
def NoEffectRoundtripObstruction {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (cases : List (EffectRoundtripCase Effect Boundary)) : Prop :=
  NoDiagramObstructionByList sem (effectRoundtripDiagrams cases)

/-- Effect roundtrip lawfulness is exactly absence of roundtrip obstruction witnesses. -/
theorem effectRoundtripLawful_iff_noEffectRoundtripObstruction
    {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    {sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs}
    {cases : List (EffectRoundtripCase Effect Boundary)} :
    EffectRoundtripLawful sem cases ↔ NoEffectRoundtripObstruction sem cases := by
  exact diagramLawfulByList_iff_noDiagramObstructionByList

/-- Compensation lawfulness for finite effect-boundary cases. -/
def EffectCompensationLawful {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (cases : List (EffectCompensationCase Effect Boundary)) : Prop :=
  DiagramLawfulByList sem (effectCompensationDiagrams cases)

/-- No compensation obstruction witness exists for finite effect-boundary cases. -/
def NoEffectCompensationObstruction {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (cases : List (EffectCompensationCase Effect Boundary)) : Prop :=
  NoDiagramObstructionByList sem (effectCompensationDiagrams cases)

/-- Effect compensation lawfulness is exactly absence of compensation obstruction witnesses. -/
theorem effectCompensationLawful_iff_noEffectCompensationObstruction
    {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    {sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs}
    {cases : List (EffectCompensationCase Effect Boundary)} :
    EffectCompensationLawful sem cases ↔ NoEffectCompensationObstruction sem cases := by
  exact diagramLawfulByList_iff_noDiagramObstructionByList

/--
Aggregate lawfulness for the finite state-transition replay, roundtrip, and
compensation law family.
-/
def StateTransitionLawFamilyLawful {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (replayCases : List (StateReplayCase State Event))
    (roundtripCases : List (StateRoundtripCase State Event))
    (compensationCases : List (StateCompensationCase State Event)) : Prop :=
  StateReplayLawful sem replayCases ∧
  StateRoundtripLawful sem roundtripCases ∧
  StateCompensationLawful sem compensationCases

/-- No obstruction witness exists for the aggregate state-transition law family. -/
def NoStateTransitionLawFamilyObstruction {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs)
    (replayCases : List (StateReplayCase State Event))
    (roundtripCases : List (StateRoundtripCase State Event))
    (compensationCases : List (StateCompensationCase State Event)) : Prop :=
  NoStateReplayObstruction sem replayCases ∧
  NoStateRoundtripObstruction sem roundtripCases ∧
  NoStateCompensationObstruction sem compensationCases

/--
The aggregate state-transition law family is lawful exactly when the replay,
roundtrip, and compensation obstruction families are all absent.
-/
theorem stateTransitionLawFamilyLawful_iff_noStateTransitionLawFamilyObstruction
    {State : Type u} {Event : Type v} {Obs : Type w}
    {sem : Semantics (StateTransitionExpr State Event) Obs}
    {replayCases : List (StateReplayCase State Event)}
    {roundtripCases : List (StateRoundtripCase State Event)}
    {compensationCases : List (StateCompensationCase State Event)} :
    StateTransitionLawFamilyLawful sem replayCases roundtripCases compensationCases ↔
      NoStateTransitionLawFamilyObstruction sem replayCases roundtripCases
        compensationCases := by
  constructor
  · intro hLawful
    exact ⟨stateReplayLawful_iff_noStateReplayObstruction.mp hLawful.1,
      stateRoundtripLawful_iff_noStateRoundtripObstruction.mp hLawful.2.1,
      stateCompensationLawful_iff_noStateCompensationObstruction.mp hLawful.2.2⟩
  · intro hNoObstruction
    exact ⟨stateReplayLawful_iff_noStateReplayObstruction.mpr hNoObstruction.1,
      stateRoundtripLawful_iff_noStateRoundtripObstruction.mpr hNoObstruction.2.1,
      stateCompensationLawful_iff_noStateCompensationObstruction.mpr
        hNoObstruction.2.2⟩

/--
Aggregate lawfulness for the finite effect-boundary replay, roundtrip, and
compensation law family.
-/
def EffectBoundaryLawFamilyLawful {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (replayCases : List (EffectReplayCase Effect Boundary))
    (roundtripCases : List (EffectRoundtripCase Effect Boundary))
    (compensationCases : List (EffectCompensationCase Effect Boundary)) : Prop :=
  EffectReplayLawful sem replayCases ∧
  EffectRoundtripLawful sem roundtripCases ∧
  EffectCompensationLawful sem compensationCases

/-- No obstruction witness exists for the aggregate effect-boundary law family. -/
def NoEffectBoundaryLawFamilyObstruction {Effect : Type u} {Boundary : Type v}
    {Obs : Type w}
    (sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs)
    (replayCases : List (EffectReplayCase Effect Boundary))
    (roundtripCases : List (EffectRoundtripCase Effect Boundary))
    (compensationCases : List (EffectCompensationCase Effect Boundary)) : Prop :=
  NoEffectReplayObstruction sem replayCases ∧
  NoEffectRoundtripObstruction sem roundtripCases ∧
  NoEffectCompensationObstruction sem compensationCases

/--
The aggregate effect-boundary law family is lawful exactly when the replay,
roundtrip, and compensation obstruction families are all absent.
-/
theorem effectBoundaryLawFamilyLawful_iff_noEffectBoundaryLawFamilyObstruction
    {Effect : Type u} {Boundary : Type v} {Obs : Type w}
    {sem : Semantics (EffectBoundaryExpr Effect Boundary) Obs}
    {replayCases : List (EffectReplayCase Effect Boundary)}
    {roundtripCases : List (EffectRoundtripCase Effect Boundary)}
    {compensationCases : List (EffectCompensationCase Effect Boundary)} :
    EffectBoundaryLawFamilyLawful sem replayCases roundtripCases compensationCases ↔
      NoEffectBoundaryLawFamilyObstruction sem replayCases roundtripCases
        compensationCases := by
  constructor
  · intro hLawful
    exact ⟨effectReplayLawful_iff_noEffectReplayObstruction.mp hLawful.1,
      effectRoundtripLawful_iff_noEffectRoundtripObstruction.mp hLawful.2.1,
      effectCompensationLawful_iff_noEffectCompensationObstruction.mp hLawful.2.2⟩
  · intro hNoObstruction
    exact ⟨effectReplayLawful_iff_noEffectReplayObstruction.mpr hNoObstruction.1,
      effectRoundtripLawful_iff_noEffectRoundtripObstruction.mpr hNoObstruction.2.1,
      effectCompensationLawful_iff_noEffectCompensationObstruction.mpr
        hNoObstruction.2.2⟩

end Formal.Arch
