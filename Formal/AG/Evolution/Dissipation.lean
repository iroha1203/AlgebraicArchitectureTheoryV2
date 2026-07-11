import Formal.AG.Evolution.ReplayDescent

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R6 / AC14--AC15 evolution functionals and dissipative policies.

This file defines the measurement-relative value reading `Phi_M`, selected
dissipative steps, terminal predicates, strict decrease outside terminal
states, and path-wise non-increase / strict-decrease predicates.  The finite
stopping theorem is intentionally left to R7.
-/

/--
IX.§5.1 / AC14: measurement-relative evolution functional `Phi_M`.

The value type and preorder are selected data.  Optional representative
readings are exposed as predicates over the selected Part VIII measurement domain;
they do not assert any empirical calibration or forecast outside the selected
profile.
-/
structure EvolutionFunctional {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T) where
  measurementProfile : Measurement.MeasurementProfile.{w, x}
  measurementProfile_eq : measurementProfile = E.measurementProfile
  Value : Type (max w x y z)
  valuePreorder : Preorder Value
  read : (p : T.Point) -> St.State p -> Value
  minimum : Value -> Prop
  obstructionMassReading : E.measurementProfile.Domain -> Value -> Prop
  harmonicMassReading : E.measurementProfile.Domain -> Value -> Prop
  distanceToFlatnessReading : E.measurementProfile.Domain -> Value -> Prop
  transferResidueNormReading : E.measurementProfile.Domain -> Value -> Prop

namespace EvolutionFunctional

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}

/-- IX.§5.1 / AC14: read the value of `Phi_M` at a selected temporal state. -/
def value (Phi : EvolutionFunctional St) (p : T.Point) (s : St.State p) :
    Phi.Value :=
  Phi.read p s

/-- IX.§5.1 / AC14: the functional is relative to the selected Part VIII profile. -/
theorem measurement_profile_selected (Phi : EvolutionFunctional St) :
    Phi.measurementProfile = E.measurementProfile :=
  Phi.measurementProfile_eq

end EvolutionFunctional

/--
IX.§5.2 / AC14: dissipative policy over selected evolution steps.

The `Step` type is the selected step universe.  No statement is made about
transitions outside this type.
-/
structure DissipativePolicy {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    (Phi : EvolutionFunctional St) where
  Step : Type (max u w x y z)
  source : Step -> T.Point
  target : Step -> T.Point
  sourceState : (step : Step) -> St.State (source step)
  targetState : (step : Step) -> St.State (target step)
  incidence : (step : Step) -> T.IncidenceLeg (source step) (target step)
  selectedEvolutionStep : Step -> Prop
  selectedEvolutionStep_cert : ∀ step : Step, selectedEvolutionStep step
  nonIncrease :
    ∀ step : Step,
      letI := Phi.valuePreorder
      Phi.value (target step) (targetState step) <=
        Phi.value (source step) (sourceState step)

namespace DissipativePolicy

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}

/-- IX.§5.2 / AC14: selected steps are selected temporal incidence legs. -/
def selectedIncidence (P : DissipativePolicy Phi) (step : P.Step) :
    T.IncidenceLeg (P.source step) (P.target step) :=
  P.incidence step

/-- IX.§5.2 / AC14: selected dissipative steps are non-increasing for `Phi_M`. -/
theorem step_nonIncrease (P : DissipativePolicy Phi) (step : P.Step) :
    letI := Phi.valuePreorder
    Phi.value (P.target step) (P.targetState step) <=
      Phi.value (P.source step) (P.sourceState step) :=
  P.nonIncrease step

/-- IX.§5.2 / AC14: every policy step is explicitly selected. -/
theorem step_selected (P : DissipativePolicy Phi) (step : P.Step) :
    P.selectedEvolutionStep step :=
  P.selectedEvolutionStep_cert step

/--
IX.§5.2 / AC15: adjacent selected steps connect as a path.

The target temporal point of the first step is the source temporal point of the
next step, and the target state transports along that equality to the next
source state.
-/
def StepConnect (P : DissipativePolicy Phi) (first next : P.Step) : Prop :=
  ∃ h : P.target first = P.source next,
    h ▸ P.targetState first = P.sourceState next

end DissipativePolicy

/--
IX.§5.2 / AC14: selected terminal and lawful predicates.

The lawful predicate is kept separate from terminality; terminal states are not
automatically lawful in R6.
-/
structure TerminalState {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    (Phi : EvolutionFunctional St) where
  terminal : (p : T.Point) -> St.State p -> Prop
  lawful : (p : T.Point) -> St.State p -> Prop

namespace TerminalState

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}

/-- IX.§5.2 / AC14: non-terminality is the complement of the selected terminal predicate. -/
def NonTerminal (Term : TerminalState Phi) (p : T.Point) (s : St.State p) : Prop :=
  ¬ Term.terminal p s

/-- IX.§5.2 boundary: terminality does not imply lawfulness without an explicit premise. -/
def TerminalLawfulAssumption (Term : TerminalState Phi) : Prop :=
  ∀ p s, Term.terminal p s -> Term.lawful p s

end TerminalState

/--
IX.§5.2 / AC14: strict dissipativity outside terminal states.

Strict decrease is only required for selected policy steps whose source state
is non-terminal.
-/
structure StrictlyDissipativeOutsideTerminal {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {E : EvolutionProfile.{u, v, w, x, y, z}} {T : TemporalSite S E}
    {St : StateTransitionPresheaf T} {Phi : EvolutionFunctional St}
    (P : DissipativePolicy Phi) (Term : TerminalState Phi) where
  strictDecrease :
    ∀ step : P.Step,
      Term.NonTerminal (P.source step) (P.sourceState step) ->
        letI := Phi.valuePreorder
        Phi.value (P.target step) (P.targetState step) <
          Phi.value (P.source step) (P.sourceState step)

namespace StrictlyDissipativeOutsideTerminal

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/-- IX.§5.2 / AC14: selected non-terminal steps strictly decrease `Phi_M`. -/
theorem step_strictDecrease (Strict : StrictlyDissipativeOutsideTerminal P Term)
    (step : P.Step)
    (hNonTerminal : Term.NonTerminal (P.source step) (P.sourceState step)) :
    letI := Phi.valuePreorder
    Phi.value (P.target step) (P.targetState step) <
      Phi.value (P.source step) (P.sourceState step) :=
  Strict.strictDecrease step hNonTerminal

end StrictlyDissipativeOutsideTerminal

/--
IX.§5.2 / AC15: selected finite evolution path.

The path is a finite list of selected policy steps.  R6 records path-wise
predicates; R7 will add the well-founded stopping package.
-/
structure SelectedEvolutionPath {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Phi : EvolutionFunctional St} (P : DissipativePolicy Phi) where
  length : Nat
  step : Fin length -> P.Step
  continuous :
    ∀ (i : Fin length) (hnext : i.val + 1 < length),
      P.StepConnect (step i) (step ⟨i.val + 1, hnext⟩)

namespace SelectedEvolutionPath

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/-- IX.§5.2 / AC15: all selected path steps are non-increasing. -/
def PathwiseNonIncrease (path : SelectedEvolutionPath P) : Prop :=
  ∀ i : Fin path.length,
    letI := Phi.valuePreorder
    Phi.value (P.target (path.step i)) (P.targetState (path.step i)) <=
      Phi.value (P.source (path.step i)) (P.sourceState (path.step i))

/-- IX.§5.2 / AC15: all selected non-terminal path steps strictly decrease. -/
def PathwiseStrictDecreaseOutsideTerminal
    (path : SelectedEvolutionPath P) : Prop :=
  ∀ i : Fin path.length,
    Term.NonTerminal (P.source (path.step i)) (P.sourceState (path.step i)) ->
      letI := Phi.valuePreorder
      Phi.value (P.target (path.step i)) (P.targetState (path.step i)) <
        Phi.value (P.source (path.step i)) (P.sourceState (path.step i))

/-- IX.§5.2 / AC15: adjacent steps in a selected path are connected. -/
theorem adjacent_steps_connect (path : SelectedEvolutionPath P)
    (i : Fin path.length) (hnext : i.val + 1 < path.length) :
    P.StepConnect (path.step i) (path.step ⟨i.val + 1, hnext⟩) :=
  path.continuous i hnext

/-- IX.§5.2 / AC15: a dissipative policy gives path-wise non-increase. -/
theorem pathwise_nonIncrease (path : SelectedEvolutionPath P) :
    path.PathwiseNonIncrease := by
  intro i
  exact P.step_nonIncrease (path.step i)

/-- IX.§5.2 / AC15: strict dissipativity gives path-wise strict decrease off terminals. -/
theorem pathwise_strictDecreaseOutsideTerminal
    (Strict : StrictlyDissipativeOutsideTerminal P Term)
    (path : SelectedEvolutionPath P) :
    SelectedEvolutionPath.PathwiseStrictDecreaseOutsideTerminal (Term := Term) path := by
  intro i hNonTerminal
  exact Strict.step_strictDecrease (path.step i) hNonTerminal

end SelectedEvolutionPath

end Evolution
end AAT.AG
