import Formal.AG.Evolution.Dissipation

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R7 / AC16 finite dissipation stopping.

Theorem 5.3 is split into two bounded statements:

* well-founded strict decrease rules out an infinite selected path that stays
  outside terminal states;
* if a finite selected path is maximal at a selected endpoint and every
  non-terminal endpoint is executable, then the path reaches a terminal state.

Terminality is kept separate from lawfulness.
-/

/-- A well-founded relation admits no infinite descending sequence. -/
theorem no_infinite_descending_sequence {α : Type u} (r : α -> α -> Prop)
    (wf : WellFounded r) :
    ¬ ∃ f : Nat -> α, ∀ n : Nat, r (f (n + 1)) (f n) := by
  rintro ⟨f, hf⟩
  have hacc : Acc r (f 0) := wf.apply (f 0)
  exact hacc.rec
    (motive := fun x _ => ∀ g : Nat -> α,
      g 0 = x -> (∀ n : Nat, r (g (n + 1)) (g n)) -> False)
    (fun x _ ih => by
      intro f h0 hf
      have hstep : r (f 1) x := by
        simpa [h0] using hf 0
      exact ih (f 1) hstep (fun n => f (n + 1)) rfl (by
        intro n
        simpa [Nat.add_assoc] using hf (n + 1)))
    f rfl hf

namespace DissipativePolicy

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable (P : DissipativePolicy Phi)

/-- IX.§5.3 / AC16: `Phi_M` value at the source of a selected step. -/
def sourceValue (step : P.Step) : Phi.Value :=
  Phi.value (P.source step) (P.sourceState step)

/-- IX.§5.3 / AC16: `Phi_M` value at the target of a selected step. -/
def targetValue (step : P.Step) : Phi.Value :=
  Phi.value (P.target step) (P.targetState step)

end DissipativePolicy

/--
IX.§5.3 / AC16: an infinite selected evolution path.

Each adjacent pair is connected in the R6 path sense.
-/
structure InfiniteSelectedEvolutionPath {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Phi : EvolutionFunctional St} (P : DissipativePolicy Phi) where
  step : Nat -> P.Step
  continuous : ∀ n : Nat, P.StepConnect (step n) (step (n + 1))
  valueContinuous : ∀ n : Nat, P.sourceValue (step (n + 1)) = P.targetValue (step n)

namespace InfiniteSelectedEvolutionPath

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/-- IX.§5.3 / AC16: source value along an infinite selected path. -/
def sourceValue (path : InfiniteSelectedEvolutionPath P) (n : Nat) :
    Phi.Value :=
  P.sourceValue (path.step n)

/-- IX.§5.3 / AC16: target value along an infinite selected path. -/
def targetValue (path : InfiniteSelectedEvolutionPath P) (n : Nat) :
    Phi.Value :=
  P.targetValue (path.step n)

/-- IX.§5.3 / AC16: the path stays outside terminal states at every source. -/
def StaysOutsideTerminal (path : InfiniteSelectedEvolutionPath P)
    (Term : TerminalState Phi) : Prop :=
  ∀ n : Nat, Term.NonTerminal (P.source (path.step n)) (P.sourceState (path.step n))

/-- IX.§5.3 / AC16: connectedness identifies the next source value with this target value. -/
theorem sourceValue_succ_eq_targetValue (path : InfiniteSelectedEvolutionPath P)
    (n : Nat) :
    path.sourceValue (n + 1) = path.targetValue n :=
  path.valueContinuous n

/-- IX.§5.3 / AC16: strict dissipativity gives strict descent of path values. -/
theorem sourceValue_strict_decrease
    (Strict : StrictlyDissipativeOutsideTerminal P Term)
    (path : InfiniteSelectedEvolutionPath P)
    (hNonTerminal : path.StaysOutsideTerminal Term) (n : Nat) :
    letI := Phi.valuePreorder
    path.sourceValue (n + 1) < path.sourceValue n := by
  have htarget :
      letI := Phi.valuePreorder
      path.targetValue n < path.sourceValue n := by
    simpa [sourceValue, targetValue, DissipativePolicy.sourceValue,
      DissipativePolicy.targetValue]
      using Strict.step_strictDecrease (path.step n) (hNonTerminal n)
  simpa [path.sourceValue_succ_eq_targetValue n] using htarget

end InfiniteSelectedEvolutionPath

/--
IX.§5.3 / AC16: finite dissipation stopping package.

The finite selected step evidence is recorded as part of the theorem package,
while the no-infinite-path theorem uses the well-founded value order and
strict decrease outside terminal states.
-/
structure FiniteDissipationStopping {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Phi : EvolutionFunctional St} (P : DissipativePolicy Phi)
    (Term : TerminalState Phi) where
  finiteSelectedSteps : Finite P.Step
  wellFoundedValue :
    letI := Phi.valuePreorder
    WellFounded (fun a b : Phi.Value => a < b)
  strict : StrictlyDissipativeOutsideTerminal P Term

namespace FiniteDissipationStopping

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/-- IX.§5.3 / AC16: read the selected finite step evidence. -/
theorem finite_selected_steps (D : FiniteDissipationStopping P Term) :
    Finite P.Step :=
  D.finiteSelectedSteps

/-- IX.§5.3 / AC16: no infinite selected path can stay outside terminals. -/
theorem no_infinite_nonterminal_path (D : FiniteDissipationStopping P Term) :
    ¬ ∃ path : InfiniteSelectedEvolutionPath P,
      path.StaysOutsideTerminal Term := by
  intro hpath
  rcases hpath with ⟨path, hNonTerminal⟩
  exact no_infinite_descending_sequence
    (fun a b : Phi.Value => by
      letI := Phi.valuePreorder
      exact a < b)
    D.wellFoundedValue
    ⟨path.sourceValue, fun n => path.sourceValue_strict_decrease D.strict hNonTerminal n⟩

end FiniteDissipationStopping

namespace SelectedEvolutionPath

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/-- IX.§5.3 / AC16: a finite selected path reaches a terminal source state. -/
def ReachesTerminal (path : SelectedEvolutionPath P)
    (Term : TerminalState Phi) : Prop :=
  ∃ i : Fin path.length,
    Term.terminal (P.source (path.step i)) (P.sourceState (path.step i))

/-- IX.§5.3 / AC16: a selected endpoint can be extended if it is non-terminal. -/
def EndpointExecutable (path : SelectedEvolutionPath P)
    (Term : TerminalState Phi) (last : Fin path.length) : Prop :=
  Term.NonTerminal (P.source (path.step last)) (P.sourceState (path.step last)) ->
    ∃ next : P.Step, P.StepConnect (path.step last) next

/-- IX.§5.3 / AC16: selected endpoint maximality. -/
def MaximalAt (path : SelectedEvolutionPath P) (last : Fin path.length) : Prop :=
  ¬ ∃ next : P.Step, P.StepConnect (path.step last) next

/--
IX.§5.3 / AC16: a maximal finite selected path reaches a terminal state.

This is the finite-path half of theorem 5.3.  Executability from the endpoint
is a selected premise; the theorem does not claim global executability or
terminal lawfulness.
-/
theorem maximal_path_reaches_terminal (path : SelectedEvolutionPath P)
    (last : Fin path.length)
    [Decidable (Term.terminal (P.source (path.step last)) (P.sourceState (path.step last)))]
    (hexecutable : path.EndpointExecutable Term last)
    (hmaximal : path.MaximalAt last) :
    path.ReachesTerminal Term := by
  by_cases hterminal :
      Term.terminal (P.source (path.step last)) (P.sourceState (path.step last))
  · exact ⟨last, hterminal⟩
  · exfalso
    exact hmaximal (hexecutable hterminal)

end SelectedEvolutionPath

end Evolution
end AAT.AG
