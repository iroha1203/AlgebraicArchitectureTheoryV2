import Formal.AG.Evolution.Dissipation

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R7 / AC16 finite dissipation stopping.

The primary theorem 5.3 proves finite-time terminal arrival for a
`PolicyGeneratedEvolutionPath`. Its proof reuses the supporting result that
well-founded strict decrease rules out an infinite selected path that stays
outside terminal states. The maximal finite-list theorem remains a separate
API bridge for explicitly bounded paths.

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
  P.selectedStateValue (P.sourceState step)

/-- IX.§5.3 / AC16: `Phi_M` value at the target of a selected step. -/
def targetValue (step : P.Step) : Phi.Value :=
  P.selectedStateValue (P.targetState step)

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
  ∀ n : Nat,
    Term.NonTerminal (P.sourcePoint (path.step n)) (P.sourceStateAt (path.step n))

/-- IX.§5.3 / AC16: connectedness identifies the next source value with this target value. -/
theorem sourceValue_succ_eq_targetValue (path : InfiniteSelectedEvolutionPath P)
    (n : Nat) :
    path.sourceValue (n + 1) = path.targetValue n := by
  change P.selectedStateValue (P.sourceState (path.step (n + 1))) =
    P.selectedStateValue (P.targetState (path.step n))
  exact congrArg P.selectedStateValue (path.continuous n).symm

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

The finite selected state evidence is recorded as part of the theorem package,
while the no-infinite-path theorem uses the well-founded value order and
strict decrease outside terminal states.
-/
structure FiniteDissipationStopping {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Phi : EvolutionFunctional St} (P : DissipativePolicy Phi)
    (Term : TerminalState Phi) where
  finiteSelectedStates : Finite P.SelectedState
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

/-- IX.§5.3 / AC16: read the selected finite-state evidence. -/
theorem finite_selected_states (D : FiniteDissipationStopping P Term) :
    Finite P.SelectedState :=
  D.finiteSelectedStates

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

/--
IX.§5.3 / AC16: a selected evolution path generated by a policy.

The state trajectory is explicit. A next selected step is required only when
the present state is non-terminal; the source and target equations tie that
step to consecutive trajectory states.

Implementation notes: terminality is not stored as a path field. Under the
assumption that every trajectory state is non-terminal, `nextStep` constructs
an infinite selected path, which can be discharged by the existing
well-founded strict-descent theorem.
-/
structure PolicyGeneratedEvolutionPath {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {E : EvolutionProfile.{u, v, w, x, y, z}} {T : TemporalSite S E}
    {St : StateTransitionPresheaf T} {Phi : EvolutionFunctional St}
    (P : DissipativePolicy Phi) (Term : TerminalState Phi) where
  state : Nat -> P.SelectedState
  nextStep : ∀ n : Nat,
    Term.NonTerminal (P.point (state n)) (P.state (state n)) -> P.Step
  step_source : ∀ (n : Nat)
    (hNonTerminal : Term.NonTerminal (P.point (state n)) (P.state (state n))),
      P.sourceState (nextStep n hNonTerminal) = state n
  step_target : ∀ (n : Nat)
    (hNonTerminal : Term.NonTerminal (P.point (state n)) (P.state (state n))),
      P.targetState (nextStep n hNonTerminal) = state (n + 1)

namespace PolicyGeneratedEvolutionPath

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/-- IX.§5.3 API: a non-terminal policy-generated path determines an infinite selected path. -/
noncomputable def toInfiniteSelectedEvolutionPath
    (path : PolicyGeneratedEvolutionPath P Term)
    (hNonTerminal : ∀ n : Nat,
      Term.NonTerminal (P.point (path.state n)) (P.state (path.state n))) :
    InfiniteSelectedEvolutionPath P where
  step := fun n => path.nextStep n (hNonTerminal n)
  continuous := by
    intro n
    exact (path.step_target n (hNonTerminal n)).trans
      (path.step_source (n + 1) (hNonTerminal (n + 1))).symm

/-- IX.§5.3 API: the constructed infinite path stays non-terminal. -/
theorem toInfiniteSelectedEvolutionPath_staysOutsideTerminal
    (path : PolicyGeneratedEvolutionPath P Term)
    (hNonTerminal : ∀ n : Nat,
      Term.NonTerminal (P.point (path.state n)) (P.state (path.state n))) :
    (path.toInfiniteSelectedEvolutionPath hNonTerminal).StaysOutsideTerminal Term := by
  intro n
  change Term.NonTerminal
    (P.point (P.sourceState (path.nextStep n (hNonTerminal n))))
    (P.state (P.sourceState (path.nextStep n (hNonTerminal n))))
  rw [path.step_source n (hNonTerminal n)]
  exact hNonTerminal n

end PolicyGeneratedEvolutionPath

namespace FiniteDissipationStopping

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/--
IX.§5.3: every selected policy-generated evolution path reaches a terminal
state at a finite time.

The finite selected state set, well-founded value order, and strict decrease
outside terminals are the three theorem-5.3 conditions carried by `D`.
The proof reuses `no_infinite_nonterminal_path`: if no terminal time existed,
the path API would generate an infinite non-terminal selected path.
-/
theorem policy_generated_path_reaches_terminal
    (D : FiniteDissipationStopping P Term)
    (path : PolicyGeneratedEvolutionPath P Term) :
    ∃ n : Nat, Term.terminal (P.point (path.state n)) (P.state (path.state n)) := by
  classical
  by_contra hNoTerminal
  have hNonTerminal : ∀ n : Nat,
      Term.NonTerminal (P.point (path.state n)) (P.state (path.state n)) := by
    intro n hTerminal
    exact hNoTerminal ⟨n, hTerminal⟩
  apply D.no_infinite_nonterminal_path
  exact ⟨path.toInfiniteSelectedEvolutionPath hNonTerminal,
    path.toInfiniteSelectedEvolutionPath_staysOutsideTerminal hNonTerminal⟩

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
    Term.terminal (P.sourcePoint (path.step i)) (P.sourceStateAt (path.step i))

/-- IX.§5.3 / AC16: a selected endpoint can be extended if it is non-terminal. -/
def EndpointExecutable (path : SelectedEvolutionPath P)
    (Term : TerminalState Phi) (last : Fin path.length) : Prop :=
  Term.NonTerminal (P.sourcePoint (path.step last)) (P.sourceStateAt (path.step last)) ->
    ∃ next : P.Step, P.StepConnect (path.step last) next

/-- IX.§5.3 / AC16: selected endpoint maximality. -/
def MaximalAt (path : SelectedEvolutionPath P) (last : Fin path.length) : Prop :=
  ¬ ∃ next : P.Step, P.StepConnect (path.step last) next

/--
IX.§5.3 / AC16: a maximal finite selected path reaches a terminal state.

This supporting bridge concerns an explicitly bounded path. Executability from
the endpoint is a selected premise; finite-time arrival for policy-generated
paths is stated separately by `policy_generated_path_reaches_terminal`.
-/
theorem maximal_path_reaches_terminal (path : SelectedEvolutionPath P)
    (last : Fin path.length)
    [Decidable (Term.terminal (P.sourcePoint (path.step last)) (P.sourceStateAt (path.step last)))]
    (hexecutable : path.EndpointExecutable Term last)
    (hmaximal : path.MaximalAt last) :
    path.ReachesTerminal Term := by
  by_cases hterminal :
      Term.terminal (P.sourcePoint (path.step last)) (P.sourceStateAt (path.step last))
  · exact ⟨last, hterminal⟩
  · exfalso
    exact hmaximal (hexecutable hterminal)

end SelectedEvolutionPath

end Evolution
end AAT.AG
