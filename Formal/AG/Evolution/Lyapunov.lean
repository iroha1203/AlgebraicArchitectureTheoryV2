import Formal.AG.Evolution.FiniteDissipation

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R8 / AC17 AAT Lyapunov reading.

The Lyapunov surface is relative to one selected evolution functional and one
selected policy.  It records non-increase inside that selected profile,
minimum readings near selected obstruction-zero states, and theorem packages
for selected path monotonicity.  It does not forecast unselected transitions or
future paths outside the selected profile.
-/

namespace DissipativePolicy

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}

/-- IX.§6.1 / AC17: selected policy non-increase for a Lyapunov reading. -/
def NonIncreasingAlongPolicy (P : DissipativePolicy Phi) : Prop :=
  ∀ step : P.Step,
    letI := Phi.valuePreorder
    Phi.value (P.target step) (P.targetState step) <=
      Phi.value (P.source step) (P.sourceState step)

/-- IX.§6.1 / AC17: every dissipative policy is non-increasing along its selected steps. -/
theorem nonIncreasingAlongPolicy_of_dissipative (P : DissipativePolicy Phi) :
    P.NonIncreasingAlongPolicy :=
  P.nonIncrease

end DissipativePolicy

/--
IX.§6.1 / AC17: AAT Lyapunov reading for a selected finite evolution profile.

The selected scope certificate is explicit.  The reading also separates
terminality from lawfulness and records only the selected obstruction-zero
neighborhood used for minimum-value claims.
-/
structure AATLyapunovReading {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Phi : EvolutionFunctional St} (P : DissipativePolicy Phi)
    (Term : TerminalState Phi) where
  selectedFiniteEvolutionProfileScope : Prop
  selectedFiniteEvolutionProfileScope_cert : selectedFiniteEvolutionProfileScope
  nonIncreasingAlongPolicy : P.NonIncreasingAlongPolicy
  NearSelectedObstructionZero : (p : T.Point) -> St.State p -> Prop
  minimalNearSelectedObstructionZero :
    ∀ {p : T.Point} {s : St.State p},
      NearSelectedObstructionZero p s -> Phi.minimum (Phi.value p s)
  terminalLawfulAssumptionBoundary : Prop
  terminalLawfulAssumptionBoundary_cert : terminalLawfulAssumptionBoundary
  noForecastOutsideSelectedProfile : Prop
  noForecastOutsideSelectedProfile_cert : noForecastOutsideSelectedProfile

namespace AATLyapunovReading

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}
variable {P : DissipativePolicy Phi}
variable {Term : TerminalState Phi}

/-- IX.§6.1 / AC17: the Lyapunov reading is scoped to the selected finite profile. -/
theorem selected_scope (L : AATLyapunovReading P Term) :
    L.selectedFiniteEvolutionProfileScope :=
  L.selectedFiniteEvolutionProfileScope_cert

/-- IX.§6.1 / AC17: read the selected policy non-increase certificate. -/
theorem nonIncreasing_policy (L : AATLyapunovReading P Term) :
    P.NonIncreasingAlongPolicy :=
  L.nonIncreasingAlongPolicy

/-- IX.§6.1 / AC17: selected obstruction-zero neighborhood states have minimum value. -/
theorem minimum_near_selected_obstruction_zero
    (L : AATLyapunovReading P Term) {p : T.Point} {s : St.State p}
    (hnear : L.NearSelectedObstructionZero p s) :
    Phi.minimum (Phi.value p s) :=
  L.minimalNearSelectedObstructionZero hnear

/-- IX.Principle 6.2 / AC17: no forecast is claimed outside the selected profile. -/
theorem no_forecast_outside_selected_profile (L : AATLyapunovReading P Term) :
    L.noForecastOutsideSelectedProfile :=
  L.noForecastOutsideSelectedProfile_cert

/-- IX.§6.1 boundary: terminal lawfulness remains an explicit external assumption. -/
theorem terminal_lawfulness_boundary (L : AATLyapunovReading P Term) :
    L.terminalLawfulAssumptionBoundary :=
  L.terminalLawfulAssumptionBoundary_cert

/-- IX.§6.1 / AC17: Lyapunov monotonicity along a selected finite path. -/
theorem selected_path_monotone
    (L : AATLyapunovReading P Term) (path : SelectedEvolutionPath P) :
    path.PathwiseNonIncrease := by
  intro i
  exact L.nonIncreasing_policy (path.step i)

/--
IX.§6.1 / AC17: strict dissipativity yields strict decrease before terminals
along a selected finite path.
-/
theorem selected_path_strict_before_terminal
    (Strict : StrictlyDissipativeOutsideTerminal P Term)
    (path : SelectedEvolutionPath P) :
    SelectedEvolutionPath.PathwiseStrictDecreaseOutsideTerminal (Term := Term) path :=
  path.pathwise_strictDecreaseOutsideTerminal Strict

/--
IX.§6.1 / AC17: terminal-before-loop boundary.

With the R7 finite stopping package, no infinite selected loop/path can stay
outside terminal states.  This is a selected-profile statement, not a forecast
over unselected transitions.
-/
theorem no_infinite_loop_before_terminal
    (D : FiniteDissipationStopping P Term) :
    ¬ ∃ path : InfiniteSelectedEvolutionPath P,
      path.StaysOutsideTerminal Term :=
  D.no_infinite_nonterminal_path

end AATLyapunovReading

/--
IX.§6.1 / AC17: harmonic-mass Lyapunov instance surface.

This is a generic selected instance hook: if a Part VIII Hodge/harmonic-mass
reading is supplied for one selected state, the Lyapunov value can be read as
that harmonic mass.  Concrete finite examples are left to R10.
-/
structure HarmonicMassLyapunovInstance {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    (Phi : EvolutionFunctional St) where
  point : T.Point
  state : St.State point
  domain : E.measurementProfile.Domain
  value : Phi.Value
  harmonicMassReading : Phi.harmonicMassReading domain value
  value_eq_harmonicMass : Phi.value point state = value

namespace HarmonicMassLyapunovInstance

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Phi : EvolutionFunctional St}

/-- IX.§6.1 / AC17: selected state value is the supplied harmonic-mass reading. -/
theorem state_value_eq_harmonic_mass (H : HarmonicMassLyapunovInstance Phi) :
    Phi.value H.point H.state = H.value :=
  H.value_eq_harmonicMass

/-- IX.§6.1 / AC17: read the supplied Part VIII harmonic-mass predicate. -/
theorem harmonic_mass_reading (H : HarmonicMassLyapunovInstance Phi) :
    Phi.harmonicMassReading H.domain H.value :=
  H.harmonicMassReading

end HarmonicMassLyapunovInstance

end Evolution
end AAT.AG
