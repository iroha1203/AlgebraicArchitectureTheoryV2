import Formal.AG.Evolution
import Formal.AG.Examples.FiniteModel
import Formal.AG.Measurement.Examples
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section

namespace AAT.AG
namespace Examples
namespace EvolutionPart9

open CategoryTheory
open Evolution

/-!
PRD-9 R10 / AC20 finite temporal examples.

These are selected finite fixtures for Part IX.  They exercise the actual
Part IX Lean surfaces on tiny finite data, while keeping nonzero obstruction
and force-integrability readings as selected fixture assumptions rather than
general theorem claims.
-/

/-- R10(a): two selected time objects. -/
inductive TinyTime where
  | t0
  | t1
  deriving DecidableEq, Fintype

/-- R10(a): explicit finite witness for the two selected time objects. -/
def tinyTimeEquivFin : TinyTime ≃ Fin 2 where
  toFun
    | .t0 => ⟨0, by decide⟩
    | .t1 => ⟨1, by decide⟩
  invFun
    | ⟨0, _⟩ => .t0
    | ⟨1, _⟩ => .t1
    | ⟨n + 2, h⟩ => False.elim (by omega : False)
  left_inv := by
    intro t
    cases t <;> rfl
  right_inv := by
    intro n
    rcases n with ⟨n, h⟩
    interval_cases n <;> rfl

instance : Finite TinyTime :=
  ⟨tinyTimeEquivFin⟩

/-- R10(a): tiny trace arrow carrier.

The selected finite regime below marks the intended `t0 -> t1` step.  The
carrier is deliberately trivial so the example focuses on the Part IX selected
trace boundary rather than on a new category construction.
-/
abbrev TinyHom (_ _ : TinyTime) : Type :=
  Unit

/-- R10(a): the selected step from `t0` to `t1`. -/
def tinyStep : TinyHom .t0 .t1 :=
  ()

/-- R10(a): explicit finite witness for every tiny hom set. -/
def tinyHomEquivFin (a b : TinyTime) : TinyHom a b ≃ Fin 1 where
  toFun _ := ⟨0, by decide⟩
  invFun _ := ()
  left_inv := by intro x; cases x; rfl
  right_inv := by
    intro n
    rcases n with ⟨n, h⟩
    interval_cases n
    rfl

instance (a b : TinyTime) : Finite (TinyHom a b) :=
  ⟨tinyHomEquivFin a b⟩

/-- R10(a): the selected two-step trace category. -/
def twoStepTrace : TraceCategory where
  Obj := TinyTime
  Hom := TinyHom
  id := fun _ => ()
  comp := fun _ _ => ()
  id_comp := by intro a b f; cases f; rfl
  comp_id := by intro a b f; cases f; rfl
  assoc := by intro a b c d f g h; cases f; cases g; cases h; rfl

/-- R10(a): all arrows of the tiny trace are selected and finite. -/
def twoStepTraceFiniteRegime : twoStepTrace.FiniteRegime where
  finiteObj := by
    change Finite TinyTime
    infer_instance
  finiteHom := by
    intro _a _b
    change Finite Unit
    infer_instance
  selectedArrow := fun _ => True
  idSelected := fun _ => trivial
  compSelected := fun _ _ => trivial

/-- R10(a): the selected transition `t0 -> t1` is in the finite trace regime. -/
theorem twoStep_step_selected :
    @TraceCategory.FiniteRegime.selectedArrow twoStepTrace twoStepTraceFiniteRegime
      TinyTime.t0 TinyTime.t1 tinyStep :=
  show True from trivial

/-- R10(a): identities compose with the selected step. -/
theorem twoStep_id_step :
    @TraceCategory.comp twoStepTrace TinyTime.t0 TinyTime.t0 TinyTime.t1
      (twoStepTrace.id TinyTime.t0) tinyStep = tinyStep :=
  rfl

/-- R10(a): the selected step composes with the target identity. -/
theorem twoStep_step_id :
    @TraceCategory.comp twoStepTrace TinyTime.t0 TinyTime.t1 TinyTime.t1
      tinyStep (twoStepTrace.id TinyTime.t1) = tinyStep :=
  rfl

/-- R10: finite temporal states used by the examples. -/
inductive TinyState where
  | high
  | mid
  | terminal
  | nonlawfulTerminal
  deriving DecidableEq, Fintype

/-- R10: selected energy for the finite dissipation fixture. -/
def TinyState.energy : TinyState -> Nat
  | .high => 2
  | .mid => 1
  | .terminal => 0
  | .nonlawfulTerminal => 0

/-- R10: finite Part IX profile over the PRD-8 pseudo-circle measurement profile. -/
def evolutionProfile : EvolutionProfile where
  BaseGeometry := Unit
  BaseMorphism := fun _ _ => Unit
  baseId := fun _ => ()
  baseComp := fun _ _ => ()
  measurementProfile := Measurement.pseudoCircleMeasurementProfile
  trace := twoStepTrace
  selectedOperations := Unit
  selectedStateFamily := fun _ => TinyState
  selectedTemporalLaws := Unit
  selectedCoefficientProfile := Unit

/-- R10(a): finite product/incidence temporal site over the finite Part I model. -/
def temporalSite : TemporalSite FiniteModel.site evolutionProfile where
  traceRegime := twoStepTraceFiniteRegime
  siteRegime := FiniteModel.finitePosetRegime

/-- R10: the singleton architecture context used by all tiny temporal states. -/
def context0 : temporalSite.siteRegime.ContextIndex :=
  PUnit.unit

/-- R10: source temporal point. -/
def p0 : temporalSite.Point :=
  (TinyTime.t0, context0)

/-- R10: target temporal point. -/
def p1 : temporalSite.Point :=
  (TinyTime.t1, context0)

/-- R10: selected incidence from `t0` to `t1`. -/
def stepLeg : temporalSite.IncidenceLeg p0 p1 where
  trace := tinyStep
  trace_selected := show True from trivial
  context := trivial

/-- R10: identity-like state-transition presheaf on the finite temporal site. -/
def statePresheaf : StateTransitionPresheaf temporalSite where
  State := fun _ => TinyState
  Transition := fun _ _ _ => Unit
  transitionId := fun _ _ => ()
  transitionComp := by
    intro _p _x _y _z' _f _g
    exact ()
  restrictContext := by
    intro _t _i _j _h x
    exact x
  restrictContext_id := fun _ _ _ => rfl
  restrictContext_comp := by
    intro _t _i _j _k _hij _hjk _x
    rfl
  transportTrace := by
    intro _t₀ _t₁ _e _he _i x
    exact x
  transportTrace_id := fun _ _ _ => rfl
  transportTrace_comp := by
    intro _t₀ _t₁ _t₂ _e₀ _e₁ _he₀ _he₁ _i _x
    rfl
  restrict_transport_commute := by
    intro _t₀ _t₁ _e _he _i _j _hij _x
    rfl

/-- R10: coerce a tiny state into any selected temporal point. -/
def stateAt (p : temporalSite.Point) (s : TinyState) : statePresheaf.State p := by
  change TinyState
  exact s

def high0 : statePresheaf.State p0 := stateAt p0 TinyState.high
def mid0 : statePresheaf.State p0 := stateAt p0 TinyState.mid
def mid1 : statePresheaf.State p1 := stateAt p1 TinyState.mid
def terminal1 : statePresheaf.State p1 := stateAt p1 TinyState.terminal
def nonlawfulTerminal1 : statePresheaf.State p1 :=
  stateAt p1 TinyState.nonlawfulTerminal

/-- R10: dummy selected temporal law for replay/force fixtures. -/
def temporalLaw : TemporalLaw statePresheaf where
  kind := .descentTemporalLaw
  Witness := Unit
  source := fun _ => p0
  target := fun _ => p1
  incidence := fun _ => stepLeg
  stateEquation := fun _ x y => x = high0 ∧ y = mid1
  transitionPredicate := by
    intro _w _x _y _tr
    exact True
  descentPredicate := fun _ x => x = high0

/-- R10(b/g): singleton sheaf carrier for the selected finite obstruction coefficient. -/
def unitSheaf : Site.AATSheaf FiniteModel.site where
  carrier := FiniteModel.siteCoefficient
  isSheaf := by
    intro _base _cover _hcover
    dsimp [Site.AATSheafConditionFor]
    intro family _compatible
    refine ⟨PUnit.unit, ?_, ?_⟩
    · intro _Y f hf
      cases family f hf
      rfl
    · intro candidate _hcandidate
      cases candidate
      rfl

/-- R10(b/g): selected obstruction sheaf with singleton additive sections. -/
def unitObstructionSheaf :
    Cohomology.ObstructionSheaf FiniteModel.site where
  carrier := unitSheaf
  addCommGroup := by
    intro _W
    change AddCommGroup PUnit
    infer_instance
  map_zero := by
    intro _source _target _f
    rfl
  map_add := by
    intro _source _target _f x y
    cases x
    cases y
    rfl

/-- R10(b/g): singleton temporal coefficient over the finite temporal site. -/
def temporalCoefficient : TemporalCoefficient temporalSite where
  coefficientProfile := ()
  obstructionSheaf := unitObstructionSheaf
  fiber := fun _ => PUnit
  fiberAddCommGroup := by
    intro _p
    exact inferInstanceAs (AddCommGroup PUnit)
  restrict := by
    intro _p _q _leg
    exact {
      toFun := fun _ => PUnit.unit
      map_zero' := rfl
      map_add' := by
        intro x y
        cases x
        cases y
        rfl
    }
  restrict_id := by
    intro _p x
    cases x
    rfl
  restrict_comp := by
    intro _p _q _r _f _g x
    cases x
    rfl
  toObstructionSection := by
    intro _p
    exact {
      toFun := fun _ => PUnit.unit
      map_zero' := rfl
      map_add' := by
        intro x y
        cases x
        cases y
        rfl
    }

/-- R10(b): selected two-chart temporal cover for the zero replay descent fixture. -/
def replayTemporalCover : TemporalCover temporalSite where
  baseTrace := TinyTime.t1
  baseContext := context0
  Index := Bool
  finiteIndex := by infer_instance
  chartTrace := fun _ => TinyTime.t0
  chartContext := fun _ => context0
  traceToBase := fun _ => tinyStep
  traceToBase_selected := fun _ => trivial
  contextToBase := fun _ => trivial

/-- R10(b/g): PRD-4 site cover induced by the finite Part II singleton site. -/
def replaySiteCover : Cohomology.CoverRelativeCechCover FiniteModel.site :=
  Cohomology.finitePosetCoverRelativeCover FiniteModel.finitePosetCechComplex

/-- R10(b/g): comparison from the selected temporal cover to the singleton site cover. -/
def replayCoverComparison :
    TemporalCoverToSiteCover replayTemporalCover replaySiteCover where
  siteIndexOf := fun _ => PUnit.unit
  chart_eq := by
    intro _i
    rfl
  base_eq := rfl
  preservesTraceLeg := fun _ => trivial
  preservesContextLeg := fun _ => rfl

/-- R10(b/g): singleton additive cover-relative Čech complex for the finite fixtures. -/
def unitCechComplex :
    Cohomology.CoverRelativeCechComplex replaySiteCover unitObstructionSheaf where
  cochainAddCommGroup := by
    intro n
    change AddCommGroup ((σ : replaySiteCover.simplex n) -> PUnit)
    infer_instance
  alternatingFaceCombination := fun _n _faces _σ => PUnit.unit
  differential := by
    intro n
    letI :
        AddCommGroup
          (Cohomology.CoverRelativeCechCochain replaySiteCover unitObstructionSheaf n) := by
      change AddCommGroup ((σ : replaySiteCover.simplex n) -> PUnit)
      infer_instance
    letI :
        AddCommGroup
          (Cohomology.CoverRelativeCechCochain replaySiteCover unitObstructionSheaf (n + 1)) := by
      change AddCommGroup ((σ : replaySiteCover.simplex (n + 1)) -> PUnit)
      infer_instance
    exact {
      toFun := fun _ _ => PUnit.unit
      map_zero' := by
        funext _σ
        rfl
      map_add' := by
        intro _x _y
        funext _σ
        rfl
    }
  differential_eq_alternatingFaceCombination := by
    intro _n _c
    funext _σ
    rfl
  differential_comp := by
    intro _n _c
    funext _σ
    rfl

/-- R10(b/g): temporal Čech bridge used by replay and force examples. -/
def temporalBridge :
    TemporalCechBridge temporalSite unitObstructionSheaf where
  temporalCover := replayTemporalCover
  siteCover := replaySiteCover
  coverComparison := replayCoverComparison
  siteComplex := unitCechComplex

/-- R10(b/g): singleton zero cochain in every selected temporal degree. -/
def unitTemporalCochain (n : Nat) : temporalBridge.siteComplex.Cn n :=
  fun _ => PUnit.unit

/-- R10(d/f): selected evolution functional with energy values. -/
def phi : EvolutionFunctional statePresheaf where
  measurementProfile := Measurement.pseudoCircleMeasurementProfile
  measurementProfile_eq := rfl
  Value := Nat
  valuePreorder := inferInstance
  read := by
    intro _p s
    change TinyState at s
    exact s.energy
  minimum := fun n => n = 0
  obstructionMassReading := fun _ _ => True
  harmonicMassReading := fun _ v => v = 0 ∨ v = 1 ∨ v = 2
  distanceToFlatnessReading := fun _ _ => True
  transferResidueNormReading := fun _ _ => True

/-- R10(d): two selected dissipative steps in a three-state finite chain. -/
inductive DissipationStep where
  | highToMid
  | midToTerminal
  | terminalStay
  deriving DecidableEq, Fintype

/-- R10(d): explicit finite witness for the three selected dissipative steps. -/
def dissipationStepEquivFin : DissipationStep ≃ Fin 3 where
  toFun
    | .highToMid => ⟨0, by decide⟩
    | .midToTerminal => ⟨1, by decide⟩
    | .terminalStay => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => .highToMid
    | ⟨1, _⟩ => .midToTerminal
    | ⟨2, _⟩ => .terminalStay
    | ⟨n + 3, h⟩ => False.elim (by omega : False)
  left_inv := by
    intro step
    cases step <;> rfl
  right_inv := by
    intro n
    rcases n with ⟨n, h⟩
    interval_cases n <;> rfl

instance : Finite DissipationStep :=
  ⟨dissipationStepEquivFin⟩

/-- R10(d): source state of each selected dissipative step. -/
def DissipationStep.sourceState : DissipationStep -> TinyState
  | .highToMid => .high
  | .midToTerminal => .mid
  | .terminalStay => .terminal

/-- R10(d): target state of each selected dissipative step. -/
def DissipationStep.targetState : DissipationStep -> TinyState
  | .highToMid => .mid
  | .midToTerminal => .terminal
  | .terminalStay => .terminal

/-- R10(d): finite strictly dissipative policy. -/
def dissipativePolicy : DissipativePolicy phi where
  Step := DissipationStep
  source := fun
    | .highToMid => p0
    | .midToTerminal => p1
    | .terminalStay => p1
  target := fun
    | .highToMid => p1
    | .midToTerminal => p1
    | .terminalStay => p1
  sourceState := fun
    | .highToMid => high0
    | .midToTerminal => mid1
    | .terminalStay => terminal1
  targetState := fun
    | .highToMid => mid1
    | .midToTerminal => terminal1
    | .terminalStay => nonlawfulTerminal1
  incidence := fun
    | .highToMid => stepLeg
    | .midToTerminal => temporalSite.idLeg p1
    | .terminalStay => temporalSite.idLeg p1
  selectedEvolutionStep := fun _ => True
  selectedEvolutionStep_cert := fun _ => trivial
  nonIncrease := by
    intro step
    cases step
    · change (1 : Nat) <= 2
      decide
    · change (0 : Nat) <= 1
      decide
    · change (0 : Nat) <= 0
      decide

/-- R10(d/e): terminal and lawful predicates are intentionally separated. -/
def terminalState : TerminalState phi where
  terminal := by
    intro _p s
    change TinyState at s
    exact s = TinyState.terminal ∨ s = TinyState.nonlawfulTerminal
  lawful := by
    intro _p s
    change TinyState at s
    exact s = TinyState.terminal

/-- R10(d): strict decrease outside terminal states. -/
def strictDissipation : StrictlyDissipativeOutsideTerminal dissipativePolicy terminalState where
  strictDecrease := by
    intro step hNonTerminal
    cases step
    · change (1 : Nat) < 2
      decide
    · change (0 : Nat) < 1
      decide
    · exact False.elim (hNonTerminal (Or.inl rfl))

/-- R10(d): finite stopping package for the three-state toy policy. -/
def finiteDissipationStopping :
    FiniteDissipationStopping dissipativePolicy terminalState where
  finiteSelectedSteps := by
    change Finite DissipationStep
    infer_instance
  wellFoundedValue := Nat.lt_wfRel.wf
  strict := strictDissipation

/-- R10(d): the finite dissipative fixture has no infinite nonterminal selected path. -/
theorem finite_dissipation_no_infinite_nonterminal_path :
    ¬ ∃ path : InfiniteSelectedEvolutionPath dissipativePolicy,
      path.StaysOutsideTerminal terminalState :=
  finiteDissipationStopping.no_infinite_nonterminal_path

/-- R10(e): a selected terminal may be non-lawful. -/
theorem nonlawful_terminal_is_terminal :
    terminalState.terminal p1 nonlawfulTerminal1 :=
  Or.inr rfl

/-- R10(e): terminality does not collapse into lawfulness in the fixture. -/
theorem nonlawful_terminal_not_lawful :
    ¬ terminalState.lawful p1 nonlawfulTerminal1 := by
  intro h
  cases h

/-- R10(f): selected path containing the high-to-mid dissipative step. -/
def oneStepPath : SelectedEvolutionPath dissipativePolicy where
  length := 1
  step := fun _ => .highToMid
  continuous := by
    intro i hnext
    omega

/-- R10(d): selected finite dissipative path from high to a terminal source. -/
def finiteDissipationPath : SelectedEvolutionPath dissipativePolicy where
  length := 3
  step := fun
    | ⟨0, _⟩ => .highToMid
    | ⟨1, _⟩ => .midToTerminal
    | ⟨2, _⟩ => .terminalStay
    | ⟨n + 3, h⟩ => False.elim (by omega : False)
  continuous := by
    intro i hnext
    rcases i with ⟨i, hi⟩
    interval_cases i
    · refine ⟨rfl, ?_⟩
      rfl
    · refine ⟨rfl, ?_⟩
      rfl
    · have : (3 : Nat) < 3 := by
        simp at hnext
      omega

/-- R10(d): the two-step dissipative fixture reaches a terminal state. -/
theorem twoStep_dissipation_reaches_terminal :
    finiteDissipationPath.ReachesTerminal terminalState :=
  ⟨⟨2, by decide⟩, Or.inl rfl⟩

/-- R10(d): the selected terminal endpoint has no selected continuation. -/
theorem twoStep_dissipation_last_maximal :
    finiteDissipationPath.MaximalAt ⟨2, by decide⟩ := by
  intro hnext
  rcases hnext with ⟨next, hconnect⟩
  rcases hconnect with ⟨hpoint, hstate⟩
  cases next
  · cases hpoint
  · cases hstate
  · cases hstate

/-- R10(d): endpoint executability is vacuous at the selected terminal endpoint. -/
theorem twoStep_dissipation_endpoint_executable :
    finiteDissipationPath.EndpointExecutable terminalState ⟨2, by decide⟩ := by
  intro hnonterminal
  exact False.elim (hnonterminal (Or.inl rfl))

/-- R10(d): theorem 5.3 finite-path half reads terminal reachability. -/
theorem twoStep_dissipation_reaches_terminal_by_theorem53 :
    finiteDissipationPath.ReachesTerminal terminalState := by
  classical
  exact finiteDissipationPath.maximal_path_reaches_terminal
    ⟨2, by decide⟩
    twoStep_dissipation_endpoint_executable
    twoStep_dissipation_last_maximal

/-- R10(f): Lyapunov reading backed by the PRD-8 harmonic-mass hook. -/
def lyapunovReading : AATLyapunovReading dissipativePolicy terminalState where
  selectedFiniteEvolutionProfileScope := True
  selectedFiniteEvolutionProfileScope_cert := trivial
  nonIncreasingAlongPolicy := dissipativePolicy.nonIncreasingAlongPolicy_of_dissipative
  NearSelectedObstructionZero := by
    intro _p s
    change TinyState at s
    exact s = TinyState.terminal
  minimalNearSelectedObstructionZero := by
    intro p s hs
    cases hs
    rfl
  terminalLawfulAssumptionBoundary := True
  terminalLawfulAssumptionBoundary_cert := trivial
  noForecastOutsideSelectedProfile := True
  noForecastOutsideSelectedProfile_cert := trivial

/-- R10(f): harmonic mass hook for the terminal state. -/
def harmonicMassLyapunov :
    HarmonicMassLyapunovInstance phi where
  point := p1
  state := terminal1
  domain := Measurement.PseudoCircleMeasurementDomain.boundaryCocycle
  value := (0 : Nat)
  harmonicMassReading := Or.inl rfl
  value_eq_harmonicMass := rfl

/-- R10(f): the selected Lyapunov path is non-increasing. -/
theorem lyapunov_path_nonIncreasing :
    oneStepPath.PathwiseNonIncrease :=
  lyapunovReading.selected_path_monotone oneStepPath

/-- R10(f): the selected terminal value is read as harmonic mass. -/
theorem harmonic_mass_value :
    phi.value harmonicMassLyapunov.point harmonicMassLyapunov.state =
      harmonicMassLyapunov.value :=
  harmonicMassLyapunov.state_value_eq_harmonic_mass

/-! Replay and force fixtures below keep obstruction detection as selected finite evidence. -/

/-- R10(b/c): selected replay mismatch value on a two-chart or pseudo-circle fixture. -/
inductive ReplayMismatchValue where
  | zero
  | pseudoCircleBoundary
  deriving DecidableEq

/-- R10(b): replay data whose zero mismatch is fed to theorem 4.2. -/
def zeroReplayDescentData :
    ReplayDescentData statePresheaf temporalCoefficient temporalLaw where
  bridge := temporalBridge
  cover := replayTemporalCover
  sourceTrace := TinyTime.t0
  targetTrace := TinyTime.t1
  traceArrow := tinyStep
  traceArrow_selected := trivial
  replay := by
    intro _i s
    change TinyState at s
    change TinyState
    exact match s with
      | .high => .mid
      | other => other
  mismatchCochain := unitTemporalCochain 1
  mismatchSupportedByLaw := True
  mismatchSupportedByLaw_cert := trivial

/-- R10(b): the selected zero replay mismatch is a cocycle. -/
def zeroReplayMismatchCocycle :
    ReplayMismatchCocycle zeroReplayDescentData where
  differential_zero := by
    funext _σ
    rfl

/-- R10(b): effective zero-cochain adjustment for the zero replay fixture. -/
def zeroReplayAdjustment :
    EffectiveTemporalAdjustment zeroReplayDescentData where
  correction := unitTemporalCochain 0
  adjustedReplay := zeroReplayDescentData.replay
  adjustedMismatchCochain := unitTemporalCochain 1
  adjustedMismatchSupportedByLaw := True
  adjustedMismatchSupportedByLaw_cert := trivial
  adjustment_equation := by
    funext _σ
    rfl

/-- R10(b): temporal class package selected by the zero replay mismatch. -/
def zeroReplayTemporalClass :
    TemporalClass zeroReplayDescentData.mismatch where
  cocycle := zeroReplayMismatchCocycle.toTemporalCocycle

/-- R10(b): concrete theorem-4.2 assumptions for the zero replay fixture. -/
def zeroReplayTemporalDescentCriterion :
    TemporalDescentCriterion zeroReplayDescentData where
  mismatchCocycle := zeroReplayMismatchCocycle
  temporalClass := zeroReplayTemporalClass
  temporalClass_matches_mismatch := rfl
  classVanishes_cert := by
    rfl
  adjustment := zeroReplayAdjustment
  adjustedCompatible := fun _ => True
  adjustedCompatible_cert := trivial
  descends_from_adjusted := by
    intro _hvanish _hadjusted
    exact ⟨fun
      | .high => .mid
      | other => other⟩

/-- R10(b): theorem 4.2 yields a global replay transition for the zero fixture. -/
theorem replay_zero_theorem42_global_transition_exists :
    Nonempty zeroReplayDescentData.GlobalReplayTransition :=
  zeroReplayTemporalDescentCriterion.temporal_descent_criterion

/-- R10(b): replay descent zero fixture. -/
structure ReplayDescentZeroExample where
  localCharts : Type
  localCharts_finite : Finite localCharts
  mismatch : ReplayMismatchValue
  mismatch_zero : mismatch = .zero
  replayData : ReplayDescentData statePresheaf temporalCoefficient temporalLaw
  theorem42Criterion : TemporalDescentCriterion replayData
  theorem42GlobalTransition : Nonempty replayData.GlobalReplayTransition
  coboundaryWitness : Prop
  coboundaryWitness_cert : coboundaryWitness
  globalReplayTransition : TinyState -> TinyState
  globalReplayTransition_cert :
    globalReplayTransition TinyState.high = TinyState.mid

/-- R10(b): concrete two-chart zero replay fixture. -/
def replayDescentZeroExample : ReplayDescentZeroExample where
  localCharts := Bool
  localCharts_finite := by infer_instance
  mismatch := .zero
  mismatch_zero := rfl
  replayData := zeroReplayDescentData
  theorem42Criterion := zeroReplayTemporalDescentCriterion
  theorem42GlobalTransition := replay_zero_theorem42_global_transition_exists
  coboundaryWitness := True
  coboundaryWitness_cert := trivial
  globalReplayTransition := fun
    | .high => .mid
    | s => s
  globalReplayTransition_cert := rfl

/-- R10(b): the zero replay fixture records actual theorem-4.2 descent data. -/
theorem replay_zero_theorem42_applied :
    Nonempty replayDescentZeroExample.replayData.GlobalReplayTransition :=
  replayDescentZeroExample.theorem42GlobalTransition

/-- R10(b): zero mismatch fixture yields a selected global replay transition. -/
theorem replay_zero_has_global_transition :
    replayDescentZeroExample.globalReplayTransition TinyState.high = TinyState.mid :=
  replayDescentZeroExample.globalReplayTransition_cert

/-- R10(c): pseudo-circle temporal cover edges. -/
inductive PseudoCircleEdge where
  | ab
  | bc
  | ca
  deriving DecidableEq, Fintype

/-- R10(c): concrete pseudo-circle boundary mismatch in `ZMod 2`. -/
def pseudoCircleMismatch : PseudoCircleEdge -> ZMod 2
  | .ab => 1
  | .bc => 0
  | .ca => 0

/-- R10(c): the pseudo-circle boundary mismatch has a concrete nonzero edge. -/
theorem pseudoCircleMismatch_ab_nonzero :
    pseudoCircleMismatch .ab ≠ 0 := by
  native_decide

/-- R10(c): selected nonzero replay class fixture without claiming global failure. -/
structure ReplayDescentNonzeroExample where
  edge : PseudoCircleEdge
  edge_nonzero : pseudoCircleMismatch edge ≠ 0
  selectedConcreteClassNonzero : Prop
  selectedConcreteClassNonzero_cert : selectedConcreteClassNonzero
  noGlobalFailureClaimWithoutDetectingAssumption : Prop
  noGlobalFailureClaimWithoutDetectingAssumption_cert :
    noGlobalFailureClaimWithoutDetectingAssumption

/-- R10(c): concrete pseudo-circle nonzero replay fixture. -/
def replayDescentNonzeroExample : ReplayDescentNonzeroExample where
  edge := .ab
  edge_nonzero := pseudoCircleMismatch_ab_nonzero
  selectedConcreteClassNonzero := True
  selectedConcreteClassNonzero_cert := trivial
  noGlobalFailureClaimWithoutDetectingAssumption := True
  noGlobalFailureClaimWithoutDetectingAssumption_cert := trivial

/-- R10(c): read the concrete nonzero pseudo-circle mismatch. -/
theorem replay_nonzero_edge_witness :
    pseudoCircleMismatch replayDescentNonzeroExample.edge ≠ 0 :=
  replayDescentNonzeroExample.edge_nonzero

/-- R10(g): toy force from high to mid state. -/
def toyForce : Force statePresheaf where
  source := p0
  target := p1
  sourceState := high0
  targetState := mid1
  incidence := stepLeg
  stateMorphism := by
    intro s
    change TinyState at s
    change TinyState
    exact match s with
      | .high => .mid
      | other => other
  stateMorphism_hits_target := rfl
  selectedForce := True
  selectedForce_cert := trivial

/-- R10(g): toy force mismatch cochain on the selected temporal bridge. -/
def toyForceMismatch :
    TemporalMismatch temporalCoefficient temporalLaw where
  bridge := temporalBridge
  degree := 1
  cochain := unitTemporalCochain 1
  supportedByLaw := True
  supportedByLaw_cert := trivial

/-- R10(g): the toy force mismatch is a selected degree-one cocycle. -/
def toyForceTemporalCocycle :
    TemporalCocycle toyForceMismatch where
  differential_zero := by
    funext _σ
    rfl

/-- R10(g): selected temporal class for the toy force mismatch. -/
def toyForceTemporalClass :
    TemporalClass toyForceMismatch where
  cocycle := toyForceTemporalCocycle

/-- R10(g): concrete R9 `ForceMismatchClass` instance for the toy force. -/
def toyForceMismatchClass :
    ForceMismatchClass (Coeff := temporalCoefficient) (Law := temporalLaw) toyForce where
  mismatch := toyForceMismatch
  temporalClass := toyForceTemporalClass
  degree_one := rfl
  traceProductSiteFixed := True
  traceProductSiteFixed_cert := trivial
  mismatchConstructedFromForce := True
  mismatchConstructedFromForce_cert := trivial

/-- R10(g): the toy force mismatch class is degree one. -/
theorem toy_force_mismatch_degree_one :
    toyForceMismatchClass.mismatch.degree = 1 :=
  toyForceMismatchClass.mismatch_degree_one

/-- R10(g): force fixture keeps statement-only theorem-candidate assumptions explicit. -/
structure ForceCandidateFixture where
  forceSelected : toyForce.selectedForce
  mismatchClass :
    ForceMismatchClass (Coeff := temporalCoefficient) (Law := temporalLaw) toyForce
  concreteObstructionValue : ZMod 2
  concreteObstruction_nonzero : concreteObstructionValue ≠ 0
  selectedNonzero :
    mismatchClass.mismatch.bridge.siteComplex.CoverRelativeHn
      mismatchClass.mismatch.degree -> Prop
  selectedNonzero_cert : selectedNonzero mismatchClass.obstructionClass
  coefficientExactness : Prop
  coefficientExactness_cert : coefficientExactness
  witnessCoverage : Prop
  witnessCoverage_cert : witnessCoverage
  temporalDescentDetecting : Prop
  temporalDescentDetecting_cert : temporalDescentDetecting
  localToGlobalControlledByDescent : Prop
  localToGlobalControlledByDescent_cert : localToGlobalControlledByDescent
  candidateOnly : Prop
  candidateOnly_cert : candidateOnly

/-- R10(g): concrete force obstruction candidate fixture. -/
def forceCandidateFixture : ForceCandidateFixture where
  forceSelected := toyForce.selected
  mismatchClass := toyForceMismatchClass
  concreteObstructionValue := 1
  concreteObstruction_nonzero := by native_decide
  selectedNonzero := fun _ => True
  selectedNonzero_cert := trivial
  coefficientExactness := True
  coefficientExactness_cert := trivial
  witnessCoverage := True
  witnessCoverage_cert := trivial
  temporalDescentDetecting := True
  temporalDescentDetecting_cert := trivial
  localToGlobalControlledByDescent := True
  localToGlobalControlledByDescent_cert := trivial
  candidateOnly := True
  candidateOnly_cert := trivial

/-- R10(g): the toy force obstruction value is concretely nonzero. -/
theorem force_candidate_obstruction_nonzero :
    forceCandidateFixture.concreteObstructionValue ≠ 0 :=
  forceCandidateFixture.concreteObstruction_nonzero

/-- R10(g): the selected force obstruction class is marked nonzero in the fixture. -/
theorem force_candidate_selected_nonzero :
    forceCandidateFixture.selectedNonzero
      forceCandidateFixture.mismatchClass.obstructionClass :=
  forceCandidateFixture.selectedNonzero_cert

/--
R10 / AC20: bundled finite temporal examples (a)-(g).

This theorem is intentionally a conjunction of selected fixture witnesses, not
a general temporal semantics theorem.
-/
theorem finite_temporal_examples_verified :
    @TraceCategory.FiniteRegime.selectedArrow twoStepTrace twoStepTraceFiniteRegime
      TinyTime.t0 TinyTime.t1 tinyStep ∧
      Nonempty replayDescentZeroExample.replayData.GlobalReplayTransition ∧
        replayDescentZeroExample.coboundaryWitness ∧
          replayDescentZeroExample.globalReplayTransition TinyState.high = TinyState.mid ∧
            replayDescentNonzeroExample.selectedConcreteClassNonzero ∧
              (¬ ∃ path : InfiniteSelectedEvolutionPath dissipativePolicy,
                path.StaysOutsideTerminal terminalState) ∧
                finiteDissipationPath.ReachesTerminal terminalState ∧
                terminalState.terminal p1 nonlawfulTerminal1 ∧
                  (¬ terminalState.lawful p1 nonlawfulTerminal1) ∧
                    oneStepPath.PathwiseNonIncrease ∧
                      forceCandidateFixture.concreteObstructionValue ≠ 0 ∧
                        forceCandidateFixture.selectedNonzero
                          forceCandidateFixture.mismatchClass.obstructionClass ∧
                        forceCandidateFixture.coefficientExactness ∧
                          forceCandidateFixture.witnessCoverage ∧
                            forceCandidateFixture.temporalDescentDetecting ∧
                              forceCandidateFixture.localToGlobalControlledByDescent ∧
                                forceCandidateFixture.candidateOnly := by
  exact ⟨twoStep_step_selected,
    replay_zero_theorem42_applied,
    replayDescentZeroExample.coboundaryWitness_cert,
    replay_zero_has_global_transition,
    replayDescentNonzeroExample.selectedConcreteClassNonzero_cert,
    finite_dissipation_no_infinite_nonterminal_path,
    twoStep_dissipation_reaches_terminal_by_theorem53,
    nonlawful_terminal_is_terminal,
    nonlawful_terminal_not_lawful,
    lyapunov_path_nonIncreasing,
    force_candidate_obstruction_nonzero,
    force_candidate_selected_nonzero,
    forceCandidateFixture.coefficientExactness_cert,
    forceCandidateFixture.witnessCoverage_cert,
    forceCandidateFixture.temporalDescentDetecting_cert,
    forceCandidateFixture.localToGlobalControlledByDescent_cert,
    forceCandidateFixture.candidateOnly_cert⟩

end EvolutionPart9
end Examples
end AAT.AG
