import Formal.AG.Evolution.ReplayDescent
import Formal.AG.Evolution.Force
import Formal.AG.Evolution.Dissipation
import Formal.AG.Evolution.FiniteDissipation
import Formal.AG.Evolution
import Formal.AG.Examples.FiniteModel
import Formal.AG.Examples.SemanticRepairPart10
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
Part IX R10 / AC20 finite temporal examples.

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

/-- R10: finite Part IX profile over the Part VIII pseudo-circle measurement profile. -/
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

/-- R10: canonical selected temporal law for replay/force fixtures. -/
def temporalLaw : TemporalLaw statePresheaf :=
  TemporalLaw.descentTemporalLaw Unit (fun _ => p0) (fun _ => p1)
    (fun _ => stepLeg) (fun _ x y => x = high0 ∧ y = mid1)

/-- IX-4: the example temporal law is built by the kind-specific constructor. -/
theorem temporalLaw_kind :
    temporalLaw.kind = .descentTemporalLaw :=
  rfl

/-- IX-4: the example temporal law exposes its concrete state equation. -/
theorem temporalLaw_stateEquation (x : statePresheaf.State p0) (y : statePresheaf.State p1) :
    temporalLaw.stateEquation () x y = (x = high0 ∧ y = mid1) :=
  rfl

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

/-- IX-3: product-site incidence complex for the singleton temporal coefficient. -/
def unitTemporalProductIncidenceComplex :
    TemporalCoefficient.ProductIncidenceComplex temporalCoefficient where
  zeroCochain := temporalCoefficient.FiberZeroCochain
  oneCochain := temporalCoefficient.FiberIncidenceOneCochain
  zero_eq := rfl
  one_eq := rfl
  d0 := temporalCoefficient.incidenceDifferential
  d0_eq := rfl

/-- IX-3: the singleton product-incidence differential is the concrete formula. -/
theorem unitTemporalProductIncidence_d0_eq :
    unitTemporalProductIncidenceComplex.d0 =
      temporalCoefficient.incidenceDifferential :=
  unitTemporalProductIncidenceComplex.d0_eq_incidenceDifferential

/-- IX-3: the singleton product-incidence differential kills identity legs. -/
theorem unitTemporalProductIncidence_d0_id
    (c : temporalCoefficient.FiberZeroCochain) (p : temporalSite.Point) :
    unitTemporalProductIncidenceComplex.d0 c (temporalSite.idLeg p) = 0 :=
  unitTemporalProductIncidenceComplex.d0_id c p

/-! ### Nondegenerate product-incidence fixture for IX-3 / #3100 -/

/--
IX-3 / #3100: nontrivial temporal coefficient over the same finite product
site.

Unlike the singleton compatibility fixture, this coefficient has `ZMod 2`
fibers.  Restrictions are identity maps, so a cochain separating `t0` and `t1`
has a genuinely nonzero incidence differential on the selected temporal step.
-/
def zmod2TemporalCoefficient : TemporalCoefficient temporalSite where
  coefficientProfile := ()
  obstructionSheaf := SemanticRepairPart10.generatedF2QuotientObstructionSheaf
  fiber := fun _ => ZMod 2
  fiberAddCommGroup := by
    intro _p
    infer_instance
  restrict := by
    intro _p _q _leg
    exact AddMonoidHom.id (ZMod 2)
  restrict_id := by
    intro _p _x
    rfl
  restrict_comp := by
    intro _p _q _r _f _g _x
    rfl
  toObstructionSection := by
    intro _p
    exact AddMonoidHom.id (ZMod 2)

/-- The selected temporal state family for the concrete `ZMod 2` replay. -/
def zmod2TemporalReplayStatePresheaf : StateTransitionPresheaf temporalSite where
  State := fun _ => ZMod 2
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
  transportTrace_id := by
    intro _t _i _x
    rfl
  transportTrace_comp := by
    intro _t₀ _t₁ _t₂ _e₀ _e₁ _he₀ _he₁ _i _x
    rfl
  restrict_transport_commute := by
    intro _t₀ _t₁ _e _he _i _j _hij _x
    rfl

/-- The singleton-site replay transition used by the independent IX-3 fixture. -/
abbrev ZMod2SingletonTemporalReplayTransition :=
  zmod2TemporalReplayStatePresheaf.State p0 ->
    zmod2TemporalReplayStatePresheaf.State p1

/-- The actual two-patch AAT site equipped with the selected finite trace regime. -/
noncomputable def twoPatchReplayTemporalSite :
    TemporalSite FiniteModel.twoPatchSite evolutionProfile where
  traceRegime := twoStepTraceFiniteRegime
  siteRegime := FiniteModel.twoPatchZMod2FinitePosetRegime

/-- The global replay source lies over the common base context at the source time. -/
noncomputable def twoPatchReplayTemporalSource : twoPatchReplayTemporalSite.Point :=
  (TinyTime.t0, FiniteModel.TwoPatchContextIndex.base)

/-- The global replay target lies over the common base context at the target time. -/
noncomputable def twoPatchReplayTemporalTarget : twoPatchReplayTemporalSite.Point :=
  (TinyTime.t1, FiniteModel.TwoPatchContextIndex.base)

/-- The selected product-incidence source lies on the actual Čech overlap. -/
noncomputable def twoPatchReplayTemporalCechSource : twoPatchReplayTemporalSite.Point :=
  (TinyTime.t0, FiniteModel.TwoPatchContextIndex.overlap)

/-- Actual `ZMod 2` obstruction coefficients on the same two-patch AAT site. -/
noncomputable def twoPatchReplayTemporalObstructionSheaf :
    Cohomology.ObstructionSheaf FiniteModel.twoPatchSite where
  carrier := FiniteModel.twoPatchZMod2CoefficientSheaf
  addCommGroup := by
    intro _W
    change AddCommGroup (ZMod 2)
    infer_instance
  map_zero := by
    intro _source _target _f
    rfl
  map_add := by
    intro _source _target _f x y
    rfl

/-- The temporal coefficient reads the actual two-patch `ZMod 2` coefficient sheaf. -/
noncomputable def twoPatchReplayTemporalCoefficient :
    TemporalCoefficient twoPatchReplayTemporalSite where
  coefficientProfile := ()
  obstructionSheaf := twoPatchReplayTemporalObstructionSheaf
  fiber := fun _ => ZMod 2
  fiberAddCommGroup := by
    intro _p
    infer_instance
  restrict := by
    intro _p _q _leg
    exact AddMonoidHom.id (ZMod 2)
  restrict_id := by
    intro _p _x
    rfl
  restrict_comp := by
    intro _p _q _r _f _g _x
    rfl
  toObstructionSection := by
    intro _p
    exact AddMonoidHom.id (ZMod 2)

/-- The actual temporal state family has `ZMod 2` states on every product point. -/
noncomputable def twoPatchReplayTemporalStatePresheaf :
    StateTransitionPresheaf twoPatchReplayTemporalSite where
  State := fun _ => ZMod 2
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
  transportTrace_id := by
    intro _t _i _x
    rfl
  transportTrace_comp := by
    intro _t₀ _t₁ _t₂ _e₀ _e₁ _he₀ _he₁ _i _x
    rfl
  restrict_transport_commute := by
    intro _t₀ _t₁ _e _he _i _j _hij _x
    rfl

/--
A replay map along one selected trace arrow, with its source and target
architecture contexts retained in the type.
-/
structure TwoPatchTemporalReplayAlong
    {sourceTime targetTime : TinyTime}
    (traceArrow : TinyHom sourceTime targetTime)
    (sourceContext targetContext : FiniteModel.TwoPatchContextIndex) where
  /-- The trace arrow belongs to the selected finite trace regime. -/
  trace_selected :
    @TraceCategory.FiniteRegime.selectedArrow twoStepTrace twoStepTraceFiniteRegime
      sourceTime targetTime traceArrow
  /-- The replay map between the indexed temporal states. -/
  toFun :
    twoPatchReplayTemporalStatePresheaf.State (sourceTime, sourceContext) ->
      twoPatchReplayTemporalStatePresheaf.State (targetTime, targetContext)

/-- Evaluate an indexed replay in the concrete `ZMod 2` state carrier. -/
def TwoPatchTemporalReplayAlong.value
    {sourceTime targetTime : TinyTime}
    {traceArrow : TinyHom sourceTime targetTime}
    {sourceContext targetContext : FiniteModel.TwoPatchContextIndex}
    (replay : TwoPatchTemporalReplayAlong traceArrow sourceContext targetContext)
    (state : twoPatchReplayTemporalStatePresheaf.State
      (sourceTime, sourceContext)) : ZMod 2 :=
  replay.toFun state

/-- The glued replay follows `tinyStep` between the common base states. -/
abbrev TwoPatchTemporalReplayTransition :=
  TwoPatchTemporalReplayAlong tinyStep
    FiniteModel.TwoPatchContextIndex.base
    FiniteModel.TwoPatchContextIndex.base

/-- The selected temporal cover reads the left and right actual two-patch charts. -/
noncomputable def twoPatchReplayTemporalCover : TemporalCover twoPatchReplayTemporalSite where
  baseTrace := TinyTime.t1
  baseContext := FiniteModel.TwoPatchContextIndex.base
  Index := FiniteModel.TwoPatchCoverIndex
  finiteIndex := by infer_instance
  chartTrace
    | .left => TinyTime.t0
    | .right => TinyTime.t1
  chartContext := FiniteModel.twoPatchCoverContextIndex
  traceToBase := fun _ => ()
  traceToBase_selected := fun _ => trivial
  contextToBase := by
    intro i
    cases i <;> simp [twoPatchReplayTemporalSite,
      FiniteModel.twoPatchZMod2FinitePosetRegime,
      FiniteModel.twoPatchCoverContextIndex,
      FiniteModel.twoPatchContextIndexLe]

/-- The global replay source and target both lie over the temporal cover base context. -/
theorem twoPatchReplayTemporalGlobalEndpoints_at_base :
    twoPatchReplayTemporalSource =
        (TinyTime.t0, twoPatchReplayTemporalCover.baseContext) ∧
      twoPatchReplayTemporalTarget =
        (TinyTime.t1, twoPatchReplayTemporalCover.baseContext) := by
  exact ⟨rfl, rfl⟩

/-- The fixed replay trace arrow `tinyStep : t0 ⟶ t1` is selected. -/
theorem twoPatchReplayTemporalTrace_selected :
    @TraceCategory.FiniteRegime.selectedArrow twoStepTrace twoStepTraceFiniteRegime
      TinyTime.t0 TinyTime.t1 tinyStep :=
  twoStep_step_selected

/--
The temporal cover is compared directly with the cover-relative Čech cover of
the same actual two-patch `ZMod 2` complex.
-/
noncomputable def twoPatchReplayTemporalCoverComparison :
    TemporalCoverToSiteCover twoPatchReplayTemporalCover
      (Cohomology.finitePosetCoverRelativeCover
        FiniteModel.twoPatchZMod2CechComplex) where
  siteIndexOf := fun i => i
  chart_eq := by
    intro i
    cases i <;> rfl
  base_eq := rfl
  preservesTraceLeg := fun _ => trivial
  preservesContextLeg := by
    intro i
    cases i <;>
      exact FiniteModel.twoPatchContextLe_sound (by
        simp [twoPatchReplayTemporalCover, twoPatchReplayTemporalSite,
          FiniteModel.twoPatchZMod2FinitePosetRegime,
          FiniteModel.twoPatchCoverContextIndex,
          FiniteModel.twoPatchContextIndexLe])

/-- The actual `Tr_E × X` coefficient carries its full product-incidence complex. -/
noncomputable def twoPatchReplayTemporalProductIncidenceComplex :
    TemporalCoefficient.ProductIncidenceComplex twoPatchReplayTemporalCoefficient where
  zeroCochain := twoPatchReplayTemporalCoefficient.FiberZeroCochain
  oneCochain := twoPatchReplayTemporalCoefficient.FiberIncidenceOneCochain
  zero_eq := rfl
  one_eq := rfl
  d0 := twoPatchReplayTemporalCoefficient.incidenceDifferential
  d0_eq := rfl

/-- The temporal incidence runs from the actual overlap to the common base. -/
noncomputable def twoPatchReplayTemporalCechLeg :
    twoPatchReplayTemporalSite.IncidenceLeg
      twoPatchReplayTemporalCechSource twoPatchReplayTemporalTarget where
  trace := tinyStep
  trace_selected := twoStep_step_selected
  context := by
    simp [twoPatchReplayTemporalCechSource, twoPatchReplayTemporalTarget,
      twoPatchReplayTemporalSite, FiniteModel.twoPatchZMod2FinitePosetRegime,
      FiniteModel.twoPatchContextIndexLe]

/-- IX-3 / #3100: nondegenerate product-incidence complex with `ZMod 2` fibers. -/
def zmod2TemporalProductIncidenceComplex :
    TemporalCoefficient.ProductIncidenceComplex zmod2TemporalCoefficient where
  zeroCochain := zmod2TemporalCoefficient.FiberZeroCochain
  oneCochain := zmod2TemporalCoefficient.FiberIncidenceOneCochain
  zero_eq := rfl
  one_eq := rfl
  d0 := zmod2TemporalCoefficient.incidenceDifferential
  d0_eq := rfl

/--
IX-3 / #3100: a nonconstant temporal zero-cochain on the two-point trace.

It reads `0` at `t0` and `1` at `t1`, so its product-incidence differential
detects the selected temporal step.
-/
def zmod2TemporalSeparatedCochain :
    zmod2TemporalCoefficient.FiberZeroCochain
  | (TinyTime.t0, _) => (show ZMod 2 from 0)
  | (TinyTime.t1, _) => (show ZMod 2 from 1)

/--
IX-3 / #3100: the product-incidence differential is nonzero on the selected
`t0 -> t1` step for the `ZMod 2` temporal coefficient.

This is the nondegenerate replacement evidence for the previous singleton
`PUnit` compatibility fixture: the carrier is nontrivial and the value is a
specific nonzero element of `ZMod 2`.
-/
theorem zmod2TemporalProductIncidence_d0_step_nonzero :
    zmod2TemporalProductIncidenceComplex.d0
        zmod2TemporalSeparatedCochain stepLeg = (1 : ZMod 2) := by
  rfl

/--
IX-3 / #3100: the same selected product-incidence differential is explicitly
nonzero, so the audit does not rely on reading `1 : ZMod 2` by convention.
-/
theorem zmod2TemporalProductIncidence_d0_step_ne_zero :
    zmod2TemporalProductIncidenceComplex.d0
        zmod2TemporalSeparatedCochain stepLeg ≠ 0 := by
  rw [zmod2TemporalProductIncidence_d0_step_nonzero]
  intro h
  have hv : (1 : ZMod 2).val = (0 : ZMod 2).val := congrArg ZMod.val h
  rw [ZMod.val_one] at hv
  simp at hv

/--
IX-3 / #3100: selected incidence-leg simplex for the nondegenerate temporal
product complex.
-/
abbrev ZMod2TemporalIncidenceSimplex :=
  Sigma fun p : temporalSite.Point =>
    Sigma fun q : temporalSite.Point =>
      temporalSite.IncidenceLeg p q

/--
IX-3 / #3100: cover-relative Part IV cover whose degree-zero simplices are
temporal points and whose degree-one simplices are selected temporal incidence
legs.
-/
def zmod2TemporalProductCoverRelativeCover :
    Cohomology.CoverRelativeCechCover FiniteModel.site where
  base := FiniteModel.siteBase
  Index := temporalSite.Point
  chart _ := FiniteModel.siteBase
  inclusion _ := 𝟙 FiniteModel.siteBase
  simplex
    | 0 => temporalSite.Point
    | 1 => ZMod2TemporalIncidenceSimplex
    | _ + 2 => Empty
  overlap
    | 0, _ => FiniteModel.siteBase
    | 1, _ => FiniteModel.siteBase
    | _ + 2, σ => Empty.elim σ
  face := by
    intro n i σ
    cases n with
    | zero =>
        rcases σ with ⟨p, q, _leg⟩
        exact if i.val = 0 then q else p
    | succ n =>
        cases n with
        | zero => exact Empty.elim σ
        | succ _ => exact Empty.elim σ
  faceRestriction := by
    intro n i σ
    cases n with
    | zero =>
        exact 𝟙 FiniteModel.siteBase
    | succ n =>
        cases n with
        | zero => exact Empty.elim σ
        | succ _ => exact Empty.elim σ

/--
IX-3 / #3100: the nondegenerate product-incidence differential as an additive
map.
-/
def zmod2TemporalIncidenceD0Add :
    zmod2TemporalCoefficient.FiberZeroCochain →+
      zmod2TemporalCoefficient.FiberIncidenceOneCochain where
  toFun := zmod2TemporalCoefficient.incidenceDifferential
  map_zero' := by
    funext p q leg
    simp [Evolution.TemporalCoefficient.incidenceDifferential,
      Evolution.TemporalCoefficient.restriction]
  map_add' := by
    intro x y
    funext p q leg
    simp [Evolution.TemporalCoefficient.incidenceDifferential,
      Evolution.TemporalCoefficient.restriction, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc]

/-- IX-3 / #3100: zero map out of the incidence one-cochains. -/
def zmod2TemporalIncidenceD1Add :
    zmod2TemporalCoefficient.FiberIncidenceOneCochain →+
      (Empty -> ZMod 2) where
  toFun := fun _ σ => Empty.elim σ
  map_zero' := by
    funext σ
    exact Empty.elim σ
  map_add' := by
    intro _x _y
    funext σ
    exact Empty.elim σ

/--
IX-3 / #3100: product-incidence three-term additive complex whose `d0` is the
actual temporal incidence formula.
-/
def zmod2TemporalProductIncidenceThreeTerm :
    Cohomology.AdditiveThreeTermComplex
      zmod2TemporalCoefficient.FiberZeroCochain
      zmod2TemporalCoefficient.FiberIncidenceOneCochain
      (Empty -> ZMod 2) where
  d0 := zmod2TemporalIncidenceD0Add
  d1 := zmod2TemporalIncidenceD1Add
  d_comp := by
    intro c
    funext σ
    exact Empty.elim σ

/--
IX-3 / #3100: product-incidence Part IV cover-relative complex over the
non-`PUnit` generated `ZMod 2` coefficient sheaf.
-/
def zmod2TemporalProductCoverRelativeComplex :
    Cohomology.CoverRelativeCechComplex
      zmod2TemporalProductCoverRelativeCover
      SemanticRepairPart10.generatedF2QuotientObstructionSheaf where
  cochainAddCommGroup := by
    intro n
    cases n with
    | zero =>
        change AddCommGroup (temporalSite.Point -> ZMod 2)
        infer_instance
    | succ n =>
        cases n with
        | zero =>
            change AddCommGroup (ZMod2TemporalIncidenceSimplex -> ZMod 2)
            infer_instance
        | succ _ =>
            change AddCommGroup (Empty -> ZMod 2)
            infer_instance
  alternatingFaceCombination := by
    intro n faces
    cases n with
    | zero =>
        intro σ
        exact faces σ ⟨0, by decide⟩ - faces σ ⟨1, by decide⟩
    | succ n =>
        cases n with
        | zero =>
            intro σ
            exact Empty.elim σ
        | succ _ =>
            intro σ
            exact Empty.elim σ
  differential := by
    intro n
    cases n with
    | zero =>
        change
          ((temporalSite.Point -> ZMod 2) →+
            (ZMod2TemporalIncidenceSimplex -> ZMod 2))
        exact {
          toFun := fun c σ =>
            zmod2TemporalCoefficient.incidenceDifferential c σ.2.2
          map_zero' := by
            funext σ
            change zmod2TemporalCoefficient.incidenceDifferential 0 σ.2.2 = 0
            simp [Evolution.TemporalCoefficient.incidenceDifferential,
              Evolution.TemporalCoefficient.restriction]
          map_add' := by
            intro x y
            funext σ
            change
              zmod2TemporalCoefficient.incidenceDifferential (x + y) σ.2.2 =
                zmod2TemporalCoefficient.incidenceDifferential x σ.2.2 +
                  zmod2TemporalCoefficient.incidenceDifferential y σ.2.2
            simp [Evolution.TemporalCoefficient.incidenceDifferential,
              Evolution.TemporalCoefficient.restriction, sub_eq_add_neg, add_comm,
              add_left_comm, add_assoc]
        }
    | succ n =>
        cases n with
        | zero =>
            change
              ((ZMod2TemporalIncidenceSimplex -> ZMod 2) →+
                (Empty -> ZMod 2))
            exact {
              toFun := fun _ σ => Empty.elim σ
              map_zero' := by
                funext σ
                exact Empty.elim σ
              map_add' := by
                intro _x _y
                funext σ
                exact Empty.elim σ
            }
        | succ _ =>
            change ((Empty -> ZMod 2) →+ (Empty -> ZMod 2))
            exact 0
  differential_eq_alternatingFaceCombination := by
    intro n c
    cases n with
    | zero =>
        funext σ
        rcases σ with ⟨p, q, leg⟩
        change
          zmod2TemporalCoefficient.incidenceDifferential
              (fun p => (show ZMod 2 from c p)) leg =
            (show ZMod 2 from c q) - (show ZMod 2 from c p)
        rfl
    | succ n =>
        cases n with
        | zero =>
            funext σ
            exact Empty.elim σ
        | succ _ =>
            funext σ
            exact Empty.elim σ
  differential_comp := by
    intro n c
    cases n with
    | zero =>
        funext σ
        exact Empty.elim σ
    | succ n =>
        cases n with
        | zero =>
            funext σ
            exact Empty.elim σ
        | succ _ =>
            rfl

/-- IX-3 / #3100: curry incidence one-cochains to Part IV degree-one cochains. -/
def zmod2TemporalIncidenceToSigma :
    zmod2TemporalCoefficient.FiberIncidenceOneCochain →+
      (ZMod2TemporalIncidenceSimplex -> ZMod 2) where
  toFun := fun c σ => c σ.2.2
  map_zero' := rfl
  map_add' := by
    intro _x _y
    rfl

/-- IX-3 / #3100: uncurry Part IV degree-one cochains to incidence one-cochains. -/
def zmod2TemporalIncidenceFromSigma :
    (ZMod2TemporalIncidenceSimplex -> ZMod 2) →+
      zmod2TemporalCoefficient.FiberIncidenceOneCochain where
  toFun := fun c {p} {q} leg => c ⟨p, q, leg⟩
  map_zero' := rfl
  map_add' := by
    intro _x _y
    rfl

/--
IX-3 / #3100: cochain-level equivalence between the product-incidence
three-term complex and the Part IV cover-relative complex.
-/
def zmod2TemporalProductCoverRelativeEquivalence :
    Cohomology.AdditiveThreeTermComplex.Equivalence
      zmod2TemporalProductIncidenceThreeTerm
      zmod2TemporalProductCoverRelativeComplex.degreeOneThreeTerm where
  to0 := AddMonoidHom.id _
  to1 := zmod2TemporalIncidenceToSigma
  to2 := AddMonoidHom.id _
  from0 := AddMonoidHom.id _
  from1 := zmod2TemporalIncidenceFromSigma
  from2 := AddMonoidHom.id _
  to0_from0 := by intro _; rfl
  from0_to0 := by intro _; rfl
  to1_from1 := by
    intro c
    funext σ
    rfl
  from1_to1 := by
    intro c
    funext p q leg
    rfl
  to2_from2 := by
    intro c
    funext σ
    exact Empty.elim σ
  from2_to2 := by
    intro c
    funext σ
    exact Empty.elim σ
  to_d0 := by
    intro c
    funext σ
    rfl
  to_d1 := by
    intro c
    funext σ
    exact Empty.elim σ
  from_d0 := by
    intro c
    funext p q leg
    rfl
  from_d1 := by
    intro c
    funext σ
    exact Empty.elim σ

/--
IX-3 / #3100: generated H¹ comparison is a left inverse on the Part IV
cover-relative side.
-/
theorem zmod2TemporalProductCoverRelativeH1_to_from
    (h :
      zmod2TemporalProductCoverRelativeComplex.degreeOneThreeTerm.H1) :
    zmod2TemporalProductCoverRelativeEquivalence.toH1
      (zmod2TemporalProductCoverRelativeEquivalence.fromH1 h) = h :=
  zmod2TemporalProductCoverRelativeEquivalence.to_from_H1 h

/--
IX-3 / #3100: generated H¹ comparison is a right inverse on the product
incidence side.
-/
theorem zmod2TemporalProductCoverRelativeH1_from_to
    (h : zmod2TemporalProductIncidenceThreeTerm.H1) :
    zmod2TemporalProductCoverRelativeEquivalence.fromH1
      (zmod2TemporalProductCoverRelativeEquivalence.toH1 h) = h :=
  zmod2TemporalProductCoverRelativeEquivalence.from_to_H1 h

/--
IX-3 / #3100: degree-one cochain detected by the identity-leg value.

The cochain is constant `1`; evaluating it on an identity incidence leg is
enough to prove that it is not an incidence coboundary, because every incidence
coboundary vanishes on identity legs.
-/
def zmod2TemporalIdentityLegCochain :
    zmod2TemporalCoefficient.FiberIncidenceOneCochain :=
  fun {_p} {_q} _leg => (1 : ZMod 2)

/-- IX-3 / #3100: the identity-leg cochain is a degree-one cocycle. -/
def zmod2TemporalIdentityLegH1Cocycle :
    zmod2TemporalProductIncidenceThreeTerm.H1Cocycle :=
  ⟨zmod2TemporalIdentityLegCochain, by
    funext σ
    exact Empty.elim σ⟩

/-- IX-3 / #3100: selected H¹ class of the identity-leg cochain. -/
def zmod2TemporalIdentityLegH1Class :
    zmod2TemporalProductIncidenceThreeTerm.H1 :=
  Quotient.mk
    zmod2TemporalProductIncidenceThreeTerm.H1CoboundarySetoid
    zmod2TemporalIdentityLegH1Cocycle

/- IX-3 / #3100: the identity-leg cochain has value `1` on the selected base identity. -/
theorem zmod2TemporalIdentityLegCochain_id_value :
    zmod2TemporalIdentityLegCochain (temporalSite.idLeg p0) = (1 : ZMod 2) := by
  rfl

/--
IX-3 / #3100: the identity-leg H¹ class is nonzero.

If it were a coboundary, evaluating the coboundary equation at an identity leg
would contradict `incidenceDifferential_id`, because all incidence coboundaries
vanish on identity legs.
-/
theorem zmod2TemporalIdentityLegH1Class_ne_zero :
    zmod2TemporalIdentityLegH1Class ≠
      zmod2TemporalProductIncidenceThreeTerm.H1ZeroClass := by
  intro hzero
  have hrel := Quotient.exact hzero
  rcases hrel with ⟨b, hb⟩
  have hvalue :=
    congrArg
      (fun c : zmod2TemporalCoefficient.FiberIncidenceOneCochain =>
        c (temporalSite.idLeg p0)) hb
  have hright :
      zmod2TemporalProductIncidenceThreeTerm.d0 b
          (temporalSite.idLeg p0) = (0 : ZMod 2) := by
    exact zmod2TemporalCoefficient.incidenceDifferential_id b p0
  change _ = zmod2TemporalProductIncidenceThreeTerm.d0 b
    (temporalSite.idLeg p0) at hvalue
  rw [hright] at hvalue
  change zmod2TemporalIdentityLegCochain (temporalSite.idLeg p0) - 0 =
    (0 : ZMod 2) at hvalue
  rw [zmod2TemporalIdentityLegCochain_id_value] at hvalue
  simp at hvalue
  exact (by decide : (1 : ZMod 2) ≠ 0) hvalue

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

/-- R10(b/g): Part IV site cover induced by the finite Part II singleton site. -/
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

/--
IX-3 / #3100: concrete finite-poset comparison data for the two-point trace
singleton coefficient instance.
-/
def unitFinitePosetTemporalCechComparisonData :
    Cohomology.FinitePosetCechComparisonData
      FiniteModel.finitePosetCechComplex unitObstructionSheaf where
  cochainAddCommGroup := unitCechComplex.cochainAddCommGroup
  alternatingFaceCombination := unitCechComplex.alternatingFaceCombination
  differential := unitCechComplex.d
  differential_eq_alternatingFaceCombination :=
    unitCechComplex.differential_eq_alternatingFaceCombination
  differential_comp := unitCechComplex.differential_comp
  toFinitePosetCochain := fun _n _c _σ => PUnit.unit
  fromFinitePosetCochain := fun _n _c _σ => PUnit.unit
  to_from_finitePosetCochain := by
    intro n c
    funext σ
    cases c σ
    rfl
  from_to_finitePosetCochain := by
    intro n c
    funext σ
    cases c σ
    rfl
  differential_compat_toFinitePoset := by
    intro n c
    funext σ
    cases n with
    | zero => exact Empty.elim σ
    | succ _ => exact Empty.elim σ
  finitePosetCoboundaryRelation := FiniteModel.finitePosetCechCoboundaryRelation
  toFinitePosetCohomology := by
    intro n comparisonComplex _h
    exact Quotient.mk
      (Site.FinitePosetCechCoboundarySetoid
        (FiniteModel.finitePosetCechCoboundaryRelation n))
      ⟨(fun σ => PUnit.unit), by
        funext σ
        cases n with
        | zero => exact Empty.elim σ
        | succ _ => exact Empty.elim σ⟩
  fromFinitePosetCohomology := by
    intro n comparisonComplex _h
    cases n with
    | zero =>
        exact ⟨(fun σ => PUnit.unit), by
          funext σ
          rfl⟩
    | succ n =>
        exact Quotient.mk (comparisonComplex.CechCoboundarySetoidSucc n)
          ⟨(fun σ => PUnit.unit), by
            funext σ
            rfl⟩
  to_from_finitePosetCohomology := by
    intro n comparisonComplex h
    refine Quotient.inductionOn h ?_
    intro h
    apply Quot.sound
    apply Subtype.ext
    funext σ
    cases n with
    | zero =>
        cases h.1 σ
        rfl
    | succ _ =>
        exact Empty.elim σ
  from_to_finitePosetCohomology := by
    intro n comparisonComplex h
    cases n with
    | zero =>
        apply Subtype.ext
        funext σ
        cases h.1 σ
        rfl
    | succ n =>
        refine Quotient.inductionOn h ?_
        intro h
        apply Quot.sound
        refine ⟨0, ?_⟩
        funext σ
        cases h.1 σ
        rfl

/-- IX-3 / #3100: finite-poset temporal Čech bridge for the two-point trace fixture. -/
def unitFinitePosetTemporalCechBridge :
    FinitePosetTemporalCechBridge temporalSite unitObstructionSheaf where
  temporalCover := replayTemporalCover
  finitePosetComplex := FiniteModel.finitePosetCechComplex
  coverComparison := replayCoverComparison
  comparison := unitFinitePosetTemporalCechComparisonData

/-- IX-3 / #3100: product incidence plus Part IV cohomology comparison instance. -/
def unitProductIncidencePartIVComparison :
    TemporalCoefficient.ProductIncidencePartIVComparison temporalCoefficient where
  incidenceComplex := unitTemporalProductIncidenceComplex
  finitePosetBridge := unitFinitePosetTemporalCechBridge

/-- IX-3 / #3100: the product instance exposes Part IV differential compatibility. -/
theorem unitProductIncidence_partIV_differential_compatible
    (n : Nat)
    (c : unitProductIncidencePartIVComparison.finitePosetBridge.comparison.generalComplex.Cn n) :
    unitProductIncidencePartIVComparison.partIV_differential_compatible n c =
      unitFinitePosetTemporalCechBridge.differential_compatible n c :=
  rfl

/-- IX-3 / #3100: cohomology comparison is a left inverse on finite-poset cohomology. -/
theorem unitProductIncidence_partIV_cohomology_to_from
    (n : Nat)
    (h : Site.FinitePosetCechCohomology
      FiniteModel.finitePosetCechComplex n
      (FiniteModel.finitePosetCechCoboundaryRelation n)) :
    unitProductIncidencePartIVComparison.partIV_cohomology_to_from n h =
      unitFinitePosetTemporalCechBridge.cohomology_to_from n h :=
  rfl

/-- IX-3 / #3100: cohomology comparison is a right inverse on Part IV cohomology. -/
theorem unitProductIncidence_partIV_cohomology_from_to
    (n : Nat)
    (h :
      unitProductIncidencePartIVComparison.finitePosetBridge.comparison.generalComplex.CoverRelativeHn n) :
    unitProductIncidencePartIVComparison.partIV_cohomology_from_to n h =
      unitFinitePosetTemporalCechBridge.cohomology_from_to n h :=
  rfl

/--
IX-3 / #3100: the Part IX finite-poset comparison surface is not only the
singleton compatibility fixture.  It also imports the two-patch finite-poset
Čech calculation from Part II, where a separated degree-zero cochain has a
nonzero degree-one differential on the selected overlap.
-/
theorem twoPatchProductCech_differential_nonzero :
    FiniteModel.twoPatchCechComplex.differential 0
        FiniteModel.twoPatchSeparatedCochain PUnit.unit = true :=
  FiniteModel.twoPatchSeparatedCochain_differential_nonzero

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
  | terminalToNonlawfulTerminal
  deriving DecidableEq, Fintype

/-- R10(d): explicit finite witness for the three selected dissipative steps. -/
def dissipationStepEquivFin : DissipationStep ≃ Fin 3 where
  toFun
    | .highToMid => ⟨0, by decide⟩
    | .midToTerminal => ⟨1, by decide⟩
    | .terminalToNonlawfulTerminal => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => .highToMid
    | ⟨1, _⟩ => .midToTerminal
    | ⟨2, _⟩ => .terminalToNonlawfulTerminal
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
  | .terminalToNonlawfulTerminal => .terminal

/-- R10(d): target state of each selected dissipative step. -/
def DissipationStep.targetState : DissipationStep -> TinyState
  | .highToMid => .mid
  | .midToTerminal => .terminal
  | .terminalToNonlawfulTerminal => .nonlawfulTerminal

/-- R10(d): selected temporal point for each state in the dissipation fixture. -/
def dissipationStatePoint : TinyState -> temporalSite.Point
  | .high => p0
  | .mid => p1
  | .terminal => p1
  | .nonlawfulTerminal => p1

/-- R10(d): presheaf state carried by each selected dissipation state. -/
def dissipationStateAt (s : TinyState) :
    statePresheaf.State (dissipationStatePoint s) :=
  stateAt (dissipationStatePoint s) s

/-- R10(d): finite strictly dissipative policy. -/
def dissipativePolicy : DissipativePolicy phi where
  SelectedState := TinyState
  point := dissipationStatePoint
  state := dissipationStateAt
  Step := DissipationStep
  sourceState := DissipationStep.sourceState
  targetState := DissipationStep.targetState
  incidence := fun
    | .highToMid => stepLeg
    | .midToTerminal => temporalSite.idLeg p1
    | .terminalToNonlawfulTerminal => temporalSite.idLeg p1
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
  finiteSelectedStates := by
    change Finite TinyState
    infer_instance
  wellFoundedValue := Nat.lt_wfRel.wf
  strict := strictDissipation

/-- R10(d): the finite dissipative fixture has no infinite nonterminal selected path. -/
theorem finite_dissipation_no_infinite_nonterminal_path :
    ¬ ∃ path : InfiniteSelectedEvolutionPath dissipativePolicy,
      path.StaysOutsideTerminal terminalState :=
  finiteDissipationStopping.no_infinite_nonterminal_path

/-- R10(d): a policy-generated trajectory for the selected finite state chain. -/
def policyGeneratedDissipationPath :
    PolicyGeneratedEvolutionPath dissipativePolicy terminalState where
  state
    | 0 => .high
    | 1 => .mid
    | _ + 2 => .terminal
  nextStep := by
    intro n hNonTerminal
    match n with
    | 0 => exact .highToMid
    | 1 => exact .midToTerminal
    | _ + 2 => exact False.elim (hNonTerminal (Or.inl rfl))
  step_source := by
    intro n hNonTerminal
    match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => exact False.elim (hNonTerminal (Or.inl rfl))
  step_target := by
    intro n hNonTerminal
    match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => exact False.elim (hNonTerminal (Or.inl rfl))

/-- R10(d): the terminal state actually occurs at time two in the finite fixture. -/
theorem policy_generated_dissipation_terminal_at_two :
    terminalState.terminal
      (dissipativePolicy.point (policyGeneratedDissipationPath.state 2))
      (dissipativePolicy.state (policyGeneratedDissipationPath.state 2)) :=
  Or.inl rfl

/-- R10(d): theorem 5.3 yields finite-time terminal arrival for the policy-generated fixture. -/
theorem policy_generated_dissipation_reaches_terminal :
    ∃ n : Nat,
      terminalState.terminal
        (dissipativePolicy.point (policyGeneratedDissipationPath.state n))
        (dissipativePolicy.state (policyGeneratedDissipationPath.state n)) :=
  finiteDissipationStopping.policy_generated_path_reaches_terminal
    policyGeneratedDissipationPath

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
    | ⟨2, _⟩ => .terminalToNonlawfulTerminal
    | ⟨n + 3, h⟩ => False.elim (by omega : False)
  continuous := by
    intro i hnext
    rcases i with ⟨i, hi⟩
    interval_cases i
    · rfl
    · rfl
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
  rcases hnext with ⟨next, hnext⟩
  cases next <;> cases hnext

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

/-- R10(f): Lyapunov reading backed by the Part VIII harmonic-mass hook. -/
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

/-- R10(b): selected singleton site cover used by the replay-function sheaf. -/
abbrev zeroReplaySheafCover : Sieve FiniteModel.siteBase :=
  Sieve.generate FiniteModel.siteSingletonCover.presieve

/-- R10(b): raw replay maps on the temporal cover selected by `temporalBridge`. -/
def zeroReplayRawDescentData :
    ReplayRawDescentData statePresheaf temporalCoefficient where
  bridge := temporalBridge
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

/--
R10(b): constructed replay/coefficient representation for the selected finite
fixture.  Every local section, coefficient reading and correction action is
the singleton instance of the corresponding representation operation.  The
generic criterion therefore constructs a global section; the nontrivial
replay-function realization is supplied by the two-patch fixture below.
-/
def zeroReplayRepresentation :
    ReplayCoefficientRepresentation zeroReplayRawDescentData where
  replaySheaf := unitSheaf
  descentCover := zeroReplaySheafCover
  descentCover_topological := FiniteModel.siteSingletonCover_topologyCover
  chartInCover := by
    intro _i
    exact Sieve.le_generate FiniteModel.siteSingletonCover.presieve _
      (Presieve.ofArrows.mk PUnit.unit)
  localSections := fun _Y _f _hf => PUnit.unit
  localReplayOfSection := fun _i _section state =>
    match state with
    | .high => .mid
    | other => other
  localReplay_from_section := by
    intro i
    funext state
    cases i <;> cases state <;> rfl
  coefficientReading := fun _X _section => PUnit.unit
  sectionAction := fun _X _section _correction => PUnit.unit
  sectionAction_zero := by
    intro _X replaySection
    cases replaySection
    rfl
  sectionAction_restrict := by
    intro _X _Y _q replaySection correction
    cases replaySection
    cases correction
    rfl
  coefficientReading_action := by
    intro _X replaySection correction
    cases replaySection
    cases correction
    rfl
  correctionSections := fun _correction _Y _f _hf => PUnit.unit
  correctionSections_zero := by
    intro _Y _f _hf
    rfl
  coefficientReading_zero_reflecting := by
    intro _X left right _hdifference
    cases left
    cases right
    rfl
  overlapCochainValue := fun _f _g _leftRestriction _rightRestriction _cochain =>
    PUnit.unit
  overlapCochainValue_zero := by
    intro _Y _Z _W _f _g _leftRestriction _rightRestriction
    rfl
  overlapCochainValue_sub := by
    intro _Y _Z _W _f _g _leftRestriction _rightRestriction _left _right
    rfl
  mismatchCochain := unitTemporalCochain 1
  restriction_difference := by
    intro _Y _Z _W _f _hf _g _hg _leftRestriction _rightRestriction
    rfl
  correction_restriction_difference := by
    intro _correction _Y _Z _W _f _hf _g _hg _leftRestriction _rightRestriction
    rfl

/-- R10(b): replay data whose constructed representation is fed to theorem 4.2. -/
def zeroReplayDescentData :
    ReplayDescentData statePresheaf temporalCoefficient temporalLaw where
  raw := zeroReplayRawDescentData
  representation := zeroReplayRepresentation
  mismatchSupportedByLaw := True
  mismatchSupportedByLaw_cert := trivial

/-- R10(b): the selected zero replay mismatch is a cocycle. -/
def zeroReplayMismatchCocycle :
    ReplayMismatchCocycle zeroReplayDescentData where
  differential_zero := by
    funext _σ
    rfl

/-- R10(b): temporal class package selected by the zero replay mismatch. -/
def zeroReplayTemporalClass :
    TemporalClass zeroReplayDescentData.mismatch where
  cocycle := zeroReplayMismatchCocycle.toTemporalCocycle

/-- R10(b): concrete theorem-4.2 assumptions for the zero replay fixture. -/
theorem zeroReplayTemporalDescentCriterion :
    TemporalDescentCriterion zeroReplayDescentData where
  mismatchCocycle := zeroReplayMismatchCocycle
  temporalClass := zeroReplayTemporalClass
  temporalClass_matches_mismatch := rfl
  classVanishes_cert := by rfl

/-- R10(b): the section-level descent lemma yields a global replay section. -/
theorem replay_zero_theorem42_global_section_exists :
    Nonempty zeroReplayDescentData.GlobalReplaySection :=
  zeroReplayTemporalDescentCriterion.temporal_descent_section_criterion

/-- R10(b): the finite theorem-4.2 construction returns an adjusted global section. -/
theorem replay_zero_theorem42_realizes_adjusted :
    ∃ (correction : temporalBridge.siteComplex.Cn 0)
      (globalSection : zeroReplayDescentData.GlobalReplaySection),
      ∀ (i : replayTemporalCover.Index),
        zeroReplayRepresentation.replaySheaf.toPresheaf.map
            (temporalBridge.siteCover.inclusion
              (temporalBridge.coverComparison.siteIndexOf i)).op globalSection =
          zeroReplayDescentData.adjustedLocalSections correction
            (temporalBridge.siteCover.inclusion
              (temporalBridge.coverComparison.siteIndexOf i))
            (zeroReplayRepresentation.chartInCover i) :=
  zeroReplayTemporalDescentCriterion.temporal_descent_section_criterion_realizes_adjusted

/-- R10(b): the zero fixture uses the theorem-4.2 global-section construction itself. -/
theorem replay_zero_theorem42_applied :
    Nonempty zeroReplayDescentData.GlobalReplaySection :=
  replay_zero_theorem42_global_section_exists

/-- R10(b): the selected finite replay transition is explicit. -/
theorem replay_zero_has_global_transition :
    ∃ globalReplay : TinyState -> TinyState,
      globalReplay TinyState.high = TinyState.mid := by
  refine ⟨fun state => match state with | .high => .mid | other => other, rfl⟩

/-- R10(b/g): explicit replay transition selected by the finite force fixture. -/
noncomputable def zeroReplayGlobalTransition : TinyState -> TinyState :=
  Classical.choose replay_zero_has_global_transition

/-- R10(b/g): the selected explicit transition sends high state to mid. -/
theorem zeroReplayGlobalTransition_hits_high :
  zeroReplayGlobalTransition TinyState.high = TinyState.mid :=
  Classical.choose_spec replay_zero_has_global_transition

/-- R10(b): two finite temporal charts carrying `ZMod 2`-valued replay corrections. -/
abbrev TwoChartTemporalCoefficient := ZMod 2

/-- R10(b): the unadjusted right replay differs from the left replay by one coefficient unit. -/
def twoChartLocalReplay (chart : Bool) (state : TwoChartTemporalCoefficient) :
    TwoChartTemporalCoefficient :=
  match chart with
  | false => state
  | true => state + 1

/-- R10(b): the nonzero degree-zero correction on the right temporal chart. -/
def twoChartCorrection (chart : Bool) : TwoChartTemporalCoefficient :=
  match chart with
  | false => 0
  | true => 1

/-- R10(b): the corrected local replay maps. -/
def twoChartAdjustedReplay (chart : Bool) (state : TwoChartTemporalCoefficient) :
    TwoChartTemporalCoefficient :=
  twoChartLocalReplay chart state - twoChartCorrection chart

/-- R10(b): the explicit two-chart replay mismatch. -/
def twoChartReplayMismatch : TwoChartTemporalCoefficient :=
  twoChartLocalReplay true 0 - twoChartLocalReplay false 0

/-- R10(b): the Čech degree-zero coboundary determined by the correction. -/
def twoChartCorrectionCoboundary : TwoChartTemporalCoefficient :=
  twoChartCorrection true - twoChartCorrection false

/-- R10(b): the selected correction is genuinely nonzero. -/
theorem twoChartCorrection_right_nonzero : twoChartCorrection true ≠ 0 := by
  decide

/-- R10(b): the mismatch is exactly the coboundary of the selected correction. -/
theorem twoChartReplayMismatch_eq_coboundary :
    twoChartReplayMismatch = twoChartCorrectionCoboundary := by
  norm_num [twoChartReplayMismatch, twoChartCorrectionCoboundary,
    twoChartLocalReplay, twoChartCorrection]

/-- R10(b): correction kills the two-chart mismatch. -/
theorem twoChartAdjustedMismatch_zero :
    twoChartReplayMismatch - twoChartCorrectionCoboundary = 0 := by
  rw [twoChartReplayMismatch_eq_coboundary]
  exact sub_self _

/-- R10(b): after correction, the two local replay maps agree on every finite state. -/
theorem twoChartAdjustedReplay_matching (state : TwoChartTemporalCoefficient) :
    twoChartAdjustedReplay false state = twoChartAdjustedReplay true state := by
  simp [twoChartAdjustedReplay, twoChartLocalReplay, twoChartCorrection]

/-- R10(b): nondegenerate finite temporal replay correction and temporal differential. -/
theorem nondegenerate_twoChart_temporal_replay_correction :
    twoChartCorrection true ≠ 0 ∧
      twoChartReplayMismatch = twoChartCorrectionCoboundary ∧
        twoChartReplayMismatch - twoChartCorrectionCoboundary = 0 ∧
          (∀ state : TwoChartTemporalCoefficient,
            twoChartAdjustedReplay false state = twoChartAdjustedReplay true state) ∧
            zmod2TemporalProductIncidenceComplex.d0
              zmod2TemporalSeparatedCochain stepLeg ≠ 0 :=
  ⟨twoChartCorrection_right_nonzero, twoChartReplayMismatch_eq_coboundary,
    twoChartAdjustedMismatch_zero, twoChartAdjustedReplay_matching,
    zmod2TemporalProductIncidence_d0_step_ne_zero⟩

/-- The two selected replay charts as objects of the actual AAT two-patch site. -/
def twoPatchReplayChartObject (i : FiniteModel.TwoPatchCoverIndex) :
    FiniteModel.twoPatchSite.category :=
  Site.ContextCategoryObject.of FiniteModel.twoPatchContextPreorder
    (FiniteModel.twoPatchCoverPatch i)

/-- The two actual replay-chart objects are distinct. -/
theorem twoPatchReplayChartObject_left_ne_right :
    twoPatchReplayChartObject .left ≠ twoPatchReplayChartObject .right := by
  intro h
  have hcontext := congrArg Site.ContextCategoryObject.ctx h
  cases hcontext

/-- The actual overlap object of the selected AAT two-patch site. -/
def twoPatchReplayOverlapObject : FiniteModel.twoPatchSite.category :=
  Site.ContextCategoryObject.of FiniteModel.twoPatchContextPreorder
    (FiniteModel.twoPatchContext FiniteModel.TwoPatchContextIndex.overlap)

/-- Restriction from the selected overlap to either replay chart. -/
noncomputable def twoPatchReplayOverlapRestriction
    (i : FiniteModel.TwoPatchCoverIndex) :
    twoPatchReplayOverlapObject ⟶ twoPatchReplayChartObject i := by
  cases i
  · exact homOfLE FiniteModel.twoPatch_overlap_le_left
  · exact homOfLE FiniteModel.twoPatch_overlap_le_right

/-- Convert a selected AAT two-patch index to the temporal replay-chart index. -/
def twoPatchReplayChart : FiniteModel.TwoPatchCoverIndex -> Bool
  | .left => false
  | .right => true

/--
The two local replay maps as sections of the actual translation-replay sheaf.

The coefficient is the translation parameter itself, so it determines the
whole replay map on every source state.
-/
def twoPatchReplayLocalSection (i : FiniteModel.TwoPatchCoverIndex) :
    FiniteModel.twoPatchZMod2TranslationReplayPresheaf.obj
      (Opposite.op (twoPatchReplayChartObject i)) :=
  match i with
  | .left => ⟨0⟩
  | .right => ⟨1⟩

/-- Each chart carries a replay along the same fixed `tinyStep : t0 ⟶ t1`. -/
def twoPatchReplayLocalTransition (i : FiniteModel.TwoPatchCoverIndex) :
    TwoPatchTemporalReplayAlong tinyStep
      (twoPatchReplayTemporalCover.chartContext i)
      (twoPatchReplayTemporalCover.chartContext i) where
  trace_selected := twoPatchReplayTemporalTrace_selected
  toFun := FiniteModel.TwoPatchZMod2TranslationReplay.apply
    (twoPatchReplayLocalSection i)

/-- Each indexed chart transition evaluates to its selected local replay map. -/
theorem twoPatchReplayLocalSection_apply (i : FiniteModel.TwoPatchCoverIndex)
    (state : twoPatchReplayTemporalStatePresheaf.State
      (TinyTime.t0, twoPatchReplayTemporalCover.chartContext i)) :
    (twoPatchReplayLocalTransition i).toFun state =
        twoChartLocalReplay (twoPatchReplayChart i) state := by
  cases i <;> simp [twoPatchReplayLocalSection,
    twoPatchReplayLocalTransition,
    FiniteModel.TwoPatchZMod2TranslationReplay.apply, twoPatchReplayChart,
    twoChartLocalReplay]

/-- The selected degree-zero correction, read on the actual two-patch AAT cover. -/
def twoPatchReplayCorrectionSection (i : FiniteModel.TwoPatchCoverIndex) : ZMod 2 :=
  twoChartCorrection (twoPatchReplayChart i)

/--
The degree-zero Čech cochain is read from the translation coefficient of each
actual local replay section.  It is not a sampled value of a general function.
-/
def twoPatchReplayCechZeroCochain :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 0 :=
  fun i => (twoPatchReplayLocalSection i).coefficient

/--
Restrict a Čech degree-zero coefficient to the actual overlap through the
translation-replay presheaf. This reader retains the two overlap morphisms
used by the Čech differential instead of copying chart values directly.
-/
def twoPatchReplayCechRestrictionToOverlap
    (cochain : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (i : FiniteModel.TwoPatchCoverIndex) : ZMod 2 :=
  (FiniteModel.twoPatchZMod2TranslationReplayPresheaf.map
      (twoPatchReplayOverlapRestriction i).op
      (show FiniteModel.TwoPatchZMod2TranslationReplay from ⟨cochain i⟩)).coefficient

/-- The nonzero degree-zero correction on the same actual two-patch Čech cover. -/
def twoPatchReplayCorrectionCochain :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 0 :=
  fun i => twoPatchReplayCorrectionSection i

/-- Pointwise additive structure on the actual two-patch `ZMod 2` Čech cochains. -/
noncomputable local instance twoPatchReplayCechCochainAddCommGroup (n : Nat) :
    AddCommGroup
      (Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime n) := by
  change AddCommGroup
    ((simplex : Site.FinitePosetCechSimplex
      FiniteModel.twoPatchZMod2FinitePosetRegime n) -> ZMod 2)
  infer_instance

/-- The mismatch is the actual degree-one differential of the replay coefficient cochain. -/
def twoPatchReplayCechMismatch :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 1 :=
  FiniteModel.twoPatchZMod2CechComplex.differential 0 twoPatchReplayCechZeroCochain

/-- The actual two-patch mismatch is exactly the coboundary of its nonzero correction. -/
theorem twoPatchReplayCechMismatch_eq_correction :
    twoPatchReplayCechMismatch =
      FiniteModel.twoPatchZMod2CechComplex.differential 0
        twoPatchReplayCorrectionCochain := by
  funext simplex
  cases simplex
  rfl

/-- The actual two-patch mismatch has a concrete degree-zero primitive. -/
theorem twoPatchReplay_class_zero :
    ∃ correction : Site.FinitePosetCechCochain
        FiniteModel.twoPatchZMod2FinitePosetRegime 0,
      twoPatchReplayCechMismatch =
        FiniteModel.twoPatchZMod2CechComplex.differential 0 correction :=
  ⟨twoPatchReplayCorrectionCochain, twoPatchReplayCechMismatch_eq_correction⟩

/--
Read an actual degree-zero Čech cochain on every point of the actual
`Tr_E × X` temporal site. Both selected endpoint values are obtained through
the actual chart-to-overlap restriction maps. The remaining product points use
the corresponding restricted face so the full temporal carrier is available
while the chosen `overlap -> base` incidence computes the oriented
right-minus-left Čech difference.

The alternative of assigning raw chart values directly is intentionally not
used: it would reproduce the coefficient difference without retaining the two
actual overlap morphisms that supply its Čech provenance.
-/
def twoPatchReplayCochainToTemporalProduct
    (cochain : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    twoPatchReplayTemporalCoefficient.FiberZeroCochain
  | (_, .overlap) => twoPatchReplayCechRestrictionToOverlap cochain .left
  | (_, .left) => twoPatchReplayCechRestrictionToOverlap cochain .left
  | (_, .right) => twoPatchReplayCechRestrictionToOverlap cochain .right
  | (_, .base) => twoPatchReplayCechRestrictionToOverlap cochain .right

/-- Read a full temporal incidence one-cochain at the actual Čech overlap simplex. -/
def twoPatchReplayTemporalProductToCechOne
    (cochain : twoPatchReplayTemporalCoefficient.FiberIncidenceOneCochain) :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 1 :=
  fun _ => cochain twoPatchReplayTemporalCechLeg

/--
The product target over the common base reads the actual right-chart
restriction to the overlap.
-/
theorem twoPatchReplayCochainToTemporalProduct_target_reads_right_chart
    (cochain : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    twoPatchReplayCochainToTemporalProduct cochain twoPatchReplayTemporalTarget =
      twoPatchReplayCochainToTemporalProduct cochain
        (twoPatchReplayTemporalCover.chartTrace .right,
          twoPatchReplayTemporalCover.chartContext .right) := by
  rfl

/--
The selected temporal source and target read the two actual chart restrictions
on the overlap. Their difference is therefore the same typed restriction pair
used by the Čech differential.
-/
theorem twoPatchReplayCochainToTemporalProduct_endpoints
    (cochain : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    twoPatchReplayCochainToTemporalProduct cochain twoPatchReplayTemporalCechSource =
        twoPatchReplayCechRestrictionToOverlap cochain .left ∧
      twoPatchReplayCochainToTemporalProduct cochain twoPatchReplayTemporalTarget =
        twoPatchReplayCechRestrictionToOverlap cochain .right := by
  exact ⟨rfl, rfl⟩

/--
The actual two-patch Čech differential is the difference of the right and left
presheaf restrictions to the overlap.
-/
theorem twoPatchReplayCechDifferential_eq_overlap_restrictions
    (cochain : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (simplex : Site.FinitePosetCechSimplex
      FiniteModel.twoPatchZMod2FinitePosetRegime 1) :
    FiniteModel.twoPatchZMod2CechComplex.differential 0 cochain simplex =
      twoPatchReplayCechRestrictionToOverlap cochain .right -
        twoPatchReplayCechRestrictionToOverlap cochain .left := by
  cases simplex
  rfl

/--
The full product-incidence differential reads to the actual two-patch Čech
differential on the selected overlap.  This compares the temporal `C⁰/C¹`
carriers to the actual Čech `C⁰/C¹` carriers, rather than retyping a Čech
cochain as a temporal one.
-/
theorem twoPatchReplayTemporalProduct_d0_compatible
    (cochain : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    twoPatchReplayTemporalProductToCechOne
        (twoPatchReplayTemporalProductIncidenceComplex.d0
          (twoPatchReplayCochainToTemporalProduct cochain)) =
      FiniteModel.twoPatchZMod2CechComplex.differential 0 cochain := by
  funext simplex
  rw [twoPatchReplayCechDifferential_eq_overlap_restrictions]
  rfl

/-- The initial and correction cochains agree on every temporal product point. -/
theorem twoPatchReplayCochainToTemporalProduct_zero_eq_correction :
    twoPatchReplayCochainToTemporalProduct twoPatchReplayCechZeroCochain =
      twoPatchReplayCochainToTemporalProduct twoPatchReplayCorrectionCochain := by
  funext point
  rcases point with ⟨time, context⟩
  cases time <;> cases context <;> rfl

/-- The product-incidence class-zero equality holds on every selected temporal leg. -/
theorem twoPatchReplayTemporalProductMismatch_eq_correction :
    ∀ {p q : twoPatchReplayTemporalSite.Point}
      (leg : twoPatchReplayTemporalSite.IncidenceLeg p q),
      twoPatchReplayTemporalProductIncidenceComplex.d0
          (twoPatchReplayCochainToTemporalProduct twoPatchReplayCechZeroCochain) leg =
        twoPatchReplayTemporalProductIncidenceComplex.d0
          (twoPatchReplayCochainToTemporalProduct twoPatchReplayCorrectionCochain) leg := by
  intro p q leg
  rw [twoPatchReplayCochainToTemporalProduct_zero_eq_correction]

/-- Every temporal replay chart is the corresponding chart of the actual two-patch cover. -/
theorem twoPatchReplayTemporalCover_reads_actual_chart
    (i : FiniteModel.TwoPatchCoverIndex) :
    (Cohomology.finitePosetCoverRelativeCover
      FiniteModel.twoPatchZMod2CechComplex).chart
        (twoPatchReplayTemporalCoverComparison.siteIndexOf i) =
      Site.ContextCategoryObject.of FiniteModel.twoPatchSite.contextPreorder
        (twoPatchReplayTemporalSite.siteRegime.context
          (twoPatchReplayTemporalCover.chartContext i)) :=
  twoPatchReplayTemporalCoverComparison.chart_eq i

/-- The actual class-zero witness is the selected reading of the product differential. -/
theorem twoPatchReplayTemporalMismatch_eq_correction :
    twoPatchReplayCechMismatch =
      twoPatchReplayTemporalProductToCechOne
        (twoPatchReplayTemporalProductIncidenceComplex.d0
          (twoPatchReplayCochainToTemporalProduct
            twoPatchReplayCorrectionCochain)) := by
  rw [twoPatchReplayCechMismatch_eq_correction]
  exact (twoPatchReplayTemporalProduct_d0_compatible
    twoPatchReplayCorrectionCochain).symm

/--
The full temporal product equality reads back to the actual Čech primitive.
This is the product-incidence step used by the subsequent corrected-zero and
sheaf-descent proof chain.
-/
theorem twoPatchReplayCechMismatch_eq_correction_via_temporal_product :
    twoPatchReplayCechMismatch =
      FiniteModel.twoPatchZMod2CechComplex.differential 0
        twoPatchReplayCorrectionCochain := by
  calc
    twoPatchReplayCechMismatch =
        twoPatchReplayTemporalProductToCechOne
          (twoPatchReplayTemporalProductIncidenceComplex.d0
            (twoPatchReplayCochainToTemporalProduct
              twoPatchReplayCechZeroCochain)) :=
      (twoPatchReplayTemporalProduct_d0_compatible
        twoPatchReplayCechZeroCochain).symm
    _ = twoPatchReplayTemporalProductToCechOne
          (twoPatchReplayTemporalProductIncidenceComplex.d0
            (twoPatchReplayCochainToTemporalProduct
              twoPatchReplayCorrectionCochain)) := by
      funext simplex
      cases simplex
      exact twoPatchReplayTemporalProductMismatch_eq_correction
        twoPatchReplayTemporalCechLeg
    _ = FiniteModel.twoPatchZMod2CechComplex.differential 0
          twoPatchReplayCorrectionCochain :=
      twoPatchReplayTemporalProduct_d0_compatible
        twoPatchReplayCorrectionCochain

/--
The replay mismatch is the difference of the two restricted translation
coefficients on the actual overlap.  The coefficient reader is reflective:
equal coefficients are equal translation replay sections.
-/
def twoPatchReplayOverlapMismatch : ZMod 2 :=
  (FiniteModel.twoPatchZMod2TranslationReplayPresheaf.map
      (twoPatchReplayOverlapRestriction .right).op
      (twoPatchReplayLocalSection .right)).coefficient -
    (FiniteModel.twoPatchZMod2TranslationReplayPresheaf.map
      (twoPatchReplayOverlapRestriction .left).op
      (twoPatchReplayLocalSection .left)).coefficient

/-- The actual overlap mismatch is the selected nonzero coefficient coboundary. -/
theorem twoPatchReplayOverlapMismatch_eq_coboundary :
    twoPatchReplayOverlapMismatch = twoChartCorrectionCoboundary :=
  rfl

/-- The pre-correction actual overlap mismatch is nonzero. -/
theorem twoPatchReplayOverlapMismatch_ne_zero :
    twoPatchReplayOverlapMismatch ≠ 0 := by
  change (1 : ZMod 2) - 0 ≠ 0
  decide

/-- The degree-one Čech mismatch is the same restricted-section coefficient difference. -/
theorem twoPatchReplayCechMismatch_eq_overlap
    (simplex : Site.FinitePosetCechSimplex
      FiniteModel.twoPatchZMod2FinitePosetRegime 1) :
    twoPatchReplayCechMismatch simplex = twoPatchReplayOverlapMismatch := by
  cases simplex
  rfl

/-- Restrict an indexed chart replay to the actual overlap along the same trace arrow. -/
noncomputable def twoPatchReplayRestrictedLocalTransition
    (i : FiniteModel.TwoPatchCoverIndex) :
    TwoPatchTemporalReplayAlong tinyStep
      FiniteModel.TwoPatchContextIndex.overlap
      FiniteModel.TwoPatchContextIndex.overlap where
  trace_selected := twoPatchReplayTemporalTrace_selected
  toFun := FiniteModel.TwoPatchZMod2TranslationReplay.apply
    (FiniteModel.twoPatchZMod2TranslationReplayPresheaf.map
      (twoPatchReplayOverlapRestriction i).op
      (twoPatchReplayLocalSection i))

/-- The coefficient mismatch equals the indexed overlap replay difference on every state. -/
theorem twoPatchReplayRestrictedDifference_eq_overlap
    (state : twoPatchReplayTemporalStatePresheaf.State
      (TinyTime.t0, FiniteModel.TwoPatchContextIndex.overlap)) :
    (twoPatchReplayRestrictedLocalTransition .right).value state -
      (twoPatchReplayRestrictedLocalTransition .left).value state =
        twoPatchReplayOverlapMismatch := by
  change ZMod 2 at state
  change state + 1 - (state + 0) = 1 - 0
  ring

/-- Apply an arbitrary degree-zero correction to each actual translation replay section. -/
def twoPatchAdjustedReplayLocalSectionBy
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (i : FiniteModel.TwoPatchCoverIndex) :
    FiniteModel.TwoPatchZMod2TranslationReplay :=
  FiniteModel.TwoPatchZMod2TranslationReplay.adjust
    (twoPatchReplayLocalSection i) (correction i)

/-- The selected correction acts on each actual translation replay section. -/
def twoPatchAdjustedReplayLocalSection (i : FiniteModel.TwoPatchCoverIndex) :
    FiniteModel.TwoPatchZMod2TranslationReplay :=
  twoPatchAdjustedReplayLocalSectionBy twoPatchReplayCorrectionCochain i

/-- Apply an arbitrary degree-zero correction to an indexed chart replay. -/
def twoPatchReplayAdjustedLocalTransitionBy
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (i : FiniteModel.TwoPatchCoverIndex) :
    TwoPatchTemporalReplayAlong tinyStep
      (twoPatchReplayTemporalCover.chartContext i)
      (twoPatchReplayTemporalCover.chartContext i) where
  trace_selected := twoPatchReplayTemporalTrace_selected
  toFun := FiniteModel.TwoPatchZMod2TranslationReplay.apply
    (twoPatchAdjustedReplayLocalSectionBy correction i)

/-- The fixed adjusted chart replay remains indexed by the same trace arrow. -/
def twoPatchAdjustedReplayLocalTransition (i : FiniteModel.TwoPatchCoverIndex) :
    TwoPatchTemporalReplayAlong tinyStep
      (twoPatchReplayTemporalCover.chartContext i)
      (twoPatchReplayTemporalCover.chartContext i) :=
  twoPatchReplayAdjustedLocalTransitionBy twoPatchReplayCorrectionCochain i

/-- The correction action realizes `m(adjust(c,r)) = m(r) - d c` pointwise. -/
theorem twoPatchAdjustedReplayLocalSection_coefficient
    (i : FiniteModel.TwoPatchCoverIndex) :
    (twoPatchAdjustedReplayLocalSection i).coefficient =
      (twoPatchReplayLocalSection i).coefficient -
        twoPatchReplayCorrectionSection i :=
  FiniteModel.TwoPatchZMod2TranslationReplay.coefficient_adjust _ _

/-- Read the corrected degree-zero cochain from an arbitrary correction action. -/
def twoPatchAdjustedReplayCechZeroCochainBy
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 0 :=
  fun i => (twoPatchAdjustedReplayLocalSectionBy correction i).coefficient

/-- The selected corrected degree-zero cochain. -/
def twoPatchAdjustedReplayCechZeroCochain :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 0 :=
  twoPatchAdjustedReplayCechZeroCochainBy twoPatchReplayCorrectionCochain

/-- Compute the adjusted mismatch from the same actual Čech differential. -/
def twoPatchAdjustedReplayCechMismatchBy
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 1 :=
  FiniteModel.twoPatchZMod2CechComplex.differential 0
    (twoPatchAdjustedReplayCechZeroCochainBy correction)

/-- The adjusted mismatch for the selected correction. -/
def twoPatchAdjustedReplayCechMismatch :
    Site.FinitePosetCechCochain FiniteModel.twoPatchZMod2FinitePosetRegime 1 :=
  twoPatchAdjustedReplayCechMismatchBy twoPatchReplayCorrectionCochain

/-- The Čech differential realizes an arbitrary correction action on actual sections. -/
theorem twoPatchAdjustedReplayCechMismatchBy_eq_sub
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    twoPatchAdjustedReplayCechMismatchBy correction =
      twoPatchReplayCechMismatch -
        FiniteModel.twoPatchZMod2CechComplex.differential 0 correction := by
  funext simplex
  cases simplex
  change ((1 : ZMod 2) - (show ZMod 2 from correction .right)) -
      ((0 : ZMod 2) - (show ZMod 2 from correction .left)) =
    ((1 : ZMod 2) - 0) -
      ((show ZMod 2 from correction .right) -
        (show ZMod 2 from correction .left))
  ring

/-- The selected correction action satisfies the same Čech subtraction formula. -/
theorem twoPatchAdjustedReplayCechMismatch_eq_sub :
    twoPatchAdjustedReplayCechMismatch =
      twoPatchReplayCechMismatch -
        FiniteModel.twoPatchZMod2CechComplex.differential 0
          twoPatchReplayCorrectionCochain :=
  twoPatchAdjustedReplayCechMismatchBy_eq_sub twoPatchReplayCorrectionCochain

/-- A supplied actual primitive makes its corrected Čech mismatch zero. -/
theorem twoPatchAdjustedReplayCechMismatchBy_zero_of_class_zero
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (hclass : twoPatchReplayCechMismatch =
      FiniteModel.twoPatchZMod2CechComplex.differential 0 correction) :
    twoPatchAdjustedReplayCechMismatchBy correction = 0 := by
  rw [twoPatchAdjustedReplayCechMismatchBy_eq_sub, hclass]
  exact sub_self _

/-- The corrected local replay cochain has zero actual Čech mismatch. -/
theorem twoPatchAdjustedReplayCechMismatch_zero :
    twoPatchAdjustedReplayCechMismatch = 0 :=
  twoPatchAdjustedReplayCechMismatchBy_zero_of_class_zero
    twoPatchReplayCorrectionCochain
    twoPatchReplayCechMismatch_eq_correction_via_temporal_product

/-- Read the post-correction mismatch as an actual restricted-section difference. -/
def twoPatchAdjustedReplayOverlapMismatchBy
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) : ZMod 2 :=
  (FiniteModel.twoPatchZMod2TranslationReplayPresheaf.map
      (twoPatchReplayOverlapRestriction .right).op
      (twoPatchAdjustedReplayLocalSectionBy correction .right)).coefficient -
    (FiniteModel.twoPatchZMod2TranslationReplayPresheaf.map
      (twoPatchReplayOverlapRestriction .left).op
      (twoPatchAdjustedReplayLocalSectionBy correction .left)).coefficient

/-- The post-correction mismatch for the selected correction. -/
def twoPatchAdjustedReplayOverlapMismatch : ZMod 2 :=
  twoPatchAdjustedReplayOverlapMismatchBy twoPatchReplayCorrectionCochain

/-- The explicit correction kills the actual overlap mismatch. -/
theorem twoPatchAdjustedReplayOverlapMismatch_zero :
    twoPatchAdjustedReplayOverlapMismatch = 0 := by
  change ((1 : ZMod 2) - 1) - (0 - 0) = 0
  ring

/-- Every adjusted degree-one Čech mismatch is its actual overlap difference. -/
theorem twoPatchAdjustedReplayCechMismatchBy_eq_overlap
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (simplex : Site.FinitePosetCechSimplex
      FiniteModel.twoPatchZMod2FinitePosetRegime 1) :
    twoPatchAdjustedReplayCechMismatchBy correction simplex =
      twoPatchAdjustedReplayOverlapMismatchBy correction := by
  cases simplex
  rfl

/-- The selected adjusted Čech mismatch is the selected overlap difference. -/
theorem twoPatchAdjustedReplayCechMismatch_eq_overlap
    (simplex : Site.FinitePosetCechSimplex
      FiniteModel.twoPatchZMod2FinitePosetRegime 1) :
    twoPatchAdjustedReplayCechMismatch simplex =
      twoPatchAdjustedReplayOverlapMismatch :=
  twoPatchAdjustedReplayCechMismatchBy_eq_overlap
    twoPatchReplayCorrectionCochain simplex

/-- Restrict an adjusted indexed chart replay to the actual overlap. -/
noncomputable def twoPatchAdjustedReplayRestrictedTransition
    (i : FiniteModel.TwoPatchCoverIndex) :
    TwoPatchTemporalReplayAlong tinyStep
      FiniteModel.TwoPatchContextIndex.overlap
      FiniteModel.TwoPatchContextIndex.overlap where
  trace_selected := twoPatchReplayTemporalTrace_selected
  toFun := FiniteModel.TwoPatchZMod2TranslationReplay.apply
    (FiniteModel.twoPatchZMod2TranslationReplayPresheaf.map
      (twoPatchReplayOverlapRestriction i).op
      (twoPatchAdjustedReplayLocalSection i))

/-- The adjusted mismatch equals the indexed overlap replay difference. -/
theorem twoPatchAdjustedReplayRestrictedDifference_eq_overlap
    (state : twoPatchReplayTemporalStatePresheaf.State
      (TinyTime.t0, FiniteModel.TwoPatchContextIndex.overlap)) :
    (twoPatchAdjustedReplayRestrictedTransition .right).value state -
      (twoPatchAdjustedReplayRestrictedTransition .left).value state =
        twoPatchAdjustedReplayOverlapMismatch := by
  change ZMod 2 at state
  change state + (1 - 1) - (state + (0 - 0)) = (1 - 1) - (0 - 0)
  ring

/-- Zero overlap mismatch reflects matching for any corrected translation sections. -/
theorem twoPatchAdjustedReplayBy_zero_reflects_matching
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (hzero : twoPatchAdjustedReplayOverlapMismatchBy correction = 0) :
    twoPatchAdjustedReplayLocalSectionBy correction .left =
      twoPatchAdjustedReplayLocalSectionBy correction .right := by
  have hcoefficient :
      (twoPatchAdjustedReplayLocalSectionBy correction .right).coefficient -
        (twoPatchAdjustedReplayLocalSectionBy correction .left).coefficient = 0 := by
    simpa [twoPatchAdjustedReplayOverlapMismatchBy] using hzero
  apply FiniteModel.TwoPatchZMod2TranslationReplay.ext
  exact (sub_eq_zero.mp hcoefficient).symm

/-- The selected zero coefficient mismatch reflects equality of corrected sections. -/
theorem twoPatchAdjustedReplay_zero_reflects_matching
    (hzero : twoPatchAdjustedReplayOverlapMismatch = 0) :
    twoPatchAdjustedReplayLocalSection .left =
      twoPatchAdjustedReplayLocalSection .right :=
  twoPatchAdjustedReplayBy_zero_reflects_matching
    twoPatchReplayCorrectionCochain hzero

/-- A supplied actual Čech primitive makes the two corrected chart sections equal. -/
theorem twoPatchAdjustedReplayLocalSectionBy_matching_of_class_zero
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (hclass : twoPatchReplayCechMismatch =
      FiniteModel.twoPatchZMod2CechComplex.differential 0 correction) :
    twoPatchAdjustedReplayLocalSectionBy correction .left =
      twoPatchAdjustedReplayLocalSectionBy correction .right := by
  have hcech : twoPatchAdjustedReplayCechMismatchBy correction = 0 :=
    twoPatchAdjustedReplayCechMismatchBy_zero_of_class_zero correction hclass
  have hoverlap : twoPatchAdjustedReplayOverlapMismatchBy correction = 0 := by
    have hvalue := congrFun hcech PUnit.unit
    rw [twoPatchAdjustedReplayCechMismatchBy_eq_overlap correction] at hvalue
    change twoPatchAdjustedReplayOverlapMismatchBy correction = (0 : ZMod 2) at hvalue
    exact hvalue
  exact twoPatchAdjustedReplayBy_zero_reflects_matching correction hoverlap

/-- The selected generated AAT cover for the two replay charts. -/
noncomputable def twoPatchReplayCover : Sieve FiniteModel.twoPatchBase :=
  Sieve.generate FiniteModel.twoPatchCover.presieve

/-- Membership of each selected replay chart in the generated AAT two-patch cover. -/
theorem twoPatchReplayCover_contains
    (i : FiniteModel.TwoPatchCoverIndex) :
    twoPatchReplayCover
      (homOfLE (FiniteModel.twoPatchCover.inclusion i)) :=
  Sieve.le_generate FiniteModel.twoPatchCover.presieve _ (Presieve.ofArrows.mk i)

/-- The actual local family obtained by correcting each selected replay chart. -/
noncomputable def twoPatchCorrectedLocalSectionsBy
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0) :
    Site.AATLocalSectionFamily FiniteModel.twoPatchSite
      FiniteModel.twoPatchZMod2TranslationReplayPresheaf twoPatchReplayCover := by
  classical
  exact fun Y _f _hf =>
    if Y = twoPatchReplayChartObject .right then
      twoPatchAdjustedReplayLocalSectionBy correction .right
    else
      twoPatchAdjustedReplayLocalSectionBy correction .left

/-- The actual corrected local family restricts to its selected corrected chart. -/
theorem twoPatchCorrectedLocalSectionsBy_chart
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (i : FiniteModel.TwoPatchCoverIndex) :
    twoPatchCorrectedLocalSectionsBy correction
        (homOfLE (FiniteModel.twoPatchCover.inclusion i))
        (twoPatchReplayCover_contains i) =
      twoPatchAdjustedReplayLocalSectionBy correction i := by
  classical
  cases i
  · change (if twoPatchReplayChartObject .left = twoPatchReplayChartObject .right then
        twoPatchAdjustedReplayLocalSectionBy correction .right
      else twoPatchAdjustedReplayLocalSectionBy correction .left) =
        twoPatchAdjustedReplayLocalSectionBy correction .left
    rw [if_neg twoPatchReplayChartObject_left_ne_right]
  · change (if twoPatchReplayChartObject .right = twoPatchReplayChartObject .right then
        twoPatchAdjustedReplayLocalSectionBy correction .right
      else twoPatchAdjustedReplayLocalSectionBy correction .left) =
        twoPatchAdjustedReplayLocalSectionBy correction .right
    rw [if_pos rfl]

/-- Corrected chart matching supplies the overlap agreement consumed by descent. -/
theorem twoPatchCorrectedLocalSectionsBy_matching
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (hmatching :
      twoPatchAdjustedReplayLocalSectionBy correction .left =
        twoPatchAdjustedReplayLocalSectionBy correction .right) :
    Site.AATOverlapAgreement (twoPatchCorrectedLocalSectionsBy correction) := by
  intro Y Z _W _h _hh _f _g _hf _hg _hcomp
  classical
  simp only [FiniteModel.twoPatchZMod2TranslationReplayPresheaf,
    twoPatchCorrectedLocalSectionsBy]
  split_ifs <;> simp_all

/--
An actual Čech primitive implies descent of the local replay sections corrected
by that same primitive.
-/
theorem twoPatchReplay_class_zero_descends
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (hclass : twoPatchReplayCechMismatch =
      FiniteModel.twoPatchZMod2CechComplex.differential 0 correction) :
    ∃ globalSection : FiniteModel.TwoPatchZMod2TranslationReplay,
      ∀ i : FiniteModel.TwoPatchCoverIndex,
        globalSection = twoPatchAdjustedReplayLocalSectionBy correction i := by
  have hmatching :=
    twoPatchAdjustedReplayLocalSectionBy_matching_of_class_zero correction hclass
  let data : Site.AATGluingData FiniteModel.twoPatchSite
      FiniteModel.twoPatchZMod2TranslationReplayPresheaf twoPatchReplayCover :=
    { localSections := twoPatchCorrectedLocalSectionsBy correction
      overlapAgreement := twoPatchCorrectedLocalSectionsBy_matching correction hmatching }
  obtain ⟨globalSection, hglobal⟩ :=
    (FiniteModel.twoPatchZMod2TranslationReplaySheaf.descent twoPatchReplayCover
      (by simpa [twoPatchReplayCover] using FiniteModel.twoPatchCover_topologyCover)).exists_global
      data
  refine ⟨globalSection, ?_⟩
  intro i
  have hchart := hglobal (homOfLE (FiniteModel.twoPatchCover.inclusion i))
    (twoPatchReplayCover_contains i)
  change globalSection =
    twoPatchCorrectedLocalSectionsBy correction
      (homOfLE (FiniteModel.twoPatchCover.inclusion i))
      (twoPatchReplayCover_contains i) at hchart
  rw [twoPatchCorrectedLocalSectionsBy_chart correction i] at hchart
  exact hchart

/-- The corrected local family is the common translation replay section obtained from zero mismatch. -/
def twoPatchCorrectedLocalSections :
    Site.AATLocalSectionFamily FiniteModel.twoPatchSite
      FiniteModel.twoPatchZMod2TranslationReplayPresheaf twoPatchReplayCover :=
  fun _Y _f _hf => twoPatchAdjustedReplayLocalSection .left

/-- The gluing family restricts to each actual corrected chart section. -/
theorem twoPatchCorrectedLocalSections_chart
    (hzero : twoPatchAdjustedReplayOverlapMismatch = 0)
    (i : FiniteModel.TwoPatchCoverIndex) :
  twoPatchCorrectedLocalSections
      (homOfLE (FiniteModel.twoPatchCover.inclusion i))
      (twoPatchReplayCover_contains i) =
        twoPatchAdjustedReplayLocalSection i := by
  cases i
  · rfl
  · exact twoPatchAdjustedReplay_zero_reflects_matching hzero

/-- The corrected local family is compatible on all common refinements. -/
theorem twoPatchCorrectedLocalSections_matching :
    Site.AATOverlapAgreement twoPatchCorrectedLocalSections := by
  intro _Y _Z _W _h _hh _f _g _hf _hg _hcomp
  rfl

/--
Zero actual overlap mismatch gives compatible translation replay sections and
therefore a descended global section of the replay-function sheaf.
-/
theorem twoPatchReplay_correction_descends_from_zero
    (hzero : twoPatchAdjustedReplayOverlapMismatch = 0) :
    ∃ globalSection : FiniteModel.TwoPatchZMod2TranslationReplay,
      ∀ i : FiniteModel.TwoPatchCoverIndex,
        globalSection = twoPatchAdjustedReplayLocalSection i := by
  let data : Site.AATGluingData FiniteModel.twoPatchSite
      FiniteModel.twoPatchZMod2TranslationReplayPresheaf twoPatchReplayCover :=
    { localSections := twoPatchCorrectedLocalSections
      overlapAgreement := twoPatchCorrectedLocalSections_matching }
  obtain ⟨globalSection, hglobal⟩ :=
    (FiniteModel.twoPatchZMod2TranslationReplaySheaf.descent twoPatchReplayCover
      (by simpa [twoPatchReplayCover] using FiniteModel.twoPatchCover_topologyCover)).exists_global
      data
  refine ⟨globalSection, ?_⟩
  intro i
  have hchart := hglobal (homOfLE (FiniteModel.twoPatchCover.inclusion i))
    (twoPatchReplayCover_contains i)
  change globalSection =
    twoPatchCorrectedLocalSections
      (homOfLE (FiniteModel.twoPatchCover.inclusion i))
      (twoPatchReplayCover_contains i) at hchart
  rw [twoPatchCorrectedLocalSections_chart hzero i] at hchart
  exact hchart

/-- The selected nonzero correction produces zero adjusted mismatch and descends. -/
theorem twoPatchReplay_nonzero_correction_descends :
    ∃ globalSection : FiniteModel.TwoPatchZMod2TranslationReplay,
      ∀ i : FiniteModel.TwoPatchCoverIndex,
        globalSection = twoPatchAdjustedReplayLocalSection i :=
  twoPatchReplay_correction_descends_from_zero
    twoPatchAdjustedReplayOverlapMismatch_zero

/--
The descended global replay function is evaluation of the descended sheaf
section, rather than an independently supplied realization map.
-/
theorem twoPatchReplay_nonzero_correction_descends_as_function :
    ∃ globalReplay : FiniteModel.TwoPatchZMod2ReplayFunction,
      ∀ (i : FiniteModel.TwoPatchCoverIndex) (state : ZMod 2),
        globalReplay state =
          FiniteModel.TwoPatchZMod2TranslationReplay.apply
            (twoPatchAdjustedReplayLocalSection i) state := by
  rcases twoPatchReplay_nonzero_correction_descends with ⟨globalSection, hglobal⟩
  refine ⟨FiniteModel.TwoPatchZMod2TranslationReplay.apply globalSection, ?_⟩
  intro i state
  rw [hglobal i]

/-- A zero corrected Čech mismatch yields a glued translation replay section. -/
theorem twoPatch_adjusted_mismatch_zero_descends :
    twoPatchAdjustedReplayCechMismatch = 0 ->
      ∃ globalSection : FiniteModel.TwoPatchZMod2TranslationReplay,
        ∀ i : FiniteModel.TwoPatchCoverIndex,
          globalSection = twoPatchAdjustedReplayLocalSection i := by
  intro hzero
  have hoverlap : twoPatchAdjustedReplayOverlapMismatch = 0 := by
    have hvalue := congrFun hzero PUnit.unit
    rw [twoPatchAdjustedReplayCechMismatch_eq_overlap] at hvalue
    change twoPatchAdjustedReplayOverlapMismatch = (0 : ZMod 2) at hvalue
    exact hvalue
  exact twoPatchReplay_correction_descends_from_zero hoverlap

/-- The fixed correction has zero mismatch and therefore glues. -/
theorem twoPatch_temporal_descent_criterion_holds :
    ∃ globalSection : FiniteModel.TwoPatchZMod2TranslationReplay,
      ∀ i : FiniteModel.TwoPatchCoverIndex,
        globalSection = twoPatchAdjustedReplayLocalSection i :=
  twoPatch_adjusted_mismatch_zero_descends twoPatchAdjustedReplayCechMismatch_zero

/--
An indexed global replay realizes one correction when restriction to every
chart agrees with the chart replay along the same `tinyStep : t0 ⟶ t1`.
-/
def TwoPatchTemporalReplayRealizesCorrection
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (globalReplay : TwoPatchTemporalReplayTransition) : Prop :=
  ∀ (i : FiniteModel.TwoPatchCoverIndex)
    (state : twoPatchReplayTemporalStatePresheaf.State
      (TinyTime.t0, twoPatchReplayTemporalCover.baseContext)),
    twoPatchReplayTemporalStatePresheaf.restrictContext TinyTime.t1
        (twoPatchReplayTemporalCover.contextToBase i)
        (globalReplay.toFun state) =
      (twoPatchReplayAdjustedLocalTransitionBy correction i).toFun
        (twoPatchReplayTemporalStatePresheaf.restrictContext TinyTime.t0
          (twoPatchReplayTemporalCover.contextToBase i) state)

/--
An actual degree-zero primitive produces a global temporal replay realizing
the chart replays corrected by that same primitive.
-/
theorem twoPatch_temporal_descent_criterion_of_class_zero
    (correction : Site.FinitePosetCechCochain
      FiniteModel.twoPatchZMod2FinitePosetRegime 0)
    (hclass : twoPatchReplayCechMismatch =
      FiniteModel.twoPatchZMod2CechComplex.differential 0 correction) :
    ∃ globalReplay : TwoPatchTemporalReplayTransition,
      TwoPatchTemporalReplayRealizesCorrection correction globalReplay := by
  rcases twoPatchReplay_class_zero_descends correction hclass with
    ⟨globalSection, hglobal⟩
  refine ⟨{
    trace_selected := twoPatchReplayTemporalTrace_selected
    toFun := FiniteModel.TwoPatchZMod2TranslationReplay.apply globalSection
  }, ?_⟩
  intro i state
  change FiniteModel.TwoPatchZMod2TranslationReplay.apply globalSection state =
    FiniteModel.TwoPatchZMod2TranslationReplay.apply
      (twoPatchAdjustedReplayLocalSectionBy correction i) state
  rw [hglobal i]

/--
The realization predicate is not vacuous: the zero correction leaves the two
chart translations unequal, so no single base replay realizes both charts.
-/
theorem twoPatchTemporalReplayRealizesCorrection_zero_unsatisfied
    (globalReplay : TwoPatchTemporalReplayTransition) :
    ¬ TwoPatchTemporalReplayRealizesCorrection
        (0 : Site.FinitePosetCechCochain
          FiniteModel.twoPatchZMod2FinitePosetRegime 0) globalReplay := by
  intro hrealizes
  let zeroState : twoPatchReplayTemporalStatePresheaf.State
      (TinyTime.t0, twoPatchReplayTemporalCover.baseContext) := by
    change ZMod 2
    exact 0
  have hleft := hrealizes FiniteModel.TwoPatchCoverIndex.left zeroState
  have hright := hrealizes FiniteModel.TwoPatchCoverIndex.right zeroState
  change globalReplay.toFun zeroState = (0 : ZMod 2) at hleft
  change globalReplay.toFun zeroState = (1 : ZMod 2) at hright
  have hzero_one : (0 : ZMod 2) = 1 := hleft.symm.trans hright
  exact zero_ne_one hzero_one

/--
The actual two-patch temporal descent criterion.

The concrete class-zero witness is a degree-zero correction on the same
two-patch Čech complex and is read through the actual temporal
product-incidence `C⁰/C¹` carriers on the same `Tr_E × X` site.  After that
correction acts on the same translation replay sections, sheaf descent
constructs a global replay transition agreeing with every corrected chart on
every source state.
-/
theorem twoPatch_temporal_descent_criterion :
    ∃ correction : Site.FinitePosetCechCochain
        FiniteModel.twoPatchZMod2FinitePosetRegime 0,
      twoPatchReplayCechMismatch =
        FiniteModel.twoPatchZMod2CechComplex.differential 0 correction ∧
        twoPatchReplayCechMismatch =
          twoPatchReplayTemporalProductToCechOne
            (twoPatchReplayTemporalProductIncidenceComplex.d0
              (twoPatchReplayCochainToTemporalProduct correction)) ∧
          (∀ {p q : twoPatchReplayTemporalSite.Point}
            (leg : twoPatchReplayTemporalSite.IncidenceLeg p q),
            twoPatchReplayTemporalProductIncidenceComplex.d0
                (twoPatchReplayCochainToTemporalProduct
                  twoPatchReplayCechZeroCochain) leg =
              twoPatchReplayTemporalProductIncidenceComplex.d0
                (twoPatchReplayCochainToTemporalProduct correction) leg) ∧
          (∀ i : FiniteModel.TwoPatchCoverIndex,
            (Cohomology.finitePosetCoverRelativeCover
              FiniteModel.twoPatchZMod2CechComplex).chart
                (twoPatchReplayTemporalCoverComparison.siteIndexOf i) =
              Site.ContextCategoryObject.of FiniteModel.twoPatchSite.contextPreorder
                (twoPatchReplayTemporalSite.siteRegime.context
                  (twoPatchReplayTemporalCover.chartContext i))) ∧
          (∀ cochain : Site.FinitePosetCechCochain
              FiniteModel.twoPatchZMod2FinitePosetRegime 0,
            twoPatchReplayCochainToTemporalProduct cochain
                twoPatchReplayTemporalCechSource =
                  twoPatchReplayCechRestrictionToOverlap cochain .left ∧
            twoPatchReplayCochainToTemporalProduct cochain
                twoPatchReplayTemporalTarget =
                  twoPatchReplayCechRestrictionToOverlap cochain .right) ∧
          ∃ globalReplay : TwoPatchTemporalReplayTransition,
            TwoPatchTemporalReplayRealizesCorrection correction globalReplay := by
  refine ⟨twoPatchReplayCorrectionCochain,
    twoPatchReplayCechMismatch_eq_correction,
    twoPatchReplayTemporalMismatch_eq_correction,
    twoPatchReplayTemporalProductMismatch_eq_correction, ?_, ?_, ?_⟩
  intro i
  exact twoPatchReplayTemporalCover_reads_actual_chart i
  intro cochain
  exact twoPatchReplayCochainToTemporalProduct_endpoints cochain
  exact twoPatch_temporal_descent_criterion_of_class_zero
    twoPatchReplayCorrectionCochain
    twoPatchReplayCechMismatch_eq_correction_via_temporal_product

/-- The actual criterion exposes the descended replay function with its chartwise realization. -/
theorem twoPatch_temporal_descent_criterion_global_replay
    :
    ∃ globalReplay : TwoPatchTemporalReplayTransition,
      TwoPatchTemporalReplayRealizesCorrection
        twoPatchReplayCorrectionCochain globalReplay := by
  exact twoPatch_temporal_descent_criterion_of_class_zero
    twoPatchReplayCorrectionCochain
    twoPatchReplayCechMismatch_eq_correction_via_temporal_product

/--
The same finite `ZMod 2` data records a nonzero correction, the actual
overlap difference, its vanishing after correction, and the sheaf-glued global replay.
-/
theorem actual_twoPatch_zmod2_replay_fixture :
    twoPatchReplayCorrectionSection .right ≠ 0 ∧
      twoPatchReplayOverlapMismatch ≠ 0 ∧
        twoPatchReplayOverlapMismatch = twoChartCorrectionCoboundary ∧
        twoPatchReplayCechMismatch =
          FiniteModel.twoPatchZMod2CechComplex.differential 0
            twoPatchReplayCorrectionCochain ∧
          twoPatchAdjustedReplayCechMismatch = 0 ∧
        twoPatchAdjustedReplayOverlapMismatch = 0 ∧
          ∃ globalReplay : TwoPatchTemporalReplayTransition,
            TwoPatchTemporalReplayRealizesCorrection
              twoPatchReplayCorrectionCochain globalReplay := by
  refine ⟨?_, twoPatchReplayOverlapMismatch_ne_zero,
    twoPatchReplayOverlapMismatch_eq_coboundary, twoPatchReplayCechMismatch_eq_correction,
    twoPatchAdjustedReplayCechMismatch_zero, twoPatchAdjustedReplayOverlapMismatch_zero,
    twoPatch_temporal_descent_criterion_global_replay⟩
  exact twoChartCorrection_right_nonzero

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
  intro h
  have hv : (1 : ZMod 2).val = (0 : ZMod 2).val := congrArg ZMod.val h
  rw [ZMod.val_one] at hv
  simp at hv

/-- R10(c): selected nonzero replay class fixture without claiming global failure. -/
structure ReplayDescentNonzeroExample where
  edge : PseudoCircleEdge
  edge_nonzero : pseudoCircleMismatch edge ≠ 0
  noGlobalFailureClaimWithoutDetectingAssumption : Prop
  noGlobalFailureClaimWithoutDetectingAssumption_cert :
    noGlobalFailureClaimWithoutDetectingAssumption

/-- R10(c): concrete pseudo-circle nonzero replay fixture. -/
def replayDescentNonzeroExample : ReplayDescentNonzeroExample where
  edge := .ab
  edge_nonzero := pseudoCircleMismatch_ab_nonzero
  noGlobalFailureClaimWithoutDetectingAssumption := True
  noGlobalFailureClaimWithoutDetectingAssumption_cert := trivial

/-- R10(c): read the concrete nonzero pseudo-circle mismatch. -/
theorem replay_nonzero_edge_witness :
    pseudoCircleMismatch replayDescentNonzeroExample.edge ≠ 0 :=
  replayDescentNonzeroExample.edge_nonzero

/-- R10(c): the selected nonzero marker is exactly the concrete mismatch nonzero theorem. -/
theorem replay_selectedConcreteClassNonzero :
    pseudoCircleMismatch replayDescentNonzeroExample.edge ≠ 0 :=
  replayDescentNonzeroExample.edge_nonzero

/--
IX.R10 / IX-5: the replay nonzero fixture is paired with the Part X
circle-nerve Part IV nonzero H1 instance.

This does not identify the temporal mismatch carrier with the semantic-repair
cover-relative H1 carrier.  It records that the finite replay obstruction and
the Part X circle instance are both backed by concrete nonzero pseudo-circle
data rather than by a `True` marker.
-/
theorem replay_nonzero_and_partX_circle_coverRelativeH1_nonzero :
    pseudoCircleMismatch replayDescentNonzeroExample.edge ≠ 0 ∧
      SemanticRepairPart10.circleCoverRelativeComplex.cohomologyClassSucc 0
          SemanticRepairPart10.circleCoverRelativeResidualCocycle ≠
        SemanticRepairPart10.circleCoverRelativeComplex.cohomologyClassSucc 0
          SemanticRepairPart10.circleCoverRelativeZeroCocycle :=
  ⟨replay_selectedConcreteClassNonzero,
    SemanticRepairPart10.circlePartIV_h0_invisible_coverRelativeH1_nonzero.2⟩

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

/-- R10(g) / AC18: theorem-4.2 replay data integrates the selected toy force. -/
def toyForceIntegrationData : ForceIntegrationData toyForce where
  globalTemporalLaw := temporalLaw
  coefficient := temporalCoefficient
  replayData := zeroReplayDescentData
  descentCriterion := zeroReplayTemporalDescentCriterion
  globalReplayTransition := zeroReplayGlobalTransition
  replaySource_eq := rfl
  replayTarget_eq := rfl
  globalReplay_hits_force := zeroReplayGlobalTransition_hits_high
  localLawData := ∃ globalReplay : TinyState -> TinyState,
    globalReplay TinyState.high = TinyState.mid
  localLawData_cert := replay_zero_has_global_transition
  descendsToGlobalTemporalLaw := Nonempty zeroReplayDescentData.GlobalReplaySection
  descendsToGlobalTemporalLaw_cert := replay_zero_theorem42_global_section_exists
  lawWitness := ()
  lawSource_eq := rfl
  lawTarget_eq := rfl
  forceRespectsGlobalLaw := ⟨rfl, rfl⟩

/-- R10(g) / AC18: the selected global replay transition realizes the toy force. -/
theorem toy_force_global_replay_hits_force :
    toyForceIntegrationData.globalReplayTransition
        (toyForceIntegrationData.replaySource_eq ▸ toyForce.sourceState) =
      (toyForceIntegrationData.replayTarget_eq ▸ toyForce.targetState) :=
  toyForceIntegrationData.global_replay_hits_force

/-- R10(g) / AC18: the toy force has concrete selected integration data. -/
theorem toy_force_integrable :
    IntegrableForce toyForce :=
  toyForceIntegrationData.integrable

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

/--
R10(g): force fixture keeps statement-only theorem-candidate assumptions explicit
and backs the selected nonzero marker by a concrete `ZMod 2` obstruction value.
-/
structure ForceCandidateFixture where
  forceSelected : toyForce.selectedForce
  integrationData : ForceIntegrationData toyForce
  forceIntegrable : IntegrableForce toyForce
  globalReplayHitsForce :
    integrationData.globalReplayTransition
        (integrationData.replaySource_eq ▸ toyForce.sourceState) =
      (integrationData.replayTarget_eq ▸ toyForce.targetState)
  mismatchClass :
    ForceMismatchClass (Coeff := temporalCoefficient) (Law := temporalLaw) toyForce
  concreteObstructionValue : ZMod 2
  concreteObstruction_nonzero : concreteObstructionValue ≠ 0
  candidateData : ForceIntegrabilityObstructionCandidateData mismatchClass
  candidatePackage : ForceIntegrabilityObstructionCandidate mismatchClass
  selectedNonzero_backed_by_concrete :
    candidateData.selectedNonzero mismatchClass.obstructionClass ↔
      concreteObstructionValue ≠ 0
  candidateOnly : Prop
  candidateOnly_cert : candidateOnly

/-- R10(g): concrete force obstruction candidate data fixture. -/
def forceCandidateFixture : ForceCandidateFixture where
  forceSelected := toyForce.selected
  integrationData := toyForceIntegrationData
  forceIntegrable := toy_force_integrable
  globalReplayHitsForce := toy_force_global_replay_hits_force
  mismatchClass := toyForceMismatchClass
  concreteObstructionValue := 1
  concreteObstruction_nonzero := by
    intro h
    have hv : (1 : ZMod 2).val = (0 : ZMod 2).val := congrArg ZMod.val h
    rw [ZMod.val_one] at hv
    simp at hv
  candidateData := {
    selectedNonzero := fun _ => (1 : ZMod 2) ≠ 0
    obstruction_nonzero := by
      intro h
      have hv : (1 : ZMod 2).val = (0 : ZMod 2).val := congrArg ZMod.val h
      rw [ZMod.val_one] at hv
      simp at hv
    coefficientExactness := True
    coefficientExactness_cert := trivial
    witnessCoverage := True
    witnessCoverage_cert := trivial
    temporalDescentDetecting := True
    temporalDescentDetecting_cert := trivial
    localToGlobalControlledByDescent := True
    localToGlobalControlledByDescent_cert := trivial
  }
  candidatePackage := {
    selectedNonzero := fun _ => (1 : ZMod 2) ≠ 0
    obstruction_nonzero := by
      intro h
      have hv : (1 : ZMod 2).val = (0 : ZMod 2).val := congrArg ZMod.val h
      rw [ZMod.val_one] at hv
      simp at hv
    coefficientExactness := True
    coefficientExactness_cert := trivial
    witnessCoverage := True
    witnessCoverage_cert := trivial
    temporalDescentDetecting := True
    temporalDescentDetecting_cert := trivial
    localToGlobalControlledByDescent := True
    localToGlobalControlledByDescent_cert := trivial
    nonintegrabilityStatement := True
    nonintegrabilityStatement_cert := trivial
  }
  selectedNonzero_backed_by_concrete := Iff.rfl
  candidateOnly := True
  candidateOnly_cert := trivial

/-- R10(g): the toy force obstruction value is concretely nonzero. -/
theorem force_candidate_obstruction_nonzero :
    forceCandidateFixture.concreteObstructionValue ≠ 0 :=
  forceCandidateFixture.concreteObstruction_nonzero

/-- R10(g): the selected force obstruction class is marked nonzero in the fixture. -/
theorem force_candidate_selected_nonzero :
    forceCandidateFixture.candidateData.selectedNonzero
      forceCandidateFixture.mismatchClass.obstructionClass :=
  forceCandidateFixture.candidateData.obstruction_nonzero_holds

/--
R10(g) / AC18: the selected nonzero marker in the force candidate fixture is
backed by the concrete `ZMod 2` obstruction value.
-/
theorem force_candidate_selected_nonzero_backed_by_concrete :
    forceCandidateFixture.candidateData.selectedNonzero
        forceCandidateFixture.mismatchClass.obstructionClass ↔
      forceCandidateFixture.concreteObstructionValue ≠ 0 :=
  forceCandidateFixture.selectedNonzero_backed_by_concrete

/-- R10(g) / AC18: the selected force candidate data is inhabitable. -/
theorem force_candidate_data_inhabited :
    Nonempty (ForceIntegrabilityObstructionCandidateData
      forceCandidateFixture.mismatchClass) :=
  ⟨forceCandidateFixture.candidateData⟩

/-- R10(g) / AC5: the literal force candidate package is inhabitable. -/
theorem force_candidate_package_inhabited :
    Nonempty (ForceIntegrabilityObstructionCandidate
      forceCandidateFixture.mismatchClass) :=
  ⟨forceCandidateFixture.candidatePackage⟩

/--
R10 / AC20: bundled finite temporal examples (a)-(g).

This theorem is intentionally a conjunction of selected fixture witnesses, not
a general temporal semantics theorem.
-/
theorem finite_temporal_examples_verified :
    @TraceCategory.FiniteRegime.selectedArrow twoStepTrace twoStepTraceFiniteRegime
      TinyTime.t0 TinyTime.t1 tinyStep ∧
      Nonempty zeroReplayDescentData.GlobalReplaySection ∧
          (∃ globalReplay : TinyState -> TinyState,
            globalReplay TinyState.high = TinyState.mid) ∧
            twoChartCorrection true ≠ 0 ∧
              twoChartReplayMismatch = twoChartCorrectionCoboundary ∧
                twoChartReplayMismatch - twoChartCorrectionCoboundary = 0 ∧
                  (∀ state : TwoChartTemporalCoefficient,
                    twoChartAdjustedReplay false state = twoChartAdjustedReplay true state) ∧
                    zmod2TemporalProductIncidenceComplex.d0 zmod2TemporalSeparatedCochain stepLeg ≠ 0 ∧
                      pseudoCircleMismatch replayDescentNonzeroExample.edge ≠ 0 ∧
                        (¬ ∃ path : InfiniteSelectedEvolutionPath dissipativePolicy,
                          path.StaysOutsideTerminal terminalState) ∧
                          (∃ n : Nat,
                            terminalState.terminal
                              (dissipativePolicy.point (policyGeneratedDissipationPath.state n))
                              (dissipativePolicy.state (policyGeneratedDissipationPath.state n))) ∧
                            finiteDissipationPath.ReachesTerminal terminalState ∧
                            terminalState.terminal p1 nonlawfulTerminal1 ∧
                              (¬ terminalState.lawful p1 nonlawfulTerminal1) ∧
                                oneStepPath.PathwiseNonIncrease ∧
                                  IntegrableForce toyForce ∧
                          forceCandidateFixture.integrationData.globalReplayTransition
                              (forceCandidateFixture.integrationData.replaySource_eq ▸
                                toyForce.sourceState) =
                            (forceCandidateFixture.integrationData.replayTarget_eq ▸
                              toyForce.targetState) ∧
                            forceCandidateFixture.concreteObstructionValue ≠ 0 ∧
                              forceCandidateFixture.candidateData.selectedNonzero
                                forceCandidateFixture.mismatchClass.obstructionClass ∧
                                (forceCandidateFixture.candidateData.selectedNonzero
                                    forceCandidateFixture.mismatchClass.obstructionClass ↔
                                  forceCandidateFixture.concreteObstructionValue ≠ 0) ∧
                                forceCandidateFixture.candidateData.coefficientExactness ∧
                                  forceCandidateFixture.candidateData.witnessCoverage ∧
                                        forceCandidateFixture.candidateData.temporalDescentDetecting ∧
                                      forceCandidateFixture.candidateData.localToGlobalControlledByDescent ∧
                                        forceCandidateFixture.candidateOnly := by
  rcases nondegenerate_twoChart_temporal_replay_correction with
    ⟨hcorrection, hmismatch, hzero, hmatching, hnonzero⟩
  exact ⟨twoStep_step_selected,
    replay_zero_theorem42_applied,
    replay_zero_has_global_transition,
    hcorrection,
    hmismatch,
    hzero,
    hmatching,
    hnonzero,
    replay_selectedConcreteClassNonzero,
    finite_dissipation_no_infinite_nonterminal_path,
    policy_generated_dissipation_reaches_terminal,
    twoStep_dissipation_reaches_terminal_by_theorem53,
    nonlawful_terminal_is_terminal,
    nonlawful_terminal_not_lawful,
    lyapunov_path_nonIncreasing,
    toy_force_integrable,
    forceCandidateFixture.globalReplayHitsForce,
    force_candidate_obstruction_nonzero,
    force_candidate_selected_nonzero,
    force_candidate_selected_nonzero_backed_by_concrete,
    forceCandidateFixture.candidateData.coefficientExactness_cert,
    forceCandidateFixture.candidateData.witnessCoverage_cert,
    forceCandidateFixture.candidateData.temporalDescentDetecting_cert,
    forceCandidateFixture.candidateData.localToGlobalControlledByDescent_cert,
    forceCandidateFixture.candidateOnly_cert⟩

end EvolutionPart9
end Examples
end AAT.AG
