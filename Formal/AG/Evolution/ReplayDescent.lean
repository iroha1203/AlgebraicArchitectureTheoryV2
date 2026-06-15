import Formal.AG.Evolution.TemporalObstruction

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
PRD-9 R5 / AC11--AC13 replay descent and the temporal descent criterion.

This file packages local replay data over a selected temporal cover, reads its
mismatch as a degree-one temporal cochain, records effective adjustment by a
zero-cochain, and states the one-way temporal descent criterion used in
Theorem 4.2.  The reverse direction is intentionally not part of this surface.
-/

/--
IX.§4 / AC11: local replay descent data over a temporal cover and trace arrow.

The replay maps are local chart maps
`St_A(W_i,t) -> St_A(W_i,t')`.  Their mismatch is recorded as a selected
degree-one cochain in the temporal Čech bridge attached to `TempCoeff_A`.
-/
structure ReplayDescentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T)
    (Coeff : TemporalCoefficient T) (Law : TemporalLaw St) where
  bridge : TemporalCechBridge T Coeff.obstructionSheaf
  cover : TemporalCover T
  sourceTrace : E.trace.Obj
  targetTrace : E.trace.Obj
  traceArrow : E.trace.Hom sourceTrace targetTrace
  traceArrow_selected : T.traceRegime.selectedArrow traceArrow
  replay :
    (i : cover.Index) ->
      St.State (sourceTrace, cover.chartContext i) ->
        St.State (targetTrace, cover.chartContext i)
  mismatchCochain : bridge.siteComplex.Cn 1
  mismatchSupportedByLaw : Prop
  mismatchSupportedByLaw_cert : mismatchSupportedByLaw

namespace ReplayDescentData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}

/-- IX.§4 / AC11: read the replay mismatch as a selected temporal mismatch. -/
def mismatch (r : ReplayDescentData St Coeff Law) :
    TemporalMismatch Coeff Law where
  bridge := r.bridge
  degree := 1
  cochain := r.mismatchCochain
  supportedByLaw := r.mismatchSupportedByLaw
  supportedByLaw_cert := r.mismatchSupportedByLaw_cert

/-- IX.§4 / AC11: the local replay map on one chart. -/
def localReplay (r : ReplayDescentData St Coeff Law) (i : r.cover.Index) :
    St.State (r.sourceTrace, r.cover.chartContext i) ->
      St.State (r.targetTrace, r.cover.chartContext i) :=
  r.replay i

/-- IX.§4 / AC13: type of a descended global replay transition over the base context. -/
abbrev GlobalReplayTransition (r : ReplayDescentData St Coeff Law) :
    Type (max u y) :=
  St.State (r.sourceTrace, r.cover.baseContext) ->
    St.State (r.targetTrace, r.cover.baseContext)

/-- IX.§4 / AC13: zero degree-one cocycle used as the replay zero class representative. -/
def zeroMismatchCocycle (r : ReplayDescentData St Coeff Law) :
    r.bridge.siteComplex.CechCocycle 1 :=
  letI := r.bridge.siteComplex.cochainAddCommGroup 1
  letI := r.bridge.siteComplex.cochainAddCommGroup 2
  ⟨0, by simp [Cohomology.CoverRelativeCechComplex.d]⟩

/-- IX.§4 / AC13: canonical zero class in the replay mismatch degree. -/
def zeroMismatchClass (r : ReplayDescentData St Coeff Law) :
    r.mismatch.bridge.siteComplex.CoverRelativeHn r.mismatch.degree := by
  simpa [mismatch, Cohomology.CoverRelativeCechComplex.CoverRelativeHn]
    using r.bridge.siteComplex.cohomologyClassSucc 0 r.zeroMismatchCocycle

end ReplayDescentData

/--
IX.§4 / AC11: replay mismatch cocycle condition.

The mismatch cochain is degree one, so the witness is the zero differential in
degree two of the selected cover-relative Čech complex.
-/
structure ReplayMismatchCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (r : ReplayDescentData St Coeff Law) where
  differential_zero :
    letI := r.bridge.siteComplex.cochainAddCommGroup 2
    r.bridge.siteComplex.d 1 r.mismatchCochain = 0

namespace ReplayMismatchCocycle

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

/-- IX.§4 / AC11: the replay mismatch has zero temporal Čech differential. -/
theorem differential_zero_holds (h : ReplayMismatchCocycle r) :
    letI := r.bridge.siteComplex.cochainAddCommGroup 2
    r.bridge.siteComplex.d 1 r.mismatchCochain = 0 :=
  h.differential_zero

/-- IX.§4 / AC11: package the replay mismatch as the R4 temporal cocycle. -/
def toTemporalCocycle (h : ReplayMismatchCocycle r) :
    TemporalCocycle r.mismatch where
  differential_zero := by
    simpa [ReplayDescentData.mismatch] using h.differential_zero

end ReplayMismatchCocycle

/--
IX.§4 / AC12: effective temporal adjustment by a zero-cochain.

The central equation is the PRD statement
`m(adjust(c,r)) = m(r) - d c`, expressed in the selected Čech complex.
-/
structure EffectiveTemporalAdjustment {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (r : ReplayDescentData St Coeff Law) where
  correction : r.bridge.siteComplex.Cn 0
  adjustedReplay :
    (i : r.cover.Index) ->
      St.State (r.sourceTrace, r.cover.chartContext i) ->
        St.State (r.targetTrace, r.cover.chartContext i)
  adjustedMismatchCochain : r.bridge.siteComplex.Cn 1
  adjustedMismatchSupportedByLaw : Prop
  adjustedMismatchSupportedByLaw_cert : adjustedMismatchSupportedByLaw
  adjustment_equation :
    letI := r.bridge.siteComplex.cochainAddCommGroup 1
    adjustedMismatchCochain =
      r.mismatchCochain - r.bridge.siteComplex.d 0 correction

namespace EffectiveTemporalAdjustment

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

/-- IX.§4 / AC12: adjusted local replay map on one chart. -/
def localReplay (A : EffectiveTemporalAdjustment r) (i : r.cover.Index) :
    St.State (r.sourceTrace, r.cover.chartContext i) ->
      St.State (r.targetTrace, r.cover.chartContext i) :=
  A.adjustedReplay i

/-- IX.§4 / AC12: adjusted replay data with the adjusted mismatch cochain. -/
def adjustedData (A : EffectiveTemporalAdjustment r) :
    ReplayDescentData St Coeff Law where
  bridge := r.bridge
  cover := r.cover
  sourceTrace := r.sourceTrace
  targetTrace := r.targetTrace
  traceArrow := r.traceArrow
  traceArrow_selected := r.traceArrow_selected
  replay := A.adjustedReplay
  mismatchCochain := A.adjustedMismatchCochain
  mismatchSupportedByLaw := A.adjustedMismatchSupportedByLaw
  mismatchSupportedByLaw_cert := A.adjustedMismatchSupportedByLaw_cert

/-- IX.§4 / AC12: `m(adjust(c,r)) = m(r) - d c`. -/
theorem mismatch_adjust_eq (A : EffectiveTemporalAdjustment r) :
    letI := r.bridge.siteComplex.cochainAddCommGroup 1
    A.adjustedMismatchCochain =
      r.mismatchCochain - r.bridge.siteComplex.d 0 A.correction :=
  A.adjustment_equation

end EffectiveTemporalAdjustment

/--
IX.§4 / AC13: assumptions of the one-way Temporal Descent Criterion.

This is the bounded theorem 4.2 surface: a selected finite temporal setup,
abelian coefficient complex, replay mismatch cocycle, vanishing temporal class,
effective adjustment, and adjusted compatibility jointly imply existence of a
global replay transition for `St_A`.
-/
structure TemporalDescentCriterion {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (r : ReplayDescentData St Coeff Law) where
  mismatchCocycle : ReplayMismatchCocycle r
  temporalClass : TemporalClass r.mismatch
  temporalClass_matches_mismatch :
    temporalClass.cocycle = mismatchCocycle.toTemporalCocycle
  classVanishes_cert :
    temporalClass.cohomologyClass = r.zeroMismatchClass
  adjustment : EffectiveTemporalAdjustment r
  adjustedCompatible : ReplayDescentData St Coeff Law -> Prop
  adjustedCompatible_cert : adjustedCompatible adjustment.adjustedData
  descends_from_adjusted :
    temporalClass.cohomologyClass = r.zeroMismatchClass ->
      adjustedCompatible adjustment.adjustedData ->
        Nonempty r.GlobalReplayTransition

namespace TemporalDescentCriterion

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

/-- IX.§4 / AC13: the selected temporal class is the class of the replay mismatch. -/
theorem class_matches_mismatch (D : TemporalDescentCriterion r) :
    D.temporalClass.cocycle = D.mismatchCocycle.toTemporalCocycle :=
  D.temporalClass_matches_mismatch

/-- IX.§4 / AC13: the selected replay mismatch class vanishes. -/
theorem class_vanishes (D : TemporalDescentCriterion r) :
    D.temporalClass.cohomologyClass = r.zeroMismatchClass :=
  D.classVanishes_cert

/-- IX.§4 / AC13: the adjusted replay data satisfies the selected compatibility predicate. -/
theorem adjusted_data_compatible (D : TemporalDescentCriterion r) :
    D.adjustedCompatible D.adjustment.adjustedData :=
  D.adjustedCompatible_cert

/--
IX.§4 / AC13 / Theorem 4.2: temporal descent criterion.

If the replay mismatch class vanishes and the effective adjustment is
compatible, then a global replay transition exists.
-/
theorem temporal_descent_criterion (D : TemporalDescentCriterion r) :
    Nonempty r.GlobalReplayTransition :=
  D.descends_from_adjusted D.class_vanishes D.adjusted_data_compatible

end TemporalDescentCriterion

end Evolution
end AAT.AG
