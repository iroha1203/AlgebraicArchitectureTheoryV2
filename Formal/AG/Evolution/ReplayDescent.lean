import Formal.AG.Evolution.TemporalObstruction
import Formal.AG.Site.Descent

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

open CategoryTheory
open Opposite

/-!
Part IX R5 / AC11--AC13 replay descent and the temporal descent criterion.

This file packages local replay data over a selected temporal cover, reads its
mismatch as a degree-one temporal cochain, records effective adjustment by a
zero-cochain, and states the one-way temporal descent criterion used in
Theorem 4.2.  The reverse direction is intentionally not part of this surface.
-/

/--
IX.§4 / AC11: local replay descent data over a temporal cover and trace arrow.

The replay maps are local chart maps
`St_A(W_i,t) -> St_A(W_i,t')`.  Their coefficient reading is a degree-zero
Čech cochain, and the replay mismatch is its actual Čech differential.  Thus
the mismatch is not supplied as an unconstrained map from local replay maps to
degree-one cochains.
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
  replayCoefficient : bridge.siteComplex.Cn 0
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

/-- IX.§4 / AC11: the degree-one mismatch is the Čech differential of the replay coefficient. -/
def mismatchCochain (r : ReplayDescentData St Coeff Law) :
    r.bridge.siteComplex.Cn 1 :=
  r.bridge.siteComplex.d 0 r.replayCoefficient

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

The central equation is the Part IX statement
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
  adjustedCoefficient : r.bridge.siteComplex.Cn 0
  adjustedMismatchSupportedByLaw : Prop
  adjustedMismatchSupportedByLaw_cert : adjustedMismatchSupportedByLaw
  coefficient_adjustment :
    adjustedCoefficient = r.replayCoefficient - correction

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

/-- IX.§4 / AC12: recompute the adjusted mismatch from its corrected coefficient reading. -/
def adjustedMismatchCochain (A : EffectiveTemporalAdjustment r) :
    r.bridge.siteComplex.Cn 1 :=
  r.bridge.siteComplex.d 0 A.adjustedCoefficient

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
  replayCoefficient := A.adjustedCoefficient
  mismatchSupportedByLaw := A.adjustedMismatchSupportedByLaw
  mismatchSupportedByLaw_cert := A.adjustedMismatchSupportedByLaw_cert

/-- IX.§4 / AC12: `m(adjust(c,r)) = m(r) - d c`. -/
theorem mismatch_adjust_eq (A : EffectiveTemporalAdjustment r) :
    letI := r.bridge.siteComplex.cochainAddCommGroup 1
  A.adjustedMismatchCochain =
      r.mismatchCochain - r.bridge.siteComplex.d 0 A.correction :=
  by
    rw [adjustedMismatchCochain, ReplayDescentData.mismatchCochain,
      A.coefficient_adjustment, map_sub]

end EffectiveTemporalAdjustment

/--
IX.§4 / AC13: sheaf presentation of replay transitions for one selected replay
descent datum.

Implementation notes: `StateTransitionPresheaf` records state restrictions,
but arbitrary local replay maps do not themselves form a contravariant
presheaf.  This structure therefore records a replay-function sheaf together
with its coefficient comparison.  The comparison reads the restricted local
sections in the obstruction sheaf and reflects a zero difference back to
section equality.  Gluing and realization are derived below; neither is stored
as a conclusion field.
-/
structure ReplayTransitionSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (r : ReplayDescentData St Coeff Law) where
  sectionSheaf : Site.AATSheaf S
  base : S.category
  base_eq :
    base = Site.ContextCategoryObject.of S.contextPreorder
      (T.siteRegime.context r.cover.baseContext)
  cover : Sieve base
  cover_topological : cover ∈ S.topology base
  adjustment : r.bridge.siteComplex.Cn 0 -> EffectiveTemporalAdjustment r
  adjustment_correction :
    ∀ correction : r.bridge.siteComplex.Cn 0,
      (adjustment correction).correction = correction
  adjustedLocalSections :
    (correction : r.bridge.siteComplex.Cn 0) ->
      Site.AATLocalSectionFamily S sectionSheaf.toPresheaf cover
  coefficientComparison :
    ∀ (X : S.category),
      sectionSheaf.toPresheaf.obj (Opposite.op X) ->
        Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op X)
  coefficientComparison_zero_reflecting :
    ∀ (X : S.category)
      (left right : sectionSheaf.toPresheaf.obj (Opposite.op X)),
      letI := Coeff.obstructionSheaf.addCommGroup X
      coefficientComparison X left - coefficientComparison X right = 0 ->
        left = right
  overlapCochainValue :
    ∀ {Y Z W : S.category} (f : Y ⟶ base) (g : Z ⟶ base)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      r.bridge.siteComplex.Cn 1 ->
        Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op W)
  overlapCochainValue_zero :
    ∀ {Y Z W : S.category} (f : Y ⟶ base) (g : Z ⟶ base)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      letI := Coeff.obstructionSheaf.addCommGroup W
      overlapCochainValue f g leftRestriction rightRestriction 0 = 0
  adjustedLocalSections_overlap_difference :
    ∀ (correction : r.bridge.siteComplex.Cn 0)
      {Y Z W : S.category} (f : Y ⟶ base) (hf : cover f)
      (g : Z ⟶ base) (hg : cover g)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      letI := Coeff.obstructionSheaf.addCommGroup W
      coefficientComparison W
          (sectionSheaf.toPresheaf.map leftRestriction.op
            (adjustedLocalSections correction Y f hf)) -
        coefficientComparison W
          (sectionSheaf.toPresheaf.map rightRestriction.op
            (adjustedLocalSections correction Z g hg)) =
          overlapCochainValue f g leftRestriction rightRestriction
            ((adjustment correction).adjustedMismatchCochain)
  chartObject : r.cover.Index -> S.category
  chartToBase : ∀ i : r.cover.Index, chartObject i ⟶ base
  chartToBase_mem : ∀ i : r.cover.Index, cover (chartToBase i)
  localReplayOfSection :
    ∀ (i : r.cover.Index),
      sectionSheaf.toPresheaf.obj (Opposite.op (chartObject i)) ->
        St.State (r.sourceTrace, r.cover.chartContext i) ->
          St.State (r.targetTrace, r.cover.chartContext i)
  baseSectionToReplay :
    sectionSheaf.toPresheaf.obj (Opposite.op base) -> r.GlobalReplayTransition
  baseSection_restriction_comparison :
    ∀ (baseSection : sectionSheaf.toPresheaf.obj (Opposite.op base))
      (i : r.cover.Index)
      (x : St.State (r.sourceTrace, r.cover.baseContext)),
      St.contextRestriction r.targetTrace (r.cover.contextToBase i)
          (baseSectionToReplay baseSection x) =
        localReplayOfSection i
          (sectionSheaf.toPresheaf.map (chartToBase i).op baseSection)
          (St.contextRestriction r.sourceTrace (r.cover.contextToBase i) x)
  adjustedLocalSection_comparison :
    ∀ (correction : r.bridge.siteComplex.Cn 0) (i : r.cover.Index),
      localReplayOfSection i
        (adjustedLocalSections correction (chartObject i) (chartToBase i)
          (chartToBase_mem i)) =
        (adjustment correction).adjustedReplay i

namespace ReplayTransitionSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

/-- IX.§4 / AC13: zero adjusted mismatch supplies matching through coefficient reflection. -/
def adjusted_replay_matching_of_zero (R : ReplayTransitionSheaf r)
    (correction : r.bridge.siteComplex.Cn 0)
    (hzero : (R.adjustment correction).adjustedMismatchCochain = 0) :
    Site.AATGluingData S R.sectionSheaf.toPresheaf R.cover :=
  {
    localSections := R.adjustedLocalSections correction
    overlapAgreement := by
      intro Y f hf Z g hg W leftRestriction rightRestriction hcomm
      apply R.coefficientComparison_zero_reflecting W
      calc
        R.coefficientComparison W
            (R.sectionSheaf.toPresheaf.map leftRestriction.op
              (R.adjustedLocalSections correction Y f hf)) -
          R.coefficientComparison W
            (R.sectionSheaf.toPresheaf.map rightRestriction.op
              (R.adjustedLocalSections correction Z g hg)) =
            R.overlapCochainValue f g leftRestriction rightRestriction
              ((R.adjustment correction).adjustedMismatchCochain) :=
          R.adjustedLocalSections_overlap_difference correction f hf g hg
            leftRestriction rightRestriction
        _ = R.overlapCochainValue f g leftRestriction rightRestriction 0 := by
          rw [hzero]
        _ = 0 :=
          R.overlapCochainValue_zero f g leftRestriction rightRestriction
  }

end ReplayTransitionSheaf

/--
IX.§4 / AC13: assumptions of the one-way Temporal Descent Criterion.

This is the bounded theorem 4.2 surface: a selected finite temporal setup,
abelian coefficient complex, replay mismatch cocycle, vanishing temporal class,
and replay-transition sheaf presentation jointly imply existence of a global
replay transition for `St_A`.
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
  replayTransitionSheaf : ReplayTransitionSheaf r

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

/--
IX.§4 / AC13: a zero temporal class yields a concrete degree-zero correction
whose Čech differential is the selected replay mismatch.
-/
theorem exists_correction_of_class_vanishes (D : TemporalDescentCriterion r) :
    ∃ correction : r.bridge.siteComplex.Cn 0,
      r.mismatchCochain = r.bridge.siteComplex.d 0 correction := by
  have hclass := D.class_vanishes
  change r.bridge.siteComplex.cohomologyClassSucc 0
      D.temporalClass.cocycle.asCechCocycle = r.zeroMismatchClass at hclass
  rw [D.class_matches_mismatch] at hclass
  change r.bridge.siteComplex.cohomologyClassSucc 0
      D.mismatchCocycle.toTemporalCocycle.asCechCocycle =
        r.bridge.siteComplex.cohomologyClassSucc 0 r.zeroMismatchCocycle at hclass
  rcases Quotient.exact hclass with ⟨correction, hcorrection⟩
  refine ⟨correction, ?_⟩
  simpa [ReplayMismatchCocycle.toTemporalCocycle, TemporalCocycle.asCechCocycle,
    ReplayDescentData.zeroMismatchCocycle] using hcorrection

/-- IX.§4 / AC13: the class-zero correction kills the adjusted replay mismatch. -/
theorem adjusted_mismatch_zero (D : TemporalDescentCriterion r)
    (correction : r.bridge.siteComplex.Cn 0)
    (hcorrection : r.mismatchCochain = r.bridge.siteComplex.d 0 correction) :
    (D.replayTransitionSheaf.adjustment correction).adjustedMismatchCochain = 0 := by
  rw [EffectiveTemporalAdjustment.mismatch_adjust_eq,
    D.replayTransitionSheaf.adjustment_correction, hcorrection]
  exact sub_self _

/--
IX.§4 / AC13: class-zero replay data has a global transition whose restrictions
realize the adjusted local replay sections.
-/
theorem temporal_descent_criterion_realizes_adjusted
    (D : TemporalDescentCriterion r) :
    ∃ (correction : r.bridge.siteComplex.Cn 0) (globalReplay : r.GlobalReplayTransition),
      ∀ (i : r.cover.Index) (x : St.State (r.sourceTrace, r.cover.baseContext)),
        St.contextRestriction r.targetTrace (r.cover.contextToBase i)
            (globalReplay x) =
          (D.replayTransitionSheaf.adjustment correction).adjustedReplay i
            (St.contextRestriction r.sourceTrace (r.cover.contextToBase i) x) := by
  rcases D.exists_correction_of_class_vanishes with ⟨correction, hcorrection⟩
  have hzero := D.adjusted_mismatch_zero correction hcorrection
  let data := D.replayTransitionSheaf.adjusted_replay_matching_of_zero correction hzero
  obtain ⟨globalSection, hglobal⟩ :=
    (D.replayTransitionSheaf.sectionSheaf.descent D.replayTransitionSheaf.cover
      D.replayTransitionSheaf.cover_topological).exists_global data
  refine ⟨correction, D.replayTransitionSheaf.baseSectionToReplay globalSection, ?_⟩
  intro i x
  rw [D.replayTransitionSheaf.baseSection_restriction_comparison]
  have hsection :
      D.replayTransitionSheaf.sectionSheaf.toPresheaf.map
          (D.replayTransitionSheaf.chartToBase i).op globalSection =
        D.replayTransitionSheaf.adjustedLocalSections correction
          (D.replayTransitionSheaf.chartObject i)
          (D.replayTransitionSheaf.chartToBase i)
          (D.replayTransitionSheaf.chartToBase_mem i) := by
    simpa [data] using hglobal (D.replayTransitionSheaf.chartToBase i)
      (D.replayTransitionSheaf.chartToBase_mem i)
  rw [hsection]
  exact congrFun
    (D.replayTransitionSheaf.adjustedLocalSection_comparison correction i) _

/--
IX.§4 / AC13 / Theorem 4.2: temporal descent criterion.

If the replay mismatch class vanishes, the induced degree-zero correction
produces matching replay sections, and sheaf descent yields a global replay
transition.
-/
theorem temporal_descent_criterion (D : TemporalDescentCriterion r) :
    Nonempty r.GlobalReplayTransition := by
  rcases D.temporal_descent_criterion_realizes_adjusted with ⟨_, globalReplay, _⟩
  exact ⟨globalReplay⟩

end TemporalDescentCriterion

end Evolution
end AAT.AG
