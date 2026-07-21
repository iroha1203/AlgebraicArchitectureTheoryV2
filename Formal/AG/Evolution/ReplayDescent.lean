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

The datum below separates a raw temporal replay from its constructed
replay/coefficient representation.  The representation fixes one temporal
cover through `TemporalCechBridge`, realizes its charts as sections of a
replay-function sheaf, reads degree-zero coefficients from those sections, and
defines every adjusted replay by acting on those same local sections.
-/

/-- IX.§4: raw local replay maps on the temporal cover selected by the bridge. -/
structure ReplayRawDescentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T)
    (Coeff : TemporalCoefficient T) where
  bridge : TemporalCechBridge T Coeff.obstructionSheaf
  sourceTrace : E.trace.Obj
  targetTrace : E.trace.Obj
  traceArrow : E.trace.Hom sourceTrace targetTrace
  traceArrow_selected : T.traceRegime.selectedArrow traceArrow
  replay :
    (i : bridge.temporalCover.Index) ->
      St.State (sourceTrace, bridge.temporalCover.chartContext i) ->
        St.State (targetTrace, bridge.temporalCover.chartContext i)

/--
IX.§4: a constructed replay/coefficient representation for one raw replay.

`localSections` and `adjustLocalSections` are sections of the same actual
replay-function sheaf over the site cover.  The only coefficient input is the
degree-zero reading of such a local section family; the degree-one mismatch is
therefore always formed by the selected Čech differential below, never by an
independent map from replay maps to `C¹`.
-/
structure ReplayCoefficientRepresentation {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {E : EvolutionProfile.{u, v, w, x, y, z}} {T : TemporalSite S E}
    {St : StateTransitionPresheaf T} {Coeff : TemporalCoefficient T}
    (r : ReplayRawDescentData St Coeff) where
  replaySheaf : Site.AATSheaf S
  descentCover : Sieve r.bridge.siteCover.base
  descentCover_topological : descentCover ∈ S.topology r.bridge.siteCover.base
  chartInCover : ∀ i : r.bridge.temporalCover.Index,
    descentCover (r.bridge.siteCover.inclusion
      (r.bridge.coverComparison.siteIndexOf i))
  localSections :
    Site.AATLocalSectionFamily S replaySheaf.toPresheaf descentCover
  localReplayOfSection :
    ∀ (i : r.bridge.temporalCover.Index),
      replaySheaf.toPresheaf.obj
          (Opposite.op (r.bridge.siteCover.chart
            (r.bridge.coverComparison.siteIndexOf i))) ->
        St.State (r.sourceTrace, r.bridge.temporalCover.chartContext i) ->
          St.State (r.targetTrace, r.bridge.temporalCover.chartContext i)
  localReplay_from_section :
    ∀ i : r.bridge.temporalCover.Index,
      localReplayOfSection i
        (localSections
          (r.bridge.siteCover.chart (r.bridge.coverComparison.siteIndexOf i))
          (r.bridge.siteCover.inclusion (r.bridge.coverComparison.siteIndexOf i))
          (chartInCover i)) = r.replay i
  coefficientReading :
    ∀ (X : S.category),
      replaySheaf.toPresheaf.obj (Opposite.op X) ->
        Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op X)
  coefficientOfLocalSections :
    Site.AATLocalSectionFamily S replaySheaf.toPresheaf descentCover ->
      r.bridge.siteComplex.Cn 0
  /-- The representation's degree-zero reading is evaluated from restricted local sections. -/
  coefficientOfLocalSections_restriction :
    ∀ (sections : Site.AATLocalSectionFamily S replaySheaf.toPresheaf descentCover)
      (σ : r.bridge.siteCover.simplex 0),
      ∃ (i : r.bridge.temporalCover.Index)
        (q : r.bridge.siteCover.overlap 0 σ ⟶
          r.bridge.siteCover.chart (r.bridge.coverComparison.siteIndexOf i))
        (hq : descentCover (r.bridge.siteCover.inclusion
          (r.bridge.coverComparison.siteIndexOf i))),
        coefficientOfLocalSections sections σ =
          coefficientReading _ (replaySheaf.toPresheaf.map q.op
            (sections _ (r.bridge.siteCover.inclusion
              (r.bridge.coverComparison.siteIndexOf i)) hq))
  adjustLocalSections : r.bridge.siteComplex.Cn 0 ->
    Site.AATLocalSectionFamily S replaySheaf.toPresheaf descentCover
  coefficient_adjustment : ∀ correction : r.bridge.siteComplex.Cn 0,
    coefficientOfLocalSections (adjustLocalSections correction) =
      coefficientOfLocalSections localSections - correction
  coefficientReading_zero_reflecting :
    ∀ (X : S.category)
      (left right : replaySheaf.toPresheaf.obj (Opposite.op X)),
      letI := Coeff.obstructionSheaf.addCommGroup X
      coefficientReading X left - coefficientReading X right = 0 ->
        left = right
  overlapCochainValue :
    ∀ {Y Z W : S.category}
      (f : Y ⟶ r.bridge.siteCover.base) (g : Z ⟶ r.bridge.siteCover.base)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      r.bridge.siteComplex.Cn 1 ->
        Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op W)
  overlapCochainValue_zero :
    ∀ {Y Z W : S.category}
      (f : Y ⟶ r.bridge.siteCover.base) (g : Z ⟶ r.bridge.siteCover.base)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      letI := Coeff.obstructionSheaf.addCommGroup W
      overlapCochainValue f g leftRestriction rightRestriction 0 = 0
  /-- The actual restricted-section coefficient difference reads the Čech mismatch. -/
  adjusted_restriction_difference :
    ∀ (correction : r.bridge.siteComplex.Cn 0)
      {Y Z W : S.category}
      (f : Y ⟶ r.bridge.siteCover.base) (hf : descentCover f)
      (g : Z ⟶ r.bridge.siteCover.base) (hg : descentCover g)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      letI := Coeff.obstructionSheaf.addCommGroup W
      coefficientReading W
          (replaySheaf.toPresheaf.map leftRestriction.op
            (adjustLocalSections correction Y f hf)) -
        coefficientReading W
          (replaySheaf.toPresheaf.map rightRestriction.op
            (adjustLocalSections correction Z g hg)) =
          overlapCochainValue f g leftRestriction rightRestriction
            (r.bridge.siteComplex.d 0
              (coefficientOfLocalSections (adjustLocalSections correction)))
  globalReplayOfSection :
    replaySheaf.toPresheaf.obj (Opposite.op r.bridge.siteCover.base) ->
      (St.State (r.sourceTrace, r.bridge.temporalCover.baseContext) ->
        St.State (r.targetTrace, r.bridge.temporalCover.baseContext))
  global_section_restriction :
    ∀ (baseSection : replaySheaf.toPresheaf.obj (Opposite.op r.bridge.siteCover.base))
      (i : r.bridge.temporalCover.Index)
      (state : St.State (r.sourceTrace, r.bridge.temporalCover.baseContext)),
      St.contextRestriction r.targetTrace
          (r.bridge.temporalCover.contextToBase i)
          (globalReplayOfSection baseSection state) =
        localReplayOfSection i
          (replaySheaf.toPresheaf.map
            (r.bridge.siteCover.inclusion
              (r.bridge.coverComparison.siteIndexOf i)).op baseSection)
          (St.contextRestriction r.sourceTrace
            (r.bridge.temporalCover.contextToBase i) state)

/-- IX.§4 / AC11: replay descent data with its constructed coefficient representation. -/
structure ReplayDescentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T)
    (Coeff : TemporalCoefficient T) (Law : TemporalLaw St) where
  raw : ReplayRawDescentData St Coeff
  representation : ReplayCoefficientRepresentation raw
  mismatchSupportedByLaw : Prop
  mismatchSupportedByLaw_cert : mismatchSupportedByLaw

namespace ReplayDescentData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E} {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}

/-- The selected temporal cover is definitionally the cover of the Čech bridge. -/
abbrev cover (r : ReplayDescentData St Coeff Law) : TemporalCover T :=
  r.raw.bridge.temporalCover

/-- IX.§4 / AC11: the coefficient cochain is read from the actual replay sections. -/
def replayCoefficient (r : ReplayDescentData St Coeff Law) :
    r.raw.bridge.siteComplex.Cn 0 :=
  r.representation.coefficientOfLocalSections r.representation.localSections

/-- IX.§4 / AC11: mismatch is the actual Čech differential of that coefficient reading. -/
def mismatchCochain (r : ReplayDescentData St Coeff Law) :
    r.raw.bridge.siteComplex.Cn 1 :=
  r.raw.bridge.siteComplex.d 0 r.replayCoefficient

/-- IX.§4 / AC11: read the replay mismatch as a selected temporal mismatch. -/
def mismatch (r : ReplayDescentData St Coeff Law) :
    TemporalMismatch Coeff Law where
  bridge := r.raw.bridge
  degree := 1
  cochain := r.mismatchCochain
  supportedByLaw := r.mismatchSupportedByLaw
  supportedByLaw_cert := r.mismatchSupportedByLaw_cert

/-- IX.§4 / AC11: the local replay map is recovered from the represented local section. -/
def localReplay (r : ReplayDescentData St Coeff Law) (i : r.cover.Index) :
    St.State (r.raw.sourceTrace, r.cover.chartContext i) ->
      St.State (r.raw.targetTrace, r.cover.chartContext i) :=
  r.representation.localReplayOfSection i
    (r.representation.localSections
      (r.raw.bridge.siteCover.chart (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.representation.chartInCover i))

/-- IX.§4 / AC11: the represented section recovers the raw local replay. -/
theorem localReplay_eq_raw (r : ReplayDescentData St Coeff Law) (i : r.cover.Index) :
    r.localReplay i = r.raw.replay i :=
  r.representation.localReplay_from_section i

/-- IX.§4 / AC13: type of a descended global replay transition over the base context. -/
abbrev GlobalReplayTransition (r : ReplayDescentData St Coeff Law) :
    Type (max u y) :=
  St.State (r.raw.sourceTrace, r.cover.baseContext) ->
    St.State (r.raw.targetTrace, r.cover.baseContext)

/-- IX.§4 / AC13: zero degree-one cocycle used as the replay zero class representative. -/
def zeroMismatchCocycle (r : ReplayDescentData St Coeff Law) :
    r.raw.bridge.siteComplex.CechCocycle 1 :=
  letI := r.raw.bridge.siteComplex.cochainAddCommGroup 1
  letI := r.raw.bridge.siteComplex.cochainAddCommGroup 2
  ⟨0, by simp [Cohomology.CoverRelativeCechComplex.d]⟩

/-- IX.§4 / AC13: canonical zero class in the replay mismatch degree. -/
def zeroMismatchClass (r : ReplayDescentData St Coeff Law) :
    r.mismatch.bridge.siteComplex.CoverRelativeHn r.mismatch.degree := by
  simpa [mismatch, Cohomology.CoverRelativeCechComplex.CoverRelativeHn]
    using r.raw.bridge.siteComplex.cohomologyClassSucc 0 r.zeroMismatchCocycle

end ReplayDescentData

/-- IX.§4 / AC11: replay mismatch cocycle condition. -/
structure ReplayMismatchCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (r : ReplayDescentData St Coeff Law) where
  differential_zero :
    letI := r.raw.bridge.siteComplex.cochainAddCommGroup 2
    r.raw.bridge.siteComplex.d 1 r.mismatchCochain = 0

namespace ReplayMismatchCocycle

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E} {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

theorem differential_zero_holds (h : ReplayMismatchCocycle r) :
    letI := r.raw.bridge.siteComplex.cochainAddCommGroup 2
    r.raw.bridge.siteComplex.d 1 r.mismatchCochain = 0 :=
  h.differential_zero

def toTemporalCocycle (h : ReplayMismatchCocycle r) :
    TemporalCocycle r.mismatch where
  differential_zero := by
    simpa [ReplayDescentData.mismatch] using h.differential_zero

end ReplayMismatchCocycle

namespace ReplayDescentData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E} {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}

/-- The correction action is the representation's action on local sheaf sections. -/
def adjustedLocalSections (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) :
    Site.AATLocalSectionFamily S r.representation.replaySheaf.toPresheaf
      r.representation.descentCover :=
  r.representation.adjustLocalSections correction

/-- The adjusted degree-zero coefficient is read from the adjusted local sections. -/
def adjustedCoefficient (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) : r.raw.bridge.siteComplex.Cn 0 :=
  r.representation.coefficientOfLocalSections (r.adjustedLocalSections correction)

/-- The adjusted local replay is recovered from the adjusted local section. -/
def adjustedReplay (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) (i : r.cover.Index) :
    St.State (r.raw.sourceTrace, r.cover.chartContext i) ->
      St.State (r.raw.targetTrace, r.cover.chartContext i) :=
  r.representation.localReplayOfSection i
    (r.adjustedLocalSections correction
      (r.raw.bridge.siteCover.chart (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.representation.chartInCover i))

/-- IX.§4 / AC12: recompute the adjusted mismatch from the adjusted local sections. -/
def adjustedMismatchCochain (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) : r.raw.bridge.siteComplex.Cn 1 :=
  r.raw.bridge.siteComplex.d 0 (r.adjustedCoefficient correction)

/-- IX.§4 / AC12: `m(adjust(c,r)) = m(r) - d c`. -/
theorem mismatch_adjust_eq (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) :
    letI := r.raw.bridge.siteComplex.cochainAddCommGroup 1
    r.adjustedMismatchCochain correction =
      r.mismatchCochain - r.raw.bridge.siteComplex.d 0 correction := by
  rw [adjustedMismatchCochain, mismatchCochain, adjustedCoefficient,
    replayCoefficient, r.representation.coefficient_adjustment, map_sub]

/-- IX.§4 / AC13: zero mismatch yields matching through the represented coefficient reading. -/
def adjusted_replay_matching_of_zero (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0)
    (hzero : r.adjustedMismatchCochain correction = 0) :
    Site.AATGluingData S r.representation.replaySheaf.toPresheaf
      r.representation.descentCover :=
  {
    localSections := r.adjustedLocalSections correction
    overlapAgreement := by
      intro Y f hf Z g hg W leftRestriction rightRestriction hcomm
      apply r.representation.coefficientReading_zero_reflecting W
      calc
        r.representation.coefficientReading W
            (r.representation.replaySheaf.toPresheaf.map leftRestriction.op
              (r.adjustedLocalSections correction Y f hf)) -
          r.representation.coefficientReading W
            (r.representation.replaySheaf.toPresheaf.map rightRestriction.op
              (r.adjustedLocalSections correction Z g hg)) =
            r.representation.overlapCochainValue f g leftRestriction rightRestriction
              (r.adjustedMismatchCochain correction) :=
          r.representation.adjusted_restriction_difference correction f hf g hg
            leftRestriction rightRestriction
        _ = r.representation.overlapCochainValue f g leftRestriction rightRestriction 0 := by
          rw [hzero]
        _ = 0 := r.representation.overlapCochainValue_zero f g
          leftRestriction rightRestriction
  }

end ReplayDescentData

/-- IX.§4 / AC13: assumptions of the one-way Temporal Descent Criterion. -/
structure TemporalDescentCriterion {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (r : ReplayDescentData St Coeff Law) where
  mismatchCocycle : ReplayMismatchCocycle r
  temporalClass : TemporalClass r.mismatch
  temporalClass_matches_mismatch : temporalClass.cocycle = mismatchCocycle.toTemporalCocycle
  classVanishes_cert : temporalClass.cohomologyClass = r.zeroMismatchClass

namespace TemporalDescentCriterion

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E} {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

theorem class_matches_mismatch (D : TemporalDescentCriterion r) :
    D.temporalClass.cocycle = D.mismatchCocycle.toTemporalCocycle :=
  D.temporalClass_matches_mismatch

theorem class_vanishes (D : TemporalDescentCriterion r) :
    D.temporalClass.cohomologyClass = r.zeroMismatchClass :=
  D.classVanishes_cert

theorem exists_correction_of_class_vanishes (D : TemporalDescentCriterion r) :
    ∃ correction : r.raw.bridge.siteComplex.Cn 0,
      r.mismatchCochain = r.raw.bridge.siteComplex.d 0 correction := by
  have hclass := D.class_vanishes
  change r.raw.bridge.siteComplex.cohomologyClassSucc 0
      D.temporalClass.cocycle.asCechCocycle = r.zeroMismatchClass at hclass
  rw [D.class_matches_mismatch] at hclass
  change r.raw.bridge.siteComplex.cohomologyClassSucc 0
      D.mismatchCocycle.toTemporalCocycle.asCechCocycle =
        r.raw.bridge.siteComplex.cohomologyClassSucc 0 r.zeroMismatchCocycle at hclass
  rcases Quotient.exact hclass with ⟨correction, hcorrection⟩
  refine ⟨correction, ?_⟩
  simpa [ReplayMismatchCocycle.toTemporalCocycle, TemporalCocycle.asCechCocycle,
    ReplayDescentData.zeroMismatchCocycle] using hcorrection

theorem adjusted_mismatch_zero (D : TemporalDescentCriterion r)
    (correction : r.raw.bridge.siteComplex.Cn 0)
    (hcorrection : r.mismatchCochain = r.raw.bridge.siteComplex.d 0 correction) :
    r.adjustedMismatchCochain correction = 0 := by
  rw [ReplayDescentData.mismatch_adjust_eq, hcorrection]
  exact sub_self _

/-- IX.§4 / AC13: class-zero replay data descends through the represented sheaf. -/
theorem temporal_descent_criterion_realizes_adjusted
    (D : TemporalDescentCriterion r) :
    ∃ (correction : r.raw.bridge.siteComplex.Cn 0) (globalReplay : r.GlobalReplayTransition),
      ∀ (i : r.cover.Index) (state : St.State (r.raw.sourceTrace, r.cover.baseContext)),
        St.contextRestriction r.raw.targetTrace (r.cover.contextToBase i)
            (globalReplay state) =
          r.adjustedReplay correction i
            (St.contextRestriction r.raw.sourceTrace (r.cover.contextToBase i) state) := by
  rcases D.exists_correction_of_class_vanishes with ⟨correction, hcorrection⟩
  have hzero := D.adjusted_mismatch_zero correction hcorrection
  let data := r.adjusted_replay_matching_of_zero correction hzero
  obtain ⟨globalSection, hglobal⟩ :=
    (r.representation.replaySheaf.descent r.representation.descentCover
      r.representation.descentCover_topological).exists_global data
  refine ⟨correction, r.representation.globalReplayOfSection globalSection, ?_⟩
  intro i state
  rw [r.representation.global_section_restriction]
  have hsection :
      r.representation.replaySheaf.toPresheaf.map
          (r.raw.bridge.siteCover.inclusion
            (r.raw.bridge.coverComparison.siteIndexOf i)).op globalSection =
        r.adjustedLocalSections correction
          (r.raw.bridge.siteCover.chart (r.raw.bridge.coverComparison.siteIndexOf i))
          (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
          (r.representation.chartInCover i) := by
    simpa [data] using hglobal
      (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.representation.chartInCover i)
  rw [hsection]

/-- IX.§4 / Theorem 4.2: a constructed representation and a vanishing class yield a global replay. -/
theorem temporal_descent_criterion (D : TemporalDescentCriterion r) :
    Nonempty r.GlobalReplayTransition := by
  rcases D.temporal_descent_criterion_realizes_adjusted with ⟨_, globalReplay, _⟩
  exact ⟨globalReplay⟩

end TemporalDescentCriterion

end Evolution
end AAT.AG
