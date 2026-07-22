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
replay/coefficient representation.  The generic section theorem is packaged
(assumption-relative): its representation supplies the replay sheaf, section
action, coefficient reflection, and restriction comparison required for
descent.  It does not discharge those premises from raw replay data.  The
actual theorem-4.2 completion target constructs the corresponding ingredients
for the two-patch translation replay sheaf in `EvolutionPart9`.
-/

/-- IX.§4: raw local replay maps on the temporal cover selected by the bridge. -/
structure ReplayRawDescentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T)
    (Coeff : TemporalCoefficient T) where
  /-- The temporal cover, site cover, and Čech complex selected for this replay. -/
  bridge : TemporalCechBridge T Coeff.obstructionSheaf
  /-- The source trace object of every local replay map. -/
  sourceTrace : E.trace.Obj
  /-- The target trace object of every local replay map. -/
  targetTrace : E.trace.Obj
  /-- The selected trace arrow from `sourceTrace` to `targetTrace`. -/
  traceArrow : E.trace.Hom sourceTrace targetTrace
  /-- Evidence that the selected trace arrow belongs to the finite trace regime. -/
  traceArrow_selected : T.traceRegime.selectedArrow traceArrow
  /-- The raw local replay transition on each chart of the selected temporal cover. -/
  replay :
    (i : bridge.temporalCover.Index) ->
      St.State (sourceTrace, bridge.temporalCover.chartContext i) ->
        St.State (targetTrace, bridge.temporalCover.chartContext i)

/--
IX.§4: a constructed replay/coefficient representation for one raw replay.

`localSections` are sections of the actual replay-function sheaf over the site
cover.  A correction is first realized as a local coefficient-section family
and then acts on those replay sections.  The degree-one mismatch is the actual
restricted-section difference and is independent of the degree-zero reading,
so its cohomology class need not vanish definitionally.

Implementation notes: this structure is the explicit premise ledger for the
generic, packaged (assumption-relative) section theorem.  The alternative of
deriving a replay-sheaf action and coefficient reflection from arbitrary raw
state functions is rejected because those constructions depend on the chosen
replay-function sheaf.  Concrete theorem-4.2 evidence must construct these
operations for its selected sheaf rather than count this package itself as a
premise discharge.
-/
structure ReplayCoefficientRepresentation {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {E : EvolutionProfile.{u, v, w, x, y, z}} {T : TemporalSite S E}
    {St : StateTransitionPresheaf T} {Coeff : TemporalCoefficient T}
    (r : ReplayRawDescentData St Coeff) where
  /-- The actual sheaf whose sections represent replay transitions. -/
  replaySheaf : Site.AATSheaf S
  /-- The sieve on which the represented local replay sections descend. -/
  descentCover : Sieve r.bridge.siteCover.base
  /-- Evidence that the selected descent sieve is a topology cover. -/
  descentCover_topological : descentCover ∈ S.topology r.bridge.siteCover.base
  /-- Membership of every selected temporal chart in the descent sieve. -/
  chartInCover : ∀ i : r.bridge.temporalCover.Index,
    descentCover (r.bridge.siteCover.inclusion
      (r.bridge.coverComparison.siteIndexOf i))
  /-- The local replay-function sections on the selected descent sieve. -/
  localSections :
    Site.AATLocalSectionFamily S replaySheaf.toPresheaf descentCover
  /-- Evaluation of a represented local section as a state-transition function. -/
  localReplayOfSection :
    ∀ (i : r.bridge.temporalCover.Index),
      replaySheaf.toPresheaf.obj
          (Opposite.op (r.bridge.siteCover.chart
            (r.bridge.coverComparison.siteIndexOf i))) ->
        St.State (r.sourceTrace, r.bridge.temporalCover.chartContext i) ->
          St.State (r.targetTrace, r.bridge.temporalCover.chartContext i)
  /-- The selected represented local section realizes the raw local replay. -/
  localReplay_from_section :
    ∀ i : r.bridge.temporalCover.Index,
      localReplayOfSection i
        (localSections
          (r.bridge.siteCover.inclusion (r.bridge.coverComparison.siteIndexOf i))
          (chartInCover i)) = r.replay i
  /-- The coefficient section read from a replay-function section over any site object. -/
  coefficientReading :
    ∀ (X : S.category),
      replaySheaf.toPresheaf.obj (Opposite.op X) ->
        Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op X)
  /-- A coefficient section acts on a replay section over the same site object. -/
  sectionAction :
    ∀ (X : S.category),
      replaySheaf.toPresheaf.obj (Opposite.op X) ->
      Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op X) ->
        replaySheaf.toPresheaf.obj (Opposite.op X)
  /-- The zero coefficient section acts as the identity on replay sections. -/
  sectionAction_zero :
    ∀ (X : S.category)
      (replaySection : replaySheaf.toPresheaf.obj (Opposite.op X)),
      letI := Coeff.obstructionSheaf.addCommGroup X
      sectionAction X replaySection 0 = replaySection
  /-- The section action commutes with restriction in the replay sheaf. -/
  sectionAction_restrict :
    ∀ {X Y : S.category} (q : Y ⟶ X)
      (replaySection : replaySheaf.toPresheaf.obj (Opposite.op X))
      (correction : Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op X)),
      replaySheaf.toPresheaf.map q.op (sectionAction X replaySection correction) =
        sectionAction Y
          (replaySheaf.toPresheaf.map q.op replaySection)
          (Coeff.obstructionSheaf.carrier.toPresheaf.map q.op correction)
  /-- The coefficient reader turns the replay-section action into subtraction. -/
  coefficientReading_action :
    ∀ (X : S.category)
      (replaySection : replaySheaf.toPresheaf.obj (Opposite.op X))
      (correction : Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op X)),
      letI := Coeff.obstructionSheaf.addCommGroup X
      coefficientReading X (sectionAction X replaySection correction) =
        coefficientReading X replaySection - correction
  /-- A degree-zero cochain supplies the coefficient section acting on each cover member. -/
  correctionSections : r.bridge.siteComplex.Cn 0 ->
    Site.AATLocalSectionFamily S
      Coeff.obstructionSheaf.carrier.toPresheaf descentCover
  /-- The zero cochain supplies the zero coefficient section on every cover member. -/
  correctionSections_zero :
    ∀ {Y : S.category} (f : Y ⟶ r.bridge.siteCover.base) (hf : descentCover f),
      letI := Coeff.obstructionSheaf.addCommGroup Y
      correctionSections 0 f hf = 0
  /-- Zero coefficient difference reflects equality of represented replay sections. -/
  coefficientReading_zero_reflecting :
    ∀ (X : S.category)
      (left right : replaySheaf.toPresheaf.obj (Opposite.op X)),
      letI := Coeff.obstructionSheaf.addCommGroup X
      coefficientReading X left - coefficientReading X right = 0 ->
        left = right
  /-- The coefficient value of a degree-one Čech cochain on a selected overlap. -/
  overlapCochainValue :
    ∀ {Y Z W : S.category}
      (_f : Y ⟶ r.bridge.siteCover.base) (_g : Z ⟶ r.bridge.siteCover.base)
      (_leftRestriction : W ⟶ Y) (_rightRestriction : W ⟶ Z),
      r.bridge.siteComplex.Cn 1 ->
        Coeff.obstructionSheaf.carrier.toPresheaf.obj (Opposite.op W)
  /-- The zero degree-one cochain has zero value on every selected overlap. -/
  overlapCochainValue_zero :
    ∀ {Y Z W : S.category}
      (f : Y ⟶ r.bridge.siteCover.base) (g : Z ⟶ r.bridge.siteCover.base)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      letI := Coeff.obstructionSheaf.addCommGroup W
      overlapCochainValue f g leftRestriction rightRestriction 0 = 0
  /-- Reading an overlap value preserves subtraction of degree-one cochains. -/
  overlapCochainValue_sub :
    ∀ {Y Z W : S.category}
      (f : Y ⟶ r.bridge.siteCover.base) (g : Z ⟶ r.bridge.siteCover.base)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z)
      (left right : r.bridge.siteComplex.Cn 1),
      letI := Coeff.obstructionSheaf.addCommGroup W
      overlapCochainValue f g leftRestriction rightRestriction (left - right) =
        overlapCochainValue f g leftRestriction rightRestriction left -
          overlapCochainValue f g leftRestriction rightRestriction right
  /-- The actual mismatch cochain reads the original restricted-section difference. -/
  mismatchCochain : r.bridge.siteComplex.Cn 1
  /-- The mismatch is obtained from the two actual restricted replay sections. -/
  restriction_difference :
    ∀ {Y Z W : S.category}
      (f : Y ⟶ r.bridge.siteCover.base) (hf : descentCover f)
      (g : Z ⟶ r.bridge.siteCover.base) (hg : descentCover g)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      letI := Coeff.obstructionSheaf.addCommGroup W
      coefficientReading W
          (replaySheaf.toPresheaf.map leftRestriction.op (localSections f hf)) -
        coefficientReading W
          (replaySheaf.toPresheaf.map rightRestriction.op (localSections g hg)) =
          overlapCochainValue f g leftRestriction rightRestriction mismatchCochain
  /-- The coboundary of a correction is its restricted coefficient-section difference. -/
  correction_restriction_difference :
    ∀ (correction : r.bridge.siteComplex.Cn 0)
      {Y Z W : S.category}
      (f : Y ⟶ r.bridge.siteCover.base) (hf : descentCover f)
      (g : Z ⟶ r.bridge.siteCover.base) (hg : descentCover g)
      (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z),
      letI := Coeff.obstructionSheaf.addCommGroup W
      Coeff.obstructionSheaf.carrier.toPresheaf.map leftRestriction.op
          (correctionSections correction f hf) -
        Coeff.obstructionSheaf.carrier.toPresheaf.map rightRestriction.op
          (correctionSections correction g hg) =
          overlapCochainValue f g leftRestriction rightRestriction
            (r.bridge.siteComplex.d 0 correction)

/-- IX.§4 / AC11: replay descent data with its constructed coefficient representation. -/
structure ReplayDescentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T)
    (Coeff : TemporalCoefficient T) (Law : TemporalLaw St) where
  /-- The raw replay data on the selected temporal cover. -/
  raw : ReplayRawDescentData St Coeff
  /-- The constructed replay-section and coefficient representation of `raw`. -/
  representation : ReplayCoefficientRepresentation raw
  /-- The proposition that the selected mismatch is supported by the temporal law. -/
  mismatchSupportedByLaw : Prop
  /-- Evidence for the selected temporal-law support proposition. -/
  mismatchSupportedByLaw_cert : mismatchSupportedByLaw

namespace ReplayDescentData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E} {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}

/-- The selected temporal cover is definitionally the cover of the Čech bridge. -/
abbrev cover (r : ReplayDescentData St Coeff Law) : TemporalCover T :=
  r.raw.bridge.temporalCover

/-- IX.§4 / AC11: mismatch is the actual restricted-section difference. -/
def mismatchCochain (r : ReplayDescentData St Coeff Law) :
    r.raw.bridge.siteComplex.Cn 1 :=
  r.representation.mismatchCochain

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
      (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.representation.chartInCover i))

/-- IX.§4 / AC11: the represented section recovers the raw local replay. -/
theorem localReplay_eq_raw (r : ReplayDescentData St Coeff Law) (i : r.cover.Index) :
    r.localReplay i = r.raw.replay i :=
  r.representation.localReplay_from_section i

/-- IX.§4 / AC13: a descended global replay section over the base context. -/
abbrev GlobalReplaySection (r : ReplayDescentData St Coeff Law) :
    Type u :=
  r.representation.replaySheaf.toPresheaf.obj
    (Opposite.op r.raw.bridge.siteCover.base)

/-- IX.§4 / AC13: type of a global replay transition over the base context. -/
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
  /-- Evidence that the selected replay mismatch is a Čech cocycle. -/
  differential_zero :
    letI := r.raw.bridge.siteComplex.cochainAddCommGroup 2
    r.raw.bridge.siteComplex.d 1 r.mismatchCochain = 0

namespace ReplayMismatchCocycle

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E} {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

/-- IX.§4 / AC11: the replay mismatch has zero temporal Čech differential. -/
theorem differential_zero_holds (h : ReplayMismatchCocycle r) :
    letI := r.raw.bridge.siteComplex.cochainAddCommGroup 2
    r.raw.bridge.siteComplex.d 1 r.mismatchCochain = 0 :=
  h.differential_zero

/-- IX.§4 / AC11: package the replay mismatch as the selected temporal cocycle. -/
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
  fun _Y f hf =>
    r.representation.sectionAction _
      (r.representation.localSections f hf)
      (r.representation.correctionSections correction f hf)

/-- The zero cochain leaves the represented local replay sections unchanged. -/
theorem adjustedLocalSections_zero (r : ReplayDescentData St Coeff Law) :
    r.adjustedLocalSections 0 = r.representation.localSections := by
  funext Y f hf
  rw [adjustedLocalSections, r.representation.correctionSections_zero f hf,
    r.representation.sectionAction_zero]

/-- The adjusted local replay is recovered from the adjusted local section. -/
def adjustedReplay (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) (i : r.cover.Index) :
    St.State (r.raw.sourceTrace, r.cover.chartContext i) ->
      St.State (r.raw.targetTrace, r.cover.chartContext i) :=
  r.representation.localReplayOfSection i
    (r.adjustedLocalSections correction
      (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.representation.chartInCover i))

/-- The replay obtained by acting on the original chart section with a correction. -/
def adjustReplayAtChart (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) (i : r.cover.Index) :
    St.State (r.raw.sourceTrace, r.cover.chartContext i) ->
      St.State (r.raw.targetTrace, r.cover.chartContext i) :=
  r.representation.localReplayOfSection i
    (r.representation.sectionAction _
      (r.representation.localSections
        (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
        (r.representation.chartInCover i))
      (r.representation.correctionSections correction
        (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
        (r.representation.chartInCover i)))

/-- Adjusted chart replay is evaluation of the coefficient action on the raw replay section. -/
theorem adjustedReplay_eq_adjustReplayAtChart (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) (i : r.cover.Index) :
    r.adjustedReplay correction i = r.adjustReplayAtChart correction i :=
  rfl

/-- The zero correction recovers the raw replay on every selected chart. -/
theorem adjustReplayAtChart_zero (r : ReplayDescentData St Coeff Law)
    (i : r.cover.Index) :
    r.adjustReplayAtChart 0 i = r.raw.replay i := by
  rw [adjustReplayAtChart, r.representation.correctionSections_zero,
    r.representation.sectionAction_zero]
  exact r.representation.localReplay_from_section i

/-- IX.§4 / AC12: subtract the correction coboundary from the actual mismatch. -/
def adjustedMismatchCochain (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) : r.raw.bridge.siteComplex.Cn 1 :=
  letI := r.raw.bridge.siteComplex.cochainAddCommGroup 1
  r.mismatchCochain - r.raw.bridge.siteComplex.d 0 correction

/-- IX.§4 / AC12: `m(adjust(c,r)) = m(r) - d c`. -/
theorem mismatch_adjust_eq (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0) :
    letI := r.raw.bridge.siteComplex.cochainAddCommGroup 1
    r.adjustedMismatchCochain correction =
      r.mismatchCochain - r.raw.bridge.siteComplex.d 0 correction := by
  letI := r.raw.bridge.siteComplex.cochainAddCommGroup 1
  rfl

/-- The adjusted restricted-section difference is the adjusted actual mismatch. -/
theorem adjusted_restriction_difference (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0)
    {Y Z W : S.category}
    (f : Y ⟶ r.raw.bridge.siteCover.base) (hf : r.representation.descentCover f)
    (g : Z ⟶ r.raw.bridge.siteCover.base) (hg : r.representation.descentCover g)
    (leftRestriction : W ⟶ Y) (rightRestriction : W ⟶ Z) :
    letI := Coeff.obstructionSheaf.addCommGroup W
    r.representation.coefficientReading W
        (r.representation.replaySheaf.toPresheaf.map leftRestriction.op
          (r.adjustedLocalSections correction f hf)) -
      r.representation.coefficientReading W
        (r.representation.replaySheaf.toPresheaf.map rightRestriction.op
          (r.adjustedLocalSections correction g hg)) =
        r.representation.overlapCochainValue f g leftRestriction rightRestriction
          (r.adjustedMismatchCochain correction) := by
  letI := Coeff.obstructionSheaf.addCommGroup W
  simp only [adjustedLocalSections]
  rw [r.representation.sectionAction_restrict,
    r.representation.sectionAction_restrict,
    r.representation.coefficientReading_action,
    r.representation.coefficientReading_action,
    adjustedMismatchCochain]
  rw [r.representation.overlapCochainValue_sub]
  calc
    _ =
        (r.representation.coefficientReading W
            (r.representation.replaySheaf.toPresheaf.map leftRestriction.op
              (r.representation.localSections f hf)) -
          r.representation.coefficientReading W
            (r.representation.replaySheaf.toPresheaf.map rightRestriction.op
              (r.representation.localSections g hg))) -
        (Coeff.obstructionSheaf.carrier.toPresheaf.map leftRestriction.op
            (r.representation.correctionSections correction f hf) -
          Coeff.obstructionSheaf.carrier.toPresheaf.map rightRestriction.op
            (r.representation.correctionSections correction g hg)) := by abel
    _ = _ := by
      rw [r.representation.restriction_difference f hf g hg
          leftRestriction rightRestriction,
        r.representation.correction_restriction_difference correction f hf g hg
          leftRestriction rightRestriction]
      rfl

/-- IX.§4 / AC13: zero mismatch yields matching through the represented coefficient reading. -/
def adjusted_replay_matching_of_zero (r : ReplayDescentData St Coeff Law)
    (correction : r.raw.bridge.siteComplex.Cn 0)
    (hzero : r.adjustedMismatchCochain correction = 0) :
    Site.AATGluingData S r.representation.replaySheaf.toPresheaf
      r.representation.descentCover :=
  {
    localSections := r.adjustedLocalSections correction
    overlapAgreement := by
      intro Y Z W leftRestriction rightRestriction f g hf hg hcomm
      apply r.representation.coefficientReading_zero_reflecting W
      calc
        r.representation.coefficientReading W
            (r.representation.replaySheaf.toPresheaf.map leftRestriction.op
              (r.adjustedLocalSections correction f hf)) -
          r.representation.coefficientReading W
            (r.representation.replaySheaf.toPresheaf.map rightRestriction.op
              (r.adjustedLocalSections correction g hg)) =
            r.representation.overlapCochainValue f g leftRestriction rightRestriction
              (r.adjustedMismatchCochain correction) :=
          r.adjusted_restriction_difference correction f hf g hg
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
  /-- The cocycle witness for the selected replay mismatch. -/
  mismatchCocycle : ReplayMismatchCocycle r
  /-- The temporal cohomology class represented by that replay mismatch. -/
  temporalClass : TemporalClass r.mismatch
  /-- Identification of the selected temporal class cocycle with the replay mismatch cocycle. -/
  temporalClass_matches_mismatch : temporalClass.cocycle = mismatchCocycle.toTemporalCocycle
  /-- Evidence that the selected temporal class equals the zero cohomology class. -/
  classVanishes_cert : temporalClass.cohomologyClass = r.zeroMismatchClass

namespace TemporalDescentCriterion

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E} {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
variable {r : ReplayDescentData St Coeff Law}

/-- IX.§4 / AC13: the selected temporal class is represented by the replay mismatch. -/
theorem class_matches_mismatch (D : TemporalDescentCriterion r) :
    D.temporalClass.cocycle = D.mismatchCocycle.toTemporalCocycle :=
  D.temporalClass_matches_mismatch

/-- IX.§4 / AC13: the selected replay mismatch class is the zero class. -/
theorem class_vanishes (D : TemporalDescentCriterion r) :
    D.temporalClass.cohomologyClass = r.zeroMismatchClass :=
  D.classVanishes_cert

/-- IX.§4 / AC13: class vanishing produces a degree-zero correction primitive. -/
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

/-- IX.§4 / AC13: a correction primitive makes the adjusted mismatch zero. -/
theorem adjusted_mismatch_zero
    (correction : r.raw.bridge.siteComplex.Cn 0)
    (hcorrection : r.mismatchCochain = r.raw.bridge.siteComplex.d 0 correction) :
    r.adjustedMismatchCochain correction = 0 := by
  rw [ReplayDescentData.mismatch_adjust_eq, hcorrection]
  exact sub_self _

/--
IX.§4 / AC13: a non-coboundary mismatch cannot satisfy the class-zero criterion.

This is the negative instance API for `TemporalDescentCriterion`: together
with a concrete non-coboundary witness it proves that the certificate is not
available.  The positive instance is supplied by the zero replay fixture.

Implementation notes: this module does not manufacture a closed negative
fixture because Issue #3684 fixes a class-zero two-patch completion target, and
the existing Part X nonzero carrier is not identified with this replay bridge.
The theorem therefore exposes the exact non-coboundary condition required by
future concrete replay data without asserting such an identification.
-/
theorem not_temporalDescentCriterion_of_mismatch_not_coboundary
    (hnot : ¬ ∃ correction : r.raw.bridge.siteComplex.Cn 0,
      r.mismatchCochain = r.raw.bridge.siteComplex.d 0 correction) :
    ¬ TemporalDescentCriterion r := by
  intro D
  exact hnot D.exists_correction_of_class_vanishes

/--
IX.§4 / AC13: class-zero replay data descends through the represented sheaf.

This is a packaged (assumption-relative) sheaf-descent statement: it constructs
a global replay section and proves that its restrictions are the corrected
local sections from a supplied `ReplayCoefficientRepresentation`.  It is not a
discharge of that representation from raw replay data.
-/
theorem temporal_descent_section_criterion_realizes_adjusted
    (D : TemporalDescentCriterion r) :
    ∃ (correction : r.raw.bridge.siteComplex.Cn 0) (globalSection : r.GlobalReplaySection),
      ∀ (i : r.cover.Index),
        r.representation.replaySheaf.toPresheaf.map
            (r.raw.bridge.siteCover.inclusion
              (r.raw.bridge.coverComparison.siteIndexOf i)).op globalSection =
          r.adjustedLocalSections correction
            (r.raw.bridge.siteCover.inclusion
              (r.raw.bridge.coverComparison.siteIndexOf i))
            (r.representation.chartInCover i) := by
  rcases D.exists_correction_of_class_vanishes with ⟨correction, hcorrection⟩
  have hzero := adjusted_mismatch_zero correction hcorrection
  let data := r.adjusted_replay_matching_of_zero correction hzero
  obtain ⟨globalSection, hglobal⟩ :=
    (r.representation.replaySheaf.descent r.representation.descentCover
      r.representation.descentCover_topological).exists_global data
  refine ⟨correction, globalSection, ?_⟩
  intro i
  have hsection :
      r.representation.replaySheaf.toPresheaf.map
          (r.raw.bridge.siteCover.inclusion
            (r.raw.bridge.coverComparison.siteIndexOf i)).op globalSection =
        r.adjustedLocalSections correction
          (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
          (r.representation.chartInCover i) := by
    simpa [data] using hglobal
      (r.raw.bridge.siteCover.inclusion (r.raw.bridge.coverComparison.siteIndexOf i))
      (r.representation.chartInCover i)
  rw [hsection]

/--
IX.§4 / AC13: a constructed representation and a vanishing class yield a
global section.  This convenience theorem has the same packaged
(assumption-relative) status as the realization theorem above.
-/
theorem temporal_descent_section_criterion (D : TemporalDescentCriterion r) :
    Nonempty r.GlobalReplaySection := by
  rcases D.temporal_descent_section_criterion_realizes_adjusted with ⟨_, globalSection, _⟩
  exact ⟨globalSection⟩

end TemporalDescentCriterion

end Evolution
end AAT.AG
