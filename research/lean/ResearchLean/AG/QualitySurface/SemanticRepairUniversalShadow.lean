import ResearchLean.AG.QualitySurface.SemanticRepairStackyH2

/-!
Cycle 8 evidence for `G-aat-quality-surface-04`.

This file strengthens the finite shadow / factorization side of the universal
semantic repair obstruction tower.  It adds a canonical all-layer shadow for a
finite tower, a sound assignment interface that factors through that shadow,
and an ArchSig-style bounded artifact schema that factors through the same
shadow.

The result remains finite/small target support.  It does not assert ArchSig
implementation correctness, runtime extraction completeness, whole-codebase
quality, or unrestricted universal properties outside the finite target
boundary.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairUniversalShadow

open SemanticRepairObstructionTower
open SemanticRepairSheafH1
open SemanticRepairNonabelianTorsor
open SemanticRepairStackyH2

universe u v w x y

/-! ## Canonical all-layer finite tower shadow -/

/-- The finite shadow vector that reads every selected tower layer. -/
structure FiniteTowerLayerShadow where
  h1 : Bool
  torsor : Bool
  higher : Bool
  stack : Bool

/-- The zero all-layer shadow. -/
def zeroFiniteTowerLayerShadow : FiniteTowerLayerShadow where
  h1 := false
  torsor := false
  higher := false
  stack := false

/-- The selected all-layer shadow of a finite semantic repair obstruction tower. -/
def canonicalTowerLayerShadow
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    FiniteTowerLayerShadow where
  h1 := T.finiteShadow T.residual
  torsor := T.torsorObstruction
  higher := T.higherObstruction
  stack := T.stackObstruction

/-- All selected finite shadow layers vanish. -/
def FiniteTowerLayerShadowZero (shadow : FiniteTowerLayerShadow) : Prop :=
  shadow.h1 = false /\
    shadow.torsor = false /\
    shadow.higher = false /\
    shadow.stack = false

/-- Tower vanishing implies the canonical all-layer finite shadow is zero. -/
theorem obstructionTowerVanishes_to_canonicalShadowZero
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    ObstructionTowerVanishes T ->
      FiniteTowerLayerShadowZero (canonicalTowerLayerShadow T) := by
  intro hvanishes
  rcases hvanishes with ⟨hh1, htorsor, hhigher, hstack⟩
  exact
    ⟨semanticRepairFiniteShadow_sound T hh1,
      htorsor, hhigher, hstack⟩

/--
Visible reflection premise for the first finite shadow layer.

The nonabelian, higher, and stack layers are already Boolean tower tokens; the
first `H1` layer needs an explicit reflection discharge from finite shadow zero
back to boundary membership.
-/
structure FiniteTowerShadowReflection
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) where
  h1_vanishes_of_shadow_zero :
    T.finiteShadow T.residual = false -> H1Vanishes T

/-- Zero canonical all-layer shadow reflects tower vanishing under explicit reflection. -/
theorem canonicalShadowZero_to_obstructionTowerVanishes
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (reflection : FiniteTowerShadowReflection T) :
    FiniteTowerLayerShadowZero (canonicalTowerLayerShadow T) ->
      ObstructionTowerVanishes T := by
  intro hzero
  rcases hzero with ⟨hh1, htorsor, hhigher, hstack⟩
  exact
    ⟨reflection.h1_vanishes_of_shadow_zero hh1,
      htorsor, hhigher, hstack⟩

/-! ## Sound all-layer assignment factorization -/

/--
A sound all-layer finite obstruction assignment.

The assignment is a finite observation algebra on all-layer shadows.  It does
not contain factorization equalities, global coherence, tower vanishing, finite
shadow completeness, or target equivalence.
-/
structure SoundAllLayerObstructionAssignment where
  readH1 : Bool -> Bool
  readTorsor : Bool -> Bool
  readHigher : Bool -> Bool
  readStack : Bool -> Bool
  h1_zero_preserved : readH1 false = false
  torsor_zero_preserved : readTorsor false = false
  higher_zero_preserved : readHigher false = false
  stack_zero_preserved : readStack false = false

/-- Read an all-layer shadow through a sound finite assignment. -/
def assignmentReadsShadow
    (assignment : SoundAllLayerObstructionAssignment)
    (shadow : FiniteTowerLayerShadow) :
    FiniteTowerLayerShadow where
  h1 := assignment.readH1 shadow.h1
  torsor := assignment.readTorsor shadow.torsor
  higher := assignment.readHigher shadow.higher
  stack := assignment.readStack shadow.stack

/-- Read a tower through a sound assignment by first taking the canonical shadow. -/
def assignmentLayerShadow
    {Atom : Type u}
    (assignment : SoundAllLayerObstructionAssignment)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    FiniteTowerLayerShadow :=
  assignmentReadsShadow assignment (canonicalTowerLayerShadow T)

/-- A sound all-layer assignment factors through the canonical tower shadow. -/
theorem soundAllLayerAssignment_factors_through_tower
    {Atom : Type u}
    (assignment : SoundAllLayerObstructionAssignment)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    assignmentLayerShadow assignment T =
      assignmentReadsShadow assignment (canonicalTowerLayerShadow T) := by
  rfl

/-- Sound assignments are extensional in the finite shadow they read. -/
theorem soundAllLayerAssignment_extensional_on_shadow
    (assignment : SoundAllLayerObstructionAssignment)
    {left right : FiniteTowerLayerShadow}
    (hshadow : left = right) :
    assignmentReadsShadow assignment left =
      assignmentReadsShadow assignment right := by
  cases hshadow
  rfl

/-- Sound all-layer assignments send finite first-layer boundaries to zero. -/
theorem soundAllLayerAssignment_boundary_zero
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (assignment : SoundAllLayerObstructionAssignment)
    (primitive : T.C0) :
    assignment.readH1 (T.finiteShadow (T.delta0 primitive)) = false := by
  rw [T.finiteShadow_boundary_zero primitive]
  exact assignment.h1_zero_preserved

/-- Sound all-layer assignments preserve zero finite shadows. -/
theorem soundAllLayerAssignment_preserves_shadow_zero
    (assignment : SoundAllLayerObstructionAssignment)
    {shadow : FiniteTowerLayerShadow} :
    FiniteTowerLayerShadowZero shadow ->
      FiniteTowerLayerShadowZero (assignmentReadsShadow assignment shadow) := by
  intro hzero
  rcases hzero with ⟨hh1, htorsor, hhigher, hstack⟩
  exact
    ⟨by simpa [assignmentReadsShadow, hh1] using assignment.h1_zero_preserved,
      by simpa [assignmentReadsShadow, htorsor] using
        assignment.torsor_zero_preserved,
      by simpa [assignmentReadsShadow, hhigher] using
        assignment.higher_zero_preserved,
      by simpa [assignmentReadsShadow, hstack] using
        assignment.stack_zero_preserved⟩

/-! ## ArchSig-style finite artifact schema -/

/--
Bounded ArchSig-style finite artifact schema.

This is a Lean guardrail for a finite artifact shape, not a theorem about the
Rust ArchSig implementation.  The schema records selected measured layer
tokens and non-conclusion flags.
-/
structure ArchSigStyleFiniteShadowArtifact where
  measuredH1 : Bool
  measuredTorsor : Bool
  measuredHigher : Bool
  measuredStack : Bool
  recordsBoundedEvidence : Bool
  recordsNonConclusions : Bool

/-- Read an ArchSig-style finite artifact as a finite tower shadow. -/
def archSigStyleArtifactShadow
    (artifact : ArchSigStyleFiniteShadowArtifact) :
    FiniteTowerLayerShadow where
  h1 := artifact.measuredH1
  torsor := artifact.measuredTorsor
  higher := artifact.measuredHigher
  stack := artifact.measuredStack

/-- Build the concrete bounded artifact associated to a finite tower shadow. -/
def archSigStyleArtifactOfShadow
    (shadow : FiniteTowerLayerShadow) :
    ArchSigStyleFiniteShadowArtifact where
  measuredH1 := shadow.h1
  measuredTorsor := shadow.torsor
  measuredHigher := shadow.higher
  measuredStack := shadow.stack
  recordsBoundedEvidence := true
  recordsNonConclusions := true

/-- Build the concrete bounded artifact associated to a finite tower. -/
def archSigStyleArtifactOfTower
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    ArchSigStyleFiniteShadowArtifact :=
  archSigStyleArtifactOfShadow (canonicalTowerLayerShadow T)

/-- The concrete bounded artifact of a tower factors through its canonical shadow. -/
theorem archSigStyleArtifactOfTower_factors_through_tower
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    archSigStyleArtifactShadow (archSigStyleArtifactOfTower T) =
      canonicalTowerLayerShadow T := by
  rfl

/-- The concrete bounded artifact records evidence and non-conclusion flags. -/
theorem archSigStyleArtifactOfTower_records_boundary
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (archSigStyleArtifactOfTower T).recordsBoundedEvidence = true /\
      (archSigStyleArtifactOfTower T).recordsNonConclusions = true := by
  exact ⟨rfl, rfl⟩

/-- Explicit adequacy bridge from a bounded artifact to the canonical tower shadow. -/
structure ArchSigStyleFiniteShadowAdequacy
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (artifact : ArchSigStyleFiniteShadowArtifact) where
  h1_matches : artifact.measuredH1 = T.finiteShadow T.residual
  torsor_matches : artifact.measuredTorsor = T.torsorObstruction
  higher_matches : artifact.measuredHigher = T.higherObstruction
  stack_matches : artifact.measuredStack = T.stackObstruction
  bounded_evidence_recorded : artifact.recordsBoundedEvidence = true
  non_conclusions_recorded : artifact.recordsNonConclusions = true

/-- A bounded ArchSig-style artifact matches the canonical tower shadow layer by layer. -/
theorem archSigStyleArtifact_matches_tower_layers
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {artifact : ArchSigStyleFiniteShadowArtifact}
    (adequacy : ArchSigStyleFiniteShadowAdequacy T artifact) :
    (archSigStyleArtifactShadow artifact).h1 =
        (canonicalTowerLayerShadow T).h1 /\
      (archSigStyleArtifactShadow artifact).torsor =
        (canonicalTowerLayerShadow T).torsor /\
      (archSigStyleArtifactShadow artifact).higher =
        (canonicalTowerLayerShadow T).higher /\
      (archSigStyleArtifactShadow artifact).stack =
        (canonicalTowerLayerShadow T).stack := by
  exact
    ⟨by
        simpa [archSigStyleArtifactShadow, canonicalTowerLayerShadow] using
          adequacy.h1_matches,
      by
        simpa [archSigStyleArtifactShadow, canonicalTowerLayerShadow] using
          adequacy.torsor_matches,
      by
        simpa [archSigStyleArtifactShadow, canonicalTowerLayerShadow] using
          adequacy.higher_matches,
      by
        simpa [archSigStyleArtifactShadow, canonicalTowerLayerShadow] using
          adequacy.stack_matches⟩

/-- ArchSig-style artifacts expose bounded evidence and non-conclusion flags. -/
theorem archSigStyleArtifact_records_boundary
    {Atom : Type u}
    {T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {artifact : ArchSigStyleFiniteShadowArtifact}
    (adequacy : ArchSigStyleFiniteShadowAdequacy T artifact) :
    artifact.recordsBoundedEvidence = true /\
      artifact.recordsNonConclusions = true := by
  exact
    ⟨adequacy.bounded_evidence_recorded,
      adequacy.non_conclusions_recorded⟩

/-! ## Source-trace blocker for canonical layer universality -/

/--
A trace-variant representative tower with prescribed finite layer shadow and
source trace reading.

The finite obstruction layers are deliberately independent of the supplied
source trace.  This makes it a small counterexample surface for attempts to
classify every source-trace-sensitive observation by the canonical layer shadow
alone.
-/
def traceVariantTowerOfShadow
    (shadow : FiniteTowerLayerShadow)
    (trace : Bool -> Bool) :
    FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool where
  Chart := PUnit
  chartOrder := [PUnit.unit]
  C0 := PUnit
  C1 := Bool
  C2 := PUnit
  c0Order := [PUnit.unit]
  c1Order := [false, true]
  c2Zero := PUnit.unit
  delta0 := fun _ => false
  delta1 := fun _ => PUnit.unit
  delta1_delta0_zero := by
    intro primitive
    rfl
  residual := shadow.h1
  residual_cocycle := rfl
  primitiveSemanticallyClosed := fun _ => True
  torsorObstruction := shadow.torsor
  higherObstruction := shadow.higher
  stackObstruction := shadow.stack
  finiteShadow := fun cochain => cochain
  finiteShadow_boundary_zero := by
    intro primitive
    rfl
  sourceTraceToken := trace

/-- Trace-variant towers have exactly the requested canonical layer shadow. -/
theorem canonicalShadow_traceVariantTowerOfShadow
    (shadow : FiniteTowerLayerShadow)
    (trace : Bool -> Bool) :
    canonicalTowerLayerShadow (traceVariantTowerOfShadow shadow trace) =
      shadow := by
  cases shadow
  rfl

/-- A source-trace-sensitive observation that ignores obstruction layers. -/
def sourceTraceAtTrueObservation
    (T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool) :
    Bool :=
  T.sourceTraceToken true

/--
The canonical layer shadow alone cannot classify every source-trace-sensitive
semantic repair observation.

This is the non-circular blocker behind the final-review veto: two towers may
have the same selected obstruction layers while differing in supplied source
trace data.
-/
theorem sourceTraceAtTrueObservation_not_factor_through_canonicalShadow :
    Not
      (exists factor : FiniteTowerLayerShadow -> Bool,
        forall T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
          sourceTraceAtTrueObservation T =
            factor (canonicalTowerLayerShadow T)) := by
  intro hfactorization
  rcases hfactorization with ⟨factor, hfactor⟩
  let shadow := zeroFiniteTowerLayerShadow
  have hfalse :
      sourceTraceAtTrueObservation
          (traceVariantTowerOfShadow shadow (fun _ => false)) =
        factor
          (canonicalTowerLayerShadow
            (traceVariantTowerOfShadow shadow (fun _ => false))) :=
    hfactor (traceVariantTowerOfShadow shadow (fun _ => false))
  have htrue :
      sourceTraceAtTrueObservation
          (traceVariantTowerOfShadow shadow (fun token => token)) =
        factor
          (canonicalTowerLayerShadow
            (traceVariantTowerOfShadow shadow (fun token => token))) :=
    hfactor (traceVariantTowerOfShadow shadow (fun token => token))
  rw [canonicalShadow_traceVariantTowerOfShadow] at hfalse
  rw [canonicalShadow_traceVariantTowerOfShadow] at htrue
  simp [shadow, sourceTraceAtTrueObservation, traceVariantTowerOfShadow] at hfalse htrue
  rw [hfalse] at htrue
  cases htrue

/-- A trace-aware finite shadow for the Bool source-trace blocker surface. -/
structure BoolTraceAwareTowerShadow where
  layer : FiniteTowerLayerShadow
  sourceAtTrue : Bool

/-- The trace-aware shadow records both obstruction layers and the trace probe. -/
def boolTraceAwareTowerShadow
    (T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool) :
    BoolTraceAwareTowerShadow where
  layer := canonicalTowerLayerShadow T
  sourceAtTrue := T.sourceTraceToken true

/-- The source-trace observation factors through the trace-aware shadow. -/
def sourceTraceAtTrueFactor
    (shadow : BoolTraceAwareTowerShadow) : Bool :=
  shadow.sourceAtTrue

/--
Adding the source trace probe to the finite shadow restores factorization for
the trace-sensitive observation.
-/
theorem sourceTraceAtTrueObservation_factors_through_traceAwareShadow
    (T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool) :
    sourceTraceAtTrueObservation T =
      sourceTraceAtTrueFactor (boolTraceAwareTowerShadow T) := by
  rfl

/--
The trace-aware factor is pointwise unique among factors through the trace-aware
shadow for the source-trace observation.
-/
theorem sourceTraceAtTrueFactor_pointwise_unique
    {factor : BoolTraceAwareTowerShadow -> Bool}
    (hfactor :
      forall T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        sourceTraceAtTrueObservation T =
          factor (boolTraceAwareTowerShadow T)) :
    forall shadow : BoolTraceAwareTowerShadow,
      factor shadow = sourceTraceAtTrueFactor shadow := by
  intro shadow
  let T :=
    traceVariantTowerOfShadow shadow.layer
      (fun token =>
        match token with
        | false => false
        | true => shadow.sourceAtTrue)
  have htower := hfactor T
  cases shadow with
  | mk layer sourceAtTrue =>
      cases layer
      cases sourceAtTrue <;>
        simpa [T, sourceTraceAtTrueObservation, sourceTraceAtTrueFactor,
          boolTraceAwareTowerShadow, traceVariantTowerOfShadow]
          using htower.symm

/--
Package form of the source-trace universality blocker.

The first component rules out canonical-layer-only universality for arbitrary
source-trace-sensitive observations.  The second and third components show the
minimal trace-aware repair route: once the trace probe is included in the shadow,
the observation factors and the factor is pointwise unique.
-/
theorem sourceTraceUniversalityBlocker_package :
    Not
      (exists factor : FiniteTowerLayerShadow -> Bool,
        forall T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
          sourceTraceAtTrueObservation T =
            factor (canonicalTowerLayerShadow T)) /\
      (forall T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        sourceTraceAtTrueObservation T =
          sourceTraceAtTrueFactor (boolTraceAwareTowerShadow T)) /\
      (forall factor : BoolTraceAwareTowerShadow -> Bool,
        (forall T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
          sourceTraceAtTrueObservation T =
            factor (boolTraceAwareTowerShadow T)) ->
          forall shadow : BoolTraceAwareTowerShadow,
            factor shadow = sourceTraceAtTrueFactor shadow) := by
  exact
    ⟨sourceTraceAtTrueObservation_not_factor_through_canonicalShadow,
      sourceTraceAtTrueObservation_factors_through_traceAwareShadow,
      fun factor hfactor =>
        sourceTraceAtTrueFactor_pointwise_unique hfactor⟩

/-! ## Integrated finite target-strength support package -/

/--
Cycle 8 target-strength finite shadow and universal factorization package.

The theorem remains conditional on explicit adequacy and reflection premises.
Those premises are visible arguments, not hidden fields of the tower or the
artifact schema.
-/
theorem targetStrengthUniversalShadowFactorization_package
    {Atom : Type u}
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)
    (adequacy : LayeredRepairAdequacy T)
    (reflection : FiniteTowerShadowReflection T) :
    (GlobalSemanticRepairCoherent T <-> ObstructionTowerVanishes T) /\
      (ObstructionTowerVanishes T ->
        FiniteTowerLayerShadowZero (canonicalTowerLayerShadow T)) /\
      (FiniteTowerLayerShadowZero (canonicalTowerLayerShadow T) ->
        ObstructionTowerVanishes T) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        assignmentLayerShadow assignment T =
          assignmentReadsShadow assignment (canonicalTowerLayerShadow T)) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        FiniteTowerLayerShadowZero (canonicalTowerLayerShadow T) ->
          FiniteTowerLayerShadowZero (assignmentLayerShadow assignment T)) /\
      (archSigStyleArtifactShadow (archSigStyleArtifactOfTower T) =
        canonicalTowerLayerShadow T) /\
      (forall artifact : ArchSigStyleFiniteShadowArtifact,
        ArchSigStyleFiniteShadowAdequacy T artifact ->
          (archSigStyleArtifactShadow artifact).h1 =
              (canonicalTowerLayerShadow T).h1 /\
            (archSigStyleArtifactShadow artifact).torsor =
              (canonicalTowerLayerShadow T).torsor /\
            (archSigStyleArtifactShadow artifact).higher =
              (canonicalTowerLayerShadow T).higher /\
            (archSigStyleArtifactShadow artifact).stack =
              (canonicalTowerLayerShadow T).stack) := by
  exact
    ⟨universalSemanticRepairObstructionTower_iff T adequacy,
      obstructionTowerVanishes_to_canonicalShadowZero T,
      canonicalShadowZero_to_obstructionTowerVanishes T reflection,
      fun assignment =>
        soundAllLayerAssignment_factors_through_tower assignment T,
      fun assignment hzero =>
        by
          simpa [assignmentLayerShadow] using
            soundAllLayerAssignment_preserves_shadow_zero assignment hzero,
      archSigStyleArtifactOfTower_factors_through_tower T,
      fun artifact artifactAdequacy =>
        archSigStyleArtifact_matches_tower_layers artifactAdequacy⟩

end SemanticRepairUniversalShadow
end QualitySurface
end ResearchLean.AG
