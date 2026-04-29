import Formal.Arch.ArchitecturePath

namespace Formal.Arch

universe u v

/--
Evolution-specific transition tags.

These tags classify steps in a bounded architecture evolution sequence. They do
not assert flatness preservation, obstruction reporting, or repair progress by
themselves.
-/
inductive ArchitectureTransitionKind where
  | featureExtension
  | drift
  | repair
  | migration
  | policyUpdate
  | runtimeTopologyChange
  | semanticContractChange
  deriving DecidableEq, Repr

namespace ArchitectureTransitionKind

/-- Human-readable transition tag used by documentation-facing theorem packages. -/
def label : ArchitectureTransitionKind -> String
  | featureExtension => "featureExtension"
  | drift => "drift"
  | repair => "repair"
  | migration => "migration"
  | policyUpdate => "policyUpdate"
  | runtimeTopologyChange => "runtimeTopologyChange"
  | semanticContractChange => "semanticContractChange"

end ArchitectureTransitionKind

/--
A primitive transition in an architecture evolution sequence.

The endpoints are indexed in the type, while coverage, exactness, lawfulness,
and non-conclusions remain explicit proof-package fields.
-/
structure ArchitectureTransition (State : Type u) (source target : State) where
  kind : ArchitectureTransitionKind
  lawful : Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

namespace ArchitectureTransition

variable {State : Type u}

/-- The endpoint obtained by applying one transition to its source state. -/
def ApplyTransition (X : State) {Y : State}
    (_t : ArchitectureTransition State X Y) : State :=
  Y

/-- A transition preserves the selected flatness predicate across its endpoints. -/
def TransitionPreservesFlatness
    (ArchitectureFlat : State -> Prop)
    {X Y : State} (t : ArchitectureTransition State X Y) : Prop :=
  ArchitectureFlat X -> ArchitectureFlat (ApplyTransition X t)

/-- The theorem package explicitly records a transition non-conclusion clause. -/
def RecordsNonConclusions
    {X Y : State} (t : ArchitectureTransition State X Y) : Prop :=
  t.nonConclusions

/--
Single-step bounded flatness preservation.

This is relative to the selected `ArchitectureFlat` predicate and the supplied
transition proof package; it does not claim global extractor completeness.
-/
theorem flatness_of_transitionPreservesFlatness
    {ArchitectureFlat : State -> Prop}
    {X Y : State} (t : ArchitectureTransition State X Y)
    (hFlat : ArchitectureFlat X)
    (hPreserves : TransitionPreservesFlatness ArchitectureFlat t) :
    ArchitectureFlat (ApplyTransition X t) :=
  hPreserves hFlat

/-- A transition tagged as a feature-extension step. -/
def FeatureExtensionStep {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  t.kind = ArchitectureTransitionKind.featureExtension

/-- A transition tagged as an architecture drift event. -/
def DriftEvent {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  t.kind = ArchitectureTransitionKind.drift

/-- A transition tagged as a repair step. -/
def RepairTransition {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  t.kind = ArchitectureTransitionKind.repair

/-- A transition tagged as a migration step. -/
def MigrationStep {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  t.kind = ArchitectureTransitionKind.migration

/-- A transition tagged as a policy update. -/
def PolicyUpdate {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  t.kind = ArchitectureTransitionKind.policyUpdate

/-- A transition tagged as a runtime topology change. -/
def RuntimeTopologyChange {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  t.kind = ArchitectureTransitionKind.runtimeTopologyChange

/-- A transition tagged as a semantic contract change. -/
def SemanticContractChange {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  t.kind = ArchitectureTransitionKind.semanticContractChange

/--
Minimal schema for drift-obstruction reporting.

The schema is intentionally bounded: it relates selected introduced witnesses
to selected reported witnesses and records coverage, exactness, and
non-conclusions separately.
-/
structure DriftObstructionSchema (State : Type u) (Witness : Type v) where
  introduces :
    {X Y : State} -> ArchitectureTransition State X Y -> Witness -> Prop
  reported : State -> Witness -> Prop
  reportIntroduced :
    ∀ {X Y : State} (t : ArchitectureTransition State X Y) (w : Witness),
      DriftEvent t -> introduces t w ->
        reported (ApplyTransition X t) w
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

variable {Witness : Type v}

/-- A selected witness introduced by a transition. -/
def IntroducesObstruction
    (S : DriftObstructionSchema State Witness)
    {X Y : State} (t : ArchitectureTransition State X Y)
    (w : Witness) : Prop :=
  S.introduces t w

/-- A selected witness reported at an architecture state. -/
def ReportedObstruction
    (S : DriftObstructionSchema State Witness)
    (X : State) (w : Witness) : Prop :=
  S.reported X w

/--
Drift-obstruction reporting soundness for the selected witness schema.
-/
theorem reportedObstruction_of_drift
    (S : DriftObstructionSchema State Witness)
    {X Y : State} (t : ArchitectureTransition State X Y)
    {w : Witness}
    (hDrift : DriftEvent t)
    (hIntroduces : IntroducesObstruction S t w) :
    ReportedObstruction S (ApplyTransition X t) w :=
  S.reportIntroduced t w hDrift hIntroduces

end ArchitectureTransition

/--
A finite architecture evolution sequence using evolution-specific transitions.
-/
abbrev ArchitectureEvolution (State : Type u) :=
  ArchitecturePath (ArchitectureTransition State)

/-- Every transition in an evolution sequence satisfies the supplied predicate. -/
def EveryTransition :
    {X Y : State} -> ArchitectureEvolution State X Y ->
      ((X Y : State) -> ArchitectureTransition State X Y -> Prop) -> Prop
  | _, _, ArchitecturePath.nil _, _P => True
  | _, _, ArchitecturePath.cons step rest, P =>
      P _ _ step ∧ EveryTransition rest P

/-- A bounded migration sequence is a path whose selected steps are migrations. -/
def MigrationSequence
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Prop :=
  EveryTransition plan (fun _ _ t => ArchitectureTransition.MigrationStep t)

/-- Every transition in the plan satisfies its local lawfulness field. -/
def EveryStepLawful
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Prop :=
  EveryTransition plan (fun _ _ t => t.lawful)

/-- The target of a plan is flat for the selected bounded flatness predicate. -/
def TargetFlat
    (ArchitectureFlat : State -> Prop)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Prop :=
  ArchitectureFlat (ArchitecturePath.ApplyPath X plan)

/-- A plan eventually reaches a flat target for the selected predicate. -/
def EventuallyFlat
    (ArchitectureFlat : State -> Prop)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Prop :=
  ArchitectureFlat (ArchitecturePath.ApplyPath X plan)

/-- A target-flat migration plan is eventually flat. -/
theorem eventuallyFlat_of_targetFlat
    {ArchitectureFlat : State -> Prop}
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (_hMigration : MigrationSequence plan)
    (_hLawful : EveryStepLawful plan)
    (hTarget : TargetFlat ArchitectureFlat plan) :
    EventuallyFlat ArchitectureFlat plan :=
  hTarget

/--
Bridge from the generic `ArchitecturePath` invariant theorem to the
evolution-specific flatness name.
-/
theorem evolutionPathPreservesFlatness
    {ArchitectureFlat : State -> Prop}
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart : ArchitectureFlat X)
    (hEvery :
      ArchitecturePath.EveryStepPreserves
        (Step := ArchitectureTransition State) plan ArchitectureFlat) :
    EventuallyFlat ArchitectureFlat plan :=
  ArchitecturePath.pathPreservesInvariant plan hStart hEvery

end Formal.Arch
