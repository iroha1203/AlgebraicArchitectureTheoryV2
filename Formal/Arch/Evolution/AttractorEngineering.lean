import Formal.Arch.Evolution.SignatureDynamics

namespace Formal.Arch

universe u v w

/--
The complement of a selected bad region, read as a selected safe region.

This is only a predicate-level wrapper: it does not assert that a review,
tooling, or empirical process can identify or avoid every bad state.
-/
abbrev AvoidsBadRegion {Sig : Type v} (Bad : Sig -> Prop) : SafeRegion Sig :=
  fun sig => ¬ Bad sig

/--
A minimal Attractor Engineering support package.

The package does not introduce a global architecture field. It bundles the
selected observation, finite operation support, bounded transition semantics,
target region, and explicit support-preservation assumption needed to reuse the
existing `SignatureDynamics` safe-trajectory theorem.
-/
structure AttractorEngineeringSupportPackage
    (State : Type u) (Sig : Type v) (OperationId : Type w) where
  observation : SignatureObservation State Sig
  kernel : FiniteOperationKernel State OperationId
  semantics : OperationTransitionSemantics State OperationId
  targetRegion : SafeRegion Sig
  supportPreserves :
    kernel.SupportOperationsPreserveSafeRegion semantics observation targetRegion
  coverageAssumptions : Prop
  measurementBoundary : Prop
  nonConclusions : Prop

namespace AttractorEngineeringSupportPackage

variable {State : Type u} {Sig : Type v} {OperationId : Type w}

/-- The package explicitly records its selected coverage assumptions. -/
def RecordsCoverageAssumptions
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    Prop :=
  package.coverageAssumptions

/--
The package explicitly records the measurement boundary: unmeasured axes,
tooling coverage, calibration, and empirical completeness remain outside the
Lean theorem claim.
-/
def RecordsMeasurementBoundary
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    Prop :=
  package.measurementBoundary

/-- The package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    Prop :=
  package.nonConclusions

/-- The selected target trajectory read by the package observation. -/
def TargetTrajectory
    (package : AttractorEngineeringSupportPackage State Sig OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    List Sig :=
  SignatureTrajectory package.observation plan

/--
The support-preservation premise stored in the package, exposed as an accessor
theorem for downstream wrappers.
-/
theorem supportPreserves_targetRegion
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    package.kernel.SupportOperationsPreserveSafeRegion
      package.semantics package.observation package.targetRegion :=
  package.supportPreserves

/--
If a bounded script is realized by the selected operation semantics, uses only
finite-support operations, and starts inside the target region, then its target
trajectory stays inside that region.

This is the Attractor Engineering reading of
`FiniteOperationKernel.boundedSampledScript_preserves_safeRegion`.
-/
theorem supportPackage_preserves_targetTrajectory
    (package : AttractorEngineeringSupportPackage State Sig OperationId)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart :
      StateInSafeRegion package.observation package.targetRegion X)
    (hRealizes : script.RealizesEvolution package.semantics plan)
    (hSupport :
      package.kernel.ScriptUsesSupport script.operations plan) :
    SignatureTrajectoryInSafeRegion package.targetRegion
      (package.TargetTrajectory plan) :=
  FiniteOperationKernel.boundedSampledScript_preserves_safeRegion
    package.kernel package.semantics package.observation package.targetRegion
    script plan hStart hRealizes hSupport package.supportPreserves

/--
Specialize a support package whose target region is the complement of a bad
region. The conclusion is still a bounded trajectory theorem, not a claim about
global bad-region discovery or empirical guardrail capacity.
-/
theorem supportPackage_avoids_badRegion
    (package : AttractorEngineeringSupportPackage State Sig OperationId)
    (Bad : Sig -> Prop)
    (hTarget : package.targetRegion = AvoidsBadRegion Bad)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart :
      StateInSafeRegion package.observation (AvoidsBadRegion Bad) X)
    (hRealizes : script.RealizesEvolution package.semantics plan)
    (hSupport :
      package.kernel.ScriptUsesSupport script.operations plan) :
    SignatureTrajectoryInSafeRegion (AvoidsBadRegion Bad)
      (package.TargetTrajectory plan) := by
  rw [← hTarget] at hStart ⊢
  exact
    package.supportPackage_preserves_targetTrajectory
      script plan hStart hRealizes hSupport

/--
A direct wrapper for support shaping against a selected bad region, using the
bad-region complement as the safe region.
-/
theorem supportShaping_avoids_badRegion
    (O : SignatureObservation State Sig)
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (Bad : Sig -> Prop)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart : StateInSafeRegion O (AvoidsBadRegion Bad) X)
    (hRealizes : script.RealizesEvolution sem plan)
    (hSupport : kernel.ScriptUsesSupport script.operations plan)
    (hPreserves :
      kernel.SupportOperationsPreserveSafeRegion sem O (AvoidsBadRegion Bad)) :
    SignatureTrajectoryInSafeRegion (AvoidsBadRegion Bad)
      (SignatureTrajectory O plan) :=
  FiniteOperationKernel.boundedSampledScript_preserves_safeRegion
    kernel sem O (AvoidsBadRegion Bad) script plan
    hStart hRealizes hSupport hPreserves

end AttractorEngineeringSupportPackage

/-
A finite witness separating accepted-step invariant preservation from
support-family preservation.

The selected controller accepts only safe self-steps. The selected support at
the safe state still contains an operation that can realize a hazardous drift,
so support preservation does not follow from accepted preservation alone.
-/
namespace AcceptedPreservationNotSupportPreservation

inductive ExampleOperation where
  | acceptedNoop
  | unsafeDrift
  deriving DecidableEq, Repr

abbrev ExampleState := Bool
abbrev ExampleSig := Bool

def safeState : ExampleState := false
def unsafeState : ExampleState := true

def observation : SignatureObservation ExampleState ExampleSig where
  observe := id
  coverageAssumptions := True
  nonConclusions := True

def safeRegion : SafeRegion ExampleSig :=
  fun sig => sig = false

def acceptedTransition :
    ArchitectureTransition ExampleState safeState safeState where
  kind := ArchitectureTransitionKind.policyUpdate
  lawful := True
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def unsafeTransition :
    ArchitectureTransition ExampleState safeState unsafeState where
  kind := ArchitectureTransitionKind.drift
  lawful := True
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def control : DampingControlSchema ExampleState ExampleSig where
  observation := observation
  invariant := safeRegion
  accepted := fun {X Y} _t => X = safeState ∧ Y = safeState
  rejected := fun {X Y} _t => Y = unsafeState
  acceptedPreservesInvariant := by
    intro X Y _t hAccepted _hStart
    simpa [StateInSafeRegion, observation, safeRegion] using hAccepted.2
  coverageAssumptions := True
  nonConclusions := True

def semantics :
    OperationTransitionSemantics ExampleState ExampleOperation where
  realizes := fun op {X Y} _t =>
    match op with
    | ExampleOperation.acceptedNoop => X = safeState ∧ Y = safeState
    | ExampleOperation.unsafeDrift => X = safeState ∧ Y = unsafeState
  coverageAssumptions := True
  nonConclusions := True

def kernel : FiniteOperationKernel ExampleState ExampleOperation where
  support := fun X =>
    if X = safeState then
      [ExampleOperation.acceptedNoop, ExampleOperation.unsafeDrift]
    else
      [ExampleOperation.acceptedNoop]
  coverageAssumptions := True
  weightSourceBoundary := True
  normalizationBoundary := True
  nonConclusions := True

theorem acceptedTransition_accepted :
    control.AcceptedStep acceptedTransition := by
  simp [DampingControlSchema.AcceptedStep, control, acceptedTransition,
    safeState]

theorem acceptedTransition_preserves_selectedInvariant :
    StepPreservesSafeRegion control.observation control.invariant
      acceptedTransition :=
  control.acceptedStep_preserves_selectedInvariant
    acceptedTransition acceptedTransition_accepted

theorem source_supports_unsafeOperation :
    kernel.Supports safeState ExampleOperation.unsafeDrift := by
  simp [FiniteOperationKernel.Supports, kernel, safeState]

theorem unsafeOperation_realizes_unsafeTransition :
    semantics.Realizes ExampleOperation.unsafeDrift unsafeTransition := by
  simp [OperationTransitionSemantics.Realizes, semantics, safeState,
    unsafeState]

theorem unsafeOperation_not_preserves_safeRegion :
    ¬ semantics.OperationPreservesSafeRegion control.observation
      control.invariant ExampleOperation.unsafeDrift := by
  intro hPreserves
  have hStep :
      StepPreservesSafeRegion control.observation control.invariant
        unsafeTransition :=
    hPreserves unsafeTransition unsafeOperation_realizes_unsafeTransition
  have hTarget :
      StateInSafeRegion control.observation control.invariant unsafeState :=
    hStep (by
      simp [StateInSafeRegion, control, observation, safeRegion, safeState])
  simp [StateInSafeRegion, control, observation, safeRegion, unsafeState] at hTarget

/--
Bundled counterexample: accepted-step invariant preservation can hold, and a
nonempty accepted safe step can exist, while the operation support still
contains an operation that does not preserve the selected safe region.

This records only a finite Lean boundary. It does not claim anything about
review capacity, CI effectiveness, policy completeness, PR outcomes, or
empirical support estimation.
-/
theorem acceptedPreservation_not_supportPreservation_counterexample :
    (∃ (t : ArchitectureTransition ExampleState safeState safeState),
      control.AcceptedStep t ∧
        StepPreservesSafeRegion control.observation control.invariant t) ∧
    (∀ {X Y : ExampleState} (t : ArchitectureTransition ExampleState X Y),
      control.AcceptedStep t ->
        StepPreservesSafeRegion control.observation control.invariant t) ∧
    (∃ X op,
      kernel.Supports X op ∧
        ¬ semantics.OperationPreservesSafeRegion control.observation
          control.invariant op) ∧
    DampingControlSchema.RecordsNonConclusions control ∧
    FiniteOperationKernel.RecordsNonConclusions kernel ∧
    OperationTransitionSemantics.RecordsNonConclusions semantics := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      ⟨acceptedTransition, acceptedTransition_accepted,
        acceptedTransition_preserves_selectedInvariant⟩
  · intro X Y t hAccepted
    exact control.acceptedStep_preserves_selectedInvariant t hAccepted
  · exact
      ⟨safeState, ExampleOperation.unsafeDrift, source_supports_unsafeOperation,
        unsafeOperation_not_preserves_safeRegion⟩
  · simp [DampingControlSchema.RecordsNonConclusions, control]
  · simp [FiniteOperationKernel.RecordsNonConclusions, kernel]
  · simp [OperationTransitionSemantics.RecordsNonConclusions, semantics]

end AcceptedPreservationNotSupportPreservation

/-
Constructive finite return for a selected strict / fair damping trace.

The theorem in this namespace is trace-relative: it proves a Nat-valued
bad-axis descent fact under explicit nonincrease and strict fair-block
assumptions. It does not assert that review, CI, policy, or tooling can
establish those assumptions for real pull-request streams.
-/
namespace ConstructiveDampingFiniteReturn

variable {State : Type u} {Sig : Type v}

/--
Minimal strict / fair block damping package for a selected bad-axis score.

`blockLength` is the selected finite block bound. The strict decrease and
nonincrease hypotheses are kept as theorem inputs over a concrete trace, so
this package remains separate from empirical support estimation.
-/
structure StrictFairBlockDampingAssumption
    (control : DampingControlSchema State Sig) where
  badAxis : Sig -> Nat
  blockLength : Nat
  acceptedNonincreaseBoundary : Prop
  empiricalSupportBoundary : Prop
  nonConclusions : Prop

namespace StrictFairBlockDampingAssumption

variable {control : DampingControlSchema State Sig}

/-- Score of the selected signature trajectory at index `n`. -/
def scoreAt
    (assumption : StrictFairBlockDampingAssumption control)
    (trajectory : Nat -> Sig) (n : Nat) : Nat :=
  assumption.badAxis (trajectory n)

/-- The selected score trace is nonincreasing at every adjacent step. -/
def TraceNonincreasing
    (assumption : StrictFairBlockDampingAssumption control)
    (trajectory : Nat -> Sig) : Prop :=
  ∀ n, assumption.scoreAt trajectory (n + 1) ≤
    assumption.scoreAt trajectory n

/--
Every positive-score block has a strict decrease within the selected finite
block length.
-/
def TraceHasStrictFairBlocks
    (assumption : StrictFairBlockDampingAssumption control)
    (trajectory : Nat -> Sig) : Prop :=
  ∀ n, 0 < assumption.scoreAt trajectory n ->
    ∃ step,
      0 < step ∧ step ≤ assumption.blockLength ∧
        assumption.scoreAt trajectory (n + step) <
          assumption.scoreAt trajectory n

/--
Nonincrease alone is only a boundary condition; finite return needs the
separate strict fair-block hypothesis.
-/
def RecordsAcceptedNonincreaseBoundary
    (assumption : StrictFairBlockDampingAssumption control) : Prop :=
  assumption.acceptedNonincreaseBoundary

/--
Whether empirical tooling supports the strict fair-block hypothesis is outside
the Lean theorem claim.
-/
def RecordsEmpiricalSupportBoundary
    (assumption : StrictFairBlockDampingAssumption control) : Prop :=
  assumption.empiricalSupportBoundary

/-- The strict damping package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (assumption : StrictFairBlockDampingAssumption control) : Prop :=
  assumption.nonConclusions

private theorem natScore_finiteReturn_of_strictFairBlocks
    (score : Nat -> Nat) (k B : Nat)
    (hStart : score 0 = B)
    (hNonincrease : ∀ n, score (n + 1) ≤ score n)
    (hStrict :
      ∀ n, 0 < score n ->
        ∃ step, 0 < step ∧ step ≤ k ∧ score (n + step) < score n) :
    ∃ n, n ≤ k * B ∧ score n = 0 := by
  revert score
  refine Nat.strongRecOn B ?_
  intro B ih score hStart hNonincrease hStrict
  cases B with
  | zero =>
      exact ⟨0, by simp, hStart⟩
  | succ B =>
      by_cases hZero : score 0 = 0
      · exact ⟨0, by simp, hZero⟩
      · have hPositive : 0 < score 0 := Nat.pos_of_ne_zero hZero
        obtain ⟨step, hStepPos, hStepLe, hStepDec⟩ :=
          hStrict 0 hPositive
        let score' : Nat -> Nat := fun n => score (step + n)
        have hStart' : score' 0 = score step := by
          simp [score']
        have hScoreStepLt : score step < Nat.succ B := by
          have hDec : score (0 + step) < score 0 := hStepDec
          simpa [hStart] using hDec
        have hScoreStepLe : score step ≤ B :=
          Nat.le_of_lt_succ hScoreStepLt
        have hNonincrease' : ∀ n, score' (n + 1) ≤ score' n := by
          intro n
          simpa [score', Nat.add_assoc] using hNonincrease (step + n)
        have hStrict' :
            ∀ n, 0 < score' n ->
              ∃ step, 0 < step ∧ step ≤ k ∧
                score' (n + step) < score' n := by
          intro n hPos
          obtain ⟨step', hStep'Pos, hStep'Le, hStep'Dec⟩ :=
            hStrict (step + n) (by simpa [score'] using hPos)
          refine ⟨step', hStep'Pos, hStep'Le, ?_⟩
          simpa [score', Nat.add_assoc] using hStep'Dec
        obtain ⟨r, hRLe, hRZero⟩ :=
          ih (score step) hScoreStepLt score' hStart'
            hNonincrease' hStrict'
        refine ⟨step + r, ?_, ?_⟩
        · have hRBound : r ≤ k * B :=
            le_trans hRLe (Nat.mul_le_mul_left k hScoreStepLe)
          have hTotal : step + r ≤ k + k * B :=
            Nat.add_le_add hStepLe hRBound
          simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hTotal
        · simpa [score'] using hRZero

/--
If a selected bad-axis score starts at `B`, is nonincreasing, and every positive
block of length `blockLength` contains a strict decrease, then the trace reaches
score zero by some index `n <= blockLength * B`.
-/
theorem strictFairBlockDamping_finiteReturn
    (assumption : StrictFairBlockDampingAssumption control)
    (trajectory : Nat -> Sig) (B : Nat)
    (hStart : assumption.scoreAt trajectory 0 = B)
    (hNonincrease : assumption.TraceNonincreasing trajectory)
    (hStrict : assumption.TraceHasStrictFairBlocks trajectory) :
    ∃ n, n ≤ assumption.blockLength * B ∧
      assumption.scoreAt trajectory n = 0 :=
  natScore_finiteReturn_of_strictFairBlocks
    (fun n => assumption.scoreAt trajectory n)
    assumption.blockLength B hStart hNonincrease hStrict

/--
Bundled Attractor Engineering reading: the finite return conclusion is paired
with explicit boundary records for nonincrease-only reasoning and empirical
tooling support.
-/
theorem strictFairBlockDamping_finiteReturn_with_boundaries
    (assumption : StrictFairBlockDampingAssumption control)
    (trajectory : Nat -> Sig) (B : Nat)
    (hStart : assumption.scoreAt trajectory 0 = B)
    (hNonincrease : assumption.TraceNonincreasing trajectory)
    (hStrict : assumption.TraceHasStrictFairBlocks trajectory)
    (hAcceptedBoundary :
      assumption.RecordsAcceptedNonincreaseBoundary)
    (hEmpiricalBoundary :
      assumption.RecordsEmpiricalSupportBoundary)
    (hNonConclusions :
      assumption.RecordsNonConclusions) :
    (∃ n, n ≤ assumption.blockLength * B ∧
      assumption.scoreAt trajectory n = 0) ∧
    assumption.RecordsAcceptedNonincreaseBoundary ∧
    assumption.RecordsEmpiricalSupportBoundary ∧
    assumption.RecordsNonConclusions := by
  exact
    ⟨assumption.strictFairBlockDamping_finiteReturn
        trajectory B hStart hNonincrease hStrict,
      hAcceptedBoundary,
      hEmpiricalBoundary,
      hNonConclusions⟩

end StrictFairBlockDampingAssumption

end ConstructiveDampingFiniteReturn

end Formal.Arch
