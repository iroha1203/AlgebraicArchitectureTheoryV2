import Formal.Arch.DependencyObstruction
import Formal.Arch.LocalReplacement

namespace Formal.Arch

universe u v w

namespace ArchitectureSignature

/-- Boundary or abstraction policy violation on one dependency pair. -/
def PolicyViolation {C : Type u} (G : ArchGraph C)
    (allowed : C -> C -> Prop) (pair : C × C) : Prop :=
  G.edge pair.1 pair.2 ∧ ¬ allowed pair.1 pair.2

instance instDecidablePredPolicyViolation {C : Type u} (G : ArchGraph C)
    (allowed : C -> C -> Prop)
    [DecidableRel G.edge] [DecidableRel allowed] :
    DecidablePred (PolicyViolation G allowed) := by
  intro pair
  unfold PolicyViolation
  infer_instance

/-- A dependency graph respects a local edge policy. -/
def PolicySound {C : Type u} (G : ArchGraph C)
    (allowed : C -> C -> Prop) : Prop :=
  ∀ {c d : C}, G.edge c d -> allowed c d

/-- Boundary-policy soundness, kept separate from obstruction counting. -/
def BoundaryPolicySound {C : Type u} (G : ArchGraph C)
    (boundaryAllowed : C -> C -> Prop) : Prop :=
  PolicySound G boundaryAllowed

/-- Abstraction-policy soundness, kept separate from obstruction counting. -/
def AbstractionPolicySound {C : Type u} (G : ArchGraph C)
    (abstractionAllowed : C -> C -> Prop) : Prop :=
  PolicySound G abstractionAllowed

/-- Boundary-policy obstruction witness on one dependency pair. -/
def BoundaryPolicyObstruction {C : Type u} (G : ArchGraph C)
    (boundaryAllowed : C -> C -> Prop) (pair : C × C) : Prop :=
  PolicyViolation G boundaryAllowed pair

/-- Abstraction-policy obstruction witness on one dependency pair. -/
def AbstractionPolicyObstruction {C : Type u} (G : ArchGraph C)
    (abstractionAllowed : C -> C -> Prop) (pair : C × C) : Prop :=
  PolicyViolation G abstractionAllowed pair

theorem boundaryPolicySound_iff_no_boundaryPolicyObstruction
    {C : Type u} {G : ArchGraph C} (boundaryAllowed : C -> C -> Prop) :
    BoundaryPolicySound G boundaryAllowed ↔
      ¬ ∃ pair : C × C, BoundaryPolicyObstruction G boundaryAllowed pair := by
  constructor
  · intro hSound hExists
    rcases hExists with ⟨pair, hBad⟩
    exact hBad.2 (hSound hBad.1)
  · intro hNoObstruction c d hEdge
    by_contra hNotAllowed
    exact hNoObstruction ⟨(c, d), hEdge, hNotAllowed⟩

theorem abstractionPolicySound_iff_no_abstractionPolicyObstruction
    {C : Type u} {G : ArchGraph C} (abstractionAllowed : C -> C -> Prop) :
    AbstractionPolicySound G abstractionAllowed ↔
      ¬ ∃ pair : C × C, AbstractionPolicyObstruction G abstractionAllowed pair := by
  constructor
  · intro hSound hExists
    rcases hExists with ⟨pair, hBad⟩
    exact hBad.2 (hSound hBad.1)
  · intro hNoObstruction c d hEdge
    by_contra hNotAllowed
    exact hNoObstruction ⟨(c, d), hEdge, hNotAllowed⟩

/-- The five concrete required-law witnesses represented by Signature v1 axes. -/
inductive ArchitectureRequiredLawWitness where
  | hasCycle
  | projectionSoundness
  | lsp
  | boundaryPolicy
  | abstractionPolicy
  deriving DecidableEq, Repr

/-- Short public name for the concrete Signature-integrated witness family. -/
abbrev ArchitectureWitness := ArchitectureRequiredLawWitness

/-- The measured universe for the current required Signature law family. -/
def architectureRequiredLawWitnesses : List ArchitectureRequiredLawWitness :=
  [ .hasCycle
  , .projectionSoundness
  , .lsp
  , .boundaryPolicy
  , .abstractionPolicy
  ]

/-- Public entry point for the measured architecture witness universe. -/
def architectureMeasuredWitnesses : List ArchitectureWitness :=
  architectureRequiredLawWitnesses

/-- Every current architecture witness is a required witness. -/
def architectureRequiredWitness (_ : ArchitectureWitness) : Prop :=
  True

/-- Selected Signature v1 axes used as required zero-law axes. -/
def architectureRequiredAxis (axis : ArchitectureSignatureV1Axis) : Prop :=
  IsSelectedRequiredLawAxis axis

/--
How a candidate law or metric participates in the full zero-curvature law
universe.

Only `requiredLaw` candidates are part of `ArchitectureLawful` and the final
required-axis theorem. Corollaries and diagnostic or empirical axes may be
connected by separate bridge theorems without changing the required-zero
policy.
-/
inductive ArchitectureLawCandidateRole where
  | requiredLaw
  | derivedCorollary
  | diagnosticAxis
  | empiricalAxis
  deriving DecidableEq, Repr

/--
Named candidates considered for the full architecture law universe.

This list includes the current required witness family plus adjacent theorem
families and extension axes that are intentionally kept outside the required
zero-axis policy.
-/
inductive ArchitectureLawUniverseCandidate where
  | closedWalkAcyclicity
  | projectionSoundness
  | lspCompatibility
  | boundaryPolicySoundness
  | abstractionPolicySoundness
  | localReplacementContract
  | stateEffectDiagramLaw
  | nilpotencyIndex
  | spectralRadius
  | runtimePropagation
  | relationComplexity
  | empiricalChangeCost
  deriving DecidableEq, Repr

/-- The finite candidate universe tracked by the current design policy. -/
def architectureFullLawUniverseCandidates :
    List ArchitectureLawUniverseCandidate :=
  [ .closedWalkAcyclicity
  , .projectionSoundness
  , .lspCompatibility
  , .boundaryPolicySoundness
  , .abstractionPolicySoundness
  , .localReplacementContract
  , .stateEffectDiagramLaw
  , .nilpotencyIndex
  , .spectralRadius
  , .runtimePropagation
  , .relationComplexity
  , .empiricalChangeCost
  ]

/--
Policy classification for each candidate in the full law universe.

`localReplacementContract` is a packaging corollary over projection and LSP
facts. `stateEffectDiagramLaw` already has its own diagram-law bridge and is
not bundled into the static dependency final theorem. Matrix and runtime axes
are diagnostics, while relation complexity and empirical change cost remain
empirical axes.
-/
def architectureLawCandidateRole :
    ArchitectureLawUniverseCandidate -> ArchitectureLawCandidateRole
  | .closedWalkAcyclicity => .requiredLaw
  | .projectionSoundness => .requiredLaw
  | .lspCompatibility => .requiredLaw
  | .boundaryPolicySoundness => .requiredLaw
  | .abstractionPolicySoundness => .requiredLaw
  | .localReplacementContract => .derivedCorollary
  | .stateEffectDiagramLaw => .derivedCorollary
  | .nilpotencyIndex => .diagnosticAxis
  | .spectralRadius => .diagnosticAxis
  | .runtimePropagation => .diagnosticAxis
  | .relationComplexity => .empiricalAxis
  | .empiricalChangeCost => .empiricalAxis

/-- Required-law candidates are exactly the five witnesses in `ArchitectureLawful`. -/
theorem architectureLawCandidateRole_requiredLaw_iff
    {candidate : ArchitectureLawUniverseCandidate} :
    architectureLawCandidateRole candidate =
        ArchitectureLawCandidateRole.requiredLaw ↔
      candidate = .closedWalkAcyclicity ∨
      candidate = .projectionSoundness ∨
      candidate = .lspCompatibility ∨
      candidate = .boundaryPolicySoundness ∨
      candidate = .abstractionPolicySoundness := by
  cases candidate <;> simp [architectureLawCandidateRole]

/--
The current final theorem requires only selected Signature axes. Matrix,
runtime, state-effect, and empirical candidates are not required-zero axes.
-/
theorem architectureLawCandidateRole_nonrequired_examples :
    architectureLawCandidateRole .localReplacementContract =
        ArchitectureLawCandidateRole.derivedCorollary ∧
    architectureLawCandidateRole .stateEffectDiagramLaw =
        ArchitectureLawCandidateRole.derivedCorollary ∧
    architectureLawCandidateRole .nilpotencyIndex =
        ArchitectureLawCandidateRole.diagnosticAxis ∧
    architectureLawCandidateRole .spectralRadius =
        ArchitectureLawCandidateRole.diagnosticAxis ∧
    architectureLawCandidateRole .runtimePropagation =
        ArchitectureLawCandidateRole.diagnosticAxis ∧
    architectureLawCandidateRole .relationComplexity =
        ArchitectureLawCandidateRole.empiricalAxis ∧
    architectureLawCandidateRole .empiricalChangeCost =
        ArchitectureLawCandidateRole.empiricalAxis := by
  simp [architectureLawCandidateRole]

/-- The concrete architecture data used by the Signature-integrated law bridge. -/
structure ArchitectureLawModel (C : Type u) (A : Type v) (Obs : Type w) where
  G : ArchGraph C
  π : InterfaceProjection C A
  GA : AbstractGraph A
  O : Observation C Obs
  U : ComponentUniverse G
  boundaryAllowed : C -> C -> Prop
  abstractionAllowed : C -> C -> Prop
  lspPairClosed :
    ∀ {x y : C}, π.expose x = π.expose y -> x ∈ U.components ∧ y ∈ U.components

namespace ArchitectureLawModel

variable {C : Type u} {A : Type v} {Obs : Type w}

/-- The Signature v1 value whose selected required law axes are populated. -/
def signatureOf (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    ArchitectureSignatureV1 :=
  v1OfFiniteWithRequiredLawAxes X.G X.π X.GA X.O X.U.components
    X.boundaryAllowed X.abstractionAllowed

end ArchitectureLawModel

/--
Concrete obstruction predicate for the Signature-integrated required law
family.
-/
def ArchitectureRequiredLawBad {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    ArchitectureRequiredLawWitness -> Prop
  | .hasCycle => HasClosedWalk X.G
  | .projectionSoundness =>
      ∃ edge : C × C, ProjectionObstruction X.G X.π X.GA edge
  | .lsp =>
      ∃ pair : C × C, LSPObstruction X.π X.O pair
  | .boundaryPolicy =>
      ∃ pair : C × C, PolicyViolation X.G X.boundaryAllowed pair
  | .abstractionPolicy =>
      ∃ pair : C × C, PolicyViolation X.G X.abstractionAllowed pair

/-- Public entry point for concrete bad architecture witnesses. -/
def architectureBad {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) : ArchitectureWitness -> Prop :=
  ArchitectureRequiredLawBad X

/-- Architecture lawfulness represented by the selected required Signature axes. -/
def ArchitectureLawful {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) : Prop :=
  WalkAcyclic X.G ∧
  ProjectionSound X.G X.π X.GA ∧
  LSPCompatible X.π X.O ∧
  PolicySound X.G X.boundaryAllowed ∧
  PolicySound X.G X.abstractionAllowed

/-- Required Signature v1 axes must be present and exactly zero. -/
def RequiredSignatureAxesAvailableAndZero (sig : ArchitectureSignatureV1) : Prop :=
  ∀ axis, IsSelectedRequiredLawAxis axis ->
    ArchitectureSignatureV1.axisAvailableAndZero sig axis

/-- Short public name for selected required Signature axes being available and zero. -/
def RequiredSignatureAxesZero (sig : ArchitectureSignatureV1) : Prop :=
  RequiredSignatureAxesAvailableAndZero sig

/--
The `hasCycle` Signature axis is exact for walk acyclicity on a finite
component universe.

`nilpotencyIndex` is not used here as a required zero axis; this theorem uses
only the executable 0/1 `hasCycle` indicator and the finite-universe
correctness theorem for closed walks.
-/
theorem hasCycle_axisExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C -> C -> Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1.axisAvailableAndZero
        (v1OfFiniteWithRequiredLawAxes G π GA O U.components
          boundaryAllowed abstractionAllowed)
        .hasCycle ↔
      WalkAcyclic G := by
  constructor
  · intro hAxis hClosed
    have hZero : boolRisk (hasCycleBool G U.components) = 0 := by
      unfold ArchitectureSignatureV1.axisAvailableAndZero at hAxis
      simpa [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
        v1CoreOfFinite, v0OfFinite, AvailableAndZero] using hAxis
    have hNoCycle : hasCycleBool G U.components = false := by
      cases h : hasCycleBool G U.components
      · rfl
      · simp [boolRisk, h] at hZero
    have hCycle : hasCycleBool G U.components = true :=
      (hasCycleBool_correct_under_finite_universe U).mpr hClosed
    rw [hNoCycle] at hCycle
    contradiction
  · intro hWalkAcyclic
    have hNoCycle : hasCycleBool G U.components = false := by
      cases h : hasCycleBool G U.components
      · rfl
      · exact False.elim
          (hWalkAcyclic
            ((hasCycleBool_correct_under_finite_universe U).mp h))
    unfold ArchitectureSignatureV1.axisAvailableAndZero
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      v1CoreOfFinite, v0OfFinite, boolRisk, hNoCycle, AvailableAndZero]

/--
The `hasCycle` Signature axis is also exact for absence of closed-walk
obstruction witnesses.
-/
theorem hasCycle_axisExact_no_closedWalkObstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C -> C -> Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1.axisAvailableAndZero
        (v1OfFiniteWithRequiredLawAxes G π GA O U.components
          boundaryAllowed abstractionAllowed)
        .hasCycle ↔
      ∀ w : ClosedWalkWitness G, ¬ ClosedWalkBad w := by
  exact Iff.trans
    (hasCycle_axisExact G π GA O U boundaryAllowed abstractionAllowed)
    walkAcyclic_iff_no_closedWalkObstruction

/--
The projection-soundness Signature axis is exact for the concrete required-law
entry point. The reverse direction from zero count to graph-level obstruction
absence uses the `ComponentUniverse.edgeClosed` coverage assumption.
-/
theorem projectionSoundnessViolation_axisExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C -> C -> Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1.axisAvailableAndZero
        (v1OfFiniteWithRequiredLawAxes G π GA O U.components
          boundaryAllowed abstractionAllowed)
        .projectionSoundnessViolation ↔
      NoProjectionObstruction G π GA := by
  constructor
  · intro hAxis
    have hZero :
        projectionSoundnessViolation G π GA U.components = 0 := by
      unfold ArchitectureSignatureV1.axisAvailableAndZero at hAxis
      simpa [ArchitectureSignatureV1.axisValue,
        v1OfFiniteWithRequiredLawAxes, AvailableAndZero] using hAxis
    exact projectionSound_iff_noProjectionObstruction.mp
      (projectionSound_of_projectionSoundnessViolation_eq_zero
        U.edgeClosed hZero)
  · intro hNoObstruction
    have hSound : ProjectionSound G π GA :=
      projectionSound_iff_noProjectionObstruction.mpr hNoObstruction
    have hZero :
        projectionSoundnessViolation G π GA U.components = 0 :=
      projectionSoundnessViolation_eq_zero_of_projectionSound
        U.components hSound
    unfold ArchitectureSignatureV1.axisAvailableAndZero
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      AvailableAndZero, hZero]

/--
The LSP Signature axis is exact for the concrete required-law entry point. The
reverse direction from zero count to implementation-pair obstruction absence
uses explicit same-abstraction pair coverage.
-/
theorem lspViolationCount_axisExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C -> C -> Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed]
    (hPairClosed :
      ∀ {x y : C}, π.expose x = π.expose y ->
        x ∈ U.components ∧ y ∈ U.components) :
    ArchitectureSignatureV1.axisAvailableAndZero
        (v1OfFiniteWithRequiredLawAxes G π GA O U.components
          boundaryAllowed abstractionAllowed)
        .lspViolationCount ↔
      NoLSPObstruction π O := by
  constructor
  · intro hAxis
    have hZero : lspViolationCount π O U.components = 0 := by
      unfold ArchitectureSignatureV1.axisAvailableAndZero at hAxis
      simpa [ArchitectureSignatureV1.axisValue,
        v1OfFiniteWithRequiredLawAxes, AvailableAndZero] using hAxis
    exact lspCompatible_iff_noLSPObstruction.mp
      (lspCompatible_of_lspViolationCount_eq_zero hPairClosed hZero)
  · intro hNoObstruction
    have hLSP : LSPCompatible π O :=
      lspCompatible_iff_noLSPObstruction.mpr hNoObstruction
    have hZero : lspViolationCount π O U.components = 0 :=
      lspViolationCount_eq_zero_of_lspCompatible U.components hLSP
    unfold ArchitectureSignatureV1.axisAvailableAndZero
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      AvailableAndZero, hZero]

/-- The witness subfamily represented by each Signature v1 axis. -/
def architectureWitnessForAxis :
    ArchitectureSignatureV1Axis -> ArchitectureRequiredLawWitness -> Prop
  | .hasCycle, .hasCycle => True
  | .projectionSoundnessViolation, .projectionSoundness => True
  | .lspViolationCount, .lsp => True
  | .boundaryViolationCount, .boundaryPolicy => True
  | .abstractionViolationCount, .abstractionPolicy => True
  | _, _ => False

/-- Public entry point for the witness subfamily represented by each axis. -/
def witnessForAxis : ArchitectureSignatureV1Axis -> ArchitectureWitness -> Prop :=
  architectureWitnessForAxis

theorem mem_architectureRequiredLawWitnesses
    (witness : ArchitectureRequiredLawWitness) :
    witness ∈ architectureRequiredLawWitnesses := by
  cases witness <;> simp [architectureRequiredLawWitnesses]

theorem architectureLawful_iff_no_measured_bad
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    ArchitectureLawful X ↔
      ∀ w, w ∈ architectureMeasuredWitnesses ->
        ¬ architectureBad X w := by
  constructor
  · intro hLawful witness _hMeasured
    rcases hLawful with ⟨hAcyclic, hProjection, hLSP, hBoundary,
      hAbstraction⟩
    cases witness
    · exact fun hClosed => hAcyclic hClosed
    · rintro ⟨edge, hBad⟩
      exact (projectionSound_iff_noProjectionObstruction.mp hProjection) edge hBad
    · rintro ⟨pair, hBad⟩
      exact (lspCompatible_iff_noLSPObstruction.mp hLSP) pair hBad
    · rintro ⟨pair, hBad⟩
      exact hBad.2 (hBoundary hBad.1)
    · rintro ⟨pair, hBad⟩
      exact hBad.2 (hAbstraction hBad.1)
  · intro hNoBad
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hClosed
      exact hNoBad .hasCycle
        (mem_architectureRequiredLawWitnesses .hasCycle) hClosed
    · exact projectionSound_iff_noProjectionObstruction.mpr (by
        intro edge hBad
        exact hNoBad .projectionSoundness
          (mem_architectureRequiredLawWitnesses .projectionSoundness)
          ⟨edge, hBad⟩)
    · exact lspCompatible_iff_noLSPObstruction.mpr (by
        intro pair hBad
        exact hNoBad .lsp (mem_architectureRequiredLawWitnesses .lsp)
          ⟨pair, hBad⟩)
    · intro c d hEdge
      by_contra hNotAllowed
      exact hNoBad .boundaryPolicy
        (mem_architectureRequiredLawWitnesses .boundaryPolicy)
        ⟨(c, d), hEdge, hNotAllowed⟩
    · intro c d hEdge
      by_contra hNotAllowed
      exact hNoBad .abstractionPolicy
        (mem_architectureRequiredLawWitnesses .abstractionPolicy)
        ⟨(c, d), hEdge, hNotAllowed⟩

theorem architectureLawFamily_completeWitnessCoverage :
    CompleteWitnessCoverage
      ({ Witness := ArchitectureRequiredLawWitness
         Axis := ArchitectureSignatureV1Axis
         measured := architectureMeasuredWitnesses
         required := architectureRequiredWitness
         bad := fun X => architectureBad X
         lawful := fun X => ArchitectureLawful X
         lawful_iff_no_measured_bad := by
          intro X
          exact architectureLawful_iff_no_measured_bad X
         requiredAxis := architectureRequiredAxis } :
        LawFamily (ArchitectureLawModel C A Obs)) := by
  intro witness
  constructor
  · intro _hMeasured
    trivial
  · intro _hRequired
    exact mem_architectureRequiredLawWitnesses witness

/-- Concrete law family used by the Signature-integrated zero-curvature bridge. -/
def architectureLawFamily (C : Type u) (A : Type v) (Obs : Type w) :
    LawFamily (ArchitectureLawModel C A Obs) where
  Witness := ArchitectureRequiredLawWitness
  Axis := ArchitectureSignatureV1Axis
  measured := architectureMeasuredWitnesses
  required := architectureRequiredWitness
  bad := fun X => architectureBad X
  lawful := fun X => ArchitectureLawful X
  lawful_iff_no_measured_bad := by
    intro X
    exact architectureLawful_iff_no_measured_bad X
  requiredAxis := architectureRequiredAxis

theorem architectureLawFamily_completeCoverage :
    CompleteWitnessCoverage (architectureLawFamily C A Obs) := by
  exact architectureLawFamily_completeWitnessCoverage

theorem architecture_axisCoversOnlyRequired :
    AxisCoversOnlyRequired (architectureLawFamily C A Obs)
      architectureWitnessForAxis := by
  intro axis _hRequiredAxis witness _hWitness
  trivial

theorem architecture_requiredWitnessCoveredByAxis :
    RequiredWitnessCoveredByAxis (architectureLawFamily C A Obs)
      architectureWitnessForAxis := by
  intro witness _hRequired
  cases witness
  · exact ⟨.hasCycle, by
      show .hasCycle ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.projectionSoundnessViolation, by
      show .projectionSoundnessViolation ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.lspViolationCount, by
      show .lspViolationCount ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.boundaryViolationCount, by
      show .boundaryViolationCount ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩
  · exact ⟨.abstractionViolationCount, by
      show .abstractionViolationCount ∈ selectedRequiredLawAxes
      simp [selectedRequiredLawAxes], by trivial⟩

private theorem availableAndZero_hasCycle_iff_no_closed_walk
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .hasCycle ↔ ¬ HasClosedWalk X.G := by
  constructor
  · intro hAvailable hClosed
    have hCycle :
        hasCycleBool X.G X.U.components = true :=
      (hasCycleBool_correct_under_finite_universe X.U).mpr hClosed
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf at hAvailable
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      v1CoreOfFinite, v0OfFinite, boolRisk, hCycle, AvailableAndZero] at hAvailable
  · intro hNoClosed
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf
    have hNoCycle : hasCycleBool X.G X.U.components = false := by
      cases h : hasCycleBool X.G X.U.components
      · rfl
      · exact False.elim (hNoClosed
          ((hasCycleBool_correct_under_finite_universe X.U).mp h))
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      v1CoreOfFinite, v0OfFinite, boolRisk, hNoCycle, AvailableAndZero]

private theorem availableAndZero_projection_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .projectionSoundnessViolation ↔
        ¬ ∃ edge : C × C, ProjectionObstruction X.G X.π X.GA edge := by
  constructor
  · intro hAvailable hExists
    have hZero :
        projectionSoundnessViolation X.G X.π X.GA X.U.components = 0 := by
      unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf at hAvailable
      simpa [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
        AvailableAndZero] using hAvailable
    have hSound : ProjectionSound X.G X.π X.GA :=
      projectionSound_of_projectionSoundnessViolation_eq_zero
        X.U.edgeClosed hZero
    rcases hExists with ⟨edge, hBad⟩
    exact (projectionSound_iff_noProjectionObstruction.mp hSound) edge hBad
  · intro hNoExists
    have hSound : ProjectionSound X.G X.π X.GA :=
      projectionSound_iff_noProjectionObstruction.mpr (by
        intro edge hBad
        exact hNoExists ⟨edge, hBad⟩)
    have hZero :
        projectionSoundnessViolation X.G X.π X.GA X.U.components = 0 :=
      projectionSoundnessViolation_eq_zero_of_projectionSound
        X.U.components hSound
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      AvailableAndZero, hZero]

private theorem availableAndZero_lsp_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .lspViolationCount ↔
        ¬ ∃ pair : C × C, LSPObstruction X.π X.O pair := by
  constructor
  · intro hAvailable hExists
    have hZero : lspViolationCount X.π X.O X.U.components = 0 := by
      unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf at hAvailable
      simpa [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
        AvailableAndZero] using hAvailable
    have hLSP : LSPCompatible X.π X.O :=
      lspCompatible_of_lspViolationCount_eq_zero X.lspPairClosed hZero
    rcases hExists with ⟨pair, hBad⟩
    exact (lspCompatible_iff_noLSPObstruction.mp hLSP) pair hBad
  · intro hNoExists
    have hLSP : LSPCompatible X.π X.O :=
      lspCompatible_iff_noLSPObstruction.mpr (by
        intro pair hBad
        exact hNoExists ⟨pair, hBad⟩)
    have hZero : lspViolationCount X.π X.O X.U.components = 0 :=
      lspViolationCount_eq_zero_of_lspCompatible X.U.components hLSP
    unfold AxisAvailableAndZero ArchitectureLawModel.signatureOf
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      AvailableAndZero, hZero]

private theorem policyViolationCount_eq_zero_iff_no_obstruction
    {C : Type u} {G : ArchGraph C} [DecidableRel G.edge]
    (U : ComponentUniverse G) (allowed : C -> C -> Prop)
    [DecidableRel allowed] :
    countWhere (componentPairs U.components) (fun pair =>
      decide (G.edge pair.1 pair.2) && ! decide (allowed pair.1 pair.2)) = 0 ↔
        ¬ ∃ pair : C × C, PolicyViolation G allowed pair := by
  constructor
  · intro hZero hExists
    rcases hExists with ⟨pair, hBad⟩
    have hPairMem : pair ∈ componentPairs U.components := by
      exact mem_componentPairs_iff.mpr (U.edgeClosed hBad.1)
    have hViolationMem :
        pair ∈ (componentPairs U.components).filter (fun pair =>
          decide (G.edge pair.1 pair.2) && ! decide (allowed pair.1 pair.2)) := by
      simp [hPairMem, hBad.1, hBad.2]
    have hPositive :
        0 <
          countWhere (componentPairs U.components) (fun pair =>
            decide (G.edge pair.1 pair.2) &&
              ! decide (allowed pair.1 pair.2)) := by
      unfold countWhere
      exact List.length_pos_of_mem hViolationMem
    exact (Nat.ne_of_gt hPositive) hZero
  · intro hNoExists
    have hNoBad :
        ∀ pair, pair ∈ componentPairs U.components ->
          ¬ PolicyViolation G allowed pair := by
      intro pair _hMem hBad
      exact hNoExists ⟨pair, hBad⟩
    have hZero :
        violationCount (PolicyViolation G allowed)
          (componentPairs U.components) = 0 :=
      (violationCount_eq_zero_iff_forall_not_bad).mpr hNoBad
    simpa [violationCount, violatingWitnesses, countWhere, PolicyViolation]
      using hZero

theorem boundaryViolationCountOfFinite_eq_zero_iff_no_boundaryPolicyObstruction
    {C : Type u} {G : ArchGraph C} [DecidableRel G.edge]
    (U : ComponentUniverse G) (boundaryAllowed : C -> C -> Prop)
    [DecidableRel boundaryAllowed] :
    boundaryViolationCountOfFinite G U.components boundaryAllowed = 0 ↔
      ¬ ∃ pair : C × C,
        BoundaryPolicyObstruction G boundaryAllowed pair := by
  simpa [boundaryViolationCountOfFinite, BoundaryPolicyObstruction]
    using policyViolationCount_eq_zero_iff_no_obstruction U boundaryAllowed

theorem abstractionViolationCountOfFinite_eq_zero_iff_no_abstractionPolicyObstruction
    {C : Type u} {G : ArchGraph C} [DecidableRel G.edge]
    (U : ComponentUniverse G) (abstractionAllowed : C -> C -> Prop)
    [DecidableRel abstractionAllowed] :
    abstractionViolationCountOfFinite G U.components abstractionAllowed = 0 ↔
      ¬ ∃ pair : C × C,
        AbstractionPolicyObstruction G abstractionAllowed pair := by
  simpa [abstractionViolationCountOfFinite, AbstractionPolicyObstruction]
    using policyViolationCount_eq_zero_iff_no_obstruction U abstractionAllowed

theorem boundaryViolation_axisExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C -> C -> Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1.axisAvailableAndZero
        (v1OfFiniteWithRequiredLawAxes G π GA O U.components
          boundaryAllowed abstractionAllowed)
        .boundaryViolationCount ↔
      BoundaryPolicySound G boundaryAllowed := by
  constructor
  · intro hAxis
    have hZero :
        boundaryViolationCountOfFinite G U.components boundaryAllowed = 0 := by
      unfold ArchitectureSignatureV1.axisAvailableAndZero at hAxis
      simpa [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
        v1CoreOfFinite, v0OfFinite, AvailableAndZero] using hAxis
    change PolicySound G boundaryAllowed
    exact (boundaryPolicySound_iff_no_boundaryPolicyObstruction
      (G := G) boundaryAllowed).mpr
        ((boundaryViolationCountOfFinite_eq_zero_iff_no_boundaryPolicyObstruction
          U boundaryAllowed).mp hZero)
  · intro hSound
    have hZero :
        boundaryViolationCountOfFinite G U.components boundaryAllowed = 0 :=
      (boundaryViolationCountOfFinite_eq_zero_iff_no_boundaryPolicyObstruction
        U boundaryAllowed).mpr
        ((boundaryPolicySound_iff_no_boundaryPolicyObstruction
          (G := G) boundaryAllowed).mp hSound)
    unfold ArchitectureSignatureV1.axisAvailableAndZero
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      v1CoreOfFinite, v0OfFinite, AvailableAndZero, hZero]

theorem abstractionViolation_axisExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (U : ComponentUniverse G)
    (boundaryAllowed abstractionAllowed : C -> C -> Prop)
    [DecidableRel boundaryAllowed] [DecidableRel abstractionAllowed] :
    ArchitectureSignatureV1.axisAvailableAndZero
        (v1OfFiniteWithRequiredLawAxes G π GA O U.components
          boundaryAllowed abstractionAllowed)
        .abstractionViolationCount ↔
      AbstractionPolicySound G abstractionAllowed := by
  constructor
  · intro hAxis
    have hZero :
        abstractionViolationCountOfFinite G U.components abstractionAllowed = 0 := by
      unfold ArchitectureSignatureV1.axisAvailableAndZero at hAxis
      simpa [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
        v1CoreOfFinite, v0OfFinite, AvailableAndZero] using hAxis
    change PolicySound G abstractionAllowed
    exact (abstractionPolicySound_iff_no_abstractionPolicyObstruction
      (G := G) abstractionAllowed).mpr
        ((abstractionViolationCountOfFinite_eq_zero_iff_no_abstractionPolicyObstruction
          U abstractionAllowed).mp hZero)
  · intro hSound
    have hZero :
        abstractionViolationCountOfFinite G U.components abstractionAllowed = 0 :=
      (abstractionViolationCountOfFinite_eq_zero_iff_no_abstractionPolicyObstruction
        U abstractionAllowed).mpr
        ((abstractionPolicySound_iff_no_abstractionPolicyObstruction
          (G := G) abstractionAllowed).mp hSound)
    unfold ArchitectureSignatureV1.axisAvailableAndZero
    simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
      v1CoreOfFinite, v0OfFinite, AvailableAndZero, hZero]

private theorem availableAndZero_boundary_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .boundaryViolationCount ↔
        ¬ ∃ pair : C × C, PolicyViolation X.G X.boundaryAllowed pair := by
  simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
    v1CoreOfFinite, v0OfFinite, boundaryViolationCountOfFinite,
    AxisAvailableAndZero, ArchitectureLawModel.signatureOf, AvailableAndZero,
    policyViolationCount_eq_zero_iff_no_obstruction X.U X.boundaryAllowed]

private theorem availableAndZero_abstraction_iff_no_obstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    AxisAvailableAndZero
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      .abstractionViolationCount ↔
        ¬ ∃ pair : C × C, PolicyViolation X.G X.abstractionAllowed pair := by
  simp [ArchitectureSignatureV1.axisValue, v1OfFiniteWithRequiredLawAxes,
    v1CoreOfFinite, v0OfFinite, abstractionViolationCountOfFinite,
    AxisAvailableAndZero, ArchitectureLawModel.signatureOf, AvailableAndZero,
    policyViolationCount_eq_zero_iff_no_obstruction X.U X.abstractionAllowed]

private theorem no_hasCycle_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    ¬ HasClosedWalk X.G ↔
      ∀ w, architectureWitnessForAxis .hasCycle w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoClosed w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    exact hNoClosed
  · intro hNoBad hClosed
    exact hNoBad .hasCycle trivial hClosed

private theorem no_projection_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ edge : C × C, ProjectionObstruction X.G X.π X.GA edge) ↔
      ∀ w, architectureWitnessForAxis .projectionSoundnessViolation w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .projectionSoundness trivial hExists

private theorem no_lsp_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ pair : C × C, LSPObstruction X.π X.O pair) ↔
      ∀ w, architectureWitnessForAxis .lspViolationCount w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .lsp trivial hExists

private theorem no_boundary_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ pair : C × C, PolicyViolation X.G X.boundaryAllowed pair) ↔
      ∀ w, architectureWitnessForAxis .boundaryViolationCount w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .boundaryPolicy trivial hExists

private theorem no_abstraction_axis_witness_iff
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) :
    (¬ ∃ pair : C × C, PolicyViolation X.G X.abstractionAllowed pair) ↔
      ∀ w, architectureWitnessForAxis .abstractionViolationCount w ->
        ¬ ArchitectureRequiredLawBad X w := by
  constructor
  · intro hNoExists w hWitness
    cases w <;> simp [architectureWitnessForAxis] at hWitness
    intro hBad
    exact hNoExists hBad
  · intro hNoBad hExists
    exact hNoBad .abstractionPolicy trivial hExists

theorem architecture_requiredAxisFamilyExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    RequiredAxisFamilyExact X (architectureLawFamily C A Obs)
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X))
      architectureWitnessForAxis := by
  intro axis hRequiredAxis
  change IsSelectedRequiredLawAxis axis at hRequiredAxis
  unfold IsSelectedRequiredLawAxis at hRequiredAxis
  rw [mem_selectedRequiredLawAxes_iff] at hRequiredAxis
  rcases hRequiredAxis with hAxis | hAxis | hAxis | hAxis | hAxis
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_hasCycle_iff_no_closed_walk X)
      (no_hasCycle_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_projection_iff_no_obstruction X)
      (no_projection_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_lsp_iff_no_obstruction X)
      (no_lsp_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_boundary_iff_no_obstruction X)
      (no_boundary_axis_witness_iff X)
  · subst axis
    unfold AxisExact architectureLawFamily
    exact Iff.trans (availableAndZero_abstraction_iff_no_obstruction X)
      (no_abstraction_axis_witness_iff X)

theorem architecture_requiredAxisExact
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    RequiredAxisExact X (architectureLawFamily C A Obs)
      (ArchitectureSignatureV1.axisValue (ArchitectureLawModel.signatureOf X)) := by
  exact requiredAxisExact_of_axisExactFamily
    (architecture_requiredAxisFamilyExact X)
    architecture_axisCoversOnlyRequired
    architecture_requiredWitnessCoveredByAxis

/--
Final Signature-integrated zero-curvature theorem for the selected required
Signature v1 axes.
-/
theorem architectureLawful_iff_requiredSignatureAxesAvailableAndZero
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    ArchitectureLawful X ↔
      RequiredSignatureAxesAvailableAndZero (ArchitectureLawModel.signatureOf X) := by
  exact lawful_iff_requiredAxesAvailableAndZero_of_completeCoverage_and_requiredAxisExact
    (architectureLawFamily_completeCoverage (C := C) (A := A) (Obs := Obs))
    (architecture_requiredAxisExact X)

/--
Final zero-curvature theorem using the short `RequiredSignatureAxesZero` name.
-/
theorem architectureLawful_iff_requiredSignatureAxesZero
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed] :
    ArchitectureLawful X ↔
      RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X) := by
  exact architectureLawful_iff_requiredSignatureAxesAvailableAndZero X

/--
Matrix diagnostics that follow from the selected required static laws.

This package is deliberately a derived corollary, not part of
`RequiredSignatureAxesZero`: `nilpotencyIndexOfFinite` returns an index value,
and `spectralRadiusOfAdjacency` is a structural matrix diagnostic.
-/
noncomputable def MatrixDiagnosticCorollaries
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableRel X.G.edge] : Prop :=
  AdjacencyNilpotent X.U ∧
  (∃ k, nilpotencyIndexOfFinite X.U = some k) ∧
  spectralRadiusOfAdjacency X.U = 0

/--
Selected required architecture lawfulness implies the matrix diagnostic
corollaries: adjacency nilpotence, a populated executable nilpotency index, and
zero structural spectral radius.
-/
theorem matrixDiagnosticCorollaries_of_architectureLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableRel X.G.edge]
    (hLawful : ArchitectureLawful X) :
    MatrixDiagnosticCorollaries X := by
  have hAcyclic : Acyclic X.G := acyclic_of_walkAcyclic hLawful.1
  exact ⟨adjacencyNilpotent_of_acyclic X.U hAcyclic,
    nilpotencyIndexOfFinite_isSome_of_acyclic X.U hAcyclic,
    spectralRadiusOfAdjacency_eq_zero_of_acyclic X.U hAcyclic⟩

/--
Zero selected required Signature axes imply the matrix diagnostic corollaries.

This is the theorem-package bridge for #224: nilpotency and spectral facts are
read as diagnostics derived from zero curvature, not as additional required
zero axes.
-/
theorem matrixDiagnosticCorollaries_of_requiredSignatureAxesZero
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (hZero : RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)) :
    MatrixDiagnosticCorollaries X := by
  exact matrixDiagnosticCorollaries_of_architectureLawful X
    ((architectureLawful_iff_requiredSignatureAxesZero X).mpr hZero)

/--
A local replacement contract is a derived corollary for the selected
projection and LSP Signature axes.
-/
theorem localReplacementContract_requiredSignatureProjectionLSPAxes
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (hLocal : LocalReplacementContract X.G X.π X.GA X.O) :
    ArchitectureSignatureV1.axisAvailableAndZero
        (ArchitectureLawModel.signatureOf X)
        .projectionSoundnessViolation ∧
      ArchitectureSignatureV1.axisAvailableAndZero
        (ArchitectureLawModel.signatureOf X)
        .lspViolationCount := by
  have hNoObstruction :
      NoProjectionObstruction X.G X.π X.GA ∧ NoLSPObstruction X.π X.O :=
    noProjectionObstruction_and_noLSPObstruction_of_localReplacementContract
      hLocal
  constructor
  · exact (projectionSoundnessViolation_axisExact X.G X.π X.GA X.O X.U
      X.boundaryAllowed X.abstractionAllowed).mpr hNoObstruction.1
  · exact (lspViolationCount_axisExact X.G X.π X.GA X.O X.U
      X.boundaryAllowed X.abstractionAllowed X.lspPairClosed).mpr
      hNoObstruction.2

/--
Local replacement supplies the projection and LSP parts of `ArchitectureLawful`;
the remaining static laws are the closed-walk and policy conditions.
-/
theorem architectureLawful_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs}
    (hWalk : WalkAcyclic X.G)
    (hLocal : LocalReplacementContract X.G X.π X.GA X.O)
    (hBoundary : BoundaryPolicySound X.G X.boundaryAllowed)
    (hAbstraction : AbstractionPolicySound X.G X.abstractionAllowed) :
    ArchitectureLawful X := by
  exact ⟨hWalk, projectionSound_of_localReplacementContract hLocal,
    lspCompatible_of_observationFactorsThrough
      (observationFactorsThrough_of_localReplacementContract hLocal),
    hBoundary, hAbstraction⟩

/--
Derived zero-curvature bridge: a local replacement contract, closed-walk
acyclicity, and the two policy laws imply that all selected required Signature
axes are zero.
-/
theorem requiredSignatureAxesZero_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (hWalk : WalkAcyclic X.G)
    (hLocal : LocalReplacementContract X.G X.π X.GA X.O)
    (hBoundary : BoundaryPolicySound X.G X.boundaryAllowed)
    (hAbstraction : AbstractionPolicySound X.G X.abstractionAllowed) :
    RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X) := by
  exact (architectureLawful_iff_requiredSignatureAxesZero X).mp
    (architectureLawful_of_localReplacementContract hWalk hLocal hBoundary
      hAbstraction)

end ArchitectureSignature

end Formal.Arch
