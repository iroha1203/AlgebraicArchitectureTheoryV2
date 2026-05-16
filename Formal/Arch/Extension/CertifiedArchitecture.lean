import Formal.Arch.Extension.Flatness
import Formal.Arch.Operation.Operation

namespace Formal.Arch

universe u v w q r s t

/--
Runtime dependency role used by `ArchitectureCore`.

The role is metadata for a selected runtime edge universe. It does not assert
that runtime telemetry is complete or that forbidden edges have been globally
excluded.
-/
inductive RuntimeDependencyRole where
  | rawDependency
  | protectedDependency
  | forbiddenDependency
  | unprotectedDependency
  deriving DecidableEq, Repr

/--
The minimal proof-carrying architecture object used by the AAT type-system
roadmap.

`flatness` reuses the existing static / runtime / semantic model. The supplied
`staticUniverse` is the proof-carrying finite measurement universe for static
components. Decidability fields record the bounded computation assumptions
needed by downstream theorem packages; they are intentionally explicit fields
instead of global extractor-completeness claims.
-/
structure ArchitectureCore (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q)
    (SemanticObs : Type r) where
  flatness : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs
  staticUniverse : ComponentUniverse flatness.static
  componentDecidableEq : DecidableEq C
  staticEdgeDecidable : DecidableRel flatness.static.edge
  runtimeEdgeDecidable : DecidableRel flatness.runtime.edge
  boundaryPolicyDecidable : DecidableRel flatness.boundaryAllowed
  abstractionPolicyDecidable : DecidableRel flatness.abstractionAllowed
  runtimeRole : C -> C -> RuntimeDependencyRole
  semanticRequiredDecidable :
    ∀ d : RequiredDiagram SemanticExpr, Decidable (flatness.requiredSemantic d)

namespace ArchitectureCore

variable {C : Type u} {A : Type v} {StaticObs : Type w}
  {SemanticExpr : Type q} {SemanticObs : Type r}

/--
The bounded selected presentation carried by an `ArchitectureCore`.

This presentation is over the core's own component carrier.  Ambient repository
extraction remains a separate premise.
-/
def selectedPresentation
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    SelectedPresentation C C :=
  X.flatness.selectedPresentation

/--
Judgement bridge for claims read at the core's selected presentation.

This is the `ArchitectureCore`-level spelling of the Foundations judgement
form: a claim is licensed exactly at the selected presentation where it is
evaluated.
-/
theorem selectedPresentationJudgement_iff
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs)
    (claim : PresentationClaim C C) :
    AATJudgement X.selectedPresentation claim ↔ claim X.selectedPresentation :=
  aatJudgement_iff X.selectedPresentation claim

/-- Forget the proof-carrying wrapper and recover the flatness model. -/
def toFlatnessModel
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs :=
  X.flatness

/-- The static law model selected by the core's finite component universe. -/
def staticLawModel
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    ArchitectureSignature.ArchitectureLawModel C A StaticObs :=
  ArchitectureFlatnessModel.staticLawModel X.flatness X.staticUniverse

/-- The core's measured semantic diagram universe. -/
def measuredSemanticUniverse
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    List (RequiredDiagram SemanticExpr) :=
  X.flatness.measuredSemantic

/-- The runtime dependency role selected for a component pair. -/
def runtimeDependencyRole
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) (c d : C) :
    RuntimeDependencyRole :=
  X.runtimeRole c d

/-- Static evidence restricts to itself through the core's selected presentation. -/
theorem staticRestriction_eq_staticEdge
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    EdgeRestriction X.selectedPresentation X.flatness.static.edge =
      X.flatness.static.edge :=
  ArchitectureFlatnessModel.staticRestriction_eq_staticEdge X.flatness

/-- Runtime evidence restricts to itself through the core's selected presentation. -/
theorem runtimeRestriction_eq_runtimeEdge
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    EdgeRestriction X.selectedPresentation X.flatness.runtime.edge =
      X.flatness.runtime.edge :=
  ArchitectureFlatnessModel.runtimeRestriction_eq_runtimeEdge X.flatness

/-- Static graph evidence restricts to itself through the core's presentation. -/
theorem staticGraphRestriction_eq_staticGraph
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    GraphRestriction X.selectedPresentation X.flatness.static = X.flatness.static :=
  graphRestriction_identity X.flatness.static

/-- Runtime graph evidence restricts to itself through the core's presentation. -/
theorem runtimeGraphRestriction_eq_runtimeGraph
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    GraphRestriction X.selectedPresentation X.flatness.runtime = X.flatness.runtime :=
  graphRestriction_identity X.flatness.runtime

/--
The core is complete for its own selected static relation.  This does not lift
to complete extraction from an ambient repository.
-/
theorem staticCompleteForSelectedPresentation
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    CompleteForRelation X.selectedPresentation X.flatness.static.edge :=
  ArchitectureFlatnessModel.staticCompleteForSelectedPresentation X.flatness

/--
The core is complete for its own selected runtime relation.  This does not
assert runtime telemetry completeness for an ambient system.
-/
theorem runtimeCompleteForSelectedPresentation
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    CompleteForRelation X.selectedPresentation X.flatness.runtime.edge :=
  ArchitectureFlatnessModel.runtimeCompleteForSelectedPresentation X.flatness

/--
The core is complete for its own selected static graph.  This is the graph-level
form of `staticCompleteForSelectedPresentation`.
-/
theorem staticCompleteGraphForSelectedPresentation
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    CompleteForGraph X.selectedPresentation X.flatness.static :=
  completeForGraph_of_completeForRelation
    (staticCompleteForSelectedPresentation X)

/--
The core is complete for its own selected runtime graph.  This is the graph-level
form of `runtimeCompleteForSelectedPresentation`.
-/
theorem runtimeCompleteGraphForSelectedPresentation
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    CompleteForGraph X.selectedPresentation X.flatness.runtime :=
  completeForGraph_of_completeForRelation
    (runtimeCompleteForSelectedPresentation X)

/-- Every component is covered by the proof-carrying static universe. -/
theorem component_mem_staticUniverse
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) (c : C) :
    c ∈ X.staticUniverse.components :=
  X.staticUniverse.covers c

/-- Static dependency evidence is covered by the core's `ComponentUniverse`. -/
theorem staticCoverageComplete
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    StaticCoverageComplete X.flatness X.staticUniverse :=
  staticCoverageComplete_of_componentUniverse X.flatness X.staticUniverse

/--
Foundations-facing claim boundary supplied by an `ArchitectureCore`.

Every field is relative to `X.selectedPresentation`.  The package bundles the
selected judgement bridge, selected static / runtime restriction facts,
selected graph / relation completeness, and finite static universe coverage.
It does not state ambient repository completeness, runtime telemetry
completeness, or global semantic universe completeness.
-/
structure SelectedClaimBoundary
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) : Prop where
  judgementBridge :
    ∀ claim : PresentationClaim C C,
      AATJudgement X.selectedPresentation claim ↔ claim X.selectedPresentation
  staticRestriction :
    EdgeRestriction X.selectedPresentation X.flatness.static.edge =
      X.flatness.static.edge
  runtimeRestriction :
    EdgeRestriction X.selectedPresentation X.flatness.runtime.edge =
      X.flatness.runtime.edge
  staticGraphRestriction :
    GraphRestriction X.selectedPresentation X.flatness.static = X.flatness.static
  runtimeGraphRestriction :
    GraphRestriction X.selectedPresentation X.flatness.runtime = X.flatness.runtime
  staticComplete :
    CompleteForRelation X.selectedPresentation X.flatness.static.edge
  runtimeComplete :
    CompleteForRelation X.selectedPresentation X.flatness.runtime.edge
  staticGraphComplete :
    CompleteForGraph X.selectedPresentation X.flatness.static
  runtimeGraphComplete :
    CompleteForGraph X.selectedPresentation X.flatness.runtime
  staticCoverage :
    StaticCoverageComplete X.flatness X.staticUniverse

/--
The core exposes its selected-presentation claim boundary as a single theorem
package.
-/
theorem selectedClaimBoundary
    (X : ArchitectureCore C A StaticObs SemanticExpr SemanticObs) :
    SelectedClaimBoundary X where
  judgementBridge := selectedPresentationJudgement_iff X
  staticRestriction := staticRestriction_eq_staticEdge X
  runtimeRestriction := runtimeRestriction_eq_runtimeEdge X
  staticGraphRestriction := staticGraphRestriction_eq_staticGraph X
  runtimeGraphRestriction := runtimeGraphRestriction_eq_runtimeGraph X
  staticComplete := staticCompleteForSelectedPresentation X
  runtimeComplete := runtimeCompleteForSelectedPresentation X
  staticGraphComplete := staticCompleteGraphForSelectedPresentation X
  runtimeGraphComplete := runtimeCompleteGraphForSelectedPresentation X
  staticCoverage := staticCoverageComplete X

end ArchitectureCore

/-- Law role tags for certified architecture law universes. -/
inductive ArchitectureLawRole where
  | required
  | optional
  | derived
  deriving DecidableEq, Repr

/-- A finite law universe with required / optional / derived role metadata. -/
structure ArchitectureLawUniverse (Law : Type s) where
  laws : List Law
  role : Law -> ArchitectureLawRole

namespace ArchitectureLawUniverse

variable {Law : Type s}

/-- Laws selected as required in this bounded law universe. -/
def Required (U : ArchitectureLawUniverse Law) (law : Law) : Prop :=
  law ∈ U.laws ∧ U.role law = ArchitectureLawRole.required

/-- Laws selected as optional in this bounded law universe. -/
def Optional (U : ArchitectureLawUniverse Law) (law : Law) : Prop :=
  law ∈ U.laws ∧ U.role law = ArchitectureLawRole.optional

/-- Laws selected as derived in this bounded law universe. -/
def Derived (U : ArchitectureLawUniverse Law) (law : Law) : Prop :=
  law ∈ U.laws ∧ U.role law = ArchitectureLawRole.derived

end ArchitectureLawUniverse

/--
Finite obstruction-witness universe.

This is a bounded theorem-package input, not a claim that every possible
architecture obstruction has been enumerated.
-/
structure ObstructionWitnessUniverse (Witness : Type t) where
  witnesses : List Witness

/--
Named theorem package with an explicit proof obligation.

The package must also record its non-conclusions, preserving the project rule
that theorem packages expose what they do not prove.
-/
structure ArchitectureTheoremPackage (State : Type s) (Witness : Type t) where
  name : String
  obligation : ProofObligation State Witness
  recordsNonConclusions : obligation.RecordsNonConclusions

/--
Claim levels used by proof-carrying architecture reports.

Only `formal` is intended to be backed by Lean theorem-package discharge.
Tooling output, empirical evidence, and research hypotheses remain separate
claim levels.
-/
inductive ClaimLevel where
  | formal
  | tooling
  | empirical
  | hypothesis
  deriving DecidableEq, Repr

namespace ClaimLevel

/-- The claim is a formal Lean theorem-package claim. -/
def IsFormal (level : ClaimLevel) : Prop :=
  level = ClaimLevel.formal

/-- The claim is supported by tooling-side evidence. -/
def IsTooling (level : ClaimLevel) : Prop :=
  level = ClaimLevel.tooling

/-- The claim is supported by empirical validation. -/
def IsEmpirical (level : ClaimLevel) : Prop :=
  level = ClaimLevel.empirical

/-- The claim is a research hypothesis rather than a theorem. -/
def IsHypothesis (level : ClaimLevel) : Prop :=
  level = ClaimLevel.hypothesis

end ClaimLevel

/--
Measurement boundary for report claims.

`unmeasured` is intentionally distinct from `measuredZero`; the latter is the
only zero-like measurement status.
-/
inductive MeasurementBoundary where
  | measuredZero
  | measuredNonzero
  | unmeasured
  | outOfScope
  deriving DecidableEq, Repr

namespace MeasurementBoundary

/-- The measured value is explicitly zero. -/
def IsMeasuredZero (boundary : MeasurementBoundary) : Prop :=
  boundary = MeasurementBoundary.measuredZero

/-- The axis or claim has not been measured. -/
def IsUnmeasured (boundary : MeasurementBoundary) : Prop :=
  boundary = MeasurementBoundary.unmeasured

/-- Unmeasured evidence is not the same as measured zero. -/
theorem unmeasured_not_measuredZero :
    ¬ IsMeasuredZero MeasurementBoundary.unmeasured := by
  intro h
  cases h

end MeasurementBoundary

/--
Architecture claim schema used to keep Lean theorem claims, tooling output,
empirical evidence, and hypotheses separated.

A formal claim may reference a theorem package; tooling and empirical fields
are evidence boundaries, not automatic Lean proofs.  The `nonConclusions`
field records what the claim explicitly does not establish.
-/
structure ArchitectureClaim (State : Type s) (Witness : Type t) where
  level : ClaimLevel
  statement : Prop
  theoremPackage : Option (ArchitectureTheoremPackage State Witness)
  toolingEvidence : Prop
  empiricalEvidence : Prop
  hypothesisContext : Prop
  measurementBoundary : MeasurementBoundary
  nonConclusions : Prop

namespace ArchitectureClaim

variable {State : Type s} {Witness : Type t}

/-- The claim explicitly records what it does not establish. -/
def RecordsNonConclusions (claim : ArchitectureClaim State Witness) : Prop :=
  claim.nonConclusions

/-- The claim is classified as formal. -/
def IsFormal (claim : ArchitectureClaim State Witness) : Prop :=
  claim.level = ClaimLevel.formal

/-- The claim carries a referenced theorem package. -/
def HasFormalPackage (claim : ArchitectureClaim State Witness) : Prop :=
  ∃ package, claim.theoremPackage = some package

/-- The claim is tooling-only and carries no formal theorem package. -/
def ToolingOnly (claim : ArchitectureClaim State Witness) : Prop :=
  claim.level = ClaimLevel.tooling ∧ claim.theoremPackage = none

/-- The claim's measurement boundary is explicitly measured zero. -/
def IsMeasuredZero (claim : ArchitectureClaim State Witness) : Prop :=
  MeasurementBoundary.IsMeasuredZero claim.measurementBoundary

/-- The claim's measurement boundary is unmeasured. -/
def IsUnmeasured (claim : ArchitectureClaim State Witness) : Prop :=
  MeasurementBoundary.IsUnmeasured claim.measurementBoundary

/-- The recorded non-conclusion predicate is exactly the schema field. -/
theorem records_nonConclusions_iff (claim : ArchitectureClaim State Witness) :
    claim.RecordsNonConclusions ↔ claim.nonConclusions := by
  rfl

/-- Tooling-only claims do not carry a formal theorem package. -/
theorem toolingOnly_no_formalPackage
    (claim : ArchitectureClaim State Witness)
    (hTooling : claim.ToolingOnly) :
    ¬ claim.HasFormalPackage := by
  intro hPackage
  rcases hPackage with ⟨package, hPackage⟩
  rw [hTooling.2] at hPackage
  cases hPackage

/-- An unmeasured claim boundary cannot be used as measured-zero evidence. -/
theorem unmeasured_not_measuredZero
    (claim : ArchitectureClaim State Witness)
    (hUnmeasured : claim.IsUnmeasured) :
    ¬ claim.IsMeasuredZero := by
  intro hZero
  unfold IsUnmeasured MeasurementBoundary.IsUnmeasured at hUnmeasured
  unfold IsMeasuredZero MeasurementBoundary.IsMeasuredZero at hZero
  rw [hUnmeasured] at hZero
  exact MeasurementBoundary.unmeasured_not_measuredZero hZero

end ArchitectureClaim

/--
Certified architecture object carrying law, invariant, witness, theorem-package,
and proof-obligation discharge data for one `ArchitectureCore`.

The proof field is bounded to the listed theorem packages. It does not assert
global completeness of the measured component universe, runtime telemetry, or
semantic diagram universe.
-/
structure CertifiedArchitecture (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q) (SemanticObs : Type r)
    (Law : Type s) (Witness : Type t) where
  core : ArchitectureCore C A StaticObs SemanticExpr SemanticObs
  laws : ArchitectureLawUniverse Law
  invariants : List (ArchitectureCore C A StaticObs SemanticExpr SemanticObs -> Prop)
  witnessUniverse : ObstructionWitnessUniverse Witness
  theoremPackages :
    List (ArchitectureTheoremPackage
      (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness)
  proofs :
    ∀ {package}, package ∈ theoremPackages ->
      package.obligation.Discharged

namespace CertifiedArchitecture

variable {C : Type u} {A : Type v} {StaticObs : Type w}
  {SemanticExpr : Type q} {SemanticObs : Type r}
  {Law : Type s} {Witness : Type t}

/-- The proof-obligation list induced by the certified theorem packages. -/
def theoremPackageObligations
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness) :
    List (ProofObligation
      (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness) :=
  X.theoremPackages.map (fun package => package.obligation)

/-- All listed theorem packages have discharged proof obligations. -/
def ProofObligationDischargeSet
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness) :
    Prop :=
  ∀ {package}, package ∈ X.theoremPackages ->
    package.obligation.Discharged

/-- Accessor for the discharge proof carried by a certified architecture. -/
theorem theoremPackage_discharged
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness)
    {package :
      ArchitectureTheoremPackage
        (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness}
    (hMem : package ∈ X.theoremPackages) :
    package.obligation.Discharged :=
  X.proofs hMem

/-- The carried theorem packages form a proof-obligation discharge set. -/
theorem proofObligationDischargeSet
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness) :
    X.ProofObligationDischargeSet := by
  intro package hMem
  exact X.theoremPackage_discharged hMem

/-- Accessor for the non-conclusion clause recorded by a theorem package. -/
theorem theoremPackage_recordsNonConclusions
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness)
    {package :
      ArchitectureTheoremPackage
        (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness}
    (_hMem : package ∈ X.theoremPackages) :
    package.obligation.RecordsNonConclusions :=
  package.recordsNonConclusions

/-- A listed theorem package contributes its obligation to the obligation list. -/
theorem theoremPackage_obligation_mem
    (X : CertifiedArchitecture C A StaticObs SemanticExpr SemanticObs Law Witness)
    {package :
      ArchitectureTheoremPackage
        (ArchitectureCore C A StaticObs SemanticExpr SemanticObs) Witness}
    (hMem : package ∈ X.theoremPackages) :
    package.obligation ∈ X.theoremPackageObligations :=
  List.mem_map.mpr ⟨package, hMem, rfl⟩

end CertifiedArchitecture

end Formal.Arch
