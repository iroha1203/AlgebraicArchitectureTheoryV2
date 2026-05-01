import Formal.Arch.OperationKernel
import Formal.Arch.LocalReplacement
import Formal.Arch.Flatness
import Formal.Arch.Reachability
import Formal.Arch.Repair
import Formal.Arch.RepairSynthesis

namespace Formal.Arch

universe u v r c q

/--
Bounded Architecture Calculus law tags.

These are law-package names, not unconditional algebraic laws over every
operation in every universe.
-/
inductive ArchitectureCalculusLawKind where
  | identity
  | associativity
  | edgeUnion
  | refinementAbstraction
  | edgeEquivalence
  | externalContractPreservation
  | explicitContractSoundness
  | protectionIdempotence
  | runtimeLocalization
  | reverseInvolution
  | witnessMappingFunctoriality
  | synthesisSoundness
  | noSolutionSoundness
  deriving DecidableEq, Repr

namespace ArchitectureCalculusLawKind

/-- Human-readable law tag used by documentation-facing theorem packages. -/
def label : ArchitectureCalculusLawKind -> String
  | identity => "identity"
  | associativity => "associativity"
  | edgeUnion => "edgeUnion"
  | refinementAbstraction => "refinementAbstraction"
  | edgeEquivalence => "edgeEquivalence"
  | externalContractPreservation => "externalContractPreservation"
  | explicitContractSoundness => "explicitContractSoundness"
  | protectionIdempotence => "protectionIdempotence"
  | runtimeLocalization => "runtimeLocalization"
  | reverseInvolution => "reverseInvolution"
  | witnessMappingFunctoriality => "witnessMappingFunctoriality"
  | synthesisSoundness => "synthesisSoundness"
  | noSolutionSoundness => "noSolutionSoundness"

end ArchitectureCalculusLawKind

/--
Minimal bounded theorem package for an Architecture Calculus law.

The package keeps compatibility, coverage, exactness, and observation
equivalence visible.  The conclusion is available only from those selected
assumptions, so this does not state global associativity, global flatness
preservation, or idempotence for every operation.
-/
structure ArchitectureCalculusLaw (State : Type u) (Witness : Type v) where
  law : ArchitectureCalculusLawKind
  operationKind : ArchitectureOperationKind
  boundedUniverse : Prop
  compatibilityAssumptions : Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  observationEquivalence : Prop
  conclusion : Prop
  sound :
    boundedUniverse ->
    compatibilityAssumptions ->
    coverageAssumptions ->
    exactnessAssumptions ->
    observationEquivalence ->
    conclusion
  nonConclusions : Prop

namespace ArchitectureCalculusLaw

variable {State : Type u} {Witness : Type v}

/-- Visible assumptions required before the law conclusion can be used. -/
def AssumptionsHold (L : ArchitectureCalculusLaw State Witness) : Prop :=
  L.boundedUniverse ∧
  L.compatibilityAssumptions ∧
  L.coverageAssumptions ∧
  L.exactnessAssumptions ∧
  L.observationEquivalence

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions (L : ArchitectureCalculusLaw State Witness) : Prop :=
  L.nonConclusions

/-- A bounded Architecture Calculus law yields its conclusion from its assumptions. -/
theorem conclusion_of_assumptions
    (L : ArchitectureCalculusLaw State Witness)
    (h : L.AssumptionsHold) :
    L.conclusion := by
  exact L.sound h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- Constructor for a bounded identity law package for a selected operation kind. -/
def identityLaw
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.identity
  operationKind := operationKind
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `compose` associativity law package. -/
def composeAssociativity
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.associativity
  operationKind := ArchitectureOperationKind.compose
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded concrete `compose` edge-union law package. -/
def composeEdgeUnion
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.edgeUnion
  operationKind := ArchitectureOperationKind.compose
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `replace` refinement/abstraction law package. -/
def replaceRefinementAbstraction
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.refinementAbstraction
  operationKind := ArchitectureOperationKind.replace
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/--
Constructor for a bounded `refine` observation-equivalence law package.

This is separate from `replaceRefinementAbstraction`: the package records a
refinement-side contract and observation bridge for the `refine` operation tag.
-/
def refineObservationEquivalence
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.refinementAbstraction
  operationKind := ArchitectureOperationKind.refine
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/--
Constructor for a bounded `abstract` observation-equivalence law package.

This records the abstraction-side projection exactness and selected external
observation equivalence without claiming strict equality or global completeness.
-/
def abstractObservationEquivalence
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.refinementAbstraction
  operationKind := ArchitectureOperationKind.abstract
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded concrete `replace` edge-equivalence law package. -/
def replaceEdgeEquivalence
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.edgeEquivalence
  operationKind := ArchitectureOperationKind.replace
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `merge` external-contract preservation law package. -/
def mergeExternalContractPreservation
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.externalContractPreservation
  operationKind := ArchitectureOperationKind.merge
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `contract` explicitization-soundness law package. -/
def contractExplicitizationSoundness
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.explicitContractSoundness
  operationKind := ArchitectureOperationKind.contract
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `protect` idempotence law package. -/
def protectIdempotence
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.protectionIdempotence
  operationKind := ArchitectureOperationKind.protect
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/--
Constructor for a bounded runtime-localization law package.

The operation kind is explicit so the same runtime package can be used for
`isolate` and policy-aware `protect`, while keeping the operation tag visible.
-/
def runtimeLocalization
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.runtimeLocalization
  operationKind := operationKind
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for a bounded reverse-involution law package. -/
def reverseInvolution
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.reverseInvolution
  operationKind := operationKind
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

/-- Constructor for the bounded `repair` monotonicity law package. -/
def repairMonotonicity
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    ArchitectureCalculusLaw State Witness where
  law := ArchitectureCalculusLawKind.witnessMappingFunctoriality
  operationKind := ArchitectureOperationKind.repair
  boundedUniverse := boundedUniverse
  compatibilityAssumptions := compatibilityAssumptions
  coverageAssumptions := coverageAssumptions
  exactnessAssumptions := exactnessAssumptions
  observationEquivalence := observationEquivalence
  conclusion := conclusion
  sound := sound
  nonConclusions := nonConclusions

theorem identityLaw_kind
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (identityLaw (State := State) (Witness := Witness)
      operationKind boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).law =
        ArchitectureCalculusLawKind.identity :=
  rfl

theorem composeAssociativity_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (composeAssociativity (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.compose :=
  rfl

theorem composeEdgeUnion_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (composeEdgeUnion (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.compose :=
  rfl

theorem replaceRefinementAbstraction_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (replaceRefinementAbstraction (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.replace :=
  rfl

theorem refineObservationEquivalence_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (refineObservationEquivalence (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.refine :=
  rfl

theorem abstractObservationEquivalence_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (abstractObservationEquivalence (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.abstract :=
  rfl

theorem replaceEdgeEquivalence_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (replaceEdgeEquivalence (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.replace :=
  rfl

theorem mergeExternalContractPreservation_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (mergeExternalContractPreservation (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.merge :=
  rfl

theorem contractExplicitizationSoundness_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (contractExplicitizationSoundness (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.contract :=
  rfl

theorem protectIdempotence_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (protectIdempotence (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.protect :=
  rfl

theorem runtimeLocalization_operationKind
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (runtimeLocalization (State := State) (Witness := Witness)
      operationKind boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        operationKind :=
  rfl

theorem reverseInvolution_kind
    (operationKind : ArchitectureOperationKind)
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (reverseInvolution (State := State) (Witness := Witness)
      operationKind boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).law =
        ArchitectureCalculusLawKind.reverseInvolution :=
  rfl

theorem repairMonotonicity_operationKind
    (boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions : Prop)
    (sound :
      boundedUniverse ->
      compatibilityAssumptions ->
      coverageAssumptions ->
      exactnessAssumptions ->
      observationEquivalence ->
      conclusion) :
    (repairMonotonicity (State := State) (Witness := Witness)
      boundedUniverse compatibilityAssumptions coverageAssumptions
      exactnessAssumptions observationEquivalence conclusion
      nonConclusions sound).operationKind =
        ArchitectureOperationKind.repair :=
  rfl

section ConcreteGraphEntrypoints

variable {C : Type u}

/--
Bounded law package connecting concrete finite `compose` to edge union.

This records only the selected graph-kernel statement; it is not an
unconditional associativity or flatness-preservation theorem.
-/
def finiteComposeEdgeUnionLaw
    (FG FH : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  composeEdgeUnion
    True True True True True
    (∀ c d : C,
      (FG.compose FH).graph.edge c d ↔
        FG.graph.edge c d ∨ FH.graph.edge c d)
    True
    (by
      intro _ _ _ _ _ c d
      exact FiniteArchGraph.compose_edge_iff FG FH)

/-- The finite compose edge-union entrypoint keeps the `compose` operation tag. -/
theorem finiteComposeEdgeUnionLaw_operationKind
    (FG FH : FiniteArchGraph C) :
    (finiteComposeEdgeUnionLaw FG FH).operationKind =
      ArchitectureOperationKind.compose :=
  rfl

/-- The finite compose edge-union entrypoint yields the concrete edge-union theorem. -/
theorem finiteComposeEdgeUnionLaw_conclusion
    (FG FH : FiniteArchGraph C)
    (h : (finiteComposeEdgeUnionLaw FG FH).AssumptionsHold) :
    ∀ c d : C,
      (FG.compose FH).graph.edge c d ↔
        FG.graph.edge c d ∨ FH.graph.edge c d :=
  conclusion_of_assumptions (finiteComposeEdgeUnionLaw FG FH) h

/--
Selected compatibility assumptions for interface-mediated finite composition.

These assumptions say the three input graphs project soundly to the declared
interface graph, and that the interface graph itself stays inside the declared
interface boundary.  They are premises for the bounded law package, not facts
derived from the `compose` tag.
-/
structure InterfaceMediatedComposeCompatibility
    {A : Type v}
    (FG FH FK : FiniteArchGraph C) (π : InterfaceProjection C A)
    (GI : AbstractGraph A) (declaredInterface : A -> Prop) : Prop where
  leftProjectionSound : ProjectionSound FG.graph π GI
  middleProjectionSound : ProjectionSound FH.graph π GI
  rightProjectionSound : ProjectionSound FK.graph π GI
  interfaceEdgeClosed :
    ∀ {a b : A}, GI.edge a b -> declaredInterface a ∧ declaredInterface b

/--
Coverage assumption for interface-mediated composition.

The selected projection exposes every component through the declared interface
boundary.  This is intentionally stronger than finite-list coverage and keeps
the interface boundary explicit.
-/
def InterfaceMediatedComposeCoverage
    {A : Type v} (π : InterfaceProjection C A)
    (declaredInterface : A -> Prop) : Prop :=
  ∀ c : C, declaredInterface (π.expose c)

/--
Selected exactness assumptions for the two associated finite compositions.

Exactness is required only for the chosen interface graph and selected
association pair.  This does not assert global projection completeness for all
future compositions.
-/
structure InterfaceMediatedComposeExact
    {A : Type v}
    (FG FH FK : FiniteArchGraph C) (π : InterfaceProjection C A)
    (GI : AbstractGraph A) : Prop where
  leftAssociatedExact :
    ProjectionExact ((FG.compose FH).compose FK).graph π GI
  rightAssociatedExact :
    ProjectionExact (FG.compose (FH.compose FK)).graph π GI

/--
External observation equivalence selected for an interface-mediated compose
associativity package.
-/
def InterfaceMediatedComposeObserved
    {Obs : Type r} (O : Observation (FiniteArchGraph C) Obs)
    (FG FH FK : FiniteArchGraph C) : Prop :=
  ObservationallyEquivalent O ((FG.compose FH).compose FK)
    (FG.compose (FH.compose FK))

/--
Bounded theorem package for declared-interface-mediated `compose`
associativity.

The conclusion combines the finite graph-kernel edge equivalence with the
selected external observation equivalence assumption.  Runtime / semantic
completeness, global flatness preservation, and unconditional associativity for
all operation tags remain non-conclusions.
-/
def interfaceMediatedComposeAssociativityLaw
    {A : Type v} {Obs : Type r}
    (FG FH FK : FiniteArchGraph C) (π : InterfaceProjection C A)
    (GI : AbstractGraph A) (declaredInterface : A -> Prop)
    (O : Observation (FiniteArchGraph C) Obs) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  composeAssociativity
    True
    (InterfaceMediatedComposeCompatibility FG FH FK π GI declaredInterface)
    (InterfaceMediatedComposeCoverage π declaredInterface)
    (InterfaceMediatedComposeExact FG FH FK π GI)
    (InterfaceMediatedComposeObserved O FG FH FK)
    (EdgeEquivalent ((FG.compose FH).compose FK).graph
        (FG.compose (FH.compose FK)).graph ∧
      InterfaceMediatedComposeObserved O FG FH FK)
    True
    (by
      intro _ _ _ _ hObserved
      exact ⟨FiniteArchGraph.compose_assoc_edgeEquivalent FG FH FK, hObserved⟩)

/-- The interface-mediated compose associativity package keeps the `compose` tag. -/
theorem interfaceMediatedComposeAssociativityLaw_operationKind
    {A : Type v} {Obs : Type r}
    (FG FH FK : FiniteArchGraph C) (π : InterfaceProjection C A)
    (GI : AbstractGraph A) (declaredInterface : A -> Prop)
    (O : Observation (FiniteArchGraph C) Obs) :
    (interfaceMediatedComposeAssociativityLaw FG FH FK π GI declaredInterface O).operationKind =
      ArchitectureOperationKind.compose :=
  rfl

/--
The interface-mediated compose associativity package exposes finite edge
associativity plus the selected external observation equivalence from its
bounded assumptions.
-/
theorem interfaceMediatedComposeAssociativityLaw_conclusion
    {A : Type v} {Obs : Type r}
    (FG FH FK : FiniteArchGraph C) (π : InterfaceProjection C A)
    (GI : AbstractGraph A) (declaredInterface : A -> Prop)
    (O : Observation (FiniteArchGraph C) Obs)
    (h : (interfaceMediatedComposeAssociativityLaw
      FG FH FK π GI declaredInterface O).AssumptionsHold) :
    EdgeEquivalent ((FG.compose FH).compose FK).graph
        (FG.compose (FH.compose FK)).graph ∧
      InterfaceMediatedComposeObserved O FG FH FK :=
  conclusion_of_assumptions
    (interfaceMediatedComposeAssociativityLaw FG FH FK π GI declaredInterface O) h

/--
Bounded law package connecting edge-equivalent finite `replace` to preservation
of the source edge relation.
-/
def finiteReplaceEdgeEquivalenceLaw
    (FG FH : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  replaceEdgeEquivalence
    True (EdgeEquivalent FG.graph FH.graph) True True True
    (∀ c d : C, (FG.replace FH).graph.edge c d ↔ FG.graph.edge c d)
    True
    (by
      intro _ hEquiv _ _ _ c d
      exact FiniteArchGraph.replace_preserves_edges_of_edgeEquivalent
        FG FH hEquiv)

/-- The finite replace edge-equivalence entrypoint keeps the `replace` operation tag. -/
theorem finiteReplaceEdgeEquivalenceLaw_operationKind
    (FG FH : FiniteArchGraph C) :
    (finiteReplaceEdgeEquivalenceLaw FG FH).operationKind =
      ArchitectureOperationKind.replace :=
  rfl

/--
The finite replace edge-equivalence entrypoint yields source-edge preservation
from its bounded assumptions.
-/
theorem finiteReplaceEdgeEquivalenceLaw_conclusion
    (FG FH : FiniteArchGraph C)
    (h : (finiteReplaceEdgeEquivalenceLaw FG FH).AssumptionsHold) :
    ∀ c d : C, (FG.replace FH).graph.edge c d ↔ FG.graph.edge c d :=
  conclusion_of_assumptions (finiteReplaceEdgeEquivalenceLaw FG FH) h

end ConcreteGraphEntrypoints

section LocalReplacementEntrypoints

variable {C : Type u} {A : Type v} {Obs : Type r}

/--
Bounded law package connecting a local replacement contract to projection and
observation preservation.

This is the contract/observation side of `replace`; it is separate from the
finite graph-kernel entrypoint based on `EdgeEquivalent`.
-/
def localReplacementPreservationLaw
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) :
    ArchitectureCalculusLaw (ArchGraph C) PUnit :=
  replaceRefinementAbstraction
    True True True
    (LocalReplacementContract G π GA O)
    True
    (ProjectionSound G π GA ∧ LSPCompatible π O)
    True
    (by
      intro _ _ _ hLocal _
      exact ⟨projectionSound_of_localReplacementContract hLocal,
        lspCompatible_of_observationFactorsThrough
          (observationFactorsThrough_of_localReplacementContract hLocal)⟩)

/-- The local replacement preservation entrypoint keeps the `replace` operation tag. -/
theorem localReplacementPreservationLaw_operationKind
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) :
    (localReplacementPreservationLaw G π GA O).operationKind =
      ArchitectureOperationKind.replace :=
  rfl

/--
The local replacement preservation entrypoint exposes projection soundness and
observation preservation from its bounded assumptions.
-/
theorem localReplacementPreservationLaw_conclusion
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    (h : (localReplacementPreservationLaw G π GA O).AssumptionsHold) :
    ProjectionSound G π GA ∧ LSPCompatible π O :=
  conclusion_of_assumptions (localReplacementPreservationLaw G π GA O) h

/--
Bounded law package connecting a local replacement contract to zero selected
projection and LSP violation counts on finite measurement universes.
-/
def localReplacementViolationZeroLaw
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableRel G.edge] [DecidableRel GA.edge] [DecidableEq A] [DecidableEq Obs]
    (components implementations : List C) :
    ArchitectureCalculusLaw (ArchGraph C) PUnit :=
  replaceRefinementAbstraction
    True True True
    (LocalReplacementContract G π GA O)
    True
    (projectionSoundnessViolation G π GA components = 0 ∧
      lspViolationCount π O implementations = 0)
    True
    (by
      intro _ _ _ hLocal _
      exact violationCounts_eq_zero_of_localReplacementContract
        components implementations hLocal)

/-- The local replacement zero-violation entrypoint keeps the `replace` operation tag. -/
theorem localReplacementViolationZeroLaw_operationKind
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableRel G.edge] [DecidableRel GA.edge] [DecidableEq A] [DecidableEq Obs]
    (components implementations : List C) :
    (localReplacementViolationZeroLaw G π GA O
      components implementations).operationKind =
      ArchitectureOperationKind.replace :=
  rfl

/--
The local replacement zero-violation entrypoint exposes finite selected
projection and LSP counts as zero from its bounded assumptions.
-/
theorem localReplacementViolationZeroLaw_conclusion
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    [DecidableRel G.edge] [DecidableRel GA.edge] [DecidableEq A] [DecidableEq Obs]
    (components implementations : List C)
    (h : (localReplacementViolationZeroLaw G π GA O
      components implementations).AssumptionsHold) :
    projectionSoundnessViolation G π GA components = 0 ∧
      lspViolationCount π O implementations = 0 :=
  conclusion_of_assumptions
    (localReplacementViolationZeroLaw G π GA O components implementations) h

end LocalReplacementEntrypoints

section RefinementAbstractionEntrypoints

variable {C : Type u} {A : Type v} {Obs : Type r} {StateObs : Type c}

/--
Selected projection contract for a refinement.

It uses the current operational DIP bridge: projection soundness plus
representative stability.  Completeness is deliberately not included here.
-/
def RefinementProjectionContract
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) :
    Prop :=
  DIPCompatible G π GA

/--
Selected observation contract for a refinement.

The component observation must factor through the selected interface
projection.  This is the assumption from which LSP-style observation
preservation is derived.
-/
def RefinementObservationContract
    (π : InterfaceProjection C A) (O : Observation C Obs) : Prop :=
  ObservationFactorsThrough π O

/--
Selected projection contract for abstraction.

Abstraction uses exact projection plus representative stability for the chosen
quotient/interface, but only as an explicit premise for this package.
-/
def AbstractionProjectionContract
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) :
    Prop :=
  StrongDIPCompatible G π GA

/--
Selected observation contract for abstraction.

As with refinement, component observations are required to factor through the
selected interface projection.
-/
def AbstractionObservationContract
    (π : InterfaceProjection C A) (O : Observation C Obs) : Prop :=
  ObservationFactorsThrough π O

/--
The external observation equivalence expected after abstracting a selected
refinement back to the original architecture.
-/
def RefinementAbstractionObserved
    (O : Observation (ArchGraph C) StateObs)
    (source abstracted : ArchGraph C) : Prop :=
  ObservationallyEquivalent O abstracted source

/-- A refinement projection contract includes projection soundness. -/
theorem projectionSound_of_refinementProjectionContract
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : RefinementProjectionContract G π GA) :
    ProjectionSound G π GA :=
  h.1

/-- A refinement observation contract yields LSP-compatible observations. -/
theorem lspCompatible_of_refinementObservationContract
    {π : InterfaceProjection C A} {O : Observation C Obs}
    (h : RefinementObservationContract π O) :
    LSPCompatible π O :=
  lspCompatible_of_observationFactorsThrough h

/-- An abstraction projection contract includes exact projection. -/
theorem projectionExact_of_abstractionProjectionContract
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : AbstractionProjectionContract G π GA) :
    ProjectionExact G π GA :=
  projectionExact_of_strongDIPCompatible h

/-- An abstraction observation contract yields LSP-compatible observations. -/
theorem lspCompatible_of_abstractionObservationContract
    {π : InterfaceProjection C A} {O : Observation C Obs}
    (h : AbstractionObservationContract π O) :
    LSPCompatible π O :=
  lspCompatible_of_observationFactorsThrough h

/--
Bounded law package for the `refine` side of a refinement/abstraction pair.

The conclusion exposes only projection soundness and selected observation
preservation from explicit refinement contracts.  It does not assert strict
equality, unique decomposition, or global projection completeness.
-/
def refinementObservationEquivalenceLaw
    (refined : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) :
    ArchitectureCalculusLaw (ArchGraph C) PUnit :=
  refineObservationEquivalence
    True
    (RefinementProjectionContract refined π GA)
    True True
    (RefinementObservationContract π O)
    (ProjectionSound refined π GA ∧ LSPCompatible π O)
    True
    (by
      intro _ hProjection _ _ hObservation
      exact ⟨projectionSound_of_refinementProjectionContract hProjection,
        lspCompatible_of_refinementObservationContract hObservation⟩)

/-- The refinement observation-equivalence package keeps the `refine` tag. -/
theorem refinementObservationEquivalenceLaw_operationKind
    (refined : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) :
    (refinementObservationEquivalenceLaw refined π GA O).operationKind =
      ArchitectureOperationKind.refine :=
  rfl

/--
The refinement observation-equivalence package exposes projection soundness and
LSP-compatible observations from its bounded assumptions.
-/
theorem refinementObservationEquivalenceLaw_conclusion
    (refined : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    (h : (refinementObservationEquivalenceLaw refined π GA O).AssumptionsHold) :
    ProjectionSound refined π GA ∧ LSPCompatible π O :=
  conclusion_of_assumptions
    (refinementObservationEquivalenceLaw refined π GA O) h

/--
Bounded law package for abstracting a selected refinement back to its external
interface.

The conclusion combines exact projection, selected LSP-compatible observation,
and the external observation equivalence assumption.  Runtime / semantic
completeness, strict equality, and global projection completeness remain
non-conclusions.
-/
def abstractionObservationEquivalenceLaw
    (source abstracted : ArchGraph C) (π : InterfaceProjection C A)
    (GA : AbstractGraph A) (componentObservation : Observation C Obs)
    (externalObservation : Observation (ArchGraph C) StateObs) :
    ArchitectureCalculusLaw (ArchGraph C) PUnit :=
  abstractObservationEquivalence
    True
    (AbstractionObservationContract π componentObservation)
    True
    (AbstractionProjectionContract abstracted π GA)
    (RefinementAbstractionObserved externalObservation source abstracted)
    (ProjectionExact abstracted π GA ∧
      LSPCompatible π componentObservation ∧
      RefinementAbstractionObserved externalObservation source abstracted)
    True
    (by
      intro _ hObservation _ hProjection hExternal
      exact ⟨projectionExact_of_abstractionProjectionContract hProjection,
        lspCompatible_of_abstractionObservationContract hObservation,
        hExternal⟩)

/-- The abstraction observation-equivalence package keeps the `abstract` tag. -/
theorem abstractionObservationEquivalenceLaw_operationKind
    (source abstracted : ArchGraph C) (π : InterfaceProjection C A)
    (GA : AbstractGraph A) (componentObservation : Observation C Obs)
    (externalObservation : Observation (ArchGraph C) StateObs) :
    (abstractionObservationEquivalenceLaw source abstracted π GA
      componentObservation externalObservation).operationKind =
      ArchitectureOperationKind.abstract :=
  rfl

/--
The abstraction observation-equivalence package exposes exact projection,
selected observation preservation, and external observation equivalence from
its bounded assumptions.
-/
theorem abstractionObservationEquivalenceLaw_conclusion
    (source abstracted : ArchGraph C) (π : InterfaceProjection C A)
    (GA : AbstractGraph A) (componentObservation : Observation C Obs)
    (externalObservation : Observation (ArchGraph C) StateObs)
    (h : (abstractionObservationEquivalenceLaw source abstracted π GA
      componentObservation externalObservation).AssumptionsHold) :
    ProjectionExact abstracted π GA ∧
      LSPCompatible π componentObservation ∧
      RefinementAbstractionObserved externalObservation source abstracted :=
  conclusion_of_assumptions
    (abstractionObservationEquivalenceLaw source abstracted π GA
      componentObservation externalObservation) h

end RefinementAbstractionEntrypoints

section MergeContractEntrypoints

variable {C : Type u} {A : Type v} {Obs : Type r}

/--
Selected contract for a merged boundary.

The merged boundary must have exact projection and representative stability for
the selected interface, and its external observation must factor through that
interface.  This is an explicit premise, not a consequence of the `merge` tag.
-/
def MergedBoundaryContract
    (merged : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) : Prop :=
  StrongDIPCompatible merged π GA ∧ ObservationFactorsThrough π O

/-- A merged-boundary contract includes exact projection. -/
theorem projectionExact_of_mergedBoundaryContract
    {merged : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : MergedBoundaryContract merged π GA O) :
    ProjectionExact merged π GA :=
  projectionExact_of_strongDIPCompatible h.1

/-- A merged-boundary contract includes representative stability. -/
theorem representativeStable_of_mergedBoundaryContract
    {merged : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : MergedBoundaryContract merged π GA O) :
    RepresentativeStable merged π :=
  representativeStable_of_strongDIPCompatible h.1

/-- A merged-boundary contract includes observation factorization. -/
theorem observationFactorsThrough_of_mergedBoundaryContract
    {merged : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : MergedBoundaryContract merged π GA O) :
    ObservationFactorsThrough π O :=
  h.2

/-- A merged-boundary contract preserves selected external observations. -/
theorem lspCompatible_of_mergedBoundaryContract
    {merged : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : MergedBoundaryContract merged π GA O) :
    LSPCompatible π O :=
  lspCompatible_of_observationFactorsThrough
    (observationFactorsThrough_of_mergedBoundaryContract h)

/--
Soundness predicate for making an implicit expectation explicit.

The explicit contract is an observation on the selected interface.  Soundness
says the concrete expectation is exactly the pullback of that interface-level
contract along the projection.
-/
def ExplicitContractSound
    (π : InterfaceProjection C A) (implicitExpectation : Observation C Obs)
    (explicitContract : Observation A Obs) : Prop :=
  ∀ c : C,
    implicitExpectation.observe c = explicitContract.observe (π.expose c)

/-- A sound explicit contract gives observation factorization. -/
theorem observationFactorsThrough_of_explicitContractSound
    {π : InterfaceProjection C A} {implicitExpectation : Observation C Obs}
    {explicitContract : Observation A Obs}
    (h : ExplicitContractSound π implicitExpectation explicitContract) :
    ObservationFactorsThrough π implicitExpectation :=
  ⟨explicitContract.observe, h⟩

/-- A sound explicit contract gives LSP-compatible selected observations. -/
theorem lspCompatible_of_explicitContractSound
    {π : InterfaceProjection C A} {implicitExpectation : Observation C Obs}
    {explicitContract : Observation A Obs}
    (h : ExplicitContractSound π implicitExpectation explicitContract) :
    LSPCompatible π implicitExpectation :=
  lspCompatible_of_observationFactorsThrough
    (observationFactorsThrough_of_explicitContractSound h)

/--
Bounded law package for `merge` external-contract preservation.

The conclusion exposes exact projection, representative stability, and selected
observation preservation from the explicit merged-boundary contract.  It does
not assert extractor completeness, semantic completeness, or global flatness.
-/
def mergeExternalContractPreservationLaw
    (merged : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) :
    ArchitectureCalculusLaw (ArchGraph C) PUnit :=
  mergeExternalContractPreservation
    True True True
    (MergedBoundaryContract merged π GA O)
    True
    (ProjectionExact merged π GA ∧
      RepresentativeStable merged π ∧
      LSPCompatible π O)
    True
    (by
      intro _ _ _ hContract _
      exact ⟨projectionExact_of_mergedBoundaryContract hContract,
        representativeStable_of_mergedBoundaryContract hContract,
        lspCompatible_of_mergedBoundaryContract hContract⟩)

/-- The merge external-contract package keeps the `merge` operation tag. -/
theorem mergeExternalContractPreservationLaw_operationKind
    (merged : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) :
    (mergeExternalContractPreservationLaw merged π GA O).operationKind =
      ArchitectureOperationKind.merge :=
  rfl

/--
The merge package exposes exact projection, representative stability, and
selected observation preservation from its bounded assumptions.
-/
theorem mergeExternalContractPreservationLaw_conclusion
    (merged : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs)
    (h : (mergeExternalContractPreservationLaw merged π GA O).AssumptionsHold) :
    ProjectionExact merged π GA ∧
      RepresentativeStable merged π ∧
      LSPCompatible π O :=
  conclusion_of_assumptions
    (mergeExternalContractPreservationLaw merged π GA O) h

/--
Bounded law package for `contract` explicitization soundness.

The conclusion exposes exact projection, representative stability, observation
factorization, and selected observation preservation.  The explicit contract is
only sound for the selected projection and observation model; semantic
completeness and global flatness remain non-conclusions.
-/
def contractExplicitizationLaw
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (implicitExpectation : Observation C Obs)
    (explicitContract : Observation A Obs) :
    ArchitectureCalculusLaw (ArchGraph C) PUnit :=
  contractExplicitizationSoundness
    True True True
    (StrongDIPCompatible G π GA)
    (ExplicitContractSound π implicitExpectation explicitContract)
    (ProjectionExact G π GA ∧
      RepresentativeStable G π ∧
      ObservationFactorsThrough π implicitExpectation ∧
      LSPCompatible π implicitExpectation)
    True
    (by
      intro _ _ _ hProjection hExplicit
      have hFactors :
          ObservationFactorsThrough π implicitExpectation :=
        observationFactorsThrough_of_explicitContractSound hExplicit
      exact ⟨projectionExact_of_strongDIPCompatible hProjection,
        representativeStable_of_strongDIPCompatible hProjection,
        hFactors,
        lspCompatible_of_observationFactorsThrough hFactors⟩)

/-- The contract explicitization package keeps the `contract` operation tag. -/
theorem contractExplicitizationLaw_operationKind
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (implicitExpectation : Observation C Obs)
    (explicitContract : Observation A Obs) :
    (contractExplicitizationLaw G π GA
      implicitExpectation explicitContract).operationKind =
      ArchitectureOperationKind.contract :=
  rfl

/--
The contract package exposes exact projection, representative stability,
observation factorization, and selected observation preservation from its
bounded assumptions.
-/
theorem contractExplicitizationLaw_conclusion
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (implicitExpectation : Observation C Obs)
    (explicitContract : Observation A Obs)
    (h : (contractExplicitizationLaw G π GA
      implicitExpectation explicitContract).AssumptionsHold) :
    ProjectionExact G π GA ∧
      RepresentativeStable G π ∧
      ObservationFactorsThrough π implicitExpectation ∧
      LSPCompatible π implicitExpectation :=
  conclusion_of_assumptions
    (contractExplicitizationLaw G π GA implicitExpectation explicitContract) h

end MergeContractEntrypoints

section RuntimeLocalizationEntrypoints

variable {C : Type u} {A : Type v} {StaticObs : Type r}
  {SemanticExpr : Type q} {SemanticObs : Type c}

/--
Selected boundary-relative runtime path localization.

Every measured runtime path whose endpoints are in the selected component
universe stays endpoint-localized to the selected region.  This is a bounded
premise; it does not assert telemetry completeness outside `U`.
-/
def RuntimePathLocalizedWithin
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop) : Prop :=
  ∀ {src dst : C}, Reachable X.runtime src dst ->
    src ∈ U.components -> dst ∈ U.components -> region src ∧ region dst

/--
Policy-aware runtime protection contract for a selected region.

The contract bundles path localization with `RuntimeInteractionProtected`.
Policy mechanisms such as timeout, fallback, queue, bulkhead, or circuit
breaker labels remain outside the static graph identity kernel.
-/
def RuntimeProtectionContract
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop) : Prop :=
  RuntimePathLocalizedWithin X U region ∧ RuntimeInteractionProtected X U

/-- A runtime protection contract includes selected path localization. -/
theorem runtimePathLocalized_of_runtimeProtectionContract
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static} {region : C -> Prop}
    (h : RuntimeProtectionContract X U region) :
    RuntimePathLocalizedWithin X U region :=
  h.1

/-- A runtime protection contract includes selected runtime interaction protection. -/
theorem runtimeInteractionProtected_of_runtimeProtectionContract
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static} {region : C -> Prop}
    (h : RuntimeProtectionContract X U region) :
    RuntimeInteractionProtected X U :=
  h.2

/-- Policy-aware runtime protection discharges bounded runtime flatness on `U`. -/
theorem runtimeFlatWithin_of_runtimeProtectionContract
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static} {region : C -> Prop}
    (hCoverage : RuntimeCoverageComplete X U)
    (h : RuntimeProtectionContract X U region) :
    RuntimeFlatWithin X U :=
  runtimeFlatWithin_of_runtimeInteractionProtected hCoverage
    (runtimeInteractionProtected_of_runtimeProtectionContract h)

/--
Bounded law package for `isolate` as runtime path localization.

The conclusion exposes only selected path localization and bounded runtime
flatness from explicit runtime coverage and protection premises.  Runtime
telemetry completeness, semantic diagram completeness, and global protection
idempotence remain non-conclusions.
-/
def isolateRuntimeLocalizationLaw
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop) :
    ArchitectureCalculusLaw
      (ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs) PUnit :=
  runtimeLocalization ArchitectureOperationKind.isolate
    True
    (RuntimePathLocalizedWithin X U region)
    (RuntimeCoverageComplete X U)
    (RuntimeInteractionProtected X U)
    True
    (RuntimePathLocalizedWithin X U region ∧ RuntimeFlatWithin X U)
    True
    (by
      intro _ hLocalized hCoverage hProtected _
      exact ⟨hLocalized,
        runtimeFlatWithin_of_runtimeInteractionProtected hCoverage hProtected⟩)

/-- The isolate runtime localization package keeps the `isolate` operation tag. -/
theorem isolateRuntimeLocalizationLaw_operationKind
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop) :
    (isolateRuntimeLocalizationLaw X U region).operationKind =
      ArchitectureOperationKind.isolate :=
  rfl

/--
The isolate runtime localization package exposes selected path localization and
bounded runtime flatness from its visible assumptions.
-/
theorem isolateRuntimeLocalizationLaw_conclusion
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop)
    (h : (isolateRuntimeLocalizationLaw X U region).AssumptionsHold) :
    RuntimePathLocalizedWithin X U region ∧ RuntimeFlatWithin X U :=
  conclusion_of_assumptions (isolateRuntimeLocalizationLaw X U region) h

/--
Bounded law package for policy-aware `protect`.

This connects the runtime policy package to bounded runtime flatness while
keeping the graph-level `protect` identity kernel separate.
-/
def protectRuntimeProtectionLaw
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop) :
    ArchitectureCalculusLaw
      (ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs) PUnit :=
  runtimeLocalization ArchitectureOperationKind.protect
    True
    (RuntimeProtectionContract X U region)
    (RuntimeCoverageComplete X U)
    True
    True
    (RuntimePathLocalizedWithin X U region ∧
      RuntimeInteractionProtected X U ∧
      RuntimeFlatWithin X U)
    True
    (by
      intro _ hContract hCoverage _ _
      exact ⟨runtimePathLocalized_of_runtimeProtectionContract hContract,
        runtimeInteractionProtected_of_runtimeProtectionContract hContract,
        runtimeFlatWithin_of_runtimeProtectionContract hCoverage hContract⟩)

/-- The protect runtime protection package keeps the `protect` operation tag. -/
theorem protectRuntimeProtectionLaw_operationKind
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop) :
    (protectRuntimeProtectionLaw X U region).operationKind =
      ArchitectureOperationKind.protect :=
  rfl

/--
The protect runtime protection package exposes selected path localization,
runtime interaction protection, and bounded runtime flatness.
-/
theorem protectRuntimeProtectionLaw_conclusion
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) (region : C -> Prop)
    (h : (protectRuntimeProtectionLaw X U region).AssumptionsHold) :
    RuntimePathLocalizedWithin X U region ∧
      RuntimeInteractionProtected X U ∧
      RuntimeFlatWithin X U :=
  conclusion_of_assumptions (protectRuntimeProtectionLaw X U region) h

end RuntimeLocalizationEntrypoints

section ConcreteGraphEntrypoints

variable {C : Type u}

/--
Bounded law package connecting graph-level `protect` identity to idempotence on
the selected finite graph kernel.
-/
def finiteProtectIdempotenceLaw
    (FG : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  protectIdempotence
    True True True True True
    (∀ c d : C, FG.protect.protect.graph.edge c d ↔ FG.protect.graph.edge c d)
    True
    (by
      intro _ _ _ _ _ c d
      exact FiniteArchGraph.protect_edge_iff FG.protect)

/-- The finite protect idempotence entrypoint keeps the `protect` operation tag. -/
theorem finiteProtectIdempotenceLaw_operationKind
    (FG : FiniteArchGraph C) :
    (finiteProtectIdempotenceLaw FG).operationKind =
      ArchitectureOperationKind.protect :=
  rfl

/-- The finite protect idempotence entrypoint yields concrete protect idempotence. -/
theorem finiteProtectIdempotenceLaw_conclusion
    (FG : FiniteArchGraph C)
    (h : (finiteProtectIdempotenceLaw FG).AssumptionsHold) :
    ∀ c d : C, FG.protect.protect.graph.edge c d ↔ FG.protect.graph.edge c d :=
  conclusion_of_assumptions (finiteProtectIdempotenceLaw FG) h

/--
Bounded law package connecting concrete finite reverse to reverse involution.
-/
def finiteReverseInvolutionLaw
    (FG : FiniteArchGraph C) :
    ArchitectureCalculusLaw (FiniteArchGraph C) PUnit :=
  reverseInvolution ArchitectureOperationKind.reverse
    True True True True True
    (∀ c d : C, FG.reverse.reverse.graph.edge c d ↔ FG.graph.edge c d)
    True
    (by
      intro _ _ _ _ _ c d
      exact FiniteArchGraph.reverse_reverse_edge_iff FG)

/-- The finite reverse involution entrypoint keeps the `reverse` operation tag. -/
theorem finiteReverseInvolutionLaw_operationKind
    (FG : FiniteArchGraph C) :
    (finiteReverseInvolutionLaw FG).operationKind =
      ArchitectureOperationKind.reverse :=
  rfl

/-- The finite reverse involution entrypoint yields concrete double-reverse restoration. -/
theorem finiteReverseInvolutionLaw_conclusion
    (FG : FiniteArchGraph C)
    (h : (finiteReverseInvolutionLaw FG).AssumptionsHold) :
    ∀ c d : C, FG.reverse.reverse.graph.edge c d ↔ FG.graph.edge c d :=
  conclusion_of_assumptions (finiteReverseInvolutionLaw FG) h

end ConcreteGraphEntrypoints

section RepairEntrypoints

variable {Rule : Type r}

/--
Bounded law package connecting repair monotonicity to a selected obstruction
universe and an admissible repair rule.

The conclusion is only the selected-measure decrease for the chosen witness,
rule, and step; it is not termination, all-obstruction clearing, or global
flatness preservation.
-/
def repairStepDecreasesLaw
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) (rule : Rule) (w : Witness) :
    ArchitectureCalculusLaw State Witness :=
  repairMonotonicity
    (U.selected w)
    (NonSplitExtensionWitness U source w)
    True
    (Nonempty (AdmissibleRepairRule U rule w))
    (Nonempty (RepairStep State Rule source rule target))
    (RepairStepDecreases U source target)
    True
    (by
      intro _ hWitness _ hRule hStep
      rcases hRule with ⟨hRule⟩
      rcases hStep with ⟨hStep⟩
      exact repairStepDecreases_of_admissible hWitness hRule hStep)

/-- The repair monotonicity entrypoint keeps the `repair` operation tag. -/
theorem repairStepDecreasesLaw_operationKind
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) (rule : Rule) (w : Witness) :
    (repairStepDecreasesLaw U source target rule w).operationKind =
      ArchitectureOperationKind.repair :=
  rfl

/--
The repair monotonicity entrypoint yields selected-measure decrease from its
bounded assumptions.
-/
theorem repairStepDecreasesLaw_conclusion
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) (rule : Rule) (w : Witness)
    (h : (repairStepDecreasesLaw U source target rule w).AssumptionsHold) :
    RepairStepDecreases U source target :=
  conclusion_of_assumptions (repairStepDecreasesLaw U source target rule w) h

end RepairEntrypoints

section SynthesisEntrypoints

variable {Constraint : Type c}
variable {Certificate : Type r}

/--
Bounded law package exposing soundness of a produced synthesis candidate.

This reads back an already sound candidate package; it does not state solver
completeness or that failure to produce a candidate means no solution exists.
-/
def synthesisCandidateSoundnessLaw
    (C : SynthesisConstraintSystem State Constraint)
    (pkg : SynthesisSoundnessPackage C) :
    ArchitectureCalculusLaw State Constraint where
  law := ArchitectureCalculusLawKind.synthesisSoundness
  operationKind := ArchitectureOperationKind.synthesize
  boundedUniverse := True
  compatibilityAssumptions := True
  coverageAssumptions := pkg.coverageAssumptions
  exactnessAssumptions := pkg.exactnessAssumptions
  observationEquivalence := True
  conclusion := ArchitectureSatisfies C pkg.candidate
  sound := by
    intro _ _ _ _ _
    exact SynthesisSoundnessPackage.candidate_satisfies pkg
  nonConclusions := pkg.nonConclusions

/-- The synthesis candidate soundness entrypoint keeps the `synthesize` operation tag. -/
theorem synthesisCandidateSoundnessLaw_operationKind
    (C : SynthesisConstraintSystem State Constraint)
    (pkg : SynthesisSoundnessPackage C) :
    (synthesisCandidateSoundnessLaw C pkg).operationKind =
      ArchitectureOperationKind.synthesize :=
  rfl

/--
The synthesis candidate soundness entrypoint yields candidate satisfaction from
its bounded assumptions.
-/
theorem synthesisCandidateSoundnessLaw_conclusion
    (C : SynthesisConstraintSystem State Constraint)
    (pkg : SynthesisSoundnessPackage C)
    (h : (synthesisCandidateSoundnessLaw C pkg).AssumptionsHold) :
    ArchitectureSatisfies C pkg.candidate :=
  conclusion_of_assumptions (synthesisCandidateSoundnessLaw C pkg) h

/--
Bounded law package exposing soundness of a valid no-solution certificate.

The certificate validity premise is explicit; solver failure alone is not
treated as evidence of non-existence.
-/
def noSolutionCertificateSoundnessLaw
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate)
    (pkg : NoSolutionCertificate Certificate C cert) :
    ArchitectureCalculusLaw State Certificate where
  law := ArchitectureCalculusLawKind.noSolutionSoundness
  operationKind := ArchitectureOperationKind.synthesize
  boundedUniverse := ValidNoSolutionCertificate pkg
  compatibilityAssumptions := True
  coverageAssumptions := pkg.coverageAssumptions
  exactnessAssumptions := pkg.exactnessAssumptions
  observationEquivalence := True
  conclusion := NoArchitectureSatisfies C
  sound := by
    intro hValid _ _ _ _
    exact NoSolutionCertificate.sound_of_valid pkg hValid
  nonConclusions := pkg.nonConclusions

/-- The no-solution certificate soundness entrypoint keeps the `synthesize` tag. -/
theorem noSolutionCertificateSoundnessLaw_operationKind
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate)
    (pkg : NoSolutionCertificate Certificate C cert) :
    (noSolutionCertificateSoundnessLaw C cert pkg).operationKind =
      ArchitectureOperationKind.synthesize :=
  rfl

/--
The no-solution certificate soundness entrypoint yields non-existence from a
valid certificate and its bounded assumptions.
-/
theorem noSolutionCertificateSoundnessLaw_conclusion
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate)
    (pkg : NoSolutionCertificate Certificate C cert)
    (h : (noSolutionCertificateSoundnessLaw C cert pkg).AssumptionsHold) :
    NoArchitectureSatisfies C :=
  conclusion_of_assumptions (noSolutionCertificateSoundnessLaw C cert pkg) h

end SynthesisEntrypoints

end ArchitectureCalculusLaw

end Formal.Arch
