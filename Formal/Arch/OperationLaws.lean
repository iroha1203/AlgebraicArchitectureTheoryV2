import Formal.Arch.Operation

namespace Formal.Arch

universe u v

/--
Bounded Architecture Calculus law tags.

These are law-package names, not unconditional algebraic laws over every
operation in every universe.
-/
inductive ArchitectureCalculusLawKind where
  | identity
  | associativity
  | refinementAbstraction
  | protectionIdempotence
  | reverseInvolution
  | witnessMappingFunctoriality
  deriving DecidableEq, Repr

namespace ArchitectureCalculusLawKind

/-- Human-readable law tag used by documentation-facing theorem packages. -/
def label : ArchitectureCalculusLawKind -> String
  | identity => "identity"
  | associativity => "associativity"
  | refinementAbstraction => "refinementAbstraction"
  | protectionIdempotence => "protectionIdempotence"
  | reverseInvolution => "reverseInvolution"
  | witnessMappingFunctoriality => "witnessMappingFunctoriality"

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

end ArchitectureCalculusLaw

end Formal.Arch
