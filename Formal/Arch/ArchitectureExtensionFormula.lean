import Formal.Arch.Flatness

namespace Formal.Arch

universe u v w q z

/--
Coverage premise used by the structural architecture extension formula.

This public name matches the roadmap terminology while reusing the
coverage-aware extension package from `Flatness`.
-/
abbrev ExtensionCoverage
    (X : FeatureExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse X.extended) : Prop :=
  ExtensionCoverageComplete X U

/--
The non-disjoint classification classes used by the first structural extension
formula package.
-/
inductive ExtensionObstructionClass where
  | inheritedCore
  | featureLocal
  | interaction
  | liftingFailure
  | fillingFailure
  | complexityTransfer
  | residualCoverageGap
  deriving DecidableEq, Repr

/--
Obstruction witness for the extended architecture, paired with the bounded
classification evidence selected by the current formula package.

The payload is intentionally abstract: concrete obstruction families can later
instantiate it with static, runtime, semantic, or analytic witnesses.
-/
structure ExtensionObstructionWitness
    (X : FeatureExtension Core Feature Extended FeatureView)
    (Witness : Type z) where
  witness : Witness
  classifiesAs : ExtensionObstructionClass

/-- The witness is inherited from the embedded core architecture. -/
def ClassifiedAsInheritedCore
    (X : FeatureExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse X.extended)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  witness.classifiesAs = .inheritedCore

/-- The witness is local to the added feature. -/
def ClassifiedAsFeatureLocal
    (X : FeatureExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse X.extended)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  witness.classifiesAs = .featureLocal

/-- The witness comes from a feature/core interaction boundary. -/
def ClassifiedAsInteraction
    (X : FeatureExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse X.extended)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  witness.classifiesAs = .interaction

/-- The witness records failure to lift a selected feature step. -/
def ClassifiedAsLiftingFailure
    (X : FeatureExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse X.extended)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  witness.classifiesAs = .liftingFailure

/-- The witness records failure to fill a required diagram. -/
def ClassifiedAsFillingFailure
    (X : FeatureExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse X.extended)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  witness.classifiesAs = .fillingFailure

/-- The witness records transfer into a complexity or analytic diagnostic axis. -/
def ClassifiedAsComplexityTransfer
    (X : FeatureExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse X.extended)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  witness.classifiesAs = .complexityTransfer

/-- The witness remains as residual evidence or a bounded coverage gap. -/
def ClassifiedAsResidualCoverageGap
    (X : FeatureExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse X.extended)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  witness.classifiesAs = .residualCoverageGap

/--
Bounded structural architecture extension formula.

Under the supplied bounded extension coverage premise, every selected extension
obstruction witness is covered by at least one classification predicate. This
is a coverage theorem, not a disjoint decomposition theorem.
-/
theorem ArchitectureExtensionFormula_structural
    (X : FeatureExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse X.extended)
    (_hCoverage : ExtensionCoverage X U)
    (witness : ExtensionObstructionWitness X Witness) :
    ClassifiedAsInheritedCore X U witness ∨
      ClassifiedAsFeatureLocal X U witness ∨
      ClassifiedAsInteraction X U witness ∨
      ClassifiedAsLiftingFailure X U witness ∨
      ClassifiedAsFillingFailure X U witness ∨
      ClassifiedAsComplexityTransfer X U witness ∨
      ClassifiedAsResidualCoverageGap X U witness := by
  rcases witness with ⟨payload, classification⟩
  cases classification <;>
    simp [ClassifiedAsInheritedCore, ClassifiedAsFeatureLocal,
      ClassifiedAsInteraction, ClassifiedAsLiftingFailure,
      ClassifiedAsFillingFailure, ClassifiedAsComplexityTransfer,
      ClassifiedAsResidualCoverageGap]

end Formal.Arch
