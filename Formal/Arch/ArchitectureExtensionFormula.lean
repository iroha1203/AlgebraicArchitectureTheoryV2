import Formal.Arch.Flatness
import Formal.Arch.DiagramFiller

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

/--
Payload bridge from semantic diagram non-fillability into the architecture
extension obstruction universe.

The payload carries a concrete `NonFillabilityWitnessFor` for one required
diagram. It does not by itself refute a selected split predicate; that bounded
connection is supplied by `FillingFailureBridgePackage` below.
-/
structure FillingFailureWitnessPayload {State : Type u}
    {Step : State -> State -> Type v}
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop)
    {X Y : State} (D : ArchitectureDiagram Step X Y)
    (DiagramWitness : Type w) : Type (max u v w) where
  witness : DiagramWitness
  nonFillability :
    NonFillabilityWitnessFor
      IndependentSquare SameExternalContract RepairFill D witness

/--
Turn a selected diagram non-fillability payload into an abstract extension
obstruction witness classified as `fillingFailure`.
-/
def fillingFailureExtensionObstructionWitness
    (X : FeatureExtension Core Feature Extended FeatureView)
    {State : Type u} {Step : State -> State -> Type v}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {A B : State} {D : ArchitectureDiagram Step A B}
    {DiagramWitness : Type w}
    (payload :
      FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness) :
    ExtensionObstructionWitness X
      (FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness) where
  witness := payload
  classifiesAs := .fillingFailure

/--
Selected split predicate for one feature extension.

The predicate is supplied by a theorem package rather than fixed globally, so
static, runtime, semantic, or analytic split notions can be handled without
claiming that one universe is complete for all axes.
-/
def SelectedSplitExtension
    (_X : FeatureExtension Core Feature Extended FeatureView)
    (splitPredicate : Prop) : Prop :=
  splitPredicate

/--
Selected obstruction witness predicate for one feature extension.

This is the bounded witness universe chosen by a theorem package. It filters
the abstract `ExtensionObstructionWitness` payloads without claiming global
coverage of every possible non-split cause.
-/
def SelectedExtensionObstructionWitness
    (_X : FeatureExtension Core Feature Extended FeatureView)
    (selected :
      ExtensionObstructionWitness X Witness -> Prop)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  selected witness

/-- Existence of a selected obstruction witness in the chosen bounded universe. -/
def SelectedExtensionObstructionWitnessExists
    (X : FeatureExtension Core Feature Extended FeatureView)
    (selected :
      ExtensionObstructionWitness X Witness -> Prop) : Prop :=
  ∃ witness : ExtensionObstructionWitness X Witness,
    SelectedExtensionObstructionWitness X selected witness

/-- Soundness relation between a selected witness universe and a split predicate. -/
def SelectedExtensionWitnessSound
    (X : FeatureExtension Core Feature Extended FeatureView)
    (splitPredicate : Prop)
    (selected :
      ExtensionObstructionWitness X Witness -> Prop) : Prop :=
  ∀ {witness : ExtensionObstructionWitness X Witness},
    SelectedExtensionObstructionWitness X selected witness ->
      ¬ SelectedSplitExtension X splitPredicate

/--
Bounded completeness relation between selected non-split failures and the
chosen witness universe.
-/
def SelectedExtensionWitnessComplete
    (X : FeatureExtension Core Feature Extended FeatureView)
    (splitPredicate : Prop)
    (selected :
      ExtensionObstructionWitness X Witness -> Prop) : Prop :=
  ¬ SelectedSplitExtension X splitPredicate ->
    SelectedExtensionObstructionWitnessExists X selected

/--
Theorem package for non-split extension witnesses.

`coverageExactnessAssumptions` is deliberately explicit: bounded completeness
is relative to the selected witness universe, while soundness is available
without assuming global witness coverage.
-/
structure NonSplitExtensionWitnessPackage
    (X : FeatureExtension Core Feature Extended FeatureView)
    (Witness : Type z) where
  splitPredicate : Prop
  selectedWitness : ExtensionObstructionWitness X Witness -> Prop
  coverageExactnessAssumptions : Prop
  soundness :
    SelectedExtensionWitnessSound X splitPredicate selectedWitness
  boundedCompleteness :
    coverageExactnessAssumptions ->
      SelectedExtensionWitnessComplete X splitPredicate selectedWitness
  nonConclusions : Prop

namespace NonSplitExtensionWitnessPackage

variable {X : FeatureExtension Core Feature Extended FeatureView}
variable {Witness : Type z}

/-- A package records the selected split predicate it reasons about. -/
def SplitPredicate
    (P : NonSplitExtensionWitnessPackage X Witness) : Prop :=
  SelectedSplitExtension X P.splitPredicate

/-- A package records the selected obstruction witness universe it reasons about. -/
def WitnessPredicate
    (P : NonSplitExtensionWitnessPackage X Witness)
    (witness : ExtensionObstructionWitness X Witness) : Prop :=
  SelectedExtensionObstructionWitness X P.selectedWitness witness

/-- A selected obstruction witness exists for the package. -/
def WitnessExists
    (P : NonSplitExtensionWitnessPackage X Witness) : Prop :=
  SelectedExtensionObstructionWitnessExists X P.selectedWitness

/-- The package explicitly records a non-conclusion clause. -/
def RecordsNonConclusions
    (P : NonSplitExtensionWitnessPackage X Witness) : Prop :=
  P.nonConclusions

/-- Soundness: a selected obstruction witness refutes the selected split predicate. -/
theorem not_selectedSplitExtension_of_selectedExtensionObstructionWitness
    (P : NonSplitExtensionWitnessPackage X Witness)
    {witness : ExtensionObstructionWitness X Witness}
    (hWitness : P.WitnessPredicate witness) :
    ¬ P.SplitPredicate :=
  P.soundness hWitness

/-- Soundness-only form using witness existence. -/
theorem not_selectedSplitExtension_of_selectedExtensionObstructionWitnessExists
    (P : NonSplitExtensionWitnessPackage X Witness)
    (hWitness : P.WitnessExists) :
    ¬ P.SplitPredicate := by
  rcases hWitness with ⟨witness, hSelected⟩
  exact P.not_selectedSplitExtension_of_selectedExtensionObstructionWitness hSelected

/--
Bounded completeness: under the package coverage / exactness assumptions, a
selected split failure has a selected obstruction witness.
-/
theorem selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension
    (P : NonSplitExtensionWitnessPackage X Witness)
    (hCoverage : P.coverageExactnessAssumptions)
    (hNonSplit : ¬ P.SplitPredicate) :
    P.WitnessExists :=
  P.boundedCompleteness hCoverage hNonSplit

/--
Soundness plus bounded completeness, relative to the package coverage /
exactness assumptions.
-/
theorem selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension
    (P : NonSplitExtensionWitnessPackage X Witness)
    (hCoverage : P.coverageExactnessAssumptions) :
    P.WitnessExists ↔ ¬ P.SplitPredicate := by
  constructor
  · exact P.not_selectedSplitExtension_of_selectedExtensionObstructionWitnessExists
  · exact
      P.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension
        hCoverage

/-- The recorded non-conclusion clause is exactly the package field. -/
theorem records_nonConclusions_iff
    (P : NonSplitExtensionWitnessPackage X Witness) :
    P.RecordsNonConclusions ↔ P.nonConclusions :=
  Iff.rfl

end NonSplitExtensionWitnessPackage

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

/--
The bridge constructor always lands in the `fillingFailure` classification.
-/
theorem fillingFailureExtensionObstructionWitness_classified
    (X : FeatureExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse X.extended)
    {State : Type u} {Step : State -> State -> Type v}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {A B : State} {D : ArchitectureDiagram Step A B}
    {DiagramWitness : Type w}
    (payload :
      FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness) :
    ClassifiedAsFillingFailure X U
      (fillingFailureExtensionObstructionWitness X payload) :=
  rfl

/--
Bounded premise connecting selected filling-failure payloads to a selected
split predicate.

This is intentionally a premise: a `NonFillabilityWitnessFor` refutes diagram
fillability, but it refutes the chosen split notion only when the surrounding
extension package supplies that interpretation.
-/
def FillingFailureRefutesSplit
    (X : FeatureExtension Core Feature Extended FeatureView)
    (splitPredicate : Prop)
    {State : Type u} {Step : State -> State -> Type v}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {A B : State} {D : ArchitectureDiagram Step A B}
    {DiagramWitness : Type w}
    (selectedPayload :
      FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness ->
        Prop) : Prop :=
  ∀ {payload :
      FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness},
    selectedPayload payload -> ¬ SelectedSplitExtension X splitPredicate

/--
Soundness from a selected filling-failure payload to non-split, relative to the
explicit `FillingFailureRefutesSplit` premise.
-/
theorem not_selectedSplitExtension_of_fillingFailurePayload
    {X : FeatureExtension Core Feature Extended FeatureView}
    {splitPredicate : Prop}
    {State : Type u} {Step : State -> State -> Type v}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {A B : State} {D : ArchitectureDiagram Step A B}
    {DiagramWitness : Type w}
    {selectedPayload :
      FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness ->
        Prop}
    (hRefutes :
      FillingFailureRefutesSplit X splitPredicate selectedPayload)
    {payload :
      FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness}
    (hSelected : selectedPayload payload) :
    ¬ SelectedSplitExtension X splitPredicate :=
  hRefutes hSelected

/--
Bounded bridge package from selected diagram filling failures to the generic
`NonSplitExtensionWitnessPackage`.

The completeness field is relative to a selected payload universe and explicit
coverage / exactness assumptions. It does not claim global semantic diagram
coverage or that every split failure is a filling failure.
-/
structure FillingFailureBridgePackage
    (X : FeatureExtension Core Feature Extended FeatureView)
    {State : Type u} {Step : State -> State -> Type v}
    (IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop)
    (SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop)
    (RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop)
    {A B : State} (D : ArchitectureDiagram Step A B)
    (DiagramWitness : Type w) where
  splitPredicate : Prop
  selectedPayload :
    FillingFailureWitnessPayload
      IndependentSquare SameExternalContract RepairFill D DiagramWitness ->
      Prop
  coverageExactnessAssumptions : Prop
  fillingFailureRefutesSplit :
    FillingFailureRefutesSplit X splitPredicate selectedPayload
  boundedCompleteness :
    coverageExactnessAssumptions ->
      ¬ SelectedSplitExtension X splitPredicate ->
        ∃ payload :
          FillingFailureWitnessPayload
            IndependentSquare SameExternalContract RepairFill D DiagramWitness,
          selectedPayload payload
  nonConclusions : Prop

namespace FillingFailureBridgePackage

variable {X : FeatureExtension Core Feature Extended FeatureView}
variable {State : Type u} {Step : State -> State -> Type v}
variable {IndependentSquare :
  (W X Y Z : State) ->
    Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
variable {SameExternalContract :
  (X Y : State) -> Step X Y -> Step X Y -> Prop}
variable {RepairFill :
  (X Y : State) -> ArchitecturePath Step X Y ->
    ArchitecturePath Step X Y -> Prop}
variable {A B : State} {D : ArchitectureDiagram Step A B}
variable {DiagramWitness : Type w}

/-- Selected extension witnesses induced by the filling-failure bridge package. -/
def SelectedWitness
    (P :
      FillingFailureBridgePackage X
        IndependentSquare SameExternalContract RepairFill D DiagramWitness)
    (witness :
      ExtensionObstructionWitness X
        (FillingFailureWitnessPayload
          IndependentSquare SameExternalContract RepairFill D DiagramWitness)) :
    Prop :=
  witness.classifiesAs = .fillingFailure ∧ P.selectedPayload witness.witness

/--
The filling-failure bridge package embeds into the generic non-split witness
package.
-/
def toNonSplitExtensionWitnessPackage
    (P :
      FillingFailureBridgePackage X
        IndependentSquare SameExternalContract RepairFill D DiagramWitness) :
    NonSplitExtensionWitnessPackage X
      (FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill D DiagramWitness) where
  splitPredicate := P.splitPredicate
  selectedWitness := P.SelectedWitness
  coverageExactnessAssumptions := P.coverageExactnessAssumptions
  soundness := by
    intro witness hSelected
    exact P.fillingFailureRefutesSplit hSelected.2
  boundedCompleteness := by
    intro hCoverage hNonSplit
    rcases P.boundedCompleteness hCoverage hNonSplit with
      ⟨payload, hSelectedPayload⟩
    exact ⟨fillingFailureExtensionObstructionWitness X payload,
      rfl, hSelectedPayload⟩
  nonConclusions := P.nonConclusions

/--
Connection corollary: selected filling-failure payload existence gives a
selected generic extension obstruction witness.
-/
theorem selectedExtensionObstructionWitnessExists_of_selectedPayloadExists
    (P :
      FillingFailureBridgePackage X
        IndependentSquare SameExternalContract RepairFill D DiagramWitness)
    (hPayload :
      ∃ payload :
        FillingFailureWitnessPayload
          IndependentSquare SameExternalContract RepairFill D DiagramWitness,
        P.selectedPayload payload) :
    (P.toNonSplitExtensionWitnessPackage).WitnessExists := by
  rcases hPayload with ⟨payload, hSelectedPayload⟩
  exact ⟨fillingFailureExtensionObstructionWitness X payload,
    rfl, hSelectedPayload⟩

end FillingFailureBridgePackage

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
