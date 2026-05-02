import Formal.Arch.Operation.Operation

namespace Formal.Arch

universe u v r

/--
A selected obstruction universe for repair theorems.

The universe records only the obstruction witnesses and measure that a repair
package has chosen to track. It does not claim coverage of every possible
runtime, semantic, or architectural obstruction.
-/
structure SelectedObstructionUniverse (State : Type u) (Witness : Type v) where
  selected : Witness -> Prop
  witnessAt : State -> Witness -> Prop
  measure : State -> Nat

/--
A selected witness explaining that the current extension is non-split within
the chosen obstruction universe.
-/
def NonSplitExtensionWitness
    {State : Type u} {Witness : Type v}
    (U : SelectedObstructionUniverse State Witness)
    (state : State) (w : Witness) : Prop :=
  U.selected w ∧ U.witnessAt state w

/-- The selected obstruction measure tracked by a repair theorem package. -/
def ExtensionObstructionMeasure
    {State : Type u} {Witness : Type v}
    (U : SelectedObstructionUniverse State Witness)
    (state : State) : Nat :=
  U.measure state

/-- A repair step applying a selected rule between two architecture states. -/
structure RepairStep (State : Type u) (Rule : Type r)
    (source : State) (rule : Rule) (target : State) where
  applied : Prop

/-- The measure-decrease predicate for a repair step. -/
def RepairStepDecreases
    {State : Type u} {Witness : Type v}
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) : Prop :=
  ExtensionObstructionMeasure U target < ExtensionObstructionMeasure U source

/--
An admissible repair rule for a selected witness.

Admissibility is deliberately relative to the selected obstruction universe:
it provides exactly the measure-decrease fact needed by the repair theorem and
records explicit non-conclusions instead of proving global flatness.
-/
structure AdmissibleRepairRule
    {State : Type u} {Witness : Type v} {Rule : Type r}
    (U : SelectedObstructionUniverse State Witness)
    (rule : Rule) (w : Witness) where
  selectedWitness : U.selected w
  decreasesSelectedMeasure :
    ∀ {source target : State},
      NonSplitExtensionWitness U source w ->
      RepairStep State Rule source rule target ->
      RepairStepDecreases U source target
  nonConclusions : Prop

namespace AdmissibleRepairRule

variable {State : Type u} {Witness : Type v} {Rule : Type r}
variable {U : SelectedObstructionUniverse State Witness}
variable {rule : Rule} {w : Witness}

/-- An admissible rule records the selected witness it is allowed to repair. -/
theorem selected
    (hRule : AdmissibleRepairRule U rule w) :
    U.selected w :=
  hRule.selectedWitness

/-- The theorem package explicitly records a non-conclusion clause. -/
def RecordsNonConclusions
    (hRule : AdmissibleRepairRule U rule w) :
    Prop :=
  hRule.nonConclusions

/-- The recorded non-conclusion clause is exactly the rule's field. -/
theorem records_nonConclusions_iff
    (hRule : AdmissibleRepairRule U rule w) :
    RecordsNonConclusions hRule ↔ hRule.nonConclusions :=
  Iff.rfl

end AdmissibleRepairRule

/--
Admissible repair decreases the selected obstruction measure.

This is the bounded repair monotonicity theorem: it applies only to the chosen
obstruction universe and the selected witness/rule pair.
-/
theorem repairStepDecreases_of_admissible
    {State : Type u} {Witness : Type v} {Rule : Type r}
    {U : SelectedObstructionUniverse State Witness}
    {source target : State} {rule : Rule} {w : Witness}
    (hWitness : NonSplitExtensionWitness U source w)
    (hRule : AdmissibleRepairRule U rule w)
    (hStep : RepairStep State Rule source rule target) :
    RepairStepDecreases U source target :=
  hRule.decreasesSelectedMeasure hWitness hStep

/--
Equivalent statement using the named selected obstruction measure.
-/
theorem extensionObstructionMeasure_decreases_of_admissible
    {State : Type u} {Witness : Type v} {Rule : Type r}
    {U : SelectedObstructionUniverse State Witness}
    {source target : State} {rule : Rule} {w : Witness}
    (hWitness : NonSplitExtensionWitness U source w)
    (hRule : AdmissibleRepairRule U rule w)
    (hStep : RepairStep State Rule source rule target) :
    ExtensionObstructionMeasure U target <
      ExtensionObstructionMeasure U source :=
  repairStepDecreases_of_admissible hWitness hRule hStep

end Formal.Arch
