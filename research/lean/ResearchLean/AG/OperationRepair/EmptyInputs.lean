import ResearchLean.AG.OperationRepair.FiniteCostDecision

/-!
# Empty finite operation-repair inputs

These are concrete boundary inputs for G-126 D. The same finite procedure is
evaluated with zero states and operations; no default state or operation is
introduced. The cost theorem remains the one for the general input.

Implementation notes: `FiniteTable.ofFn` over `Fin 0` is the canonical empty
table constructor. Supplying a fictitious default state would change the
GOAL's empty-set quantification, so the input is assembled solely from empty
tables.
-/

namespace AAT.AG.OperationRepair.EmptyInputs

/-- The unique empty-state, empty-operation Boolean request input. -/
def zero : FiniteRepairInput 0 0 Unit where
  transition := FiniteTable.ofFn fun e => Fin.elim0 e
  observation := FiniteTable.ofFn fun x => Fin.elim0 x
  request := FiniteTable.ofFn fun x => Fin.elim0 x

/-- The actual lower table of the empty input has no cells. -/
theorem zero_lower_empty :
    (FiniteConstruction.runRepair zero).lowerCells =
      FiniteClosure.initial zero := by
  rfl

/-- The actual upper word table of the empty input is its initial table. -/
theorem zero_upper_empty :
    (FiniteConstruction.runRepair zero).upperWords =
      FiniteBehavior.initial zero := by
  rfl

/-- No requested pair can be returned for a zero-state input. -/
theorem zero_failureSearch_none :
    FiniteConstruction.failureSearch zero = none := by
  rfl

/-- The same D run takes its success branch on the empty input. -/
theorem zero_success :
    ∃ tables : FiniteConstruction.SuccessTables 0 0 Unit,
      (FiniteConstruction.runRepair zero).outcome = Sum.inr tables := by
  exact (FiniteConstruction.runRepair_success_iff zero).mpr (by
    intro x
    exact Fin.elim0 x)

/-- Both actual success payload quotients have zero classes. -/
theorem zero_success_counts
    (tables : FiniteConstruction.SuccessTables 0 0 Unit)
    (h : (FiniteConstruction.runRepair zero).outcome = Sum.inr tables) :
    tables.lower.classCount = 0 ∧ tables.upper.classCount = 0 := by
  have hp := FiniteConstruction.runRepair_success_payload zero tables h
  rw [hp]
  constructor <;> simp [FiniteConstruction.makeSuccessTables,
    FiniteConstruction.makeNumberedTables,
    FiniteConstruction.PartitionTable.classCount,
    FiniteConstruction.PartitionTable.representatives]

/-- Two states with no operation names; the requested pair differs now. -/
def twoNoOps : FiniteRepairInput 2 0 Bool where
  transition := FiniteTable.ofFn fun e => Fin.elim0 e
  observation := FiniteTable.ofFn fun x => x.val == 1
  request := FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    decide (x.val = 0 ∧ y.val = 1)

/-- With no operation names, D can still return the empty separating word. -/
theorem twoNoOps_empty_word_failure :
    (FiniteConstruction.runRepair twoNoOps).outcome =
      Sum.inl (0, 1, []) := by
  rfl

/-- That computed empty word is a D certificate for the original pair. -/
theorem twoNoOps_failure_certificate :
    twoNoOps.requestRel 0 1 ∧ ([] : List (Fin 0)).length < 2 * 2 ∧
      FiniteBehavior.separates twoNoOps 0 1 [] := by
  exact FiniteConstruction.runRepair_failure twoNoOps 0 1 []
    twoNoOps_empty_word_failure

/-- A populated source may have an empty operation-name type and succeed. -/
def oneNoOps : FiniteRepairInput 1 0 Bool where
  transition := FiniteTable.ofFn fun e => Fin.elim0 e
  observation := FiniteTable.ofFn fun _ => false
  request := FiniteTable.ofFn fun _ => FiniteTable.ofFn fun _ => true

/-- The actual D run succeeds and returns two one-class quotients. -/
theorem oneNoOps_success_counts :
    ∃ tables : FiniteConstruction.SuccessTables 1 0 Bool,
      (FiniteConstruction.runRepair oneNoOps).outcome = Sum.inr tables ∧
      tables.lower.classCount = 1 ∧ tables.upper.classCount = 1 := by
  obtain ⟨tables, h⟩ :=
    (FiniteConstruction.runRepair_success_iff oneNoOps).mpr (by
      intro x y _
      have hx : x = 0 := Fin.eq_zero x
      have hy : y = 0 := Fin.eq_zero y
      subst x
      subst y
      exact (behavior oneNoOps.system oneNoOps.observe).setoid.refl 0)
  have hp := FiniteConstruction.runRepair_success_payload oneNoOps tables h
  refine ⟨tables, h, ?_, ?_⟩
  · rw [hp]
    simp [FiniteConstruction.makeSuccessTables,
      FiniteConstruction.makeNumberedTables,
      FiniteConstruction.PartitionTable.classCount,
      FiniteConstruction.PartitionTable.representatives]
  · rw [hp]
    simp [FiniteConstruction.makeSuccessTables,
      FiniteConstruction.makeNumberedTables,
      FiniteConstruction.PartitionTable.classCount,
      FiniteConstruction.PartitionTable.representatives]

end AAT.AG.OperationRepair.EmptyInputs

#assert_standard_axioms_only AAT.AG.OperationRepair.EmptyInputs
