import ResearchLean.AG.OperationRepair.FiniteCostDecision
import ResearchLean.AG.OperationRepair.FiniteRamNumbering

/-!
# Complete primitive trace for finite repair

The counted lower and upper loops, first-failure decision, and success-table
assembly share their stored values in one run. The success branch counts the
actual numbered cells it returns; the failure branch skips that assembly.
-/

namespace AAT.AG.OperationRepair.FiniteCostOutput

open FiniteRamPrimitives
open FiniteConstruction
variable {n m : Nat} {O : Type*} [DecidableEq O]

/-- Materialize the Boolean upper partition from the stored witness cells. -/
def upperCells (words : FiniteBehavior.WitnessTable n m) :
    Counted (RelationTable n) :=
  FiniteRamNumbering.tabulate n fun x =>
    FiniteRamNumbering.tabulate n fun y =>
      ⟨(FiniteBehavior.get words x y).isNone,
        [.tableRead, .tableRead, .boolOp]⟩

theorem upperCells_value (words : FiniteBehavior.WitnessTable n m) :
    (upperCells words).value =
      (FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
        (FiniteBehavior.get words x y).isNone) := by
  apply RelationTable.ext
  intro x y
  simp only [RelationTable.get, upperCells,
    FiniteRamNumbering.tabulate_get, FiniteTable.get_ofFn]

theorem upperCells_cost_le (words : FiniteBehavior.WitnessTable n m) :
    (upperCells words).cost ≤ 20 * (n + 1) ^ 2 := by
  have hi (x : Fin n) :
      (FiniteRamNumbering.tabulate n fun y =>
        (⟨(FiniteBehavior.get words x y).isNone,
          [.tableRead, .tableRead, .boolOp]⟩ : Counted Bool)).cost ≤
        n * 9 := by
    apply FiniteRamNumbering.tabulate_cost_le
    intro y
    rfl
  have ho := FiniteRamNumbering.tabulate_cost_le n _ (n * 9) hi
  change (FiniteRamNumbering.tabulate n fun x =>
    FiniteRamNumbering.tabulate n fun y =>
      ⟨(FiniteBehavior.get words x y).isNone,
        [.tableRead, .tableRead, .boolOp]⟩).cost ≤ 20 * (n + 1) ^ 2
  have hsq : n * n ≤ (n + 1) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  nlinarith

private def upperPartitionFromCells (input : FiniteRepairInput n m O)
    (words : FiniteBehavior.WitnessTable n m)
    (hwords : words = FiniteBehavior.upper input)
    (cells : RelationTable n)
    (hc : cells = (upperPartitionFrom input words hwords).cells) :
    PartitionTable n where
  cells := cells
  refl := by rw [hc]; exact (upperPartitionFrom input words hwords).refl
  symm := by rw [hc]; exact (upperPartitionFrom input words hwords).symm
  trans := by rw [hc]; exact (upperPartitionFrom input words hwords).trans

private theorem upperPartitionFromCells_eq (input : FiniteRepairInput n m O)
    (words : FiniteBehavior.WitnessTable n m)
    (hwords : words = FiniteBehavior.upper input)
    (cells : RelationTable n)
    (hc : cells = (upperPartitionFrom input words hwords).cells) :
    upperPartitionFromCells input words hwords cells hc =
      upperPartitionFrom input words hwords := by
  apply PartitionTable.ext
  exact hc

/-- Copy the returned failure word; its output cells are the counted cells. -/
def copyWord : List (Fin m) → Counted (List (Fin m))
  | [] => Counted.pure []
  | e :: rest =>
      let tail := copyWord rest
      ⟨e :: tail.value, .wordCell :: tail.trace⟩

theorem copyWord_value (word : List (Fin m)) :
    (copyWord word).value = word := by
  induction word with
  | nil => rfl
  | cons e rest ih => simp [copyWord, ih]

theorem copyWord_cost (word : List (Fin m)) :
    (copyWord word).cost = word.length := by
  induction word with
  | nil => rfl
  | cons e rest ih =>
      simp [copyWord, Counted.cost] at ih ⊢
      omega

def runWithTrace (input : FiniteRepairInput n m O) :
    Counted (RunOutput n m O) :=
  let lower := FiniteRamEnumeration.lower input
  let upper := FiniteRamUpper.upper input
  let decision := FiniteRamDecision.decision input upper.value
  let lowerPart := lowerPartitionFrom input lower.value
    (FiniteRamEnumeration.lower_value input)
  match decision.value with
  | some (x, y, word) =>
      let copied := copyWord word
      ⟨⟨lower.value, upper.value, Sum.inl (x, y, copied.value)⟩,
        lower.trace ++ upper.trace ++ decision.trace ++
          copied.trace ++
          List.replicate 3 .tableCell⟩
  | none =>
      let upperCells := upperCells upper.value
      let upperPart := upperPartitionFromCells input upper.value
        (FiniteRamUpper.upper_value input) upperCells.value
        (by rw [upperCells_value]; rfl)
      let success := FiniteRamNumbering.successTablesFrom input lowerPart upperPart
      ⟨⟨lower.value, upper.value, Sum.inr success.value⟩,
        lower.trace ++ upper.trace ++ decision.trace ++
          upperCells.trace ++ success.trace ++
          List.replicate 3 .tableCell⟩

theorem runWithTrace_value (input : FiniteRepairInput n m O) :
    (runWithTrace input).value = runRepair input := by
  unfold runWithTrace runRepair
  cases h : (FiniteRamDecision.decision input
    (FiniteRamUpper.upper input).value).value with
  | some bad =>
      rcases bad with ⟨x, y, word⟩
      simp [h, copyWord_value]
  | none =>
      simp [h, FiniteRamNumbering.successTablesFrom_value,
        upperPartitionFromCells_eq]

/-- Failure correctness holds for the same counted run whose cost is bounded. -/
theorem runWithTrace_failure (input : FiniteRepairInput n m O)
    (x y : Fin n) (word : List (Fin m))
    (h : (runWithTrace input).value.outcome = Sum.inl (x, y, word)) :
    input.requestRel x y ∧ word.length < n * n ∧
      FiniteBehavior.separates input x y word := by
  rw [runWithTrace_value] at h
  exact runRepair_failure input x y word h

/-- Success and repair existence are equivalent for this counted run. -/
theorem runWithTrace_success_iff_repair_exists
    (input : FiniteRepairInput n m O) :
    (∃ tables : SuccessTables n m O,
      (runWithTrace input).value.outcome = Sum.inr tables) ↔
      Nonempty (RepairQuotient.{0, 0, _, 0} input.system input.observe
        input.requestRel) := by
  rw [runWithTrace_value]
  exact runRepair_success_iff_repair_exists input

theorem runWithTrace_cost_le (input : FiniteRepairInput n m O) :
    (runWithTrace input).cost ≤
      1100 * (m + 1) * (n + 1) ^ 5 := by
  have hl := FiniteRamEnumeration.lower_cost_poly input
  have hu := FiniteRamUpper.upper_cost_le input
  have hd := FiniteRamDecision.decision_cost_le input
    (FiniteRamUpper.upper input).value
  let lowerPart := lowerPartitionFrom input
    (FiniteRamEnumeration.lower input).value
    (FiniteRamEnumeration.lower_value input)
  let upperPart := upperPartitionFromCells input
    (FiniteRamUpper.upper input).value
    (FiniteRamUpper.upper_value input)
    (upperCells (FiniteRamUpper.upper input).value).value
    (by rw [upperCells_value]; rfl)
  have hs := FiniteRamNumbering.successTablesFrom_cost_le
    input lowerPart upperPart
  have hc := upperCells_cost_le (FiniteRamUpper.upper input).value
  have hn : 1 ≤ n + 1 := by omega
  have hm : 1 ≤ m + 1 := by omega
  have hpow4 : (n + 1) ^ 4 ≤ (n + 1) ^ 5 :=
    Nat.pow_le_pow_right hn (by decide)
  have hpow2 : (n + 1) ^ 2 ≤ (n + 1) ^ 5 :=
    Nat.pow_le_pow_right hn (by decide)
  have hupper : (FiniteRamUpper.upper input).cost ≤
      60 * (m + 1) * (n + 1) ^ 5 :=
    hu.trans (Nat.mul_le_mul_left (60 * (m + 1)) hpow4)
  have hdecision :
      (FiniteRamDecision.decision input
        (FiniteRamUpper.upper input).value).cost ≤
          30 * (m + 1) * (n + 1) ^ 5 := by
    calc
      _ ≤ 30 * (n + 1) ^ 2 := hd
      _ ≤ 30 * (n + 1) ^ 5 := Nat.mul_le_mul_left 30 hpow2
      _ ≤ 30 * (m + 1) * (n + 1) ^ 5 := by nlinarith
  have hsuccess :
      (FiniteRamNumbering.successTablesFrom input lowerPart upperPart).cost ≤
        300 * (m + 1) * (n + 1) ^ 5 :=
    hs.trans (Nat.mul_le_mul_left (300 * (m + 1)) hpow4)
  have hcells :
      (upperCells (FiniteRamUpper.upper input).value).cost ≤
        20 * (m + 1) * (n + 1) ^ 5 := by
    calc
      _ ≤ 20 * (n + 1) ^ 2 := hc
      _ ≤ 20 * (n + 1) ^ 5 := Nat.mul_le_mul_left 20 hpow2
      _ ≤ 20 * (m + 1) * (n + 1) ^ 5 := by nlinarith
  have hcopy (bad : Fin n × Fin n × List (Fin m))
      (h : (FiniteRamDecision.decision input
        (FiniteRamUpper.upper input).value).value = some bad) :
      bad.2.2.length ≤ n * n := by
    have hf : failureSearch input = some bad := by
      simpa only [failureSearch, FiniteRamDecision.decision_value,
        FiniteRamUpper.upper_value] using h
    rcases bad with ⟨x, y, word⟩
    exact (failureSearch_sound input hf).2.1.le
  unfold runWithTrace
  cases h : (FiniteRamDecision.decision input
    (FiniteRamUpper.upper input).value).value with
  | some bad =>
      simp only [h, Counted.cost, List.length_append,
        List.length_replicate]
      dsimp [Counted.cost] at hl hupper hdecision
      have hb := hcopy bad h
      have hsq : n * n ≤ (n + 1) ^ 5 := by
        nlinarith [hpow2]
      have hword := copyWord_cost bad.2.2
      dsimp [Counted.cost] at hword
      nlinarith
  | none =>
      simp only [h, Counted.cost, List.length_append,
        List.length_replicate]
      dsimp [Counted.cost] at hl hupper hdecision hsuccess hcells
      change (FiniteRamEnumeration.lower input).trace.length +
          (FiniteRamUpper.upper input).trace.length +
          (FiniteRamDecision.decision input
            (FiniteRamUpper.upper input).value).trace.length +
          (upperCells (FiniteRamUpper.upper input).value).trace.length +
          (FiniteRamNumbering.successTablesFrom input lowerPart upperPart).trace.length +
          3 ≤ 1100 * (m + 1) * (n + 1) ^ 5
      nlinarith

end AAT.AG.OperationRepair.FiniteCostOutput

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteCostOutput
