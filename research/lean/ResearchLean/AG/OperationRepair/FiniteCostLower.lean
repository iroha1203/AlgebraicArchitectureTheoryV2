import ResearchLean.AG.OperationRepair.FiniteClosure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Charged execution of the lower finite closure

The value and charge are accumulated by the same folds. Each visited item is
charged thirty-two primitive RAM actions, enough for its relation reads, Boolean
test, index operations, and optional two-cell array update. Enumeration
construction is charged one action per generated item; initialization is
charged one action per relation cell. These are deliberately conservative
charges for the finite-table RAM model, not Lean runtime measurements.
-/

namespace AAT.AG.OperationRepair

namespace FiniteCostLower

variable {n m : Nat} {O : Type*}

def markPassWithCost {α : Type*} (items : List α) (pred : α → Bool)
    (target : α → Fin n × Fin n) (out : RelationTable n) :
    RelationTable n × Nat :=
  items.foldl (fun acc a =>
    (if pred a then acc.1.set (target a).1 (target a).2 true else acc.1,
      acc.2 + 32)) (out, 0)

private theorem markPass_value_aux {α : Type*} (items : List α)
    (pred : α → Bool) (target : α → Fin n × Fin n)
    (out : RelationTable n) (cost : Nat) :
    (items.foldl (fun acc a =>
      (if pred a then acc.1.set (target a).1 (target a).2 true else acc.1,
        acc.2 + 32)) (out, cost)).1 =
      FiniteClosure.markPass items pred target out := by
  induction items generalizing out cost with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.foldl_cons, FiniteClosure.markPass]
      exact ih (if pred a then out.set (target a).1 (target a).2 true else out)
        (cost + 32)

theorem markPassWithCost_value {α : Type*} (items : List α)
    (pred : α → Bool) (target : α → Fin n × Fin n)
    (out : RelationTable n) :
    (markPassWithCost items pred target out).1 =
      FiniteClosure.markPass items pred target out :=
  markPass_value_aux items pred target out 0

private theorem markPass_cost_aux {α : Type*} (items : List α)
    (pred : α → Bool) (target : α → Fin n × Fin n)
    (out : RelationTable n) (cost : Nat) :
    (items.foldl (fun acc a =>
      (if pred a then acc.1.set (target a).1 (target a).2 true else acc.1,
        acc.2 + 32)) (out, cost)).2 = cost + 32 * items.length := by
  induction items generalizing out cost with
  | nil => simp
  | cons a rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      omega

theorem markPassWithCost_cost {α : Type*} (items : List α)
    (pred : α → Bool) (target : α → Fin n × Fin n)
    (out : RelationTable n) :
    (markPassWithCost items pred target out).2 = 32 * items.length := by
  simpa [markPassWithCost] using
    markPass_cost_aux items pred target out 0

def operationItems (n m : Nat) : List (Fin m × (Fin n × Fin n)) :=
  (FiniteClosure.states m).flatMap fun e =>
    (FiniteClosure.pairs n).map fun p => (e, p)

theorem pairs_length (n : Nat) :
    (FiniteClosure.pairs n).length = n * n := by
  simp [FiniteClosure.pairs, FiniteClosure.states, List.length_flatMap]

theorem triples_length (n : Nat) :
    (FiniteClosure.triples n).length = n * n * n := by
  simp [FiniteClosure.triples, FiniteClosure.states,
    List.length_flatMap, Nat.mul_assoc]

theorem operationItems_length (n m : Nat) :
    (operationItems n m).length = m * (n * n) := by
  simp [operationItems, FiniteClosure.pairs, FiniteClosure.states,
    List.length_flatMap]

/-- A costed version of exactly the three passes of one synchronous update. -/
def closeStepWithCost (input : FiniteRepairInput n m O)
    (old : RelationTable n) : RelationTable n × Nat := Id.run do
  let ps := FiniteClosure.pairs n
  let ts := FiniteClosure.triples n
  let os := operationItems n m
  let converse := markPassWithCost ps
    (fun p => old.get p.1 p.2) (fun p => (p.2, p.1)) old
  let transitive := markPassWithCost ts
    (fun p => old.get p.1 p.2.1 && old.get p.2.1 p.2.2)
    (fun p => (p.1, p.2.2)) converse.1
  let image := markPassWithCost os
    (fun p => old.get p.2.1 p.2.2)
    (fun p => (input.step p.1 p.2.1, input.step p.1 p.2.2)) transitive.1
  return (image.1,
    m + n + 1 + n * n + ps.length + ts.length + os.length +
      converse.2 + transitive.2 + image.2)

theorem closeStepWithCost_value (input : FiniteRepairInput n m O)
    (old : RelationTable n) :
    (closeStepWithCost input old).1 = FiniteClosure.closeStep input old := by
  simp [closeStepWithCost, FiniteClosure.closeStep, operationItems,
    markPassWithCost_value]

theorem closeStepWithCost_cost (input : FiniteRepairInput n m O)
    (old : RelationTable n) :
    (closeStepWithCost input old).2 =
      m + n + 1 + n * n +
        33 * (n * n + n * n * n + m * (n * n)) := by
  simp [closeStepWithCost, markPassWithCost_cost,
    pairs_length, triples_length, operationItems_length]
  omega

/-- Each round uses the costed pass result as the next round's input. -/
def roundsWithCost (input : FiniteRepairInput n m O) :
    Nat → RelationTable n × Nat
  | 0 => (FiniteClosure.initial input, n * n + 1)
  | k + 1 =>
      let previous := roundsWithCost input k
      let next := closeStepWithCost input previous.1
      (next.1, previous.2 + next.2)

theorem roundsWithCost_value (input : FiniteRepairInput n m O) (k : Nat) :
    (roundsWithCost input k).1 = FiniteClosure.rounds input k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [roundsWithCost, FiniteClosure.rounds_succ,
        closeStepWithCost_value, ih]

theorem roundsWithCost_cost (input : FiniteRepairInput n m O) (k : Nat) :
    (roundsWithCost input k).2 =
      n * n + 1 +
        k * (m + n + 1 + n * n +
          33 * (n * n + n * n * n + m * (n * n))) := by
  induction k with
  | zero => simp [roundsWithCost]
  | succ k ih =>
      simp only [roundsWithCost, closeStepWithCost_cost, ih,
        Nat.succ_mul]
      omega

def lowerWithCost (input : FiniteRepairInput n m O) :
    RelationTable n × Nat :=
  roundsWithCost input (n * n)

theorem lowerWithCost_value (input : FiniteRepairInput n m O) :
    (lowerWithCost input).1 = FiniteClosure.lower input := by
  exact roundsWithCost_value input (n * n)

theorem lowerWithCost_cost (input : FiniteRepairInput n m O) :
    (lowerWithCost input).2 =
      n * n + 1 +
        (n * n) *
          (m + n + 1 + n * n +
            33 * (n * n + n * n * n + m * (n * n))) := by
  exact roundsWithCost_cost input (n * n)

theorem lowerWithCost_bound (input : FiniteRepairInput n m O) :
    (lowerWithCost input).2 ≤ 200 * (m + 1) * (n + 1) ^ 5 := by
  rw [lowerWithCost_cost]
  have hn : n ≤ n + 1 := Nat.le_succ n
  have hm : m ≤ m + 1 := Nat.le_succ m
  have hN : 0 < n + 1 := by omega
  have hM : 1 ≤ m + 1 := by omega
  have hpow (k : Nat) (hk : k ≤ 5) :
      n ^ k ≤ (m + 1) * (n + 1) ^ 5 := by
    calc
      n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left hn k
      _ ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right hN hk
      _ ≤ (m + 1) * (n + 1) ^ 5 := by
        simpa using Nat.mul_le_mul_right ((n + 1) ^ 5) hM
  have hmn : m * n ^ 4 ≤ (m + 1) * (n + 1) ^ 5 := by
    calc
      m * n ^ 4 ≤ (m + 1) * (n + 1) ^ 4 :=
        Nat.mul_le_mul hm (Nat.pow_le_pow_left hn 4)
      _ ≤ (m + 1) * (n + 1) ^ 5 :=
        Nat.mul_le_mul_left (m + 1)
          (Nat.pow_le_pow_right hN (by decide))
  have hmn2 : m * n ^ 2 ≤ (m + 1) * (n + 1) ^ 5 := by
    calc
      m * n ^ 2 ≤ (m + 1) * (n + 1) ^ 2 :=
        Nat.mul_le_mul hm (Nat.pow_le_pow_left hn 2)
      _ ≤ (m + 1) * (n + 1) ^ 5 :=
        Nat.mul_le_mul_left (m + 1)
          (Nat.pow_le_pow_right hN (by decide))
  have hpoly :
      n * n + 1 + (n * n) *
          (m + n + 1 + n * n +
            33 * (n * n + n * n * n + m * (n * n))) =
        1 + n ^ 2 + m * n ^ 2 + n ^ 3 + n ^ 2 +
          34 * n ^ 4 + 33 * n ^ 5 + 33 * (m * n ^ 4) := by
    ring
  rw [hpoly]
  rw [Nat.mul_assoc]
  have h0 := hpow 0 (by decide)
  have h2 := hpow 2 (by decide)
  have h3 := hpow 3 (by decide)
  have h4 := hpow 4 (by decide)
  have h5 := hpow 5 (by decide)
  norm_num at h0
  omega

end FiniteCostLower

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
