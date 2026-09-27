import ResearchLean.AG.OperationRepair.FiniteBehavior
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Counter instrumentation for the upper word-discovery loop

Each visited operation is charged in the same recursive search that returns
the first discovered word. The counted table cells are then assembled into
the synchronous next table. This is a checkpoint toward the full RAM model;
the relation between table construction and all RAM primitives remains open.
-/

namespace AAT.AG.OperationRepair.FiniteCostUpper

variable {n m : Nat} {O : Type*} [DecidableEq O]

def scan (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m)
    (x y : Fin n) : List (Fin m) → Option (List (Fin m)) × Nat
  | [] => (none, 1)
  | e :: rest =>
      match FiniteBehavior.get old (input.step e x) (input.step e y) with
      | some word => (some (e :: word), 8)
      | none =>
          let tail := scan input old x y rest
          (tail.1, tail.2 + 8)

theorem scan_value (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m)
    (x y : Fin n) (items : List (Fin m)) :
    (scan input old x y items).1 =
      items.findSome? (fun e =>
        (FiniteBehavior.get old (input.step e x) (input.step e y)).map (e :: ·)) := by
  induction items with
  | nil => rfl
  | cons e rest ih =>
      simp only [scan, List.findSome?_cons]
      cases h : FiniteBehavior.get old (input.step e x) (input.step e y) with
      | none => simp [h, ih]
      | some word => simp [h]

theorem scan_cost_le (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m)
    (x y : Fin n) (items : List (Fin m)) :
    (scan input old x y items).2 ≤ 8 * (items.length + 1) := by
  induction items with
  | nil => simp [scan]
  | cons e rest ih =>
      simp only [scan, List.length_cons]
      cases h : FiniteBehavior.get old (input.step e x) (input.step e y) with
      | some word => simp [h]
      | none => simp [h]; omega

def cell (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) (x y : Fin n) :
    Option (List (Fin m)) × Nat :=
  match FiniteBehavior.get old x y with
  | some word => (some word, 2)
  | none =>
      let found := scan input old x y (List.finRange m)
      (found.1, found.2 + 2)

theorem cell_value (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) (x y : Fin n) :
    (cell input old x y).1 = FiniteBehavior.get (FiniteBehavior.step input old) x y := by
  rw [FiniteBehavior.step_get]
  cases h : FiniteBehavior.get old x y with
  | some word => simp [cell, h]
  | none => simp [cell, h, scan_value]

theorem cell_cost_le (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) (x y : Fin n) :
    (cell input old x y).2 ≤ 10 * (m + 1) := by
  cases h : FiniteBehavior.get old x y with
  | some word => simp [cell, h]; omega
  | none =>
      simp only [cell, h]
      have hs := scan_cost_le input old x y (List.finRange m)
      simp only [List.length_finRange] at hs
      omega

/-- Each cell is computed once; the payload projection and sum read that
same table of counted cells. -/
def step (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) :
    FiniteBehavior.WitnessTable n m × Nat :=
  let cells : FiniteTable (FiniteTable (Option (List (Fin m)) × Nat) n) n :=
    FiniteTable.ofFn fun x => FiniteTable.ofFn fun y => cell input old x y
  let words : FiniteBehavior.WitnessTable n m :=
    FiniteTable.ofFn fun x => FiniteTable.ofFn fun y => (cells.get x).get y |>.1
  let charges := ∑ x : Fin n, ∑ y : Fin n, ((cells.get x).get y).2
  (words, n * n * 4 + charges)

theorem step_value (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) :
    (step input old).1 = FiniteBehavior.step input old := by
  apply FiniteTable.ext
  intro x
  apply FiniteTable.ext
  intro y
  simp only [step, FiniteTable.get_ofFn]
  exact cell_value input old x y

theorem step_cost_le (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) :
    (step input old).2 ≤ 14 * (m + 1) * (n * n) := by
  have hc : ∀ x y : Fin n,
      (cell input old x y).2 ≤ 10 * (m + 1) :=
    fun x y => cell_cost_le input old x y
  have hsum : (∑ x : Fin n, ∑ y : Fin n,
      (cell input old x y).2) ≤ n * n * (10 * (m + 1)) := by
    calc
      (∑ x : Fin n, ∑ y : Fin n, (cell input old x y).2)
          ≤ ∑ _x : Fin n, ∑ _y : Fin n, 10 * (m + 1) := by
            apply Finset.sum_le_sum
            intro x _
            apply Finset.sum_le_sum
            intro y _
            exact hc x y
      _ = n * n * (10 * (m + 1)) := by simp [Finset.sum_const_zero, Nat.mul_assoc]
  simp only [step, FiniteTable.get_ofFn]
  change n * n * 4 +
      (∑ x : Fin n, ∑ y : Fin n, (cell input old x y).2) ≤
        14 * (m + 1) * (n * n)
  calc
    n * n * 4 + (∑ x : Fin n, ∑ y : Fin n,
        (cell input old x y).2)
        ≤ n * n * 4 + n * n * (10 * (m + 1)) :=
          Nat.add_le_add_left hsum _
    _ = n * n * (4 + 10 * (m + 1)) := by ring
    _ ≤ n * n * (14 * (m + 1)) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 14 * (m + 1) * (n * n) := by ring

/-- The same counted successor table is fed to the next round. -/
def rounds (input : FiniteRepairInput n m O) :
    Nat → FiniteBehavior.WitnessTable n m × Nat
  | 0 => (FiniteBehavior.initial input, 4 * (n * n + 1))
  | k + 1 =>
      let previous := rounds input k
      let next := step input previous.1
      (next.1, previous.2 + next.2)

theorem rounds_value (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).1 = FiniteBehavior.rounds input k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [rounds, FiniteBehavior.rounds_succ, step_value, ih]

theorem rounds_cost_le (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).2 ≤
      4 * (n * n + 1) + k * (14 * (m + 1) * (n * n)) := by
  induction k with
  | zero => simp [rounds]
  | succ k ih =>
      have hs := step_cost_le input (rounds input k).1
      change (rounds input k).2 +
        (step input (rounds input k).1).2 ≤
          4 * (n * n + 1) + (k + 1) * (14 * (m + 1) * (n * n))
      calc
        (rounds input k).2 +
            (step input (rounds input k).1).2 ≤
          (4 * (n * n + 1) + k * (14 * (m + 1) * (n * n))) +
            14 * (m + 1) * (n * n) := Nat.add_le_add ih hs
        _ = 4 * (n * n + 1) + (k + 1) *
          (14 * (m + 1) * (n * n)) := by ring

def upper (input : FiniteRepairInput n m O) :
    FiniteBehavior.WitnessTable n m × Nat :=
  rounds input (n * n - 1)

theorem upper_value (input : FiniteRepairInput n m O) :
    (upper input).1 = FiniteBehavior.upper input :=
  rounds_value input (n * n - 1)

theorem upper_cost_le (input : FiniteRepairInput n m O) :
    (upper input).2 ≤ 18 * (m + 1) * (n + 1) ^ 4 := by
  have h := rounds_cost_le input (n * n - 1)
  have hsq : n * n ≤ (n + 1) ^ 2 := by
    simpa only [pow_two] using
      Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  have hsqplus : n * n + 1 ≤ (n + 1) ^ 2 := by
    rw [pow_two]
    nlinarith
  have hpow : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hinit : 4 * (n * n + 1) ≤
      4 * (m + 1) * (n + 1) ^ 4 := by
    calc
      4 * (n * n + 1) ≤ 4 * (n + 1) ^ 4 := by
        exact Nat.mul_le_mul_left 4 (hsqplus.trans hpow)
      _ ≤ 4 * (m + 1) * (n + 1) ^ 4 := by
        have hm : 1 ≤ m + 1 := by omega
        nlinarith
  have hloop : (n * n - 1) * (14 * (m + 1) * (n * n)) ≤
      14 * (m + 1) * (n + 1) ^ 4 := by
    have hmul : (n * n - 1) * (n * n) ≤ (n + 1) ^ 4 := by
      calc
        (n * n - 1) * (n * n) ≤ (n + 1) ^ 2 * (n + 1) ^ 2 := by
          exact Nat.mul_le_mul (by omega : n * n - 1 ≤ (n + 1) ^ 2) hsq
        _ = (n + 1) ^ 4 := by ring
    calc
      (n * n - 1) * (14 * (m + 1) * (n * n)) =
          14 * (m + 1) * ((n * n - 1) * (n * n)) := by ring
      _ ≤ 14 * (m + 1) * (n + 1) ^ 4 :=
        Nat.mul_le_mul_left _ hmul
  change (upper input).2 ≤ 18 * (m + 1) * (n + 1) ^ 4
  have htotal := Nat.add_le_add hinit hloop
  have hsum : 4 * (m + 1) * (n + 1) ^ 4 +
      14 * (m + 1) * (n + 1) ^ 4 =
      18 * (m + 1) * (n + 1) ^ 4 := by ring
  exact h.trans (by simpa [hsum] using htotal)

end AAT.AG.OperationRepair.FiniteCostUpper

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteCostUpper
