import ResearchLean.AG.OperationRepair.FiniteConstruction
import ResearchLean.AG.OperationRepair.FiniteCostLower
import ResearchLean.AG.OperationRepair.FiniteCostUpper
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Counted decision scan and shared finite repair run

This module places the lower and upper counted loops into one value/counter
program and counts the first-failure search through the actual upper words.
The success-table construction remains outside the counter, so this is a
checkpoint toward G-126 D's complete RAM primitive bound.

Implementation notes: the scan mirrors `List.findSome?` in the original
pair order, returning as soon as the first requested separator is found.
`runWithCount` uses the counted endpoints as values, then assembles the
existing success/failure payload without rerunning either endpoint loop.
The alternative of attaching an independent polynomial to `runRepair` would
not track branch choice and is not used.
-/

namespace AAT.AG.OperationRepair.FiniteCostDecision

variable {n m : Nat} {O : Type*} [DecidableEq O]

/-- Count the first requested pair having a stored separating word. -/
def scan (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    List (Fin n × Fin n) →
      Option (Fin n × Fin n × List (Fin m)) × Nat
  | [] => (none, 1)
  | p :: rest =>
      if input.wants p.1 p.2 then
        match FiniteBehavior.get upperWords p.1 p.2 with
        | some word => (some (p.1, p.2, word), 8)
        | none =>
            let tail := scan input upperWords rest
            (tail.1, tail.2 + 8)
      else
        let tail := scan input upperWords rest
        (tail.1, tail.2 + 8)

omit [DecidableEq O] in
/-- The scan's result is exactly the original first-failure search. -/
theorem scan_value (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m)
    (items : List (Fin n × Fin n)) :
    (scan input upperWords items).1 =
      items.findSome? (fun p =>
        if input.wants p.1 p.2 then
          (FiniteBehavior.get upperWords p.1 p.2).map
            (fun word => (p.1, p.2, word))
        else none) := by
  induction items with
  | nil => rfl
  | cons p rest ih =>
      simp only [scan, List.findSome?_cons]
      by_cases hw : input.wants p.1 p.2 = true
      · simp only [hw, ↓reduceIte]
        cases hget : FiniteBehavior.get upperWords p.1 p.2 with
        | none => simp [ih]
        | some word => simp
      · have hf : input.wants p.1 p.2 = false := Bool.eq_false_iff.mpr hw
        simp [hf, ih]

omit [DecidableEq O] in
/-- Eight charges per visited pair plus one at the exhausted-list branch. -/
theorem scan_cost_le (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m)
    (items : List (Fin n × Fin n)) :
    (scan input upperWords items).2 ≤ 8 * (items.length + 1) := by
  induction items with
  | nil => simp [scan]
  | cons p rest ih =>
      simp only [scan, List.length_cons]
      by_cases hw : input.wants p.1 p.2 = true
      · simp only [hw, ↓reduceIte]
        cases hget : FiniteBehavior.get upperWords p.1 p.2 with
        | none => simp; omega
        | some word => simp
      · have hf : input.wants p.1 p.2 = false := Bool.eq_false_iff.mpr hw
        simp [hf]; omega

omit [DecidableEq O] in
/-- The counted decision result matches `failureSearchFrom` on the same words. -/
theorem scan_pairs_value (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    (scan input upperWords (FiniteClosure.pairs n)).1 =
      FiniteConstruction.failureSearchFrom input upperWords := by
  exact scan_value input upperWords (FiniteClosure.pairs n)

omit [DecidableEq O] in
/-- Uniform bound for the requested-pair decision scan. -/
theorem scan_pairs_cost_le (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    (scan input upperWords (FiniteClosure.pairs n)).2 ≤
      8 * (n * n + 1) := by
  simpa [FiniteCostLower.pairs_length] using
    scan_cost_le input upperWords (FiniteClosure.pairs n)

/-- The counted endpoint values and decision scan feed one output branch. -/
def runWithCount (input : FiniteRepairInput n m O) :
    FiniteConstruction.RunOutput n m O × Nat :=
  let lower := FiniteRamEnumeration.lower input
  let upper := FiniteRamUpper.upper input
  let decision := scan input upper.value (FiniteClosure.pairs n)
  let lowerPart := FiniteConstruction.lowerPartitionFrom input lower.value
    (FiniteRamEnumeration.lower_value input)
  let upperPart := FiniteConstruction.upperPartitionFrom input upper.value
    (FiniteRamUpper.upper_value input)
  let outcome := match decision.1 with
    | some bad => Sum.inl bad
    | none => Sum.inr
        (FiniteConstruction.makeSuccessTablesFrom input lowerPart upperPart)
  (⟨lower.value, upper.value, outcome⟩,
    lower.cost + upper.cost + decision.2)

/-- The partially counted program has exactly the original run output. -/
theorem runWithCount_value (input : FiniteRepairInput n m O) :
    (runWithCount input).1 = FiniteConstruction.runRepair input := by
  simp only [runWithCount, scan_pairs_value]
  rfl

/-- A numeric bound for the counted lower, upper, and decision stages.
The success table generation is excluded from this counter. -/
theorem runWithCount_cost_le (input : FiniteRepairInput n m O) :
    (runWithCount input).2 ≤ 668 * (m + 1) * (n + 1) ^ 5 := by
  let P := (m + 1) * (n + 1) ^ 5
  have hlow : (FiniteRamEnumeration.lower input).cost ≤ 600 * P := by
    simpa only [P, Nat.mul_assoc] using FiniteRamEnumeration.lower_cost_poly input
  have hu := FiniteRamUpper.upper_cost_le input
  have hupper : (FiniteRamUpper.upper input).cost ≤ 60 * P := by
    calc
      (FiniteRamUpper.upper input).cost ≤
          60 * (m + 1) * (n + 1) ^ 4 := hu
      _ ≤ 60 * (m + 1) * (n + 1) ^ 5 := by
        exact Nat.mul_le_mul_left (60 * (m + 1))
          (Nat.pow_le_pow_right (by omega) (by decide))
      _ = 60 * P := by ring
  have hd := scan_pairs_cost_le input (FiniteRamUpper.upper input).value
  have hsqplus : n * n + 1 ≤ (n + 1) ^ 2 := by
    rw [pow_two]
    nlinarith
  have hpow : (n + 1) ^ 2 ≤ (n + 1) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hdecision :
      (scan input (FiniteRamUpper.upper input).value
        (FiniteClosure.pairs n)).2 ≤ 8 * P := by
    calc
      (scan input (FiniteRamUpper.upper input).value
          (FiniteClosure.pairs n)).2 ≤ 8 * (n * n + 1) := hd
      _ ≤ 8 * (n + 1) ^ 5 :=
        Nat.mul_le_mul_left 8 (hsqplus.trans hpow)
      _ ≤ 8 * (m + 1) * (n + 1) ^ 5 := by
        have hm : 1 ≤ m + 1 := by omega
        nlinarith
      _ = 8 * P := by ring
  change (FiniteRamEnumeration.lower input).cost +
      (FiniteRamUpper.upper input).cost +
      (scan input (FiniteRamUpper.upper input).value
        (FiniteClosure.pairs n)).2 ≤ 668 * (m + 1) * (n + 1) ^ 5
  have hsum := Nat.add_le_add (Nat.add_le_add hlow hupper) hdecision
  have hP : 600 * P + 60 * P + 8 * P = 668 * (m + 1) * (n + 1) ^ 5 := by
    dsimp [P]
    ring
  exact hsum.trans (le_of_eq hP)

end AAT.AG.OperationRepair.FiniteCostDecision

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteCostDecision
