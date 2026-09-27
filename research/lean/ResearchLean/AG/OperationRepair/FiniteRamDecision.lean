import ResearchLean.AG.OperationRepair.FiniteRamUpper

/-!
# Primitive trace for the first failed repair request

The ordered pair list and first-success scan are costed in the same value
branch. A returned witness word is shared with the stored upper table;
copying it to an external output remains a separate obligation.
-/

namespace AAT.AG.OperationRepair.FiniteRamDecision

open FiniteRamPrimitives
variable {n m : Nat} {O : Type*} [DecidableEq O]

/-- Inspect requested pairs in order. An upper word is read only when the
request bit is true; the first stored word determines the result. -/
def scan (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    List (Fin n × Fin n) →
      Counted (Option (Fin n × Fin n × List (Fin m)))
  | [] => ⟨none, [.boolOp]⟩
  | p :: rest =>
      if input.wants p.1 p.2 then
        match FiniteBehavior.get upperWords p.1 p.2 with
        | some word =>
            ⟨some (p.1, p.2, word),
              [.tableRead, .tableRead, .boolOp, .indexOp, .indexOp,
                .tableRead, .tableRead, .boolOp, .indexOp]⟩
        | none =>
            let tail := scan input upperWords rest
            ⟨tail.value,
              [.tableRead, .tableRead, .boolOp, .indexOp, .indexOp,
                .tableRead, .tableRead, .boolOp, .indexOp] ++ tail.trace⟩
      else
        let tail := scan input upperWords rest
        ⟨tail.value,
          [.tableRead, .tableRead, .boolOp, .indexOp, .indexOp] ++ tail.trace⟩

omit [DecidableEq O] in
theorem scan_value (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m)
    (items : List (Fin n × Fin n)) :
    (scan input upperWords items).value =
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
theorem scan_cost_le (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m)
    (items : List (Fin n × Fin n)) :
    (scan input upperWords items).cost ≤ 10 * (items.length + 1) := by
  induction items with
  | nil => simp [scan, Counted.cost]
  | cons p rest ih =>
      simp only [scan, List.length_cons]
      by_cases hw : input.wants p.1 p.2 = true
      · simp only [hw, ↓reduceIte]
        cases hget : FiniteBehavior.get upperWords p.1 p.2 with
        | none => simp [Counted.cost] at ih ⊢; omega
        | some word => simp [Counted.cost]; omega
      · have hf : input.wants p.1 p.2 = false := Bool.eq_false_iff.mpr hw
        simp [hf, Counted.cost] at ih ⊢
        omega

/-- Construct the ordered pair list and consume that same list in the scan. -/
def decision (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    Counted (Option (Fin n × Fin n × List (Fin m))) :=
  let pairs := FiniteRamEnumeration.pairs n
  let found := scan input upperWords pairs.value
  ⟨found.value, pairs.trace ++ found.trace⟩

theorem decision_value (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    (decision input upperWords).value =
      (FiniteClosure.pairs n).findSome? (fun p =>
        if input.wants p.1 p.2 then
          (FiniteBehavior.get upperWords p.1 p.2).map
            (fun word => (p.1, p.2, word))
        else none) := by
  simp [decision, scan_value, FiniteRamEnumeration.pairs_value]

theorem decision_cost_le (input : FiniteRepairInput n m O)
    (upperWords : FiniteBehavior.WitnessTable n m) :
    (decision input upperWords).cost ≤ 30 * (n + 1) ^ 2 := by
  have hp := FiniteRamEnumeration.pairs_cost_le n
  have hs := scan_cost_le input upperWords
    (FiniteRamEnumeration.pairs n).value
  rw [FiniteRamEnumeration.pairs_length] at hs
  have hsq : n * n ≤ (n + 1) ^ 2 := by
    simpa only [pow_two] using
      Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  simp only [decision, Counted.cost, List.length_append] at ⊢
  dsimp [Counted.cost] at hp hs
  nlinarith

end AAT.AG.OperationRepair.FiniteRamDecision

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteRamDecision
