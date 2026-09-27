import ResearchLean.AG.OperationRepair.FiniteRamPrimitives
import ResearchLean.AG.OperationRepair.FiniteCostLower

/-!
# Concrete primitive-trace bound for one lower closure round

This module instantiates the generic marking-pass bound with the actual
converse, transitivity, and operation-image callbacks, then accounts for
initial-table construction and all lower rounds. Enumeration-list cell
construction remains a separate obligation.
-/

namespace AAT.AG.OperationRepair.FiniteRamLower

open FiniteRamPrimitives

variable {n m : Nat} {O : Type*}

theorem readRelation_cost (table : RelationTable n) (x y : Fin n) :
    (FiniteRamPrimitives.readRelation table x y).cost = 2 := rfl

theorem withIndexOps_cost (q : Nat) (a : Counted α) :
    (withIndexOps q a).cost = q + a.cost := by
  simp [withIndexOps, Counted.cost]

theorem converse_pred_cost (old : RelationTable n) (p : Fin n × Fin n) :
    (withIndexOps 2 (FiniteRamPrimitives.readRelation old p.1 p.2)).cost = 4 := by
  simp [withIndexOps_cost, readRelation_cost]

theorem converse_target_cost (p : Fin n × Fin n) :
    (withIndexOps 3 (Counted.pure (p.2, p.1))).cost = 3 := by
  simp [withIndexOps, Counted.cost, Counted.pure]

theorem transitive_pred_cost (old : RelationTable n)
    (p : Fin n × Fin n × Fin n) :
    (withIndexOps 7
      (let first := FiniteRamPrimitives.readRelation old p.1 p.2.1
       let second := FiniteRamPrimitives.readRelation old p.2.1 p.2.2
       ⟨first.value && second.value,
         first.trace ++ second.trace ++ [.boolOp]⟩)).cost = 12 := by
  simp [withIndexOps, Counted.cost, FiniteRamPrimitives.readRelation,
    FiniteRamPrimitives.read]

theorem transitive_target_cost (p : Fin n × Fin n × Fin n) :
    (withIndexOps 4 (Counted.pure (p.1, p.2.2))).cost = 4 := by
  simp [withIndexOps, Counted.cost, Counted.pure]

theorem image_pred_cost (old : RelationTable n)
    (p : Fin m × (Fin n × Fin n)) :
    (withIndexOps 4 (FiniteRamPrimitives.readRelation old p.2.1 p.2.2)).cost = 6 := by
  simp [withIndexOps_cost, readRelation_cost]

theorem image_target_cost (input : FiniteRepairInput n m O)
    (p : Fin m × (Fin n × Fin n)) :
    (withIndexOps 7
      (let x := readStep input p.1 p.2.1
       let y := readStep input p.1 p.2.2
       ⟨(x.value, y.value), x.trace ++ y.trace⟩)).cost = 11 := by
  simp [withIndexOps, Counted.cost, readStep, FiniteRamPrimitives.read]

/-- The three copies and every visited item in a synchronous round have a
concrete primitive-trace bound. Enumeration-list creation is not included. -/
theorem closeStep_cost_le (input : FiniteRepairInput n m O)
    (old : RelationTable n) :
    (FiniteRamPrimitives.closeStep input old).cost ≤
      3 * (n * (2 * n + 2)) + 13 * (n * n) +
        22 * (n * n * n) + 23 * (m * (n * n)) := by
  let converse := FiniteRamPrimitives.markPass (FiniteClosure.pairs n)
    (fun p => withIndexOps 2 (FiniteRamPrimitives.readRelation old p.1 p.2))
    (fun p => withIndexOps 3 (Counted.pure (p.2, p.1))) old
  let transitive := FiniteRamPrimitives.markPass (FiniteClosure.triples n)
    (fun p =>
      let first := FiniteRamPrimitives.readRelation old p.1 p.2.1
      let second := FiniteRamPrimitives.readRelation old p.2.1 p.2.2
      withIndexOps 7 ⟨first.value && second.value,
        first.trace ++ second.trace ++ [.boolOp]⟩)
    (fun p => withIndexOps 4 (Counted.pure (p.1, p.2.2))) converse.value
  let image := FiniteRamPrimitives.markPass
    ((FiniteClosure.states m).flatMap fun e =>
      (FiniteClosure.pairs n).map fun p => (e, p))
    (fun p => withIndexOps 4
      (FiniteRamPrimitives.readRelation old p.2.1 p.2.2))
    (fun p =>
      let x := readStep input p.1 p.2.1
      let y := readStep input p.1 p.2.2
      withIndexOps 7 ⟨(x.value, y.value), x.trace ++ y.trace⟩)
    transitive.value
  have hc : converse.cost ≤ n * (2 * n + 2) +
      (FiniteClosure.pairs n).length * 13 := by
    apply FiniteRamPrimitives.markPass_cost_le _ _ _ _ 4 3
    · intro p _; exact converse_pred_cost old p |>.le
    · intro p _; exact converse_target_cost p |>.le
  have ht : transitive.cost ≤ n * (2 * n + 2) +
      (FiniteClosure.triples n).length * 22 := by
    apply FiniteRamPrimitives.markPass_cost_le _ _ _ _ 12 4
    · intro p _; exact transitive_pred_cost old p |>.le
    · intro p _; exact transitive_target_cost p |>.le
  have hi : image.cost ≤ n * (2 * n + 2) +
      ((FiniteClosure.states m).flatMap fun e =>
        (FiniteClosure.pairs n).map fun p => (e, p)).length * 23 := by
    apply FiniteRamPrimitives.markPass_cost_le _ _ _ _ 6 11
    · intro p _; exact image_pred_cost old p |>.le
    · intro p _; exact image_target_cost input p |>.le
  have hsum : (FiniteRamPrimitives.closeStep input old).cost =
      converse.cost + transitive.cost + image.cost := by
    simp [FiniteRamPrimitives.closeStep, converse, transitive, image,
      Counted.cost, List.length_append, Nat.add_assoc]
  rw [hsum]
  rw [FiniteCostLower.pairs_length] at hc
  rw [FiniteCostLower.triples_length] at ht
  change image.cost ≤ n * (2 * n + 2) +
    (FiniteCostLower.operationItems n m).length * 23 at hi
  rw [FiniteCostLower.operationItems_length] at hi
  omega

/-- Construct the initial diagonal/request table. Every output Boolean cell
charges two request-table reads, one index equality, one Boolean operation,
and one table-cell allocation; each outer row charges one allocation. -/
def initialCell (input : FiniteRepairInput n m O) (x y : Fin n) :
    Counted Bool :=
  let equality : Counted Bool := ⟨decide (x = y), [.indexOp]⟩
  let requested := FiniteRamPrimitives.readRelation input.request x y
  ⟨equality.value || requested.value,
    equality.trace ++ requested.trace ++ [.boolOp, .tableCell]⟩

theorem initialCell_value (input : FiniteRepairInput n m O) (x y : Fin n) :
    (initialCell input x y).value =
      (decide (x = y) || input.wants x y) := rfl

theorem initialCell_cost (input : FiniteRepairInput n m O) (x y : Fin n) :
    (initialCell input x y).cost = 5 := rfl

def initial (input : FiniteRepairInput n m O) : Counted (RelationTable n) :=
  ⟨FiniteTable.ofFn fun x =>
      FiniteTable.ofFn fun y => (initialCell input x y).value,
    (List.finRange n).flatMap fun x =>
      ((List.finRange n).flatMap fun y => (initialCell input x y).trace) ++
        [.tableCell]⟩

theorem initial_value (input : FiniteRepairInput n m O) :
    (initial input).value = FiniteClosure.initial input := by
  apply RelationTable.ext
  intro x y
  simp [initial, initialCell_value, FiniteClosure.initial,
    RelationTable.get]

theorem initial_cost (input : FiniteRepairInput n m O) :
    (initial input).cost = n * (5 * n + 1) := by
  have hc (x y : Fin n) : (initialCell input x y).trace.length = 5 :=
    initialCell_cost input x y
  simp [initial, Counted.cost, List.length_flatMap, hc,
    List.length_append, Nat.mul_add]
  omega

def roundBound (n m : Nat) : Nat :=
  3 * (n * (2 * n + 2)) + 13 * (n * n) +
    22 * (n * n * n) + 23 * (m * (n * n))

/-- The next round consumes the value made by the preceding round. -/
def rounds (input : FiniteRepairInput n m O) :
    Nat → Counted (RelationTable n)
  | 0 => initial input
  | k + 1 =>
      let previous := rounds input k
      let next := FiniteRamPrimitives.closeStep input previous.value
      ⟨next.value, previous.trace ++ next.trace⟩

theorem rounds_value (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).value = FiniteClosure.rounds input k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [rounds, FiniteClosure.rounds_succ,
        FiniteRamPrimitives.closeStep_value, ih]

theorem rounds_cost_le (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).cost ≤ n * (5 * n + 1) + k * roundBound n m := by
  induction k with
  | zero => simp [rounds, initial_cost]
  | succ k ih =>
      have hs := closeStep_cost_le input (rounds input k).value
      change (FiniteRamPrimitives.closeStep input (rounds input k).value).cost ≤
        roundBound n m at hs
      have hsum : (rounds input (k + 1)).cost =
          (rounds input k).cost +
            (FiniteRamPrimitives.closeStep input (rounds input k).value).cost := by
        simp [rounds, Counted.cost, List.length_append]
      calc
        (rounds input (k + 1)).cost =
            (rounds input k).cost +
              (FiniteRamPrimitives.closeStep input (rounds input k).value).cost :=
          hsum
        _ ≤ (n * (5 * n + 1) + k * roundBound n m) +
            roundBound n m := Nat.add_le_add ih hs
        _ = n * (5 * n + 1) + (k + 1) * roundBound n m := by
          simp [Nat.succ_mul, Nat.add_assoc]

def lower (input : FiniteRepairInput n m O) : Counted (RelationTable n) :=
  rounds input (n * n)

theorem lower_value (input : FiniteRepairInput n m O) :
    (lower input).value = FiniteClosure.lower input := by
  simpa [lower, FiniteClosure.lower_eq_rounds] using
    rounds_value input (n * n)

theorem lower_cost_le (input : FiniteRepairInput n m O) :
    (lower input).cost ≤
      n * (5 * n + 1) + (n * n) * roundBound n m :=
  rounds_cost_le input (n * n)

/-- The recorded lower trace fits a uniform degree-five envelope.
Enumeration-list creation remains outside this trace and this bound is
not the full D RAM-cost theorem.
The older numerical counter is used only for its established arithmetic
inequality, not as a certificate of primitive coverage. -/
theorem lower_trace_cost_poly (input : FiniteRepairInput n m O) :
    (lower input).cost ≤ 200 * (m + 1) * (n + 1) ^ 5 := by
  have hsq : n ≤ n * n := by
    cases n with
    | zero => simp
    | succ k =>
        have h : 1 ≤ k + 1 := by omega
        have hm := Nat.mul_le_mul_left (k + 1) h
        simpa only [Nat.mul_one] using hm
  have hinit : n * (5 * n + 1) ≤ 8 * (n * n + n + 1) := by
    nlinarith
  have hround : roundBound n m ≤
      m + n + 1 + n * n +
        33 * (n * n + n * n * n + m * (n * n)) := by
    dsimp [roundBound]
    nlinarith [hsq]
  have hbudget :
      n * (5 * n + 1) + (n * n) * roundBound n m ≤
        (FiniteCostLower.lowerWithCost input).2 := by
    rw [FiniteCostLower.lowerWithCost_cost]
    exact Nat.add_le_add hinit (Nat.mul_le_mul_left (n * n) hround)
  exact (lower_cost_le input |>.trans hbudget).trans
    (FiniteCostLower.lowerWithCost_bound input)

end AAT.AG.OperationRepair.FiniteRamLower

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteRamLower
