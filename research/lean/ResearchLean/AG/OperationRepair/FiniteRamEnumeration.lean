import ResearchLean.AG.OperationRepair.FiniteRamLower

/-!
# Costed finite list enumeration for G-126 D

List construction is made explicit before it is used to drive the lower
closure passes. These combinators charge list-cell allocation and a bounded
index operation for visiting each input item. The trace is ghost bookkeeping
in the same abstract RAM semantics as `FiniteRamPrimitives.Counted`.
-/

namespace AAT.AG.OperationRepair.FiniteRamEnumeration

open FiniteRamPrimitives

variable {α β : Type*}

/-- Construct the standard `Fin n` enumeration, with one new list cell and
one index operation per element. -/
def states (n : Nat) : Counted (List (Fin n)) :=
  ⟨List.finRange n,
    List.replicate n .listCell ++ List.replicate n .indexOp⟩

theorem states_value (n : Nat) :
    (states n).value = FiniteClosure.states n := rfl

theorem states_length (n : Nat) : (states n).value.length = n := by
  simp [states]

theorem states_cost (n : Nat) : (states n).cost = 2 * n := by
  simp [states, Counted.cost]
  omega

/-- Copy the left list onto the right list, charging each copied cons cell
and visit. The right tail is shared. -/
def appendItems : List α → List α → Counted (List α)
  | [], ys => Counted.pure ys
  | x :: xs, ys =>
      let tail := appendItems xs ys
      ⟨x :: tail.value, [.listCell, .indexOp] ++ tail.trace⟩

theorem appendItems_value (xs ys : List α) :
    (appendItems xs ys).value = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendItems, ih]

theorem appendItems_cost (xs ys : List α) :
    (appendItems xs ys).cost = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [appendItems, Counted.cost] at ih ⊢
      omega

/-- Map with a counted callback, allocating one output cons cell and
visiting each input cell exactly once. -/
def mapItems (f : α → Counted β) : List α → Counted (List β)
  | [] => Counted.pure []
  | x :: xs =>
      let head := f x
      let tail := mapItems f xs
      ⟨head.value :: tail.value,
        head.trace ++ [.listCell, .indexOp] ++ tail.trace⟩

theorem mapItems_value (f : α → Counted β) (xs : List α) :
    (mapItems f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapItems, ih]

theorem mapItems_length (f : α → Counted β) (xs : List α) :
    (mapItems f xs).value.length = xs.length := by
  simp [mapItems_value]

theorem mapItems_cost_le (f : α → Counted β) (xs : List α)
    (q : Nat) (hf : ∀ x ∈ xs, (f x).cost ≤ q) :
    (mapItems f xs).cost ≤ xs.length * (q + 2) := by
  induction xs with
  | nil => simp [mapItems, Counted.cost, Counted.pure]
  | cons x xs ih =>
      have hx : (f x).cost ≤ q := hf x (by simp)
      have hxs : ∀ a ∈ xs, (f a).cost ≤ q := by
        intro a ha; exact hf a (by simp [ha])
      have hr := ih hxs
      simp only [mapItems, Counted.cost, List.length_append,
        List.length_cons] at hr ⊢
      simp only [Counted.cost] at hx
      simp only [Nat.succ_mul] at *
      simp only [List.length_nil, Nat.zero_add] at *
      omega

/-- Flat-map by constructing each piece and explicitly copying its cons
cells onto the already constructed remainder. -/
def flatMapItems (f : α → Counted (List β)) :
    List α → Counted (List β)
  | [] => Counted.pure []
  | x :: xs =>
      let head := f x
      let tail := flatMapItems f xs
      let joined := appendItems head.value tail.value
      ⟨joined.value,
        head.trace ++ tail.trace ++ joined.trace ++ [.indexOp]⟩

theorem flatMapItems_value (f : α → Counted (List β)) (xs : List α) :
    (flatMapItems f xs).value = xs.flatMap (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [flatMapItems, appendItems_value, ih]

theorem flatMapItems_cost_le (f : α → Counted (List β))
    (xs : List α) (q ℓ : Nat)
    (hcost : ∀ x ∈ xs, (f x).cost ≤ q)
    (hlen : ∀ x ∈ xs, (f x).value.length ≤ ℓ) :
    (flatMapItems f xs).cost ≤ xs.length * (q + 2 * ℓ + 1) := by
  induction xs with
  | nil => simp [flatMapItems, Counted.cost, Counted.pure]
  | cons x xs ih =>
      have hx : (f x).cost ≤ q := hcost x (by simp)
      have hlx : (f x).value.length ≤ ℓ := hlen x (by simp)
      have hxs : ∀ a ∈ xs, (f a).cost ≤ q := by
        intro a ha; exact hcost a (by simp [ha])
      have hls : ∀ a ∈ xs, (f a).value.length ≤ ℓ := by
        intro a ha; exact hlen a (by simp [ha])
      have hr := ih hxs hls
      have ha := appendItems_cost (f x).value (flatMapItems f xs).value
      simp only [flatMapItems, Counted.cost, List.length_append,
        List.length_cons] at hr ⊢
      simp only [Counted.cost] at hx ha
      simp only [Nat.succ_mul] at *
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at *
      omega

/-- Construct one row of ordered state pairs. -/
def pairRow (n : Nat) (x : Fin n) :
    Counted (List (Fin n × Fin n)) :=
  let ys := states n
  let row := mapItems (fun y => (⟨(x, y), [.indexOp]⟩ :
    Counted (Fin n × Fin n))) ys.value
  ⟨row.value, ys.trace ++ row.trace⟩

theorem pairRow_value (n : Nat) (x : Fin n) :
    (pairRow n x).value = (FiniteClosure.states n).map fun y => (x, y) := by
  simp [pairRow, mapItems_value, states_value]

theorem pairRow_length (n : Nat) (x : Fin n) :
    (pairRow n x).value.length = n := by
  simp [pairRow_value, FiniteClosure.states]

theorem pairRow_cost_le (n : Nat) (x : Fin n) :
    (pairRow n x).cost ≤ 5 * n := by
  have hm := mapItems_cost_le
    (fun y : Fin n => (⟨(x, y), [.indexOp]⟩ :
      Counted (Fin n × Fin n))) (states n).value 1
    (by intro y _; rfl)
  rw [states_length] at hm
  simp only [pairRow, Counted.cost, List.length_append]
  have hs := states_cost n
  dsimp [Counted.cost] at hm hs
  omega

/-- Ordered state pairs, constructed through the charged list primitives. -/
def pairs (n : Nat) : Counted (List (Fin n × Fin n)) :=
  let xs := states n
  let out := flatMapItems (pairRow n) xs.value
  ⟨out.value, xs.trace ++ out.trace⟩

theorem pairs_value (n : Nat) :
    (pairs n).value = FiniteClosure.pairs n := by
  simp [pairs, flatMapItems_value, pairRow_value,
    states_value, FiniteClosure.pairs]

theorem pairs_length (n : Nat) : (pairs n).value.length = n * n := by
  rw [pairs_value]
  exact FiniteCostLower.pairs_length n

theorem pairs_cost_le (n : Nat) :
    (pairs n).cost ≤ 2 * n + n * (5 * n + 2 * n + 1) := by
  have hf := flatMapItems_cost_le (pairRow n) (states n).value
    (5 * n) n
    (by intro x _; exact pairRow_cost_le n x)
    (by intro x _; exact le_of_eq (pairRow_length n x))
  rw [states_length] at hf
  have hs := states_cost n
  simp only [pairs, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hf hs
  omega

/-- For fixed first state, enumerate the remaining two coordinates. -/
def tripleRow (n : Nat) (x : Fin n) :
    Counted (List (Fin n × Fin n × Fin n)) :=
  let ps := pairs n
  let out := mapItems (fun p => (⟨(x, p.1, p.2),
    [.indexOp, .indexOp, .indexOp]⟩ :
      Counted (Fin n × Fin n × Fin n))) ps.value
  ⟨out.value, ps.trace ++ out.trace⟩

theorem tripleRow_value (n : Nat) (x : Fin n) :
    (tripleRow n x).value =
      (FiniteClosure.states n).flatMap fun y =>
        (FiniteClosure.states n).map fun z => (x, y, z) := by
  simp [tripleRow, mapItems_value, pairs_value,
    FiniteClosure.pairs, List.map_flatMap, Function.comp_def]

theorem tripleRow_length (n : Nat) (x : Fin n) :
    (tripleRow n x).value.length = n * n := by
  simp [tripleRow, mapItems_length, pairs_length]

theorem tripleRow_cost_le (n : Nat) (x : Fin n) :
    (tripleRow n x).cost ≤
      (2 * n + n * (5 * n + 2 * n + 1)) + (n * n) * 5 := by
  have hm := mapItems_cost_le
    (fun p : Fin n × Fin n => (⟨(x, p.1, p.2),
      [.indexOp, .indexOp, .indexOp]⟩ :
        Counted (Fin n × Fin n × Fin n))) (pairs n).value 3
    (by intro p _; rfl)
  rw [pairs_length] at hm
  have hp := pairs_cost_le n
  simp only [tripleRow, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hm hp
  omega

/-- Ordered state triples used by the transitivity pass. -/
def triples (n : Nat) : Counted (List (Fin n × Fin n × Fin n)) :=
  let xs := states n
  let out := flatMapItems (tripleRow n) xs.value
  ⟨out.value, xs.trace ++ out.trace⟩

theorem triples_value (n : Nat) :
    (triples n).value = FiniteClosure.triples n := by
  simp [triples, flatMapItems_value, tripleRow_value,
    states_value, FiniteClosure.triples]

theorem triples_length (n : Nat) :
    (triples n).value.length = n * n * n := by
  rw [triples_value]
  exact FiniteCostLower.triples_length n

theorem triples_cost_le (n : Nat) :
    (triples n).cost ≤ 2 * n + n *
      ((2 * n + n * (5 * n + 2 * n + 1) +
        (n * n) * 5) + 2 * (n * n) + 1) := by
  have hf := flatMapItems_cost_le (tripleRow n) (states n).value
    (2 * n + n * (5 * n + 2 * n + 1) + (n * n) * 5)
    (n * n)
    (by intro x _; exact tripleRow_cost_le n x)
    (by intro x _; exact le_of_eq (tripleRow_length n x))
  rw [states_length] at hf
  have hs := states_cost n
  simp only [triples, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hf hs
  omega

/-- Pair list tagged with one operation name. -/
def operationRow (n : Nat) (e : Fin m) :
    Counted (List (Fin m × (Fin n × Fin n))) :=
  let ps := pairs n
  let out := mapItems (fun p => (⟨(e, p), [.indexOp]⟩ :
    Counted (Fin m × (Fin n × Fin n)))) ps.value
  ⟨out.value, ps.trace ++ out.trace⟩

theorem operationRow_value (n : Nat) (e : Fin m) :
    (operationRow n e).value =
      (FiniteClosure.pairs n).map fun p => (e, p) := by
  simp [operationRow, mapItems_value, pairs_value]

theorem operationRow_length (n : Nat) (e : Fin m) :
    (operationRow n e).value.length = n * n := by
  simp [operationRow, mapItems_length, pairs_length]

theorem operationRow_cost_le (n : Nat) (e : Fin m) :
    (operationRow n e).cost ≤
      (2 * n + n * (5 * n + 2 * n + 1)) + (n * n) * 3 := by
  have hm := mapItems_cost_le
    (fun p : Fin n × Fin n => (⟨(e, p), [.indexOp]⟩ :
      Counted (Fin m × (Fin n × Fin n)))) (pairs n).value 1
    (by intro p _; rfl)
  rw [pairs_length] at hm
  have hp := pairs_cost_le n
  simp only [operationRow, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hm hp
  omega

/-- Ordered operation/pair items used by the image pass. -/
def operationItems (n m : Nat) :
    Counted (List (Fin m × (Fin n × Fin n))) :=
  let es := states m
  let out := flatMapItems (operationRow n) es.value
  ⟨out.value, es.trace ++ out.trace⟩

theorem operationItems_value (n m : Nat) :
    (operationItems n m).value = FiniteCostLower.operationItems n m := by
  simp [operationItems, flatMapItems_value, operationRow_value,
    states_value, FiniteCostLower.operationItems]

theorem operationItems_length (n m : Nat) :
    (operationItems n m).value.length = m * (n * n) := by
  rw [operationItems_value]
  exact FiniteCostLower.operationItems_length n m

theorem operationItems_cost_le (n m : Nat) :
    (operationItems n m).cost ≤ 2 * m + m *
      ((2 * n + n * (5 * n + 2 * n + 1) +
        (n * n) * 3) + 2 * (n * n) + 1) := by
  have hf := flatMapItems_cost_le (operationRow n) (states m).value
    (2 * n + n * (5 * n + 2 * n + 1) + (n * n) * 3)
    (n * n)
    (by intro e _; exact operationRow_cost_le n e)
    (by intro e _; exact le_of_eq (operationRow_length n e))
  rw [states_length] at hf
  have hs := states_cost m
  simp only [operationItems, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hf hs
  omega

/-- One synchronous closure round, parametrized by already constructed
enumeration lists. Every predicate still reads only the previous table. -/
def closeStepWithItems (input : FiniteRepairInput n m O)
    (old : RelationTable n)
    (ps : List (Fin n × Fin n))
    (ts : List (Fin n × Fin n × Fin n))
    (os : List (Fin m × (Fin n × Fin n))) :
    Counted (RelationTable n) :=
  let converse := FiniteRamPrimitives.markPass ps
    (fun p => withIndexOps 2 (FiniteRamPrimitives.readRelation old p.1 p.2))
    (fun p => withIndexOps 3 (Counted.pure (p.2, p.1))) old
  let transitive := FiniteRamPrimitives.markPass ts
    (fun p =>
      let first := FiniteRamPrimitives.readRelation old p.1 p.2.1
      let second := FiniteRamPrimitives.readRelation old p.2.1 p.2.2
      withIndexOps 7 ⟨first.value && second.value,
        first.trace ++ second.trace ++ [.boolOp]⟩)
    (fun p => withIndexOps 4 (Counted.pure (p.1, p.2.2))) converse.value
  let image := FiniteRamPrimitives.markPass os
    (fun p => withIndexOps 4
      (FiniteRamPrimitives.readRelation old p.2.1 p.2.2))
    (fun p =>
      let x := FiniteRamPrimitives.readStep input p.1 p.2.1
      let y := FiniteRamPrimitives.readStep input p.1 p.2.2
      withIndexOps 7 ⟨(x.value, y.value), x.trace ++ y.trace⟩)
    transitive.value
  ⟨image.value, converse.trace ++ transitive.trace ++ image.trace⟩

theorem closeStepWithItems_canonical (input : FiniteRepairInput n m O)
    (old : RelationTable n) :
    closeStepWithItems input old (FiniteClosure.pairs n)
      (FiniteClosure.triples n) (FiniteCostLower.operationItems n m) =
        FiniteRamPrimitives.closeStep input old := rfl

/-- The closure pass consumes the values returned by the counted
enumerations; none of its three lists is reconstructed afterward. -/
def closeStep (input : FiniteRepairInput n m O)
    (old : RelationTable n) : Counted (RelationTable n) :=
  let ps := pairs n
  let ts := triples n
  let os := operationItems n m
  let out := closeStepWithItems input old ps.value ts.value os.value
  ⟨out.value, ps.trace ++ ts.trace ++ os.trace ++ out.trace⟩

theorem closeStep_value (input : FiniteRepairInput n m O)
    (old : RelationTable n) :
    (closeStep input old).value = FiniteClosure.closeStep input old := by
  simp only [closeStep, pairs_value, triples_value,
    operationItems_value, closeStepWithItems_canonical,
    FiniteRamPrimitives.closeStep_value]

def enumerationBound (n m : Nat) : Nat :=
  (2 * n + n * (5 * n + 2 * n + 1)) +
    (2 * n + n * ((2 * n + n * (5 * n + 2 * n + 1) +
      (n * n) * 5) + 2 * (n * n) + 1)) +
    (2 * m + m * ((2 * n + n * (5 * n + 2 * n + 1) +
      (n * n) * 3) + 2 * (n * n) + 1))

theorem closeStep_cost_le (input : FiniteRepairInput n m O)
    (old : RelationTable n) :
    (closeStep input old).cost ≤
      enumerationBound n m + FiniteRamLower.roundBound n m := by
  have hp := pairs_cost_le n
  have ht := triples_cost_le n
  have ho := operationItems_cost_le n m
  have hpass := FiniteRamLower.closeStep_cost_le input old
  have hsame : closeStepWithItems input old (pairs n).value
      (triples n).value (operationItems n m).value =
        FiniteRamPrimitives.closeStep input old := by
    rw [pairs_value, triples_value, operationItems_value]
    exact closeStepWithItems_canonical input old
  have hcost : (closeStep input old).cost =
      (pairs n).cost + (triples n).cost +
        (operationItems n m).cost +
          (FiniteRamPrimitives.closeStep input old).cost := by
    simp [closeStep, hsame, Counted.cost, List.length_append,
      Nat.add_assoc]
  rw [hcost]
  change (FiniteRamPrimitives.closeStep input old).cost ≤
    FiniteRamLower.roundBound n m at hpass
  dsimp [enumerationBound]
  omega

/-- Lower rounds now include the charge of constructing the three driving
enumeration lists in each synchronous step. -/
def rounds (input : FiniteRepairInput n m O) :
    Nat → Counted (RelationTable n)
  | 0 => FiniteRamLower.initial input
  | k + 1 =>
      let previous := rounds input k
      let next := closeStep input previous.value
      ⟨next.value, previous.trace ++ next.trace⟩

theorem rounds_value (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).value = FiniteClosure.rounds input k := by
  induction k with
  | zero => exact FiniteRamLower.initial_value input
  | succ k ih =>
      simp only [rounds, FiniteClosure.rounds_succ,
        closeStep_value, ih]

theorem rounds_cost_le (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).cost ≤ n * (5 * n + 1) +
      k * (enumerationBound n m + FiniteRamLower.roundBound n m) := by
  induction k with
  | zero => simp [rounds, FiniteRamLower.initial_cost]
  | succ k ih =>
      have hs := closeStep_cost_le input (rounds input k).value
      have hsum : (rounds input (k + 1)).cost =
          (rounds input k).cost +
            (closeStep input (rounds input k).value).cost := by
        simp [rounds, Counted.cost, List.length_append]
      calc
        (rounds input (k + 1)).cost =
            (rounds input k).cost +
              (closeStep input (rounds input k).value).cost := hsum
        _ ≤ (n * (5 * n + 1) +
            k * (enumerationBound n m + FiniteRamLower.roundBound n m)) +
              (enumerationBound n m + FiniteRamLower.roundBound n m) :=
          Nat.add_le_add ih hs
        _ = n * (5 * n + 1) +
            (k + 1) * (enumerationBound n m +
              FiniteRamLower.roundBound n m) := by
          simp [Nat.succ_mul, Nat.add_assoc]

def lower (input : FiniteRepairInput n m O) :
    Counted (RelationTable n) :=
  rounds input (n * n)

theorem lower_value (input : FiniteRepairInput n m O) :
    (lower input).value = FiniteClosure.lower input := by
  simpa [lower, FiniteClosure.lower_eq_rounds] using
    rounds_value input (n * n)

/-- A degree-five bound for the complete lower table construction,
including the cells of all three enumeration lists at every round. -/
theorem lower_cost_poly (input : FiniteRepairInput n m O) :
    (lower input).cost ≤ 600 * (m + 1) * (n + 1) ^ 5 := by
  have hsq : n ≤ n * n := by
    cases n with
    | zero => simp
    | succ k =>
        have h : 1 ≤ k + 1 := by omega
        have hm := Nat.mul_le_mul_left (k + 1) h
        simpa only [Nat.mul_one] using hm
  have hmn := Nat.mul_le_mul_left m hsq
  have hinit : n * (5 * n + 1) ≤
      3 * (8 * (n * n + n + 1)) := by
    nlinarith
  have hround : enumerationBound n m + FiniteRamLower.roundBound n m ≤
      3 * (m + n + 1 + n * n +
        33 * (n * n + n * n * n + m * (n * n))) := by
    dsimp [enumerationBound, FiniteRamLower.roundBound]
    nlinarith [hsq, hmn]
  have hbudget : n * (5 * n + 1) + (n * n) *
      (enumerationBound n m + FiniteRamLower.roundBound n m) ≤
        3 * (FiniteCostLower.lowerWithCost input).2 := by
    rw [FiniteCostLower.lowerWithCost_cost]
    have hm := Nat.mul_le_mul_left (n * n) hround
    calc
      n * (5 * n + 1) + (n * n) *
          (enumerationBound n m + FiniteRamLower.roundBound n m) ≤
        3 * (8 * (n * n + n + 1)) +
          (n * n) * (3 * (m + n + 1 + n * n +
            33 * (n * n + n * n * n + m * (n * n)))) :=
        Nat.add_le_add hinit hm
      _ = 3 * (8 * (n * n + n + 1) +
          (n * n) * (m + n + 1 + n * n +
            33 * (n * n + n * n * n + m * (n * n)))) := by ring
  have hscaled := Nat.mul_le_mul_left 3
    (FiniteCostLower.lowerWithCost_bound input)
  calc
    (lower input).cost ≤ n * (5 * n + 1) + (n * n) *
        (enumerationBound n m + FiniteRamLower.roundBound n m) :=
      rounds_cost_le input (n * n)
    _ ≤ 3 * (FiniteCostLower.lowerWithCost input).2 := hbudget
    _ ≤ 600 * (m + 1) * (n + 1) ^ 5 := by
      have heq : 3 * (200 * (m + 1) * (n + 1) ^ 5) =
          600 * (m + 1) * (n + 1) ^ 5 := by ring
      simpa only [heq] using hscaled

end AAT.AG.OperationRepair.FiniteRamEnumeration

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteRamEnumeration
