import ResearchLean.AG.OperationRepair.FiniteRamEnumeration
import ResearchLean.AG.OperationRepair.FiniteCostUpper

/-! # Primitive trace for upper witness-word discovery

The scan consumes the counted operation-name list and stores the first word
it constructs. Table assembly and whole-round traces remain separate. -/

namespace AAT.AG.OperationRepair.FiniteRamUpper

open FiniteRamPrimitives
variable {n m : Nat} {O : Type*} [DecidableEq O]

/-- Charge transition reads, witness reads, branch tests, and a new word cell. -/
def scan (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m)
    (x y : Fin n) : List (Fin m) → Counted (Option (List (Fin m)))
  | [] => ⟨none, [.boolOp]⟩
  | e :: rest =>
      match FiniteBehavior.get old (input.step e x) (input.step e y) with
      | some word =>
          ⟨some (e :: word),
            [.indexOp, .indexOp, .tableRead, .tableRead,
              .tableRead, .tableRead, .tableRead, .tableRead,
              .boolOp, .wordCell]⟩
      | none =>
          let tail := scan input old x y rest
          ⟨tail.value,
            [.indexOp, .indexOp, .tableRead, .tableRead,
              .tableRead, .tableRead, .tableRead, .tableRead,
              .boolOp] ++ tail.trace⟩

omit [DecidableEq O] in
theorem scan_value (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m)
    (x y : Fin n) (items : List (Fin m)) :
    (scan input old x y items).value =
      items.findSome? (fun e =>
        (FiniteBehavior.get old (input.step e x) (input.step e y)).map (e :: ·)) := by
  induction items with
  | nil => rfl
  | cons e rest ih =>
      simp only [scan, List.findSome?_cons]
      cases h : FiniteBehavior.get old (input.step e x) (input.step e y) with
      | none => simp [ih]
      | some word => simp

omit [DecidableEq O] in
theorem scan_cost_le (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m)
    (x y : Fin n) (items : List (Fin m)) :
    (scan input old x y items).cost ≤ 10 * (items.length + 1) := by
  induction items with
  | nil => simp [scan, Counted.cost]
  | cons e rest ih =>
      simp only [scan, List.length_cons]
      cases h : FiniteBehavior.get old (input.step e x) (input.step e y) with
      | some word => simp [Counted.cost]
      | none => simp [Counted.cost] at ih ⊢; omega

/-- Reuse an old word or search the constructed operation-name list. -/
def cell (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) (x y : Fin n) :
    Counted (Option (List (Fin m))) :=
  match FiniteBehavior.get old x y with
  | some word => ⟨some word, [.tableRead, .tableRead, .boolOp]⟩
  | none =>
      let names := FiniteRamEnumeration.states m
      let found := scan input old x y names.value
      ⟨found.value,
        [.tableRead, .tableRead, .boolOp] ++ names.trace ++ found.trace⟩

theorem cell_value (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) (x y : Fin n) :
    (cell input old x y).value =
      FiniteBehavior.get (FiniteBehavior.step input old) x y := by
  rw [FiniteBehavior.step_get]
  cases h : FiniteBehavior.get old x y with
  | some word => simp [cell, h]
  | none => simp [cell, h, scan_value, FiniteRamEnumeration.states_value,
      FiniteClosure.states]

omit [DecidableEq O] in
theorem cell_cost_le (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) (x y : Fin n) :
    (cell input old x y).cost ≤ 16 * (m + 1) := by
  cases h : FiniteBehavior.get old x y with
  | some word => simp [cell, h, Counted.cost]; omega
  | none =>
      have hn := FiniteRamEnumeration.states_cost m
      have hs := scan_cost_le input old x y
        (FiniteRamEnumeration.states m).value
      rw [FiniteRamEnumeration.states_length] at hs
      simp only [cell, h, Counted.cost, List.length_append, List.length_cons,
        List.length_nil] at hn hs ⊢
      omega

/-- Construct the next table from counted cells. Both the output and the
trace projection read the same stored cell results. The pair-list trace
accounts for index enumeration; table allocation and trace aggregation are
charged separately. -/
def step (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) :
    Counted (FiniteBehavior.WitnessTable n m) :=
  let pairs := FiniteRamEnumeration.pairs n
  let cells : FiniteTable
      (FiniteTable (Counted (Option (List (Fin m)))) n) n :=
    FiniteTable.ofFn fun x => FiniteTable.ofFn fun y => cell input old x y
  let words : FiniteBehavior.WitnessTable n m :=
    FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
      ((cells.get x).get y).value
  let cellTraces := pairs.value.flatMap fun p =>
    ((cells.get p.1).get p.2).trace
  ⟨words,
    pairs.trace ++ cellTraces ++
      List.replicate (2 * n * n + 2 * n) .tableCell ++
      List.replicate (2 * n * n) .tableRead⟩

/-- Erasing the counted cells gives the accepted synchronous upper step. -/
theorem step_value (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) :
    (step input old).value = FiniteBehavior.step input old := by
  apply FiniteTable.ext
  intro x
  apply FiniteTable.ext
  intro y
  simp only [step, FiniteTable.get_ofFn]
  exact cell_value input old x y

/-- The trace includes every stored cell's branch trace in ordered pair
enumeration, along with table construction and projection charges. -/
theorem step_cost_components (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) :
    (step input old).cost =
      (FiniteRamEnumeration.pairs n).cost +
      ((FiniteRamEnumeration.pairs n).value.flatMap fun p =>
        (cell input old p.1 p.2).trace).length +
      (2 * n * n + 2 * n) + (2 * n * n) := by
  simp [step, Counted.cost, List.length_append]
  omega

private theorem cellTraces_cost_le (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m)
    (items : List (Fin n × Fin n)) :
    (items.flatMap fun p => (cell input old p.1 p.2).trace).length ≤
      items.length * (16 * (m + 1)) := by
  induction items with
  | nil => simp
  | cons p rest ih =>
      have hc := cell_cost_le input old p.1 p.2
      dsimp [Counted.cost] at hc
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.add_le_add hc ih

/-- A uniform bound for one complete counted upper round, including the
ordered cell traces, pair-index enumeration and both table allocations. -/
theorem step_cost_le (input : FiniteRepairInput n m O)
    (old : FiniteBehavior.WitnessTable n m) :
    (step input old).cost ≤ 40 * (m + 1) * (n + 1) ^ 2 := by
  have ht := cellTraces_cost_le input old (FiniteRamEnumeration.pairs n).value
  rw [FiniteRamEnumeration.pairs_length] at ht
  have hp := FiniteRamEnumeration.pairs_cost_le n
  have hc := step_cost_components input old
  have hsq : n * n ≤ (n + 1) ^ 2 := by
    simpa only [pow_two] using
      Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  have hn : n ≤ (n + 1) ^ 2 := by nlinarith [sq_nonneg (n : ℤ)]
  have hm : 1 ≤ m + 1 := by omega
  nlinarith

/-- Construct the initial witness cell from two observation reads and one
observation equality test. The empty word needs no allocated list cell. -/
def initialCell (input : FiniteRepairInput n m O) (x y : Fin n) :
    Counted (Option (List (Fin m))) :=
  let equal := observationEqual (input.observe x) (input.observe y)
  ⟨if equal.value then none else some [],
    [.tableRead, .tableRead] ++ equal.trace ++ [.boolOp]⟩

theorem initialCell_value (input : FiniteRepairInput n m O) (x y : Fin n) :
    (initialCell input x y).value =
      FiniteBehavior.get (FiniteBehavior.initial input) x y := by
  simp [initialCell, observationEqual, FiniteBehavior.initial_get]

theorem initialCell_cost (input : FiniteRepairInput n m O) (x y : Fin n) :
    (initialCell input x y).cost = 4 := by
  simp [initialCell, Counted.cost, observationEqual]

/-- Store every counted initial cell once, then project the witness table. -/
def initial (input : FiniteRepairInput n m O) :
    Counted (FiniteBehavior.WitnessTable n m) :=
  let pairs := FiniteRamEnumeration.pairs n
  let cells : FiniteTable
      (FiniteTable (Counted (Option (List (Fin m)))) n) n :=
    FiniteTable.ofFn fun x => FiniteTable.ofFn fun y => initialCell input x y
  let words : FiniteBehavior.WitnessTable n m :=
    FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
      ((cells.get x).get y).value
  let cellTraces := pairs.value.flatMap fun p =>
    ((cells.get p.1).get p.2).trace
  ⟨words,
    pairs.trace ++ cellTraces ++
      List.replicate (2 * n * n + 2 * n) .tableCell ++
      List.replicate (2 * n * n) .tableRead⟩

theorem initial_value (input : FiniteRepairInput n m O) :
    (initial input).value = FiniteBehavior.initial input := by
  apply FiniteTable.ext
  intro x
  apply FiniteTable.ext
  intro y
  simp only [initial, FiniteTable.get_ofFn]
  exact initialCell_value input x y

theorem initial_cost_le (input : FiniteRepairInput n m O) :
    (initial input).cost ≤ 20 * (n + 1) ^ 2 := by
  have hc : ((FiniteRamEnumeration.pairs n).value.flatMap fun p =>
      (initialCell input p.1 p.2).trace).length = 4 * (n * n) := by
    have hcell : ∀ p : Fin n × Fin n,
        (initialCell input p.1 p.2).trace.length = 4 := by
      intro p
      exact initialCell_cost input p.1 p.2
    simp [List.length_flatMap, hcell, FiniteRamEnumeration.pairs_length]
    ring
  have hp := FiniteRamEnumeration.pairs_cost_le n
  dsimp [Counted.cost] at hp
  have hsq : n * n ≤ (n + 1) ^ 2 := by
    simpa only [pow_two] using
      Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  simp only [initial, Counted.cost, List.length_append,
    List.length_replicate, FiniteTable.get_ofFn] at hc ⊢
  nlinarith

/-- Each next round consumes the immediately previous counted table value. -/
def rounds (input : FiniteRepairInput n m O) : Nat →
    Counted (FiniteBehavior.WitnessTable n m)
  | 0 => initial input
  | k + 1 =>
      let previous := rounds input k
      let next := step input previous.value
      ⟨next.value, previous.trace ++ next.trace⟩

theorem rounds_value (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).value = FiniteBehavior.rounds input k := by
  induction k with
  | zero => exact initial_value input
  | succ k ih =>
      simp only [rounds, FiniteBehavior.rounds_succ, step_value, ih]

theorem rounds_cost_le (input : FiniteRepairInput n m O) (k : Nat) :
    (rounds input k).cost ≤
      20 * (n + 1) ^ 2 + k * (40 * (m + 1) * (n + 1) ^ 2) := by
  induction k with
  | zero => simpa [rounds] using initial_cost_le input
  | succ k ih =>
      have hs := step_cost_le input (rounds input k).value
      simpa only [rounds, Counted.cost, List.length_append,
        Nat.succ_mul, Nat.add_assoc] using Nat.add_le_add ih hs

/-- Run the same bounded word discovery as the accepted upper endpoint. -/
def upper (input : FiniteRepairInput n m O) :
    Counted (FiniteBehavior.WitnessTable n m) :=
  rounds input (n * n - 1)

theorem upper_value (input : FiniteRepairInput n m O) :
    (upper input).value = FiniteBehavior.upper input :=
  rounds_value input (n * n - 1)

/-- A concrete primitive-trace bound for initial table and all upper rounds. -/
theorem upper_cost_le (input : FiniteRepairInput n m O) :
    (upper input).cost ≤ 60 * (m + 1) * (n + 1) ^ 4 := by
  have h := rounds_cost_le input (n * n - 1)
  have hsq : n * n ≤ (n + 1) ^ 2 := by
    simpa only [pow_two] using
      Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  have hpow : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hm : 1 ≤ m + 1 := by omega
  dsimp [upper] at h ⊢
  nlinarith [Nat.sub_le (n * n) 1]

end AAT.AG.OperationRepair.FiniteRamUpper

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteRamUpper
