import ResearchLean.AG.OperationRepair.FiniteClosure

/-!
# Explicit RAM primitive traces for finite repair tables

The cost model in G-126 D gives unit charge to a table read/write, index or
Boolean operation, and observation equality test. Table copying and word-cell
allocation are represented by one charge per copied or allocated cell.
`Counted` retains the actual value and a ghost trace of these named
primitives. Trace-list construction is bookkeeping for the cost semantics;
its `List.append` calls are not operations of the RAM program obtained by
erasing the trace. Value-erasure theorems below identify that program.

Implementation notes: a primitive trace is data constructed by the same
branch as the value; a separately attached polynomial would not establish
coverage. The semantics here is the GOAL's abstract RAM model, not elapsed
time of Lean's persistent Array runtime. Explicit table copies use `ofFn`
and pay per cell. Array updates are modeled as the unit table-write primitive
specified by the RAM model; subsequent lower-loop work must invoke this
wrapper so that the charge cannot be omitted.
-/

namespace AAT.AG.OperationRepair.FiniteRamPrimitives

universe u

/-- Primitive operations named in G-126 D's RAM cost model. -/
inductive Primitive where
  | tableRead | tableWrite | indexOp | boolOp | observationEq
  | tableCell | copiedCell | wordCell
  deriving DecidableEq, Repr

/-- A computation value and its explicit primitive-operation trace. -/
structure Counted (α : Type u) where
  value : α
  trace : List Primitive

namespace Counted

/-- The trace length is the modeled RAM charge. -/
def cost (a : Counted α) : Nat := a.trace.length

/-- Sequence two computations without discarding either trace. -/
def bind (a : Counted α) (f : α → Counted β) : Counted β :=
  let b := f a.value
  ⟨b.value, a.trace ++ b.trace⟩

/-- A charge-free pure value. -/
def pure (a : α) : Counted α := ⟨a, []⟩

end Counted

variable {α : Type u} {k n : Nat}

/-- Read one size-indexed cell and record the table access. -/
def read (table : FiniteTable α k) (i : Fin k) : Counted α :=
  ⟨table.get i, [.tableRead]⟩

/-- Update one size-indexed cell in the abstract unit-write RAM model. -/
def write (table : FiniteTable α k) (i : Fin k) (value : α) :
    Counted (FiniteTable α k) :=
  ⟨table.set i value, [.tableWrite]⟩

/-- Read one Boolean relation cell (two nested table reads). -/
def readRelation (table : RelationTable n) (x y : Fin n) : Counted Bool :=
  let row := read table x
  let cell := read row.value y
  ⟨cell.value, row.trace ++ cell.trace⟩

/-- Write one Boolean relation cell (row read, row write, outer write). -/
def writeRelation (table : RelationTable n) (x y : Fin n)
    (value : Bool) : Counted (RelationTable n) :=
  let row := read table x
  let changed := write row.value y value
  let result := write table x changed.value
  ⟨result.value, row.trace ++ changed.trace ++ result.trace⟩

/-- Charge one Boolean operation. -/
def test (value : Bool) : Counted Bool := ⟨value, [.boolOp]⟩

/-- Charge one observation equality test. -/
def observationEqual [DecidableEq α] (x y : α) : Counted Bool :=
  ⟨decide (x = y), [.observationEq]⟩

/-- Attach an explicit allowance for a fixed number of index projections,
tuple constructions, or other constant-time index operations. -/
def withIndexOps (q : Nat) (a : Counted α) : Counted α :=
  ⟨a.value, List.replicate q .indexOp ++ a.trace⟩

/-- Construct a copied table rather than aliasing the original array.
Both the copy's source read and new cell allocation are charged. -/
def copy (table : FiniteTable α k) : Counted (FiniteTable α k) :=
  let result := FiniteTable.ofFn fun i => table.get i
  let trace := (List.finRange k).flatMap fun _ =>
    [.tableRead, .copiedCell]
  ⟨result, trace⟩

/-- The copied table has the same contents as its source. -/
theorem copy_value (table : FiniteTable α k) :
    (copy table).value = table := by
  apply FiniteTable.ext
  intro i
  simp [copy]

/-- The copy trace contains a read and allocation for each copied cell. -/
theorem copy_cost (table : FiniteTable α k) :
    (copy table).cost = 2 * k := by
  simp [Counted.cost, copy, List.length_flatMap, Nat.mul_comm]

/-- A relation-table copy recursively copies every row and its outer cell. -/
def copyRelation (table : RelationTable n) : Counted (RelationTable n) :=
  let result := FiniteTable.ofFn fun x =>
    let row := FiniteTable.get table x
    (copy row).value
  let trace := (List.finRange n).flatMap fun _ =>
    [.tableRead] ++
      ((List.finRange n).flatMap fun _ => [.tableRead, .copiedCell]) ++
      [.copiedCell]
  ⟨result, trace⟩

/-- Copying a relation table preserves every Boolean cell. -/
theorem copyRelation_value (table : RelationTable n) :
    (copyRelation table).value = table := by
  apply FiniteTable.ext
  intro x
  simp [copyRelation, copy_value]

/-- Relation copying charges its two-dimensional contents and row cells. -/
theorem copyRelation_cost (table : RelationTable n) :
    (copyRelation table).cost = n * (2 * n + 2) := by
  simp [Counted.cost, copyRelation, List.length_flatMap, Nat.mul_add,
    Nat.mul_comm]
  omega

variable {γ : Type*}

/-- One branch of a charged closure-marking fold. -/
def markItem (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n))
    (acc : Counted (RelationTable n)) (item : γ) :
    Counted (RelationTable n) :=
  let condition := pred item
  if condition.value then
    let destination := target item
    let changed := writeRelation acc.value destination.value.1
      destination.value.2 true
    ⟨changed.value,
      acc.trace ++ condition.trace ++ destination.trace ++ changed.trace ++
        [.indexOp, .indexOp, .boolOp]⟩
  else
    ⟨acc.value, acc.trace ++ condition.trace ++ [.boolOp]⟩

/-- Run one closure marking pass through counted predicates, targets, and
relation writes, after a charged copy of the source table. -/
def markPass (items : List γ) (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n)) (out : RelationTable n) :
    Counted (RelationTable n) :=
  items.foldl (markItem pred target) (copyRelation out)

/-- The value branch performs exactly the original conditional table write. -/
theorem markItem_value (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n))
    (acc : Counted (RelationTable n)) (item : γ) :
    (markItem pred target acc item).value =
      if (pred item).value then
        acc.value.set (target item).value.1 (target item).value.2 true
      else acc.value := by
  cases h : (pred item).value <;>
    simp [markItem, h, writeRelation, read, write, RelationTable.set]

/-- The taken branch determines the exact primitive trace added by one item. -/
theorem markItem_cost (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n))
    (acc : Counted (RelationTable n)) (item : γ) :
    (markItem pred target acc item).cost =
      acc.cost + (pred item).cost +
        (if (pred item).value then (target item).cost + 6 else 1) := by
  cases h : (pred item).value <;>
    simp [markItem, h, Counted.cost, writeRelation, read, write,
      List.length_append, Nat.add_assoc]

private theorem markPass_value_aux (items : List γ)
    (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n))
    (acc : Counted (RelationTable n)) :
    (items.foldl (markItem pred target) acc).value =
      FiniteClosure.markPass items (fun a => (pred a).value)
        (fun a => (target a).value) acc.value := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      change (rest.foldl (markItem pred target)
        (markItem pred target acc item)).value = _
      rw [ih, markItem_value]
      rfl

/-- The charged pass computes the same Boolean table as the original pass. -/
theorem markPass_value (items : List γ)
    (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n)) (out : RelationTable n) :
    (markPass items pred target out).value =
      FiniteClosure.markPass items (fun a => (pred a).value)
        (fun a => (target a).value) out := by
  rw [markPass, markPass_value_aux, copyRelation_value]

private theorem markPass_cost_aux (items : List γ)
    (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n))
    (p t : Nat) (hpred : ∀ a ∈ items, (pred a).cost ≤ p)
    (htarget : ∀ a ∈ items, (target a).cost ≤ t)
    (acc : Counted (RelationTable n)) :
    (items.foldl (markItem pred target) acc).cost ≤
      acc.cost + items.length * (p + t + 6) := by
  induction items generalizing acc with
  | nil => simp [Counted.cost]
  | cons item rest ih =>
      have hp : (pred item).cost ≤ p := hpred item (by simp)
      have ht : (target item).cost ≤ t := htarget item (by simp)
      have hrp : ∀ a ∈ rest, (pred a).cost ≤ p := by
        intro a ha
        exact hpred a (by simp [ha])
      have hrt : ∀ a ∈ rest, (target a).cost ≤ t := by
        intro a ha
        exact htarget a (by simp [ha])
      have hrest := ih hrp hrt (markItem pred target acc item)
      have hitem := markItem_cost pred target acc item
      simp only [List.foldl_cons, List.length_cons] at hrest ⊢
      have hstep : (markItem pred target acc item).cost ≤
          acc.cost + (p + t + 6) := by
        rw [hitem]
        cases (pred item).value <;> simp <;> omega
      have hbound := hrest.trans
        (Nat.add_le_add_right hstep (rest.length * (p + t + 6)))
      simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hbound

/-- A charged pass pays for the explicit copy and every taken primitive
branch; the bound is independent of predicate results. -/
theorem markPass_cost_le (items : List γ)
    (pred : γ → Counted Bool)
    (target : γ → Counted (Fin n × Fin n)) (out : RelationTable n)
    (p t : Nat) (hpred : ∀ a ∈ items, (pred a).cost ≤ p)
    (htarget : ∀ a ∈ items, (target a).cost ≤ t) :
    (markPass items pred target out).cost ≤
      n * (2 * n + 2) + items.length * (p + t + 6) := by
  have h := markPass_cost_aux items pred target p t hpred htarget
    (copyRelation out)
  simpa [markPass, copyRelation_cost] using h

/-- A relation write records exactly one row read and two table writes. -/
theorem writeRelation_cost (table : RelationTable n) (x y : Fin n)
    (value : Bool) : (writeRelation table x y value).cost = 3 := rfl

/-- The input to a marking pass is explicitly copied, including empty tables. -/
theorem markPass_initial_cost (out : RelationTable n) :
    (copyRelation out).cost = n * (2 * n + 2) :=
  copyRelation_cost out

/-- A transition lookup consists of an operation-row read and a state-cell
read. No transition oracle is hidden in a predicate callback. -/
def readStep (input : FiniteRepairInput n m O) (e : Fin m) (x : Fin n) :
    Counted (Fin n) :=
  let row := read input.transition e
  let cell := read row.value x
  ⟨cell.value, row.trace ++ cell.trace⟩

theorem readStep_value (input : FiniteRepairInput n m O)
    (e : Fin m) (x : Fin n) :
    (readStep input e x).value = input.step e x := rfl

theorem readStep_cost (input : FiniteRepairInput n m O)
    (e : Fin m) (x : Fin n) :
    (readStep input e x).cost = 2 := rfl

/-- A counted synchronous round uses the previous table as the only premise
source in all three marking passes. The trace includes each pass copy. -/
def closeStep (input : FiniteRepairInput n m O) (old : RelationTable n) :
    Counted (RelationTable n) :=
  let converse := markPass (FiniteClosure.pairs n)
    (fun p => withIndexOps 2 (readRelation old p.1 p.2))
    (fun p => withIndexOps 3 (Counted.pure (p.2, p.1))) old
  let transitive := markPass (FiniteClosure.triples n)
    (fun p =>
      let first := readRelation old p.1 p.2.1
      let second := readRelation old p.2.1 p.2.2
      withIndexOps 7 ⟨first.value && second.value,
        first.trace ++ second.trace ++ [.boolOp]⟩)
    (fun p => withIndexOps 4 (Counted.pure (p.1, p.2.2))) converse.value
  let image := markPass ((FiniteClosure.states m).flatMap fun e =>
      (FiniteClosure.pairs n).map fun p => (e, p))
    (fun p => withIndexOps 4 (readRelation old p.2.1 p.2.2))
    (fun p =>
      let x := readStep input p.1 p.2.1
      let y := readStep input p.1 p.2.2
      withIndexOps 7 ⟨(x.value, y.value), x.trace ++ y.trace⟩)
    transitive.value
  ⟨image.value, converse.trace ++ transitive.trace ++ image.trace⟩

/-- The trace-producing round has exactly the original synchronous value. -/
theorem closeStep_value (input : FiniteRepairInput n m O)
    (old : RelationTable n) :
    (closeStep input old).value = FiniteClosure.closeStep input old := by
  simp only [closeStep, FiniteClosure.closeStep, markPass_value,
    withIndexOps]
  rfl

end AAT.AG.OperationRepair.FiniteRamPrimitives

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteRamPrimitives
