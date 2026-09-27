import ResearchLean.AG.OperationRepair.FiniteConstruction

/-!
# Counted least representatives for numbered repair quotients

The representative is found by scanning numbered states and reading the
computed partition table. This gives a primitive trace for one piece of the
success-table construction. Class-list and quotient-table assembly remain
separate obligations.
-/

namespace AAT.AG.OperationRepair.FiniteRamNumbering

open FiniteRamPrimitives
open FiniteConstruction
variable {n : Nat}

/-- Inspect one candidate state and retain the smaller related state. -/
def repStep (p : PartitionTable n) (x current y : Fin n) : Counted (Fin n) :=
  ⟨if p.cells.get y x then min current y else current,
    [.tableRead, .tableRead, .boolOp, .indexOp]⟩

@[simp] theorem repStep_cost (p : PartitionTable n) (x current y : Fin n) :
    (repStep p x current y).cost = 4 := rfl

theorem repStep_le (p : PartitionTable n) (x current y : Fin n) :
    (repStep p x current y).value ≤ current := by
  by_cases h : p.cells.get y x = true
  · simp [repStep, h]
  · have hf : p.cells.get y x = false := Bool.eq_false_iff.mpr h
    simp [repStep, hf]

theorem repStep_related (p : PartitionTable n) (x current y : Fin n)
    (hcurrent : p.cells.get current x = true) :
    p.cells.get (repStep p x current y).value x = true := by
  by_cases h : p.cells.get y x = true
  · simp only [repStep, h, ↓reduceIte]
    by_cases hle : current ≤ y
    · simpa [min_eq_left hle] using hcurrent
    · have hyc : y ≤ current := le_of_not_ge hle
      simpa [min_eq_right hyc] using h
  · have hf : p.cells.get y x = false := Bool.eq_false_iff.mpr h
    simpa [repStep, hf] using hcurrent

/-- Thread the current minimum through the actual input list. -/
def repFold (p : PartitionTable n) (x : Fin n) :
    List (Fin n) → Fin n → Counted (Fin n)
  | [], current => Counted.pure current
  | y :: rest, current =>
      let next := repStep p x current y
      let tail := repFold p x rest next.value
      ⟨tail.value, next.trace ++ tail.trace⟩

theorem repFold_le (p : PartitionTable n) (x : Fin n)
    (items : List (Fin n)) (current : Fin n) :
    (repFold p x items current).value ≤ current := by
  induction items generalizing current with
  | nil => rfl
  | cons y rest ih =>
      exact (ih (repStep p x current y).value).trans (repStep_le p x current y)

theorem repFold_related (p : PartitionTable n) (x : Fin n)
    (items : List (Fin n)) (current : Fin n)
    (hcurrent : p.cells.get current x = true) :
    p.cells.get (repFold p x items current).value x = true := by
  induction items generalizing current with
  | nil => exact hcurrent
  | cons y rest ih =>
      exact ih _ (repStep_related p x current y hcurrent)

theorem repFold_le_of_mem (p : PartitionTable n) (x : Fin n)
    (items : List (Fin n)) (current y : Fin n)
    (hy : y ∈ items) (hrelated : p.cells.get y x = true) :
    (repFold p x items current).value ≤ y := by
  induction items generalizing current with
  | nil => simp at hy
  | cons z rest ih =>
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · have hz : (repStep p x current y).value ≤ y := by
          simp [repStep, hrelated]
        exact (repFold_le p x rest (repStep p x current y).value).trans hz
      · exact ih _ hy

/-- The scan pays for each enumerated list cell and each candidate test. -/
def rep (p : PartitionTable n) (x : Fin n) : Counted (Fin n) :=
  let names := FiniteRamEnumeration.states n
  let found := repFold p x names.value x
  ⟨found.value, names.trace ++ found.trace⟩

theorem repFold_cost (p : PartitionTable n) (x : Fin n)
    (items : List (Fin n)) (current : Fin n) :
    (repFold p x items current).cost = 4 * items.length := by
  induction items generalizing current with
  | nil => simp [repFold, Counted.cost, Counted.pure]
  | cons y rest ih =>
      simp only [repFold, Counted.cost, List.length_append,
        List.length_cons]
      rw [show (repStep p x current y).trace.length = 4 by rfl]
      rw [show (repFold p x rest (repStep p x current y).value).trace.length =
        4 * rest.length by exact ih _]
      omega

theorem rep_cost (p : PartitionTable n) (x : Fin n) :
    (rep p x).cost = 6 * n := by
  have hn := FiniteRamEnumeration.states_cost n
  have hf := repFold_cost p x (FiniteRamEnumeration.states n).value x
  rw [FiniteRamEnumeration.states_length] at hf
  simp only [rep, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hn hf
  omega

/-- The counted scan returns the same least representative as the existing
finite partition construction. -/
theorem rep_value (p : PartitionTable n) (x : Fin n) :
    (rep p x).value = p.rep x := by
  have hrelated : p.cells.get (rep p x).value x = true := by
    exact repFold_related p x (FiniteRamEnumeration.states n).value x (p.refl x)
  have hleast : ∀ y : Fin n, p.cells.get y x = true → (rep p x).value ≤ y := by
    intro y hy
    exact repFold_le_of_mem p x (FiniteRamEnumeration.states n).value x y
      (by simp [FiniteRamEnumeration.states]) hy
  unfold PartitionTable.rep
  symm
  apply (Finset.min'_eq_iff (p.classSet x)
    ⟨x, p.self_mem_classSet x⟩ (rep p x).value).2
  constructor
  · simpa [PartitionTable.classSet] using hrelated
  · intro y hy
    exact hleast y (by simpa [PartitionTable.classSet] using hy)

/-- Select exactly the least representatives while retaining their input
number order. Each candidate invokes the concrete counted least-state scan. -/
def collect (p : PartitionTable n) : List (Fin n) →
    Counted (List (Fin n))
  | [] => Counted.pure []
  | y :: rest =>
      let candidate := rep p y
      if candidate.value = y then
        let tail := collect p rest
        ⟨y :: tail.value,
          candidate.trace ++ [.boolOp, .indexOp, .listCell] ++ tail.trace⟩
      else
        let tail := collect p rest
        ⟨tail.value,
          candidate.trace ++ [.boolOp, .indexOp] ++ tail.trace⟩

theorem collect_value (p : PartitionTable n) (items : List (Fin n)) :
    (collect p items).value = items.filter fun y => p.rep y = y := by
  induction items with
  | nil => rfl
  | cons y rest ih =>
      simp only [collect, List.filter_cons, rep_value]
      by_cases h : p.rep y = y <;> simp [h, ih]

theorem collect_cost_le (p : PartitionTable n) (items : List (Fin n)) :
    (collect p items).cost ≤ items.length * (6 * n + 3) := by
  induction items with
  | nil => simp [collect, Counted.pure, Counted.cost]
  | cons y rest ih =>
      have hc : (rep p y).trace.length = 6 * n := rep_cost p y
      by_cases h : (rep p y).value = y
      · simp [collect, h, Counted.cost, List.length_append,
          Nat.add_mul, hc] at ih ⊢
        omega
      · simp [collect, h, Counted.cost, List.length_append,
          Nat.add_mul, hc] at ih ⊢
        omega

def representatives (p : PartitionTable n) : Counted (List (Fin n)) :=
  let names := FiniteRamEnumeration.states n
  let selected := collect p names.value
  ⟨selected.value, names.trace ++ selected.trace⟩

theorem representatives_value (p : PartitionTable n) :
    (representatives p).value =
      (List.finRange n).filter fun y => p.rep y = y := by
  simp [representatives, collect_value, FiniteRamEnumeration.states]

theorem representatives_cost_le (p : PartitionTable n) :
    (representatives p).cost ≤ 2 * n + n * (6 * n + 3) := by
  have hn := FiniteRamEnumeration.states_cost n
  have hc := collect_cost_le p (FiniteRamEnumeration.states n).value
  rw [FiniteRamEnumeration.states_length] at hc
  simp only [representatives, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hn hc
  omega

/-- The selected list covers precisely the mathematical representative set. -/
theorem mem_representatives_value (p : PartitionTable n) (y : Fin n) :
    y ∈ (representatives p).value ↔ y ∈ p.representatives := by
  rw [representatives_value]
  simp only [List.mem_filter, List.mem_finRange, true_and]
  constructor
  · intro hy
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _,
      of_decide_eq_true hy⟩
  · intro hy
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
    rw [← hx]
    exact decide_eq_true (p.rep_idempotent x)

theorem representatives_nodup (p : PartitionTable n) :
    (representatives p).value.Nodup := by
  rw [representatives_value]
  exact (List.nodup_finRange n).filter _

theorem representatives_sort_eq (p : PartitionTable n) :
    (representatives p).value = p.representatives.sort (· ≤ ·) := by
  apply List.SortedLT.eq_of_mem_iff
  · rw [representatives_value]
    exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  · exact Finset.sortedLT_sort _
  · intro y
    exact (mem_representatives_value p y).trans
      (Finset.mem_sort (· ≤ ·)).symm

theorem representatives_length (p : PartitionTable n) :
    (representatives p).value.length = p.classCount := by
  rw [representatives_sort_eq]
  exact Finset.length_sort (· ≤ ·)

variable {α : Type*}

/-- Read a list element by walking exactly the visited prefix. -/
def getAt : List α → Nat → Counted (Option α)
  | [], _ => ⟨none, [.indexOp]⟩
  | x :: _, 0 => ⟨some x, [.indexOp]⟩
  | _ :: rest, k + 1 =>
      let tail := getAt rest k
      ⟨tail.value, .indexOp :: tail.trace⟩

theorem getAt_value (items : List α) (k : Nat) :
    (getAt items k).value = items[k]? := by
  induction items generalizing k with
  | nil => simp [getAt]
  | cons x rest ih =>
      cases k with
      | zero => simp [getAt]
      | succ k => simpa [getAt] using ih k

theorem getAt_cost_le (items : List α) (k : Nat) :
    (getAt items k).cost ≤ items.length + 1 := by
  induction items generalizing k with
  | nil => simp [getAt, Counted.cost]
  | cons x rest ih =>
      cases k with
      | zero => simp [getAt, Counted.cost]
      | succ k =>
          have ht := ih k
          simp [getAt, Counted.cost] at ht ⊢
          omega

/-- Read the numbered class section from the counted sorted representatives. -/
def classSection (p : PartitionTable n) (c : Fin p.classCount) : Counted (Fin n) :=
  let reps := representatives p
  let hlen : c.val < reps.value.length := by
    change c.val < (representatives p).value.length
    rw [representatives_length]
    exact c.isLt
  let found := getAt reps.value c.val
  let hsome : found.value.isSome = true := by
    rw [getAt_value, List.getElem?_eq_getElem hlen]
    rfl
  ⟨found.value.get hsome, reps.trace ++ found.trace⟩

theorem classSection_value (p : PartitionTable n) (c : Fin p.classCount) :
    (classSection p c).value = p.classSection c := by
  simp only [classSection]
  simp [getAt_value]
  simp only [representatives_sort_eq, PartitionTable.classSection]
  have hlen : c.val < (p.representatives.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]
    exact c.isLt
  change p.representatives.sort[c.val]'hlen = p.representatives.orderEmbOfFin rfl c
  exact (Finset.orderEmbOfFin_apply p.representatives rfl c).symm

theorem classSection_cost_le (p : PartitionTable n) (c : Fin p.classCount) :
    (classSection p c).cost ≤ 10 * (n + 1) ^ 2 := by
  have hr := representatives_cost_le p
  have hg := getAt_cost_le (representatives p).value c.val
  rw [representatives_length] at hg
  have hcount : p.classCount ≤ n := by
    unfold PartitionTable.classCount
    exact (Finset.card_image_le).trans (by simp)
  simp only [classSection, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hr hg
  nlinarith

/-- Walk the ordered representative list to locate one class name. -/
def findIndex (target : Fin n) : List (Fin n) → Counted Nat
  | [] => ⟨0, [.boolOp]⟩
  | y :: rest =>
      if y = target then ⟨0, [.boolOp, .tableRead]⟩
      else
        let tail := findIndex target rest
        ⟨tail.value + 1, [.boolOp, .tableRead, .indexOp] ++ tail.trace⟩

theorem findIndex_value (target : Fin n) (items : List (Fin n)) :
    (findIndex target items).value = items.idxOf target := by
  induction items with
  | nil => rfl
  | cons y rest ih =>
      by_cases h : y = target
      · simp [findIndex, h]
      · simp [findIndex, h, List.idxOf_cons_ne rest h, ih]

theorem findIndex_cost_le (target : Fin n) (items : List (Fin n)) :
    (findIndex target items).cost ≤ 3 * (items.length + 1) := by
  induction items with
  | nil => simp [findIndex, Counted.cost]
  | cons y rest ih =>
      by_cases h : y = target
      · simp [findIndex, h, Counted.cost]
        omega
      · simp [findIndex, h, Counted.cost] at ih ⊢
        omega

/-- Number a class by the position of its counted least representative. -/
def quotient (p : PartitionTable n) (x : Fin n) : Counted (Fin p.classCount) :=
  let representatives := representatives p
  let representative := rep p x
  let index := findIndex representative.value representatives.value
  let hin : representative.value ∈ representatives.value := by
    rw [rep_value]
    exact (mem_representatives_value p _).mpr (p.rep_mem_representatives x)
  let hlt : index.value < p.classCount := by
    rw [findIndex_value]
    calc
      representatives.value.idxOf representative.value <
          representatives.value.length := List.idxOf_lt_length_of_mem hin
      _ = p.classCount := representatives_length p
  ⟨⟨index.value, hlt⟩,
    representatives.trace ++ representative.trace ++ index.trace⟩

theorem quotient_value (p : PartitionTable n) (x : Fin n) :
    (quotient p x).value = p.quotient x := by
  apply Fin.ext
  simp only [quotient, findIndex_value, rep_value, representatives_sort_eq]
  exact (Finset.orderIsoOfFin_symm_apply p.representatives rfl
    ⟨p.rep x, p.rep_mem_representatives x⟩).symm

theorem quotient_cost_le (p : PartitionTable n) (x : Fin n) :
    (quotient p x).cost ≤ 20 * (n + 1) ^ 2 := by
  have hr := representatives_cost_le p
  have hp := rep_cost p x
  have hi := findIndex_cost_le (rep p x).value (representatives p).value
  rw [representatives_length] at hi
  have hcount : p.classCount ≤ n := by
    unfold PartitionTable.classCount
    exact (Finset.card_image_le).trans (by simp)
  simp only [quotient, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hr hp hi
  nlinarith

variable {β : Type*}

/-- Allocate a finite table from stored counted cells, visiting each cell
once to collect its primitive trace. -/
def tabulate (k : Nat) (f : Fin k → Counted β) :
    Counted (FiniteTable β k) :=
  let cells : FiniteTable (Counted β) k := FiniteTable.ofFn f
  let values : FiniteTable β k :=
    FiniteTable.ofFn fun i => (cells.get i).value
  let names := FiniteRamEnumeration.states k
  let traces := names.value.flatMap fun i => (cells.get i).trace
  ⟨values, names.trace ++ traces ++
    List.replicate (2 * k) .tableCell ++ List.replicate (2 * k) .tableRead⟩

theorem tabulate_get (k : Nat) (f : Fin k → Counted β) (i : Fin k) :
    (tabulate k f).value.get i = (f i).value := by
  simp [tabulate]

private theorem traceCells_le (k : Nat) (f : Fin k → Counted β)
    (q : Nat) (hf : ∀ i, (f i).cost ≤ q)
    (items : List (Fin k)) :
    (items.flatMap fun i => (f i).trace).length ≤ items.length * q := by
  induction items with
  | nil => simp
  | cons i rest ih =>
      have h := hf i
      dsimp [Counted.cost] at h
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      simp only [Nat.succ_mul]
      omega

theorem tabulate_cost_le (k : Nat) (f : Fin k → Counted β)
    (q : Nat) (hf : ∀ i, (f i).cost ≤ q) :
    (tabulate k f).cost ≤ k * (q + 6) := by
  have ht := traceCells_le k f q hf (FiniteRamEnumeration.states k).value
  rw [FiniteRamEnumeration.states_length] at ht
  have hn := FiniteRamEnumeration.states_cost k
  simp only [tabulate, Counted.cost, List.length_append,
    List.length_replicate] at hn ⊢
  simp only [FiniteTable.get_ofFn]
  nlinarith

variable {m : Nat} {O : Type*} [DecidableEq O]

/-- Build every numbered quotient table from counted indexed cells. -/
def numberedTables (input : FiniteRepairInput n m O)
    (p : PartitionTable n) : Counted (NumberedQuotientTables n m O) :=
  let map := tabulate n (quotient p)
  let sectionTable := tabulate p.classCount (classSection p)
  let operations := tabulate m fun e =>
    let row := tabulate p.classCount fun c =>
      let selected := classSection p c
      let image := quotient p (input.step e selected.value)
      ⟨image.value, selected.trace ++ [.tableRead] ++ image.trace⟩
    row
  let observations := tabulate p.classCount fun c =>
    let selected := classSection p c
    ⟨input.observe selected.value, selected.trace ++ [.tableRead]⟩
  ⟨⟨p.classCount, map.value, sectionTable.value,
      operations.value, observations.value⟩,
    map.trace ++ sectionTable.trace ++ operations.trace ++ observations.trace⟩

omit [DecidableEq O] in
theorem numberedTables_value (input : FiniteRepairInput n m O)
    (p : PartitionTable n) :
    (numberedTables input p).value = makeNumberedTables input p := by
  unfold numberedTables makeNumberedTables
  simp only
  congr 1
  · apply FiniteTable.ext
    intro x
    simp [quotientMapTable,
      tabulate_get, quotient_value]
  · apply FiniteTable.ext
    intro c
    simp [tabulate_get,
      classSection_value]
  · apply FiniteTable.ext
    intro e
    apply FiniteTable.ext
    intro c
    simp [quotientOperationTable,
      tabulate_get, classSection_value, quotient_value]
  · apply FiniteTable.ext
    intro c
    simp [quotientObservationTable,
      tabulate_get, classSection_value]

omit [DecidableEq O] in
theorem numberedTables_cost_le (input : FiniteRepairInput n m O)
    (p : PartitionTable n) :
    (numberedTables input p).cost ≤
      100 * (m + 1) * (n + 1) ^ 4 := by
  let N := n + 1
  let c := p.classCount
  have hc : c ≤ n := by
    dsimp [c, PartitionTable.classCount]
    exact (Finset.card_image_le).trans (by simp)
  have hm : (tabulate n (quotient p)).cost ≤ n * (20 * N ^ 2 + 6) := by
    apply tabulate_cost_le
    intro x
    simpa [N] using quotient_cost_le p x
  have hs : (tabulate c (classSection p)).cost ≤ c * (10 * N ^ 2 + 6) := by
    apply tabulate_cost_le
    intro x
    simpa [N, c] using classSection_cost_le p x
  have hi (e : Fin m) :
      (tabulate c fun x =>
        let selected := classSection p x
        let image := quotient p (input.step e selected.value)
        ⟨image.value, selected.trace ++ [.tableRead] ++ image.trace⟩).cost ≤
          c * (30 * N ^ 2 + 7) := by
    apply tabulate_cost_le
    intro x
    have ha := classSection_cost_le p x
    have hb := quotient_cost_le p (input.step e (classSection p x).value)
    simp only [Counted.cost, List.length_append, List.length_singleton]
    dsimp [Counted.cost] at ha hb
    dsimp [N]
    omega
  have ho :
      (tabulate m fun e =>
        tabulate c fun x =>
          let selected := classSection p x
          let image := quotient p (input.step e selected.value)
          ⟨image.value, selected.trace ++ [.tableRead] ++ image.trace⟩).cost ≤
        m * (c * (30 * N ^ 2 + 7) + 6) := by
    exact tabulate_cost_le m _ _ hi
  have hb :
      (tabulate c fun x =>
        let selected := classSection p x
        ⟨input.observe selected.value, selected.trace ++ [.tableRead]⟩).cost ≤
        c * (10 * N ^ 2 + 7) := by
    apply tabulate_cost_le
    intro x
    have ha := classSection_cost_le p x
    simp only [Counted.cost, List.length_append, List.length_singleton]
    dsimp [Counted.cost] at ha
    dsimp [N]
    omega
  simp only [numberedTables, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hm hs ho hb
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hcN : c ≤ N := by omega
  have hnN : n ≤ N := by dsimp [N]; omega
  dsimp only [c] at hs ho hb hcN
  have hN2 : N ^ 2 ≤ N ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hN3 : N ^ 3 ≤ N ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hN4 : 1 ≤ N ^ 4 := by nlinarith
  have hnm : n * N ^ 2 ≤ N ^ 3 := by
    nlinarith [Nat.mul_le_mul_right (N ^ 2) hnN]
  have hcm : p.classCount * N ^ 2 ≤ N ^ 3 := by
    nlinarith [Nat.mul_le_mul_right (N ^ 2) hcN]
  have hmap : n * (20 * N ^ 2 + 6) ≤ 26 * N ^ 4 := by
    nlinarith [Nat.mul_le_mul_right 6 hnN, hN3]
  have hsec : p.classCount * (10 * N ^ 2 + 6) ≤ 16 * N ^ 4 := by
    nlinarith [Nat.mul_le_mul_right 6 hcN, hN3]
  have hobs : p.classCount * (10 * N ^ 2 + 7) ≤ 17 * N ^ 4 := by
    nlinarith [Nat.mul_le_mul_right 7 hcN, hN3]
  have hrow : p.classCount * (30 * N ^ 2 + 7) + 6 ≤ 43 * N ^ 4 := by
    nlinarith [Nat.mul_le_mul_right 7 hcN, hN3]
  have hoperation :
      m * (p.classCount * (30 * N ^ 2 + 7) + 6) ≤
        m * (43 * N ^ 4) := Nat.mul_le_mul_left m hrow
  dsimp only [N] at *
  nlinarith

/-- Assemble both numbered quotients and their canonical comparison map. -/
def successTablesFrom (input : FiniteRepairInput n m O)
    (lowerPart upperPart : PartitionTable n) :
    Counted (SuccessTables n m O) :=
  let lower := numberedTables input lowerPart
  let upper := numberedTables input upperPart
  let comparison := tabulate lowerPart.classCount fun c =>
    let selected := classSection lowerPart c
    let image := quotient upperPart selected.value
    ⟨image.value, selected.trace ++ image.trace⟩
  ⟨⟨lower.value, upper.value, comparison.value⟩,
    lower.trace ++ upper.trace ++ comparison.trace⟩

omit [DecidableEq O] in
theorem successTablesFrom_value (input : FiniteRepairInput n m O)
    (lowerPart upperPart : PartitionTable n) :
    (successTablesFrom input lowerPart upperPart).value =
      makeSuccessTablesFrom input lowerPart upperPart := by
  unfold successTablesFrom makeSuccessTablesFrom
  simp only
  congr 1
  · exact numberedTables_value input lowerPart
  · exact numberedTables_value input upperPart
  · apply FiniteTable.ext
    intro c
    simp [tabulate_get, classSection_value, quotient_value]

omit [DecidableEq O] in
theorem successTablesFrom_cost_le (input : FiniteRepairInput n m O)
    (lowerPart upperPart : PartitionTable n) :
    (successTablesFrom input lowerPart upperPart).cost ≤
      300 * (m + 1) * (n + 1) ^ 4 := by
  have hl := numberedTables_cost_le input lowerPart
  have hu := numberedTables_cost_le input upperPart
  have hc : lowerPart.classCount ≤ n := by
    unfold PartitionTable.classCount
    exact (Finset.card_image_le).trans (by simp)
  have hcomp :
      (tabulate lowerPart.classCount fun c =>
        let selected := classSection lowerPart c
        let image := quotient upperPart selected.value
        ⟨image.value, selected.trace ++ image.trace⟩).cost ≤
      lowerPart.classCount * (30 * (n + 1) ^ 2 + 6) := by
    apply tabulate_cost_le
    intro c
    have hs := classSection_cost_le lowerPart c
    have hq := quotient_cost_le upperPart (classSection lowerPart c).value
    simp only [Counted.cost, List.length_append]
    dsimp [Counted.cost] at hs hq
    omega
  simp only [successTablesFrom, Counted.cost, List.length_append]
  dsimp [Counted.cost] at hl hu hcomp
  have hn : 1 ≤ n + 1 := by omega
  have hN3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right hn (by decide)
  have hN4 : 1 ≤ (n + 1) ^ 4 := by nlinarith
  have hcm : lowerPart.classCount * (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by
    nlinarith [Nat.mul_le_mul_right ((n + 1) ^ 2) (hc.trans (Nat.le_succ n))]
  have hcomparison :
      lowerPart.classCount * (30 * (n + 1) ^ 2 + 6) ≤
        36 * (n + 1) ^ 4 := by
    nlinarith [Nat.mul_le_mul_right 6 (hc.trans (Nat.le_succ n))]
  nlinarith

end AAT.AG.OperationRepair.FiniteRamNumbering

#assert_standard_axioms_only AAT.AG.OperationRepair.FiniteRamNumbering
