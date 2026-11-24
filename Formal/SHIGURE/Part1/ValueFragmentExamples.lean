import Formal.SHIGURE.Part1.ValueFragments
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Range

/-! # Finite observations without a global realization

Example 3.10 gives two independent obstructions. A total function's witness
may lie beyond every finite graph table that asks about its input. A finite
support condition may also fail when every finite restriction is realizable.

## Implementation notes

Fin indices represent the exact prefix intervals of Example 3.10 and their
inclusions use Fin.castLE. General finite grid embeddings would introduce
extra choices in this example. The sequence takes ordinary function values
and carries its finite support as a proof. A sparse function representation
would also require translating its evaluations into the ordinary structure.
-/

namespace SHIGURE.ValueFragment

/-- A single sort contributes exactly one copy of its finite collection of sample names. -/
private theorem finite_names_one_sort (Name : Type) [Finite Name] :
    Finite (Σ _ : PUnit, Name) := by
  apply Finite.of_injective (fun x : Σ _ : PUnit, Name => x.2)
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  cases h
  rfl

namespace EqualityObservation

/-- A single sort with no operation or relation symbols. -/
def signature : Signature.{0} where
  SortType := PUnit
  Total := PEmpty
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity := PEmpty.elim
  relInputs := PEmpty.elim
  partialArity := PEmpty.elim
  quantityArity := PEmpty.elim

/-- The two equality queries read ordinary states of the same natural-number sort. -/
def stateStructure : Structure signature where
  carrier _ := ℕ
  total name := PEmpty.elim name
  relation name := PEmpty.elim name
  partialDomain name := PEmpty.elim name
  partialValue name := PEmpty.elim name
  quantity name := PEmpty.elim name

/-- A schema that compares the first sample with each of two named states. -/
def schema : Schema.{0,0} signature where
  Name _ := Bool
  finiteNames := finite_names_one_sort Bool
  Index := Bool
  finiteIndices := inferInstance
  query b := .truth .both (.eq (s := PUnit.unit) false b)

/-- The two names designate zero and one. -/
def samples : Samples schema.Name stateStructure.carrier :=
  fun _ name => (if (show Bool from name) then 1 else 0 : Nat)

/-- This schema can read equality even in a signature without operation or relation symbols. -/
theorem read_equality (b : Bool) :
    ((schema.read stateStructure samples).answer b).down = true ↔ b = false := by
  rw [Schema.read_answer]
  letI : Finite (Σ s, schema.Name s) := schema.finiteNames
  exact (Query.read_equality_true_iff (A := stateStructure) samples
    (s := PUnit.unit) false b).trans (by cases b <;> simp [samples])

/-- Comparing a sample with itself records true. -/
theorem read_same : ((schema.read stateStructure samples).answer false).down = true :=
  (read_equality false).2 rfl

/-- Comparing samples with different states records false. -/
theorem read_different : ((schema.read stateStructure samples).answer true).down = false := by
  rw [← Bool.not_eq_true, read_equality]
  decide

end EqualityObservation

namespace GraphFailure

/-- The signature of a total unary operation on one sort. -/
def signature : Signature.{0} where
  SortType := PUnit
  Total := PUnit
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity _ := ⟨[PUnit.unit], PUnit.unit⟩
  relInputs := PEmpty.elim
  partialArity := PEmpty.elim
  quantityArity := PEmpty.elim

/-- The ordinary structure on the fixed natural-number carrier with total operation f. -/
def structureOf (f : ℕ → ℕ) : Structure signature where
  carrier _ := ℕ
  total _ xs := f xs.head
  relation := fun name => PEmpty.elim name
  partialDomain := fun name => PEmpty.elim name
  partialValue := fun name => PEmpty.elim name
  quantity := fun name => PEmpty.elim name

/-- The grid Qₙ of all queried input and output pairs up to n. -/
abbrev Grid (n : ℕ) := Fin (n + 1) × Fin (n + 1)

/-- Ask both truth values for every graph pair in the finite grid. -/
def schema (n : ℕ) : Schema.{0,0} signature where
  Name _ := Fin (n + 1)
  finiteNames := finite_names_one_sort (Fin (n + 1))
  Index := Grid n
  finiteIndices := inferInstance
  query q := .truth .both (.graph (.total PUnit.unit) (.cons q.1 .empty) q.2)

/-- The named state for an index in the grid is that natural number. -/
def samples (n : ℕ) : Samples (schema n).Name (structureOf id).carrier :=
  fun _ i => i.val

/-- Read the graph table from the ordinary value-fragment restriction. -/
noncomputable def observe (f : ℕ → ℕ) (n : ℕ) : Grid n → Bool :=
  fun q => (((schema n).read (structureOf f) (samples n)).answer q).down

/-- The observed answer is precisely graph membership of the ordinary operation. -/
theorem observe_true_iff (f : ℕ → ℕ) (n : ℕ) (q : Grid n) :
    observe f n q = true ↔ f q.1.val = q.2.val := by
  unfold observe
  rw [Schema.read_answer]
  letI : Finite (Σ s, (schema n).Name s) := (schema n).finiteNames
  let inputs : Assignment (schema n).Name [PUnit.unit] := .cons q.1 .empty
  let atom : AtomicQuery signature (schema n).Name := .graph (.total PUnit.unit) inputs q.2
  have observes := Query.read_truth (A := structureOf f) (samples n) .both atom
  change ((Query.truth .both atom).read (structureOf f) (samples n)).down = true ↔ _
  rw [observes]
  change TruthRecording.record .both
    ((AtomicQuery.graph (sig := signature) (.total PUnit.unit) inputs q.2).holds
      (structureOf f) (samples n)) = true ↔ _
  rw [TruthRecording.record_both_eq_true, AtomicQuery.holds_graph_iff, Structure.graph_total_iff]
  change f ((samples n).tuple inputs .here) = q.2.val ↔ _
  rw [Samples.tuple_apply]
  simp only [inputs, Assignment.cons_here]
  rfl

/-- The prescribed table: exactly the nonzero diagonal pairs are true. -/
def table (n : ℕ) (q : Grid n) : Bool :=
  decide (0 < q.1.val ∧ q.2.val = q.1.val)

/-- Restrict a larger graph table to a smaller prefix grid. -/
def restrict {m n : ℕ} (h : m ≤ n) (values : Grid n → Bool) : Grid m → Bool :=
  fun q => values (Fin.castLE (Nat.succ_le_succ h) q.1, Fin.castLE (Nat.succ_le_succ h) q.2)

/-- These graph tables agree strictly under every prefix restriction. -/
theorem restrict_table {m n : ℕ} (h : m ≤ n) :
    restrict h (table n) = table m :=
  rfl

/-- The total operation of equation (3.7) at the n-th stage. -/
def stageMap (n : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then n + 1 else i

/-- The output witness at input zero lies strictly beyond the n-th grid. -/
@[simp] theorem stageMap_zero (n : ℕ) : stageMap n 0 = n + 1 :=
  if_pos rfl

/-- At every positive input the stage operation is the identity. -/
theorem stageMap_pos (n i : ℕ) (h : 0 < i) : stageMap n i = i :=
  if_neg (Nat.ne_of_gt h)

/-- The n-th table is an actual finite restriction of the total map in (3.7). -/
theorem observe_stageMap (n : ℕ) : observe (stageMap n) n = table n := by
  funext q
  apply Bool.eq_iff_iff.mpr
  rw [observe_true_iff]
  change (stageMap n q.1.val = q.2.val) ↔ decide (0 < q.1.val ∧ q.2.val = q.1.val) = true
  rw [decide_eq_true_iff]
  by_cases zero : q.1.val = 0
  · rw [zero, stageMap_zero]
    simp [Nat.ne_of_gt q.2.isLt]
  · have pos := Nat.pos_of_ne_zero zero
    rw [stageMap_pos _ _ pos]
    simp [pos, eq_comm]

/-- A global map would answer true to the already prescribed false query (0, f(0)). -/
theorem no_global :
    ¬ ∃ f : ℕ → ℕ, ∀ n, observe f n = table n := by
  rintro ⟨f, observes⟩
  let n := f 0
  let q : Grid n := (⟨0, Nat.succ_pos n⟩, ⟨n, Nat.lt_succ_self n⟩)
  have present : observe f n q = true := (observe_true_iff _ _ _).2 rfl
  rw [observes n] at present
  simp [table, q] at present

end GraphFailure

namespace SupportFailure

/-- The selected support condition on a binary sequence. -/
abbrev FiniteSequence := {f : ℕ → Bool // Set.Finite {i | f i = true}}

/-- The finite binary table on the first n + 1 indices. -/
abbrev Stage (n : ℕ) := Fin (n + 1) → Bool

/-- The index and value sorts for reading binary sequence entries. -/
inductive SequenceSort
  | index
  | bit

/-- The query reads a Boolean-valued quantity on a natural-number input. -/
def signature : Signature.{0} where
  SortType := SequenceSort
  Total := PEmpty
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PUnit
  totalArity := PEmpty.elim
  relInputs := PEmpty.elim
  partialArity := PEmpty.elim
  quantityArity _ := ⟨[SequenceSort.index], SequenceSort.bit⟩

/-- The ordinary two-sorted structure for a binary sequence. -/
def structureOf (f : ℕ → Bool) : Structure signature where
  carrier
    | .index => ℕ
    | .bit => Bool
  total := fun name => PEmpty.elim name
  relation := fun name => PEmpty.elim name
  partialDomain := fun name => PEmpty.elim name
  partialValue := fun name => PEmpty.elim name
  quantity _ xs := f xs.head

/-- The initial index interval is sampled and the Boolean results are read as raw outputs. -/
private def sampleNames (n : ℕ) : SequenceSort → Type
  | .index => Fin (n + 1)
  | .bit => PEmpty

/-- All sample names in the binary example lie in the finite initial index interval. -/
private theorem sampleNames_finite (n : ℕ) : Finite (Σ s, sampleNames n s) := by
  let index : (Σ s, sampleNames n s) → Fin (n + 1)
    | ⟨.index, i⟩ => i
    | ⟨.bit, i⟩ => PEmpty.elim i
  apply Finite.of_injective index
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  cases a <;> cases b
  · exact congrArg (Sigma.mk SequenceSort.index) h
  · exact PEmpty.elim j
  · exact PEmpty.elim i
  · exact PEmpty.elim i

/-- Sample only the initial index interval and retain raw answers to its value queries. -/
def schema (n : ℕ) : Schema.{0,0} signature where
  Name := sampleNames n
  finiteNames := sampleNames_finite n
  Index := Fin (n + 1)
  finiteIndices := inferInstance
  query i := .value (.quantity PUnit.unit) (.cons i .empty) .raw

/-- The sample names designate the corresponding natural-number indices. -/
def samples (n : ℕ) : Samples (schema n).Name (structureOf (fun _ => false)).carrier
  | .index, i => i.val
  | .bit, i => PEmpty.elim i

/-- Reading a binary entry through the finite query schema gives the original Boolean value. -/
theorem read_answer (f : ℕ → Bool) (n : ℕ) (i : Fin (n + 1)) :
    ((schema n).read (structureOf f) (samples n)).answer i =
      (show Query.Answer (structureOf f).carrier ((schema n).query i) from some ⟨f i.val⟩) := by
  rw [Schema.read_answer]
  letI : Finite (Σ s, (schema n).Name s) := (schema n).finiteNames
  exact Query.read_value_raw (A := structureOf f) (samples n) (.quantity PUnit.unit) _
    (((structureOf f).graph_quantity_iff PUnit.unit _ _).2 rfl)

/-- Restrict a binary sequence to the finite stage. -/
def observe (f : ℕ → Bool) (n : ℕ) : Stage n := fun i => f i.val

/-- Restrict a larger binary table to the smaller prefix. -/
def restrict {m n : ℕ} (h : m ≤ n) (table : Stage n) : Stage m :=
  fun i => table (Fin.castLE (Nat.succ_le_succ h) i)

/-- The padded extension of a finite binary table has finite support. -/
def extend {n : ℕ} (table : Stage n) : FiniteSequence :=
  ⟨fun i => if h : i < n + 1 then table ⟨i, h⟩ else false, by
    apply (Set.finite_range (fun i : Fin (n + 1) => i.val)).subset
    intro i keep
    by_cases h : i < n + 1
    · exact ⟨⟨i, h⟩, rfl⟩
    · simp [h] at keep⟩

/-- Every finite binary table is the restriction of a finite-support sequence. -/
theorem observe_extend {n : ℕ} (table : Stage n) : observe (extend table).val n = table := by
  funext i
  exact dif_pos i.isLt

/-- Each entry in this prescribed family of tables is true. -/
def allTrue (n : ℕ) : Stage n := fun _ => true

/-- The all-true finite binary tables agree strictly on prefixes. -/
theorem restrict_allTrue {m n : ℕ} (h : m ≤ n) :
    restrict h (allTrue n) = allTrue m :=
  rfl

/-- Any simultaneous realization of all prefixes is pointwise true. -/
theorem all_true_of_observations (f : ℕ → Bool)
    (realizes : ∀ n, observe f n = allTrue n) (i : ℕ) : f i = true :=
  congrFun (realizes i) ⟨i, Nat.lt_succ_self i⟩

/-- No single binary sequence with finite support realizes all the prescribed prefixes. -/
theorem no_finite_support_global :
    ¬ ∃ f : FiniteSequence, ∀ n, observe f.val n = allTrue n := by
  rintro ⟨f, realizes⟩
  have support : {i | f.val i = true} = Set.univ :=
    Set.eq_univ_of_forall (all_true_of_observations _ realizes)
  exact Set.infinite_univ (support ▸ f.property)

/-- Every finite binary table is also realized through the ordinary value-fragment reader. -/
theorem read_extend {n : ℕ} (table : Stage n) (i : Fin (n + 1)) :
    ((schema n).read (structureOf (extend table).val) (samples n)).answer i =
      (show Query.Answer (structureOf (extend table).val).carrier ((schema n).query i) from
        some ⟨table i⟩) := by
  rw [read_answer]
  exact congrArg (fun b => some (⟨b⟩ : ULift Bool)) (congrFun (observe_extend table) i)

/-- The ordinary value-fragment reader cannot simultaneously read every all-true table
from a single binary sequence with finite support. -/
theorem no_finite_support_global_read :
    ¬ ∃ f : FiniteSequence, ∀ (n : ℕ) (i : Fin (n + 1)),
      ((schema n).read (structureOf f.val) (samples n)).answer i =
        (show Query.Answer (structureOf f.val).carrier ((schema n).query i) from some ⟨true⟩) := by
  rintro ⟨f, observes⟩
  apply no_finite_support_global
  refine ⟨f, fun n => funext fun i => ?_⟩
  have answer := observes n i
  rw [read_answer] at answer
  exact congrArg ULift.down (Option.some.inj answer)

end SupportFailure

end SHIGURE.ValueFragment
