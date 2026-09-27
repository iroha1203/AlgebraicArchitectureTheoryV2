import ResearchLean.AG.OperationRepair.FiniteTables
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

/-!
# Synchronous lower-endpoint closure on Boolean relation tables

Each round reads only the previous table. The four update passes copy the
input, add converse pairs, add composable pairs, and add operation images.
The passes write to the new table but never use those new cells as premises.
-/

namespace AAT.AG.OperationRepair

namespace FiniteClosure

variable {n m : Nat} {O : Type*}

def states (n : Nat) : List (Fin n) := List.finRange n

def pairs (n : Nat) : List (Fin n × Fin n) :=
  (states n).flatMap fun x => (states n).map fun y => (x, y)

def triples (n : Nat) : List (Fin n × Fin n × Fin n) :=
  (states n).flatMap fun x =>
    (states n).flatMap fun y => (states n).map fun z => (x, y, z)

/-- The initial table contains the diagonal and every requested pair. -/
def initial (input : FiniteRepairInput n m O) : RelationTable n :=
  FiniteTable.ofFn fun x =>
    FiniteTable.ofFn fun y => decide (x = y) || input.wants x y

@[simp] theorem initial_get (input : FiniteRepairInput n m O) (x y : Fin n) :
    (initial input).get x y = (decide (x = y) || input.wants x y) := by
  simp [initial, RelationTable.get]

/-- Add the targets of exactly those list entries whose predicate is true. -/
def markPass {α : Type*} (items : List α) (pred : α → Bool)
    (target : α → Fin n × Fin n) (out : RelationTable n) : RelationTable n :=
  items.foldl (fun table a =>
    if pred a then table.set (target a).1 (target a).2 true else table) out

theorem markPass_get_iff {α : Type*} (items : List α) (pred : α → Bool)
    (target : α → Fin n × Fin n) (out : RelationTable n) (x y : Fin n) :
    (markPass items pred target out).get x y = true ↔
      out.get x y = true ∨
        ∃ a ∈ items, pred a = true ∧ target a = (x, y) := by
  induction items generalizing out with
  | nil => simp [markPass]
  | cons a rest ih =>
      simp only [markPass, List.foldl_cons]
      change (markPass rest pred target
        (if pred a then out.set (target a).1 (target a).2 true else out)).get x y = true ↔ _
      rw [ih]
      by_cases hp : pred a = true
      · simp only [if_pos hp, RelationTable.get_set_true_iff]
        have heq :
            (x = (target a).1 ∧ y = (target a).2) ↔ target a = (x, y) := by
          cases h : target a with
          | mk u v => simp [h, eq_comm]
        simp [hp, heq, or_assoc, or_left_comm, or_comm]
      · have hf : pred a = false := Bool.eq_false_iff.mpr hp
        simp [hf, ih]

/-- One synchronous update. The source `old` remains read-only in every
pass, including the pass for transitivity and the pass for operation images. -/
def closeStep (input : FiniteRepairInput n m O) (old : RelationTable n) :
    RelationTable n :=
  let converse := markPass (pairs n)
    (fun p => old.get p.1 p.2) (fun p => (p.2, p.1)) old
  let transitive := markPass (triples n)
    (fun p => old.get p.1 p.2.1 && old.get p.2.1 p.2.2)
    (fun p => (p.1, p.2.2)) converse
  markPass ((states m).flatMap fun e => (pairs n).map fun p => (e, p))
    (fun p => old.get p.2.1 p.2.2)
    (fun p => (input.step p.1 p.2.1, input.step p.1 p.2.2)) transitive

/-- Exactly `n²` synchronous rounds, including zero rounds for `n = 0`. -/
def lower (input : FiniteRepairInput n m O) : RelationTable n :=
  (closeStep input)^[n * n] (initial input)

def rounds (input : FiniteRepairInput n m O) (k : Nat) : RelationTable n :=
  (closeStep input)^[k] (initial input)

@[simp] theorem rounds_zero (input : FiniteRepairInput n m O) :
    rounds input 0 = initial input := rfl

theorem rounds_succ (input : FiniteRepairInput n m O) (k : Nat) :
    rounds input (k + 1) = closeStep input (rounds input k) := by
  simp [rounds, Function.iterate_succ_apply']

theorem lower_eq_rounds (input : FiniteRepairInput n m O) :
    lower input = rounds input (n * n) := rfl

theorem mem_pairs (x y : Fin n) : (x, y) ∈ pairs n := by
  simp [pairs, states]

theorem mem_triples (x y z : Fin n) : (x, y, z) ∈ triples n := by
  simp [triples, states]

/-- The concrete synchronous table update has exactly the four closure
premises specified by GOAL D. -/
theorem closeStep_get_iff (input : FiniteRepairInput n m O)
    (old : RelationTable n) (x y : Fin n) :
    (closeStep input old).get x y = true ↔
      old.get x y = true ∨ old.get y x = true ∨
      (∃ z : Fin n, old.get x z = true ∧ old.get z y = true) ∨
      (∃ e : Fin m, ∃ a b : Fin n, old.get a b = true ∧
        input.step e a = x ∧ input.step e b = y) := by
  simp only [closeStep, markPass_get_iff]
  simp [pairs, triples, states, List.mem_flatMap, List.mem_map,
    Prod.mk.injEq, and_assoc, or_assoc]

/-- The set of true cells of a Boolean relation table. -/
def support (r : RelationTable n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => r.get p.1 p.2

@[simp] theorem mem_support (r : RelationTable n) (x y : Fin n) :
    (x, y) ∈ support r ↔ r.get x y = true := by
  simp [support]

theorem support_card_le (r : RelationTable n) : (support r).card ≤ n * n := by
  calc
    (support r).card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n * n := by simp

theorem support_subset_closeStep (input : FiniteRepairInput n m O)
    (r : RelationTable n) : support r ⊆ support (closeStep input r) := by
  intro p hp
  rcases p with ⟨x, y⟩
  exact (mem_support _ _ _).mpr ((closeStep_get_iff input r x y).mpr
    (Or.inl ((mem_support _ _ _).mp hp)))

theorem support_initial_subset_rounds (input : FiniteRepairInput n m O)
    (k : Nat) : support (initial input) ⊆ support (rounds input k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        support (initial input) ⊆ support (rounds input k) := ih
        _ ⊆ support (rounds input (k + 1)) := by
          rw [rounds_succ]
          exact support_subset_closeStep input _

theorem closeStep_mono (input : FiniteRepairInput n m O)
    {r s : RelationTable n} (hrs : support r ⊆ support s) :
    support (closeStep input r) ⊆ support (closeStep input s) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hs : ∀ a b, r.get a b = true → s.get a b = true := by
    intro a b h
    exact (mem_support _ _ _).mp (hrs ((mem_support _ _ _).mpr h))
  apply (mem_support _ _ _).mpr
  rcases (closeStep_get_iff input r x y).mp ((mem_support _ _ _).mp hp) with
    h | h | ⟨z, h₁, h₂⟩ | ⟨e, a, b, h, ha, hb⟩
  · exact (closeStep_get_iff input s x y).mpr (Or.inl (hs _ _ h))
  · exact (closeStep_get_iff input s x y).mpr (Or.inr (Or.inl (hs _ _ h)))
  · exact (closeStep_get_iff input s x y).mpr
      (Or.inr (Or.inr (Or.inl ⟨z, hs _ _ h₁, hs _ _ h₂⟩)))
  · exact (closeStep_get_iff input s x y).mpr
      (Or.inr (Or.inr (Or.inr ⟨e, a, b, hs _ _ h, ha, hb⟩)))

theorem support_injective : Function.Injective (support (n := n)) := by
  intro r s h
  apply RelationTable.ext
  intro x y
  have hmem : r.get x y = true ↔ s.get x y = true := by
    simpa only [← mem_support] using
      (congrArg (fun t : Finset (Fin n × Fin n) => (x, y) ∈ t) h).to_iff
  cases hr : r.get x y <;> cases hs : s.get x y <;> simp_all

private theorem iterate_eq_after {α : Type*} (f : α → α) (x : α) (k : Nat)
    (h : f^[k] x = f^[k + 1] x) (j : Nat) :
    f^[k + j] x = f^[k] x := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply', ih]
      simpa only [Function.iterate_succ_apply'] using h.symm

/-- There are `n²` possible pairs, so the synchronous increasing sequence
has reached a fixed point after exactly `n²` rounds. -/
theorem lower_fixed (input : FiniteRepairInput n m O) :
    closeStep input (lower input) = lower input := by
  let f := closeStep input
  let start := initial input
  let N := n * n
  have hnext (k : Nat) : support (f^[k] start) ⊆ support (f^[k + 1] start) := by
    simpa only [Function.iterate_succ_apply'] using
      support_subset_closeStep input (f^[k] start)
  by_contra hfixed
  have hnot (k : Nat) (hk : k ≤ N) : f^[k] start ≠ f^[k + 1] start := by
    intro heq
    have h₁ := iterate_eq_after f start k heq (N - k)
    have h₂ := iterate_eq_after f start k heq (N + 1 - k)
    have hkn : k + (N - k) = N := by omega
    have hkn₁ : k + (N + 1 - k) = N + 1 := by omega
    rw [hkn] at h₁
    rw [hkn₁] at h₂
    apply hfixed
    change f (f^[N] start) = f^[N] start
    simpa only [Function.iterate_succ_apply'] using h₂.trans h₁.symm
  have hstrict (k : Nat) (hk : k ≤ N) :
      (support (f^[k] start)).card < (support (f^[k + 1] start)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · exact hnext k
    · intro heq
      exact hnot k hk (support_injective heq)
  have hcard (k : Nat) (hk : k ≤ N + 1) :
      k ≤ (support (f^[k] start)).card := by
    induction k with
    | zero => omega
    | succ k ih =>
        have hkN : k ≤ N := by omega
        have hs := hstrict k hkN
        have hle := ih (by omega)
        omega
  have hbound := support_card_le (f^[N + 1] start)
  have hlarge := hcard (N + 1) (by omega)
  omega

theorem lower_refl (input : FiniteRepairInput n m O) (x : Fin n) :
    (lower input).get x x = true := by
  apply (mem_support _ _ _).mp
  apply support_initial_subset_rounds input (n * n)
  exact (mem_support _ _ _).mpr (by simp)

theorem lower_symm (input : FiniteRepairInput n m O) {x y : Fin n}
    (h : (lower input).get x y = true) : (lower input).get y x = true := by
  have hs := (closeStep_get_iff input (lower input) y x).mpr
    (Or.inr (Or.inl h))
  simpa [lower_fixed input] using hs

theorem lower_trans (input : FiniteRepairInput n m O) {x y z : Fin n}
    (hxy : (lower input).get x y = true)
    (hyz : (lower input).get y z = true) : (lower input).get x z = true := by
  have ht := (closeStep_get_iff input (lower input) x z).mpr
    (Or.inr (Or.inr (Or.inl ⟨y, hxy, hyz⟩)))
  simpa [lower_fixed input] using ht

theorem lower_stable (input : FiniteRepairInput n m O) (e : Fin m)
    {x y : Fin n} (h : (lower input).get x y = true) :
    (lower input).get (input.step e x) (input.step e y) = true := by
  have ht := (closeStep_get_iff input (lower input)
    (input.step e x) (input.step e y)).mpr
      (Or.inr (Or.inr (Or.inr ⟨e, x, y, h, rfl, rfl⟩)))
  simpa [lower_fixed input] using ht

/-- The output of the concrete lower table algorithm is an operation
congruence, with no certificate supplied by the caller. -/
def lowerCongruence (input : FiniteRepairInput n m O) :
    OperationCongruence input.system where
  setoid :=
    { r := fun x y => (lower input).get x y = true
      iseqv := ⟨lower_refl input, fun {_ _} h => lower_symm input h,
        fun {_ _ _} h₁ h₂ => lower_trans input h₁ h₂⟩ }
  stable := by
    intro e x y h
    exact lower_stable input e h

theorem lower_contains_request (input : FiniteRepairInput n m O)
    {x y : Fin n} (h : input.requestRel x y) :
    (lowerCongruence input).setoid.r x y := by
  apply (mem_support _ _ _).mp
  apply support_initial_subset_rounds input (n * n)
  exact (mem_support _ _ _).mpr (by
    rw [initial_get]
    change input.wants x y = true at h
    simp [h])

theorem rounds_le_congruence (input : FiniteRepairInput n m O)
    (c : OperationCongruence input.system)
    (hR : ∀ x y, input.requestRel x y → c.setoid.r x y)
    (k : Nat) (x y : Fin n)
    (h : (rounds input k).get x y = true) : c.setoid.r x y := by
  induction k generalizing x y with
  | zero =>
      rw [rounds_zero, initial_get] at h
      by_cases heq : x = y
      · subst y
        exact c.setoid.refl x
      · have hr : input.wants x y = true := by simpa [heq] using h
        exact hR x y hr
  | succ k ih =>
      rw [rounds_succ] at h
      rcases (closeStep_get_iff input (rounds input k) x y).mp h with
        hxy | hyx | ⟨z, hxz, hzy⟩ | ⟨e, a, b, hab, ha, hb⟩
      · exact ih x y hxy
      · exact c.setoid.symm (ih y x hyx)
      · exact c.setoid.trans (ih x z hxz) (ih z y hzy)
      · subst x; subst y
        exact c.stable e a b (ih a b hab)

/-- The `n²`-round table is exactly A's least operation congruence. -/
theorem computedLower_eq_generated (input : FiniteRepairInput n m O) :
    lowerCongruence input = generated input.system input.requestRel := by
  apply le_antisymm
  · intro x y h
    exact rounds_le_congruence input
      (generated input.system input.requestRel)
      (fun _ _ hr => generated_contains input.system hr)
      (n * n) x y h
  · exact (generated_le_iff input.system (lowerCongruence input)).mpr
      (fun _ _ hr => lower_contains_request input hr)

end FiniteClosure

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
