import ResearchLean.AG.OperationRepair.FiniteTables
import Mathlib.Computability.DFA

/-!
# Short observation-separating words from numbered tables

The table stores a concrete word when found. Round `k + 1` reads only round
`k`, retaining existing words and prepending the first successful operation
name to a word for its successor pair.
-/

namespace AAT.AG.OperationRepair

namespace FiniteBehavior

variable {n m : Nat} {O : Type*} [DecidableEq O]

abbrev WitnessTable (n m : Nat) :=
  FiniteTable (FiniteTable (Option (List (Fin m))) n) n

def get (table : WitnessTable n m) (x y : Fin n) : Option (List (Fin m)) :=
  FiniteTable.get (FiniteTable.get table x) y

/-- Current observation disagreement has the empty separating word. -/
def initial (input : FiniteRepairInput n m O) : WitnessTable n m :=
  FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    if input.observe x = input.observe y then none else some []

@[simp] theorem initial_get (input : FiniteRepairInput n m O) (x y : Fin n) :
    get (initial input) x y =
      (if input.observe x = input.observe y then none else some []) := by
  simp [get, initial]

/-- One synchronous word-discovery round. -/
def step (input : FiniteRepairInput n m O) (old : WitnessTable n m) :
    WitnessTable n m :=
  FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    match get old x y with
    | some word => some word
    | none => (List.finRange m).findSome? fun e =>
        (get old (input.step e x) (input.step e y)).map (e :: ·)

@[simp] theorem step_get (input : FiniteRepairInput n m O)
    (old : WitnessTable n m) (x y : Fin n) :
    get (step input old) x y =
      match get old x y with
      | some word => some word
      | none => (List.finRange m).findSome? fun e =>
          (get old (input.step e x) (input.step e y)).map (e :: ·) := by
  simp [get, step]

def rounds (input : FiniteRepairInput n m O) (k : Nat) : WitnessTable n m :=
  (step input)^[k] (initial input)

@[simp] theorem rounds_zero (input : FiniteRepairInput n m O) :
    rounds input 0 = initial input := rfl

theorem rounds_succ (input : FiniteRepairInput n m O) (k : Nat) :
    rounds input (k + 1) = step input (rounds input k) := by
  simp [rounds, Function.iterate_succ_apply']

theorem step_none_iff (input : FiniteRepairInput n m O)
    (old : WitnessTable n m) (x y : Fin n) :
    get (step input old) x y = none ↔
      get old x y = none ∧
      ∀ e : Fin m, get old (input.step e x) (input.step e y) = none := by
  rw [step_get]
  cases h : get old x y with
  | some w => simp [h]
  | none =>
      simp [h, List.findSome?_eq_none_iff, Option.map_eq_none_iff]

theorem step_some_iff (input : FiniteRepairInput n m O)
    (old : WitnessTable n m) (x y : Fin n) (word : List (Fin m)) :
    get (step input old) x y = some word →
      get old x y = some word ∨
      ∃ e : Fin m, ∃ tail : List (Fin m),
        get old (input.step e x) (input.step e y) = some tail ∧ word = e :: tail := by
  rw [step_get]
  cases h : get old x y with
  | some w =>
      simp only [h]
      intro hw
      left
      simpa [h] using hw
  | none =>
      simp only [h]
      intro hw
      obtain ⟨e, he, hmap⟩ := List.exists_of_findSome?_eq_some hw
      right
      cases ht : get old (input.step e x) (input.step e y) with
      | none => simp [ht] at hmap
      | some tail =>
          refine ⟨e, tail, ht, ?_⟩
          simpa [ht] using hmap.symm

def separates (input : FiniteRepairInput n m O)
    (x y : Fin n) (word : List (Fin m)) : Prop :=
  input.observe (input.system.eval x word) ≠
    input.observe (input.system.eval y word)

theorem rounds_some_sound (input : FiniteRepairInput n m O)
    (k : Nat) (x y : Fin n) (word : List (Fin m))
    (h : get (rounds input k) x y = some word) :
    word.length ≤ k ∧ separates input x y word := by
  induction k generalizing x y word with
  | zero =>
      rw [rounds_zero, initial_get] at h
      split at h
      · contradiction
      · have hw : word = [] := by simpa using h.symm
        subst word
        constructor
        · simp
        · simpa [separates] using ‹input.observe x ≠ input.observe y›
  | succ k ih =>
      rw [rounds_succ] at h
      rcases step_some_iff input (rounds input k) x y word h with
        hold | ⟨e, tail, htail, rfl⟩
      · obtain ⟨hlen, hsep⟩ := ih x y word hold
        exact ⟨by omega, hsep⟩
      · obtain ⟨hlen, hsep⟩ := ih (input.step e x) (input.step e y) tail htail
        exact ⟨by simp; omega, by simpa [separates] using hsep⟩

/-- A `none` cell means that no word of length at most this round's index
separates the pair. This is proved for the same stored-word recurrence. -/
theorem rounds_none_iff (input : FiniteRepairInput n m O)
    (k : Nat) (x y : Fin n) :
    get (rounds input k) x y = none ↔
      ∀ word : List (Fin m), word.length ≤ k →
        input.observe (input.system.eval x word) =
          input.observe (input.system.eval y word) := by
  induction k generalizing x y with
  | zero =>
      rw [rounds_zero, initial_get]
      have hz :
          (∀ word : List (Fin m), word.length ≤ 0 →
            input.observe (input.system.eval x word) =
              input.observe (input.system.eval y word)) ↔
            input.observe x = input.observe y := by
        constructor
        · intro h
          simpa using h [] (by simp)
        · intro h word hw
          cases word with
          | nil => simpa using h
          | cons e tail => simp at hw
      rw [hz]
      by_cases h : input.observe x = input.observe y <;> simp [h]
  | succ k ih =>
      rw [rounds_succ, step_none_iff]
      constructor
      · rintro ⟨hxy, hsucc⟩ word hw
        cases word with
        | nil =>
            exact (ih x y).mp hxy [] (by simp)
        | cons e tail =>
            have ht : tail.length ≤ k := by simp at hw; omega
            have htail := (ih (input.step e x) (input.step e y)).mp (hsucc e) tail ht
            simpa using htail
      · intro hall
        constructor
        · by_cases hxy : get (rounds input k) x y = none
          · exact hxy
          · cases hw : get (rounds input k) x y with
            | none => contradiction
            | some word =>
                obtain ⟨hlen, hsep⟩ := rounds_some_sound input k x y word hw
                exact False.elim (hsep (hall word (by omega)))
        · intro e
          by_cases he : get (rounds input k) (input.step e x) (input.step e y) = none
          · exact he
          · cases hw : get (rounds input k) (input.step e x) (input.step e y) with
            | none => contradiction
            | some tail =>
                obtain ⟨hlen, hsep⟩ := rounds_some_sound input k
                  (input.step e x) (input.step e y) tail hw
                have hsame := hall (e :: tail) (by simp; omega)
                exact False.elim (hsep (by simpa using hsame))

/-- The pair automaton used solely to shorten a distinguishing word. Its
start is the pair under consideration, so the empty state type is never
inhabited artificially. -/
def pairDFA (input : FiniteRepairInput n m O) (x y : Fin n) :
    DFA (Fin m) (Fin n × Fin n) where
  step := fun p e => (input.step e p.1, input.step e p.2)
  start := (x, y)
  accept := {p | input.observe p.1 ≠ input.observe p.2}

theorem pairDFA_evalFrom (input : FiniteRepairInput n m O)
    (x y : Fin n) (p : Fin n × Fin n) (word : List (Fin m)) :
    (pairDFA input x y).evalFrom p word =
      (input.system.eval p.1 word, input.system.eval p.2 word) := by
  induction word generalizing p with
  | nil => rfl
  | cons e tail ih =>
      simpa [pairDFA, FiniteRepairInput.system, FiniteRepairInput.step] using
        ih (input.step e p.1, input.step e p.2)

theorem short_separator (input : FiniteRepairInput n m O)
    (x y : Fin n) (word : List (Fin m))
    (h : separates input x y word) :
    ∃ short : List (Fin m), short.length < n * n ∧
      separates input x y short := by
  have aux : ∀ len : Nat, ∀ w : List (Fin m), w.length = len →
      separates input x y w →
      ∃ short : List (Fin m), short.length < n * n ∧
        separates input x y short := by
    intro len
    induction len using Nat.strong_induction_on with
    | h len ih =>
        intro w hwlen hwsep
        by_cases hshort : w.length < n * n
        · exact ⟨w, hshort, hwsep⟩
        · have hlen : Fintype.card (Fin n × Fin n) ≤ w.length := by
            simpa using (Nat.le_of_not_gt hshort)
          let M := pairDFA input x y
          have heval : M.evalFrom (x, y) w =
              (input.system.eval x w, input.system.eval y w) :=
            pairDFA_evalFrom input x y (x, y) w
          obtain ⟨q, a, b, c, hword, _, hbne, hstart, hloop, hend⟩ :=
            M.evalFrom_split hlen heval
          have hsame : M.evalFrom (x, y) (a ++ c) = M.evalFrom (x, y) w := by
            rw [hword, M.evalFrom_of_append, hstart, hend,
              M.evalFrom_of_append, M.evalFrom_of_append, hstart, hloop, hend]
          have hsep : separates input x y (a ++ c) := by
            have hp := congrArg (fun p : Fin n × Fin n =>
              input.observe p.1 ≠ input.observe p.2) hsame
            have hacc : input.observe (M.evalFrom (x, y) w).1 ≠
                input.observe (M.evalFrom (x, y) w).2 := by
              simpa [M, pairDFA_evalFrom, separates] using hwsep
            simpa [M, pairDFA_evalFrom, separates] using (hp.mpr hacc)
          have hlt : (a ++ c).length < w.length := by
            rw [hword]
            simp only [List.length_append]
            have hbpos : 0 < b.length := List.length_pos_of_ne_nil hbne
            omega
          exact ih (a ++ c).length (by omega) (a ++ c) rfl hsep
  exact aux word.length word rfl h

/-- All discovered words have length strictly below `n²` after the last
round, and `none` cells form the upper partition. -/
def upper (input : FiniteRepairInput n m O) : WitnessTable n m :=
  rounds input (n * n - 1)

def upperRel (input : FiniteRepairInput n m O) (x y : Fin n) : Prop :=
  get (upper input) x y = none

/-- The computed upper partition is exactly behavioral equivalence. -/
theorem computedUpper_iff_behavior (input : FiniteRepairInput n m O)
    (x y : Fin n) :
    upperRel input x y ↔
      (behavior input.system input.observe).setoid.r x y := by
  rw [behavior_iff]
  unfold upperRel upper
  constructor
  · intro h word
    by_contra hneq
    obtain ⟨short, hlength, hsep⟩ :=
      short_separator input x y word hneq
    have hlength' : short.length ≤ n * n - 1 := by omega
    exact hsep ((rounds_none_iff input (n * n - 1) x y).mp h short hlength')
  · intro h
    exact (rounds_none_iff input (n * n - 1) x y).mpr
      (fun word _ => h word)

/-- Every stored failure word separates its pair and meets GOAL D's
strict `n²` bound. -/
theorem upper_some_certificate (input : FiniteRepairInput n m O)
    (x y : Fin n) (word : List (Fin m))
    (h : get (upper input) x y = some word) :
    word.length < n * n ∧ separates input x y word := by
  obtain ⟨hlen, hsep⟩ := rounds_some_sound input (n * n - 1) x y word h
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le x.val) x.isLt
  have hpositive : 0 < n * n := Nat.mul_pos hn hn
  exact ⟨by omega, hsep⟩

end FiniteBehavior

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
