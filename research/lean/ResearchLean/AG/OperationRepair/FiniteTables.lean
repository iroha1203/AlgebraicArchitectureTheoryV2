import ResearchLean.AG.OperationRepair.Endpoints

/-!
# Numbered finite operation tables

The input contains only the transition, observation, and request tables. A
table read uses a `Fin` index and its stored size invariant; no default state
is required when the state type is empty.
-/

namespace AAT.AG.OperationRepair

universe u

/-- An array with its number of cells fixed by the type. -/
structure FiniteTable (α : Type u) (k : Nat) where
  data : Array α
  size_eq : data.size = k

namespace FiniteTable

variable {α : Type u} {k : Nat}

/-- An in-bounds table read. -/
def get (t : FiniteTable α k) (i : Fin k) : α :=
  t.data[i.val]'(by simpa [t.size_eq] using i.isLt)

/-- A table built from an indexed function. -/
def ofFn (f : Fin k → α) : FiniteTable α k :=
  ⟨Array.ofFn f, by simp⟩

@[simp] theorem get_ofFn (f : Fin k → α) (i : Fin k) :
    (ofFn f).get i = f i := by
  simp [get, ofFn]

@[ext] theorem ext {a b : FiniteTable α k}
    (h : ∀ i : Fin k, a.get i = b.get i) : a = b := by
  have hd : a.data = b.data := by
    apply Array.ext
    · simpa [a.size_eq, b.size_eq]
    · intro i hi hj
      let fi : Fin k := ⟨i, by simpa [a.size_eq] using hi⟩
      exact h fi
  cases a with
  | mk ad ah =>
    cases b with
    | mk bd bh =>
      cases hd
      rfl

/-- Replace one in-bounds cell without changing table size. -/
def set (t : FiniteTable α k) (i : Fin k) (value : α) : FiniteTable α k :=
  ⟨t.data.set i.val value (by simpa [t.size_eq] using i.isLt), by simp [t.size_eq]⟩

@[simp] theorem get_set_same (t : FiniteTable α k) (i : Fin k) (value : α) :
    (t.set i value).get i = value := by
  simp [get, set]

@[simp] theorem get_set_ne (t : FiniteTable α k) (i j : Fin k)
    (value : α) (h : j ≠ i) :
    (t.set i value).get j = t.get j := by
  have hij : i.val ≠ j.val := Fin.val_ne_of_ne (Ne.symm h)
  have hi : i.val < t.data.size := by simpa [t.size_eq] using i.isLt
  have hj : j.val < t.data.size := by simpa [t.size_eq] using j.isLt
  change (t.data.set i.val value hi)[j.val]'(by simpa using hj) = t.data[j.val]'hj
  exact Array.getElem_set_ne hi hj hij

end FiniteTable

/-- A Boolean relation stored as an `n × n` array table. -/
abbrev RelationTable (n : Nat) := FiniteTable (FiniteTable Bool n) n

namespace RelationTable

variable {n : Nat}

def get (r : RelationTable n) (x y : Fin n) : Bool :=
  FiniteTable.get (FiniteTable.get r x) y

def set (r : RelationTable n) (x y : Fin n) (value : Bool) : RelationTable n :=
  FiniteTable.set r x (FiniteTable.set (FiniteTable.get r x) y value)

@[ext] theorem ext {a b : RelationTable n}
    (h : ∀ x y, a.get x y = b.get x y) : a = b := by
  apply FiniteTable.ext
  intro x
  apply FiniteTable.ext
  intro y
  exact h x y

@[simp] theorem get_set_same (r : RelationTable n) (x y : Fin n) (value : Bool) :
    (r.set x y value).get x y = value := by
  simp [get, set]

@[simp] theorem get_set_other (r : RelationTable n) (x y a b : Fin n)
    (value : Bool) (h : a ≠ x ∨ b ≠ y) :
    (r.set x y value).get a b = r.get a b := by
  rcases h with ha | hb
  · simp [get, set, ha]
  · by_cases ha : a = x
    · subst a
      simp [get, set, hb]
    · simp [get, set, ha]

theorem get_set_true_iff (r : RelationTable n) (x y a b : Fin n) :
    (r.set a b true).get x y = true ↔
      r.get x y = true ∨ (x = a ∧ y = b) := by
  by_cases hxa : x = a
  · by_cases hyb : y = b
    · subst x; subst y
      simp
    · simp [get_set_other, hyb, hxa]
  · simp [get_set_other, hxa]

end RelationTable

/-- The numbered input specified in GOAL D. `O` need only have decidable
equality; it need not be finite. -/
structure FiniteRepairInput (n m : Nat) (O : Type u) where
  transition : FiniteTable (FiniteTable (Fin n) n) m
  observation : FiniteTable O n
  request : RelationTable n

namespace FiniteRepairInput

variable {n m : Nat} {O : Type u} (input : FiniteRepairInput n m O)

def step (e : Fin m) (s : Fin n) : Fin n :=
  (input.transition.get e).get s

def observe (s : Fin n) : O := input.observation.get s

def wants (x y : Fin n) : Bool := input.request.get x y

def system : OperationSystem (Fin n) (Fin m) := ⟨input.step⟩

def requestRel (x y : Fin n) : Prop := input.wants x y = true

end FiniteRepairInput

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
