import Formal.Util.AssertStandardAxioms
import Mathlib.Data.Setoid.Basic

/-!
# Operation congruences

The state type and operation names may be empty. Finiteness is needed only by
the later table algorithm.
-/

namespace AAT.AG.OperationRepair

universe u v

/-- A family of total named operations on states. -/
structure OperationSystem (S : Type u) (E : Type v) where
  step : E → S → S

namespace OperationSystem

variable {S : Type u} {E : Type v} (T : OperationSystem S E)

/-- Execute a word in list order, including the empty word. -/
def eval (s : S) (w : List E) : S := w.foldl (fun x e => T.step e x) s

@[simp] theorem eval_nil (s : S) : T.eval s [] = s := rfl

@[simp] theorem eval_cons (s : S) (e : E) (w : List E) :
    T.eval s (e :: w) = T.eval (T.step e s) w := rfl

theorem eval_append (s : S) (u v : List E) :
    T.eval s (u ++ v) = T.eval (T.eval s u) v := by
  simp [eval, List.foldl_append]

@[simp] theorem eval_singleton (s : S) (e : E) : T.eval s [e] = T.step e s := rfl

end OperationSystem

/-- An equivalence relation stable under each named operation. -/
structure OperationCongruence {S : Type u} {E : Type v}
    (T : OperationSystem S E) where
  setoid : Setoid S
  stable : ∀ e x y, setoid.r x y → setoid.r (T.step e x) (T.step e y)

namespace OperationCongruence

variable {S : Type u} {E : Type v} {T : OperationSystem S E}

instance : LE (OperationCongruence T) :=
  ⟨fun a b => a.setoid ≤ b.setoid⟩

@[ext] theorem ext {a b : OperationCongruence T} (h : a.setoid = b.setoid) : a = b := by
  cases a; cases b; cases h; rfl

instance : PartialOrder (OperationCongruence T) where
  le_refl _ := fun x y h => h
  le_trans _ _ _ hab hbc := fun x y h => hbc (hab h)
  le_antisymm a b hab hba := ext (le_antisymm hab hba)

/-- Intersections of operation congruences are operation congruences. -/
instance : InfSet (OperationCongruence T) where
  sInf A :=
    { setoid := sInf (OperationCongruence.setoid '' A)
      stable := by
        intro e x y h c hc
        rcases hc with ⟨a, ha, rfl⟩
        exact a.stable e x y (h a.setoid ⟨a, ha, rfl⟩) }

theorem sInf_setoid (A : Set (OperationCongruence T)) :
    (sInf A).setoid = sInf (OperationCongruence.setoid '' A) := rfl

instance : CompleteLattice (OperationCongruence T) :=
  { completeLatticeOfInf (OperationCongruence T) (by
      intro A
      constructor
      · intro a ha
        show (sInf A).setoid ≤ a.setoid
        rw [sInf_setoid]
        intro x y h
        exact (Setoid.sInf_iff.mp h) a.setoid ⟨a, ha, rfl⟩
      · intro a ha
        show a.setoid ≤ (sInf A).setoid
        rw [sInf_setoid]
        intro x y h c hc
        rcases hc with ⟨b, hb, rfl⟩
        exact ha hb h) with
    top :=
      { setoid := ⊤
        stable := by intro e x y h; trivial }
    le_top := by
      intro a
      show a.setoid ≤ (⊤ : Setoid S)
      intro x y h
      trivial }

end OperationCongruence

end AAT.AG.OperationRepair
