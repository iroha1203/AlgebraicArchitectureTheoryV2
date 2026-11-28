import Formal.SHIGURE.Part2.Minimal.TypedWords

/-! Concatenation and reversal of typed words. -/

namespace SHIGURE.Minimal.Word

universe u v
variable {S : Type u} {Op : S → S → Type v}

/-- Execute `w` and then `v`. -/
noncomputable def append {s t u : S} (w : Word Op s t) (v : Word Op t u) : Word Op s u := by
  induction v with
  | nil => exact w
  | snoc v e ih => exact .snoc ih e

@[simp] theorem append_nil {s t : S} (w : Word Op s t) :
    w.append (.nil t) = w := rfl

@[simp] theorem append_snoc {r s t u : S} (w : Word Op r s)
    (v : Word Op s t) (e : Op t u) :
    w.append (.snoc v e) = .snoc (w.append v) e := rfl

@[simp] theorem nil_append {s t : S} (w : Word Op s t) :
    (Word.nil s : Word Op s s).append w = w := by
  induction w with
  | nil => rfl
  | snoc w e ih => simp [ih]

theorem append_assoc {r s t u : S} (w : Word Op r s)
    (v : Word Op s t) (z : Word Op t u) :
    (w.append v).append z = w.append (v.append z) := by
  induction z with
  | nil => rfl
  | snoc z e ih => simp [ih]

@[simp] theorem length_append {s t u : S} (w : Word Op s t) (v : Word Op t u) :
    (w.append v).length = w.length + v.length := by
  induction v with
  | nil => simp [length]
  | snoc v e ih =>
    change (w.append v).length + 1 = w.length + (v.length + 1)
    rw [ih, Nat.add_assoc]

/-- Reverse a word, reversing the source and target of each operation name. -/
noncomputable def reverse {s t : S} (w : Word Op s t) : Word (fun s t => Op t s) t s := by
  induction w with
  | nil => exact .nil _
  | snoc w e ih =>
    exact (Word.snoc (Word.nil _ : Word (fun s t => Op t s) _ _) e).append ih

@[simp] theorem reverse_nil (s : S) :
    (Word.nil s : Word Op s s).reverse = .nil s := rfl

@[simp] theorem reverse_snoc {s t u : S} (w : Word Op s t) (e : Op t u) :
    (w.snoc e).reverse =
      (Word.snoc (Word.nil u : Word (fun s t => Op t s) u u) e).append w.reverse := rfl

@[simp] theorem reverse_append {s t u : S} (w : Word Op s t) (v : Word Op t u) :
    (w.append v).reverse = v.reverse.append w.reverse := by
  induction v with
  | nil => simp
  | snoc v e ih => simp [ih, append_assoc]

@[simp] theorem reverse_reverse {s t : S} (w : Word Op s t) :
    w.reverse.reverse = w := by
  induction w with
  | nil => simp
  | snoc w e ih =>
    rw [reverse_snoc, reverse_append, ih]
    simp only [reverse_snoc, reverse_nil, append_nil, append_snoc]

@[simp] theorem length_reverse {s t : S} (w : Word Op s t) :
    w.reverse.length = w.length := by
  induction w with
  | nil => rfl
  | snoc w e ih =>
    rw [reverse_snoc, length_append, ih]
    change 1 + w.length = w.length + 1
    exact Nat.add_comm _ _

variable {K : Type*} [Field K]
variable {E I : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]

@[simp] theorem evaluate_append (A : LinearSystem (K := K) Op E I)
    {s t u : S} (w : Word Op s t) (v : Word Op t u) :
    (w.append v).evaluate A = (v.evaluate A).comp (w.evaluate A) := by
  induction v with
  | nil => ext x; rfl
  | snoc v e ih =>
    change (A.operation e).comp ((w.append v).evaluate A) =
      ((A.operation e).comp (v.evaluate A)).comp (w.evaluate A)
    rw [ih]
    exact (LinearMap.comp_assoc (w.evaluate A) (v.evaluate A) (A.operation e)).symm

end SHIGURE.Minimal.Word
