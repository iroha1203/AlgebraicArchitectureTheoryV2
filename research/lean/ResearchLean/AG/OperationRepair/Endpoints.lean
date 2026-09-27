import ResearchLean.AG.OperationRepair.Basic

/-!
# Generated and behavioral operation congruences

Both endpoints are constructed from the original operation system, request,
and observation. No finiteness or nonemptiness assumption is needed.
-/

namespace AAT.AG.OperationRepair

universe u v w

variable {S : Type u} {E : Type v} {O : Type w}
variable (T : OperationSystem S E)

/-- The least operation congruence containing a requested relation. -/
def generated (R : S → S → Prop) : OperationCongruence T :=
  sInf {c | ∀ x y, R x y → c.setoid.r x y}

theorem generated_contains {R : S → S → Prop} {x y : S} (h : R x y) :
    (generated T R).setoid.r x y := by
  intro c hc
  rcases hc with ⟨d, hd, rfl⟩
  exact hd x y h

/-- Universal property of the generated operation congruence. -/
theorem generated_le_iff {R : S → S → Prop} (c : OperationCongruence T) :
    generated T R ≤ c ↔ ∀ x y, R x y → c.setoid.r x y := by
  constructor
  · intro h x y hr
    exact h (generated_contains T hr)
  · intro h
    exact sInf_le h

/-- Two states are behaviorally equivalent when every future word has the
same observation. -/
def behavior (observe : S → O) : OperationCongruence T where
  setoid := Setoid.ker (fun x => fun w : List E => observe (T.eval x w))
  stable := by
    intro e x y h
    funext word
    exact congrFun h (e :: word)

@[simp] theorem behavior_iff (observe : S → O) (x y : S) :
    (behavior T observe).setoid.r x y ↔
      ∀ word : List E, observe (T.eval x word) = observe (T.eval y word) := by
  simp [behavior, Setoid.ker_def, funext_iff]

theorem behavior_le_kernel (observe : S → O) :
    (behavior T observe).setoid ≤ Setoid.ker observe := by
  intro x y h
  exact (behavior_iff T observe x y).mp h []

/-- Every operation congruence preserving present observations also preserves
observations after every operation word. -/
theorem le_behavior_iff (observe : S → O) (c : OperationCongruence T) :
    c ≤ behavior T observe ↔ c.setoid ≤ Setoid.ker observe := by
  constructor
  · intro h
    exact le_trans h (behavior_le_kernel T observe)
  · intro h x y hxy
    apply (behavior_iff T observe x y).mpr
    intro word
    have stable_word : ∀ (w : List E) (a b : S),
        c.setoid.r a b → c.setoid.r (T.eval a w) (T.eval b w) := by
      intro w
      induction w with
      | nil => intro a b hab; exact hab
      | cons e w ih =>
          intro a b hab
          exact ih (T.step e a) (T.step e b) (c.stable e a b hab)
    exact h (stable_word word x y hxy)

theorem generated_le_behavior_iff (observe : S → O) (R : S → S → Prop) :
    generated T R ≤ behavior T observe ↔
      ∀ x y, R x y → (behavior T observe).setoid.r x y :=
  generated_le_iff T (behavior T observe)

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
