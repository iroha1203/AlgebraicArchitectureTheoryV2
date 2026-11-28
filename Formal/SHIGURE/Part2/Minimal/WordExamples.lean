import Formal.SHIGURE.Part2.Minimal.DualObservation

/-! A two-sort system in which a word of length one is necessary. -/

namespace SHIGURE.Minimal.WordExamples

variable (K : Type*) [Field K]

/-- One operation from the first sort to the second, and no others. -/
def TwoSortOp : Bool → Bool → Type
  | false, true => PUnit
  | _, _ => PEmpty

/-- Both state spaces are `K`; the first receives the identity input and the
second receives zero.  The sole operation is the identity. -/
def twoSortSystem : Word.LinearSystem (K := K) TwoSortOp (fun _ => K) (fun _ => K) where
  input
    | false => LinearMap.id
    | true => 0
  operation _ := LinearMap.id

/-- The first sort is reached by empty words. -/
theorem first_reached_at_zero : boundedReach (twoSortSystem K) false 0 = ⊤ := by
  apply top_unique
  intro x _
  apply Submodule.subset_span
  exact ⟨false, Word.nil false, x, le_rfl, rfl⟩

/-- The operation carries the first input to the second sort at length one. -/
theorem second_reached_at_one : boundedReach (twoSortSystem K) true 1 = ⊤ := by
  apply top_unique
  intro x _
  apply Submodule.subset_span
  exact ⟨false, Word.snoc (Word.nil false) PUnit.unit, x, le_rfl, rfl⟩

/-- Thus both sorts are reached by finite words. -/
theorem all_sorts_reached : ∀ s, allReach (twoSortSystem K) s = ⊤ := by
  intro s
  cases s with
  | false =>
    apply top_unique
    rw [← first_reached_at_zero K]
    exact boundedReach_le_allReach _ _ _
  | true =>
    apply top_unique
    rw [← second_reached_at_one K]
    exact boundedReach_le_allReach _ _ _

/-- Empty words cannot reach a nonzero value in the second sort. -/
theorem second_not_reached_at_zero : boundedReach (twoSortSystem K) true 0 = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨s, w, a, hw, rfl⟩
  cases w with
  | nil => simp [Word.evaluate, twoSortSystem]
  | snoc w e => simp [Word.length] at hw

/-- The product of the two state spaces has dimension two. -/
theorem twoSort_dimension : Module.finrank K (∀ _ : Bool, K) = 2 := by
  simp [Module.finrank_pi]

/-- The length bound `N - 1 = 1` cannot be replaced by zero, even for two sorts. -/
theorem length_one_is_necessary :
    (∀ s, allReach (twoSortSystem K) s = ⊤) ∧
      boundedReach (twoSortSystem K) true (2 - 2) ≠ ⊤ := by
  refine ⟨all_sorts_reached K, ?_⟩
  rw [show 2 - 2 = 0 by decide, second_not_reached_at_zero]
  intro h
  have h1 : (1 : K) ∈ (⊥ : Submodule K K) := by rw [h]; exact Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot K).mp h1)

end SHIGURE.Minimal.WordExamples
