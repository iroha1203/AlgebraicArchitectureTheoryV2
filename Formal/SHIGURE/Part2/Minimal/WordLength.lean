import Formal.SHIGURE.Part2.Minimal.TypedWords
import Formal.SHIGURE.Part2.Minimal.DimensionGrowth
import Mathlib.LinearAlgebra.Pi

/-! Finite-dimensional reachability by short typed words. -/

namespace SHIGURE.Minimal

variable {K S : Type*} [Field K]
variable {Op : S → S → Type*} {E I : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]

/-- The direct sum of the per-sort reachable spaces, represented by a finite product. -/
noncomputable def totalReach (A : Word.LinearSystem (K := K) Op E I) (n : ℕ) :
    Submodule K (∀ s, E s) :=
  Submodule.pi Set.univ (fun s => boundedReach A s n)

/-- Inclusion of products of subspaces implies inclusion in each component. -/
theorem component_le_of_pi_le (p q : ∀ s, Submodule K (E s))
    (h : Submodule.pi Set.univ p ≤ Submodule.pi Set.univ q) (s : S) : p s ≤ q s := by
  classical
  intro x hx
  have hx' : (LinearMap.single K E s) x ∈ Submodule.pi Set.univ p := by
    exact Submodule.le_comap_single_pi p hx
  have hy := (Submodule.mem_pi.mp (h hx')) s (Set.mem_univ s)
  simpa [LinearMap.single_apply] using hy

/-- Reachability on the finite product is an increasing filtration. -/
theorem totalReach_mono (A : Word.LinearSystem (K := K) Op E I) :
    Monotone (totalReach A) := by
  intro m n hmn
  apply Submodule.pi_mono
  intro s _
  exact boundedReach_mono A s hmn

/-- If every input is zero then all finite-word reachable spaces are zero. -/
theorem allReach_eq_bot_of_input_eq_zero (A : Word.LinearSystem (K := K) Op E I)
    (hinput : ∀ s a, A.input s a = 0) (s : S) : allReach A s = ⊥ := by
  have word_zero : ∀ {u t : S} (w : Word Op u t) (a : I u),
      w.evaluate A (A.input u a) = 0 := by
    intro u t w
    induction w with
    | nil =>
      intro a
      exact hinput u a
    | @snoc t v w e ih =>
      intro a
      change A.operation e (w.evaluate A (A.input u a)) = 0
      rw [ih a, map_zero]
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨u, w, a, rfl⟩
  rw [word_zero w a]
  exact Submodule.zero_mem _

/-- If the product filtration stops, all-word reachability makes it the whole product. -/
theorem totalReach_stationary_eq_top (A : Word.LinearSystem (K := K) Op E I)
    (hall : ∀ s, allReach A s = ⊤) (n : ℕ)
    (h : totalReach A n = totalReach A (n + 1)) : totalReach A n = ⊤ := by
  have hcomponents : ∀ s, boundedReach A s (n + 1) = boundedReach A s n := by
    intro s
    apply le_antisymm
    · exact component_le_of_pi_le _ _ (le_of_eq h.symm) s
    · exact boundedReach_mono A s (Nat.le_succ n)
  have ht : ∀ s, boundedReach A s n = ⊤ := by
    intro s
    apply top_unique
    rw [← hall s]
    exact allReach_le_of_stationary A n hcomponents s
  simp [totalReach, ht]

section Finite

variable [Fintype S] [∀ s, FiniteDimensional K (E s)]

/-- Under all-word reachability, positive total dimension forces a nonzero input stage. -/
theorem totalReach_zero_ne_bot (A : Word.LinearSystem (K := K) Op E I)
    (hall : ∀ s, allReach A s = ⊤)
    (hpositive : 0 < Module.finrank K (∀ s, E s)) : totalReach A 0 ≠ ⊥ := by
  intro hbot
  have hcomponents : ∀ s, boundedReach A s 0 = ⊥ := by
    intro s
    apply le_antisymm
    · apply component_le_of_pi_le (fun t => boundedReach A t 0) (fun _ => ⊥) _ s
      rw [Submodule.pi_univ_bot]
      exact le_of_eq hbot
    · exact bot_le
  have hinput : ∀ s a, A.input s a = 0 := by
    intro s a
    have ha : A.input s a ∈ boundedReach A s 0 := by
      apply Submodule.subset_span
      exact ⟨s, Word.nil s, a, le_rfl, rfl⟩
    rw [hcomponents s] at ha
    exact (Submodule.mem_bot K).mp ha
  have hallbot : ∀ s, allReach A s = ⊥ := allReach_eq_bot_of_input_eq_zero A hinput
  have htopbot : (⊤ : Submodule K (∀ s, E s)) = ⊥ := by
    apply le_antisymm
    · intro x _
      rw [Submodule.mem_bot]
      funext s
      have hs : (⊤ : Submodule K (E s)) ≤ ⊥ := by rw [← hall s, hallbot s]
      exact (Submodule.mem_bot K).mp (hs (Submodule.mem_top))
    · exact bot_le
  have hr := congrArg (fun p : Submodule K (∀ s, E s) => Module.finrank K p) htopbot
  have hzero : Module.finrank K (∀ s, E s) = 0 := by simpa using hr
  omega

/-- All-word reachability is equivalent to reachability by words of length at most N−1,
where N is the sum of the dimensions of the state spaces. -/
theorem allReach_iff_boundedReach (A : Word.LinearSystem (K := K) Op E I)
    (hpositive : 0 < Module.finrank K (∀ s, E s)) :
    (∀ s, allReach A s = ⊤) ↔
      (∀ s, boundedReach A s (Module.finrank K (∀ s, E s) - 1) = ⊤) := by
  constructor
  · intro hall
    have htotal := filtration_eq_top_at_finrank_sub_one (totalReach A) (totalReach_mono A)
      (totalReach_zero_ne_bot A hall hpositive) (totalReach_stationary_eq_top A hall) hpositive
    intro s
    apply top_unique
    have h : (Submodule.pi Set.univ (fun t => (⊤ : Submodule K (E t)))) ≤
        totalReach A (Module.finrank K (∀ s, E s) - 1) := by
      rw [Submodule.pi_top, htotal]
    exact component_le_of_pi_le _ _ h s
  · intro h s
    apply top_unique
    rw [← h s]
    exact boundedReach_le_allReach A s _

/-- The same statement with the total dimension written as a sum over sorts. -/
theorem allReach_iff_boundedReach_sum (A : Word.LinearSystem (K := K) Op E I)
    (hpositive : 0 < ∑ s, Module.finrank K (E s)) :
    (∀ s, allReach A s = ⊤) ↔
      (∀ s, boundedReach A s ((∑ t, Module.finrank K (E t)) - 1) = ⊤) := by
  have hp : 0 < Module.finrank K (∀ s, E s) := by
    simpa only [Module.finrank_pi_fintype] using hpositive
  simpa only [Module.finrank_pi_fintype] using allReach_iff_boundedReach A hp

end Finite

end SHIGURE.Minimal
