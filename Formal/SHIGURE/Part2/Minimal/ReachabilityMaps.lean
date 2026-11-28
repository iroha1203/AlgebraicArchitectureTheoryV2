import Formal.SHIGURE.Part2.Minimal.DualObservation
import Formal.SHIGURE.Part2.Minimal.DirectSumRange
import Mathlib.Algebra.DirectSum.Module

/-! The reachability spaces are ranges of the actual word-indexed direct-sum maps. -/

namespace SHIGURE.Minimal

open scoped DirectSum

variable {K S : Type*} [Field K]
variable {Op : S → S → Type*} {E I : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]

/-- Words ending in a given sort, retaining their source sort. -/
abbrev InputWord (Op : S → S → Type*) (s : S) := Σ t, Word Op t s

/-- Words ending in a given sort whose length is bounded by `n`. -/
abbrev ShortInputWord (Op : S → S → Type*) (s : S) (n : ℕ) :=
  {w : InputWord Op s // w.2.length ≤ n}

/-- The direct-sum reachability map indexed by all typed input words. -/
noncomputable def allWordReachMap (A : Word.LinearSystem (K := K) Op E I) (s : S) :
    (⨁ w : InputWord Op s, I w.1) →ₗ[K] E s := by
  classical
  exact DirectSum.toModule K _ _ (fun w => (w.2.evaluate A).comp (A.input w.1))

/-- The direct-sum reachability map indexed by typed input words of bounded length. -/
noncomputable def boundedWordReachMap (A : Word.LinearSystem (K := K) Op E I)
    (s : S) (n : ℕ) :
    (⨁ w : ShortInputWord Op s n, I w.1.1) →ₗ[K] E s := by
  classical
  exact DirectSum.toModule K _ _ (fun w => (w.1.2.evaluate A).comp (A.input w.1.1))

/-- The all-words span is the range of the all-words direct-sum map. -/
theorem range_allWordReachMap (A : Word.LinearSystem (K := K) Op E I) (s : S) :
    LinearMap.range (allWordReachMap A s) = allReach A s := by
  classical
  unfold allWordReachMap allReach
  apply range_toModule_eq_span
  intro x
  constructor
  · rintro ⟨t, w, a, rfl⟩
    exact ⟨⟨t, w⟩, a, rfl⟩
  · rintro ⟨⟨t, w⟩, a, rfl⟩
    exact ⟨t, w, a, rfl⟩

/-- The bounded span is the range of the bounded direct-sum map. -/
theorem range_boundedWordReachMap (A : Word.LinearSystem (K := K) Op E I)
    (s : S) (n : ℕ) :
    LinearMap.range (boundedWordReachMap A s n) = boundedReach A s n := by
  classical
  unfold boundedWordReachMap boundedReach
  apply range_toModule_eq_span
  intro x
  constructor
  · rintro ⟨t, w, a, hw, rfl⟩
    exact ⟨⟨⟨t, w⟩, hw⟩, a, rfl⟩
  · rintro ⟨⟨⟨t, w⟩, hw⟩, a, rfl⟩
    exact ⟨t, w, a, hw, rfl⟩

variable [Fintype S] [∀ s, FiniteDimensional K (E s)]

/-- The N−1 theorem stated as surjectivity of the direct-sum reachability maps. -/
theorem surjective_allWordReachMap_iff_bounded
    (A : Word.LinearSystem (K := K) Op E I)
    (hpositive : 0 < ∑ s, Module.finrank K (E s)) :
    (∀ s, Function.Surjective (allWordReachMap A s)) ↔
      (∀ s, Function.Surjective
        (boundedWordReachMap A s ((∑ t, Module.finrank K (E t)) - 1))) := by
  simpa only [← LinearMap.range_eq_top, range_allWordReachMap, range_boundedWordReachMap]
    using allReach_iff_boundedReach_sum A hpositive

section ObservationMaps

variable {O : S → Type*}
variable [∀ s, AddCommGroup (O s)] [∀ s, Module K (O s)]

/-- Words starting at a given sort, retaining their destination sort. -/
abbrev OutputWord (Op : S → S → Type*) (s : S) := Σ t, Word Op s t

/-- Words starting at a given sort whose length is bounded by `n`. -/
abbrev ShortOutputWord (Op : S → S → Type*) (s : S) (n : ℕ) :=
  {w : OutputWord Op s // w.2.length ≤ n}

/-- The all-words direct-sum dual observation map. -/
noncomputable def allWordDualObservationMap (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) :
    (⨁ w : OutputWord Op s, Module.Dual K (O w.1)) →ₗ[K] Module.Dual K (E s) := by
  classical
  exact DirectSum.toModule K _ _ (fun w => (w.2.evaluate A).dualMap.comp (observe w.1).dualMap)

/-- The bounded direct-sum dual observation map. -/
noncomputable def boundedWordDualObservationMap (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) :
    (⨁ w : ShortOutputWord Op s n, Module.Dual K (O w.1.1)) →ₗ[K]
      Module.Dual K (E s) := by
  classical
  exact DirectSum.toModule K _ _
    (fun w => (w.1.2.evaluate A).dualMap.comp (observe w.1.1).dualMap)

/-- The all-words dual observation span is the range of its direct-sum map. -/
theorem range_allWordDualObservationMap (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) :
    LinearMap.range (allWordDualObservationMap A observe s) = allObservation O A observe s := by
  classical
  unfold allWordDualObservationMap allObservation
  apply range_toModule_eq_span
  intro φ
  constructor
  · rintro ⟨t, w, ℓ, rfl⟩
    exact ⟨⟨t, w⟩, ℓ, rfl⟩
  · rintro ⟨⟨t, w⟩, ℓ, rfl⟩
    exact ⟨t, w, ℓ, rfl⟩

/-- The bounded dual observation span is the range of its direct-sum map. -/
theorem range_boundedWordDualObservationMap (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) :
    LinearMap.range (boundedWordDualObservationMap A observe s n) =
      boundedObservation O A observe s n := by
  classical
  unfold boundedWordDualObservationMap boundedObservation
  apply range_toModule_eq_span
  intro φ
  constructor
  · rintro ⟨t, w, ℓ, hw, rfl⟩
    exact ⟨⟨⟨t, w⟩, hw⟩, ℓ, rfl⟩
  · rintro ⟨⟨⟨t, w⟩, hw⟩, ℓ, rfl⟩
    exact ⟨t, w, ℓ, hw, rfl⟩

/-- The N−1 theorem stated for the direct-sum dual observation maps. -/
theorem surjective_allWordDualObservationMap_iff_bounded
    (A : Word.LinearSystem (K := K) Op E I) (observe : ∀ s, E s →ₗ[K] O s)
    (hpositive : 0 < ∑ s, Module.finrank K (E s)) :
    (∀ s, Function.Surjective (allWordDualObservationMap A observe s)) ↔
      (∀ s, Function.Surjective
        (boundedWordDualObservationMap A observe s ((∑ t, Module.finrank K (E t)) - 1))) := by
  simpa only [← LinearMap.range_eq_top, range_allWordDualObservationMap,
    range_boundedWordDualObservationMap] using
      allObservation_iff_boundedObservation_sum A observe hpositive

end ObservationMaps

end SHIGURE.Minimal
