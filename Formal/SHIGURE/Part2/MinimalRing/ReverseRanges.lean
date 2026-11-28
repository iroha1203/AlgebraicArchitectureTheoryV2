import Formal.SHIGURE.Part2.MinimalRing.ReverseSystem
import Formal.SHIGURE.Part2.MinimalRing.DualProduct
import Formal.SHIGURE.Part2.Minimal.DirectSumRange

/-!
# Images of dual observation and reversed-system reachability

The equalities compare the ranges of the actual direct-sum maps.  They are
proved by transporting each word-indexed generator through word reversal.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal

noncomputable section

variable {R S : Type*} [CommRing R]
variable {Op : S → S → Type*} {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]

/-- Values obtained from inputs by arbitrary typed words ending at `s`. -/
def allReachValues (A : LinearSystem (R := R) Op E I) (s : S) : Set (E s) :=
  {x | ∃ (t : S) (w : Word Op t s) (a : I t), x = evaluate A w (A.input t a)}

/-- Values obtained from inputs by typed words of length at most `n`. -/
def boundedReachValues (A : LinearSystem (R := R) Op E I) (s : S) (n : ℕ) : Set (E s) :=
  {x | ∃ (t : S) (w : Word Op t s) (a : I t),
    w.length ≤ n ∧ x = evaluate A w (A.input t a)}

/-- Dual observations indexed by all finite words starting at `s`. -/
def allObservationValues (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) : Set (Module.Dual R (E s)) :=
  {φ | ∃ (t : S) (w : Word Op s t) (ℓ : Module.Dual R (O t)),
    φ = ℓ.comp ((observe t).comp (evaluate A w))}

/-- Dual observations indexed by words of length at most `n`. -/
def boundedObservationValues (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) (n : ℕ) : Set (Module.Dual R (E s)) :=
  {φ | ∃ (t : S) (w : Word Op s t) (ℓ : Module.Dual R (O t)),
    w.length ≤ n ∧ φ = ℓ.comp ((observe t).comp (evaluate A w))}

/-- The actual all-word reachability map has the expected image. -/
theorem range_allWordReachMap (A : LinearSystem (R := R) Op E I) (s : S) :
    LinearMap.range (allWordReachMap A s) = Submodule.span R (allReachValues A s) := by
  classical
  unfold allWordReachMap
  apply range_toModule_eq_span
  intro x
  constructor
  · rintro ⟨t, w, a, rfl⟩
    exact ⟨⟨t, w⟩, a, rfl⟩
  · rintro ⟨⟨t, w⟩, a, rfl⟩
    exact ⟨t, w, a, rfl⟩

/-- The actual bounded reachability map has the expected image. -/
theorem range_boundedWordReachMap (A : LinearSystem (R := R) Op E I) (s : S) (n : ℕ) :
    LinearMap.range (boundedWordReachMap A s n) = Submodule.span R (boundedReachValues A s n) := by
  classical
  unfold boundedWordReachMap
  apply range_toModule_eq_span
  intro x
  constructor
  · rintro ⟨t, w, a, hw, rfl⟩
    exact ⟨⟨⟨t, w⟩, hw⟩, a, rfl⟩
  · rintro ⟨⟨⟨t, w⟩, hw⟩, a, rfl⟩
    exact ⟨t, w, a, hw, rfl⟩

/-- The actual all-word dual observation map has the expected image. -/
theorem range_allWordDualObservationMap (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) :
    LinearMap.range (allWordDualObservationMap A observe s) =
      Submodule.span R (allObservationValues A observe s) := by
  classical
  unfold allWordDualObservationMap
  apply range_toModule_eq_span
  intro φ
  constructor
  · rintro ⟨t, w, ℓ, rfl⟩
    exact ⟨⟨t, w⟩, ℓ, rfl⟩
  · rintro ⟨⟨t, w⟩, ℓ, rfl⟩
    exact ⟨t, w, ℓ, rfl⟩

/-- The actual bounded component-dual map has the expected image. -/
theorem range_boundedWordDualObservationMap (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) (n : ℕ) :
    LinearMap.range (boundedWordDualObservationMap A observe s n) =
      Submodule.span R (boundedObservationValues A observe s n) := by
  classical
  unfold boundedWordDualObservationMap
  apply range_toModule_eq_span
  intro φ
  constructor
  · rintro ⟨t, w, ℓ, hw, rfl⟩
    exact ⟨⟨⟨t, w⟩, hw⟩, ℓ, rfl⟩
  · rintro ⟨⟨⟨t, w⟩, hw⟩, ℓ, rfl⟩
    exact ⟨t, w, ℓ, hw, rfl⟩

/-- Reversing words identifies every all-word observation generator with a
reversed-system input generator. -/
theorem allObservationValues_eq_reverseReachValues
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s) (s : S) :
    allObservationValues A observe s =
      allReachValues (E := fun u => Module.Dual R (E u))
        (I := fun u => Module.Dual R (O u))
        (reverseSystem (E := E) (I := I) (O := O) A observe) s := by
  ext φ
  constructor
  · rintro ⟨t, w, ℓ, rfl⟩
    refine ⟨t, w.reverse, ℓ, ?_⟩
    rw [evaluate_reverseSystem]
    ext x
    rfl
  · rintro ⟨t, w, ℓ, rfl⟩
    refine ⟨t, w.reverse, ℓ, ?_⟩
    have he := evaluate_reverseSystem A observe w.reverse
    simp only [Word.reverse_reverse] at he
    rw [he]
    ext x
    rfl

/-- The same word reversal preserves the bound on word length. -/
theorem boundedObservationValues_eq_reverseReachValues
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (s : S) (n : ℕ) :
    boundedObservationValues A observe s n =
      boundedReachValues (E := fun u => Module.Dual R (E u))
        (I := fun u => Module.Dual R (O u))
        (reverseSystem (E := E) (I := I) (O := O) A observe) s n := by
  ext φ
  constructor
  · rintro ⟨t, w, ℓ, hw, rfl⟩
    refine ⟨t, w.reverse, ℓ, (Word.length_reverse w).le.trans hw, ?_⟩
    rw [evaluate_reverseSystem]
    ext x
    rfl
  · rintro ⟨t, w, ℓ, hw, rfl⟩
    refine ⟨t, w.reverse, ℓ, (Word.length_reverse w).le.trans hw, ?_⟩
    have he := evaluate_reverseSystem A observe w.reverse
    simp only [Word.reverse_reverse] at he
    rw [he]
    ext x
    rfl

/-- The all-word dual observation and reversed reachability maps have equal ranges. -/
theorem range_allWordDualObservationMap_eq_reverseReach
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s) (s : S) :
    LinearMap.range (allWordDualObservationMap A observe s) =
      LinearMap.range (allWordReachMap
        (E := fun u => Module.Dual R (E u)) (I := fun u => Module.Dual R (O u))
        (reverseSystem (E := E) (I := I) (O := O) A observe) s) := by
  rw [range_allWordDualObservationMap, range_allWordReachMap,
    allObservationValues_eq_reverseReachValues]

/-- The bounded dual observation and reversed reachability maps have equal ranges. -/
theorem range_boundedWordDualObservationMap_eq_reverseReach
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s) (s : S) (n : ℕ) :
    LinearMap.range (boundedWordDualObservationMap A observe s n) =
      LinearMap.range (boundedWordReachMap
        (E := fun u => Module.Dual R (E u)) (I := fun u => Module.Dual R (O u))
        (reverseSystem (E := E) (I := I) (O := O) A observe) s n) := by
  rw [range_boundedWordDualObservationMap, range_boundedWordReachMap,
    boundedObservationValues_eq_reverseReachValues]

end
end SHIGURE.MinimalRing
