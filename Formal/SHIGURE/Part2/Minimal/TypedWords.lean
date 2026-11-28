import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Typed operation words and reachability

The words below are paths before quotienting by any Laws.  Their evaluation
uses the input and the named, typed linear operations of the realization.
-/

namespace SHIGURE.Minimal

noncomputable section

universe u v

variable {S : Type u} (Op : S → S → Type v)

/-- A typed word, with the outermost operation applied last. -/
inductive Word : S → S → Type (max u v)
  | nil (s : S) : Word s s
  | snoc {s t u : S} : Word s t → Op t u → Word s u

namespace Word

/-- Number of operations in a typed word. -/
def length {s t : S} (w : Word Op s t) : ℕ := by
  induction w with
  | nil => exact 0
  | snoc w e ih => exact ih + 1

variable {K : Type*} [Field K]
variable (E I : S → Type*)
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]

/-- The maps defining the input and the named unary operations. -/
structure LinearSystem where
  input : ∀ s, I s →ₗ[K] E s
  operation : ∀ {s t}, Op s t → E s →ₗ[K] E t

variable {Op E I}

/-- Evaluate a typed operation word as a linear map. -/
def evaluate (A : LinearSystem (K := K) Op E I) {s t : S} (w : Word Op s t) :
    E s →ₗ[K] E t := by
  induction w with
  | nil => exact LinearMap.id
  | snoc w e ih => exact (A.operation e).comp ih

end Word

variable {K : Type*} [Field K]
variable (E I : S → Type*)
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]
variable {Op E I}

/-- The states obtained by words of length at most `n`. -/
def boundedGenerators (A : Word.LinearSystem (K := K) Op E I) (s : S) (n : ℕ) : Set (E s) :=
  {x | ∃ (t : S) (w : Word Op t s) (a : I t),
    w.length ≤ n ∧ x = w.evaluate A (A.input t a)}

/-- The states obtained by arbitrary finite typed words. -/
def allGenerators (A : Word.LinearSystem (K := K) Op E I) (s : S) : Set (E s) :=
  {x | ∃ (t : S) (w : Word Op t s) (a : I t),
    x = w.evaluate A (A.input t a)}

/-- The range of the length-bounded reachability map. -/
def boundedReach (A : Word.LinearSystem (K := K) Op E I) (s : S) (n : ℕ) : Submodule K (E s) :=
  Submodule.span K (boundedGenerators A s n)

/-- The range of the all-words reachability map. -/
def allReach (A : Word.LinearSystem (K := K) Op E I) (s : S) : Submodule K (E s) :=
  Submodule.span K (allGenerators A s)

/-- Increasing the word-length bound can only enlarge reachability. -/
theorem boundedReach_mono (A : Word.LinearSystem (K := K) Op E I) (s : S) :
    Monotone (boundedReach A s) := by
  intro m n hmn
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨t, w, a, hw, rfl⟩
  exact ⟨t, w, a, hw.trans hmn, rfl⟩

/-- Every bounded word is an arbitrary finite word. -/
theorem boundedReach_le_allReach (A : Word.LinearSystem (K := K) Op E I) (s : S) (n : ℕ) :
    boundedReach A s n ≤ allReach A s := by
  apply Submodule.span_mono
  intro x hx
  rcases hx with ⟨t, w, a, _, rfl⟩
  exact ⟨t, w, a, rfl⟩

/-- Appending one named operation increases the length bound by one. -/
theorem operation_boundedReach_le (A : Word.LinearSystem (K := K) Op E I)
    {s t : S} (e : Op s t) (n : ℕ) :
    (boundedReach A s n).map (A.operation e) ≤ boundedReach A t (n + 1) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨u, w, a, hw, rfl⟩
  apply Submodule.subset_span
  exact ⟨u, Word.snoc w e, a, Nat.add_le_add_right hw 1, rfl⟩

/-- If every sort has stopped growing, all later words stay in that stage. -/
theorem allReach_le_of_stationary (A : Word.LinearSystem (K := K) Op E I) (n : ℕ)
    (h : ∀ s, boundedReach A s (n + 1) = boundedReach A s n) (s : S) :
    allReach A s ≤ boundedReach A s n := by
  have word_mem : ∀ {u t : S} (w : Word Op u t) (a : I u),
      w.evaluate A (A.input u a) ∈ boundedReach A t n := by
    intro u t w
    induction w with
    | nil =>
      intro a
      apply Submodule.subset_span
      exact ⟨u, Word.nil u, a, Nat.zero_le n, rfl⟩
    | @snoc t v w e ih =>
      intro a
      have hm : (boundedReach A t n).map (A.operation e) ≤ boundedReach A v n := by
        rw [← h v]
        exact operation_boundedReach_le A e n
      apply hm
      exact Submodule.mem_map.mpr ⟨_, ih a, rfl⟩
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨u, w, a, rfl⟩
  exact word_mem w a

/-- All finite words are obtained by taking the supremum over length bounds. -/
theorem iSup_boundedReach (A : Word.LinearSystem (K := K) Op E I) (s : S) :
    (⨆ n, boundedReach A s n) = allReach A s := by
  apply le_antisymm
  · exact iSup_le (boundedReach_le_allReach A s)
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨t, w, a, rfl⟩
    apply (le_iSup (boundedReach A s) w.length)
    apply Submodule.subset_span
    exact ⟨t, w, a, le_rfl, rfl⟩

section Observation

variable (O : S → Type*)
variable [∀ s, AddCommGroup (O s)] [∀ s, Module K (O s)]

/-- The dual observations indexed by words of bounded length. -/
def boundedObservationGenerators (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) : Set (Module.Dual K (E s)) :=
  {φ | ∃ (t : S) (w : Word Op s t) (ℓ : Module.Dual K (O t)),
    w.length ≤ n ∧ φ = ℓ.comp ((observe t).comp (w.evaluate A))}

/-- The image of the dual of the bounded observation map. -/
def boundedObservation (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) :
    Submodule K (Module.Dual K (E s)) :=
  Submodule.span K (boundedObservationGenerators O A observe s n)

/-- The dual observations indexed by all finite typed words. -/
def allObservationGenerators (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) : Set (Module.Dual K (E s)) :=
  {φ | ∃ (t : S) (w : Word Op s t) (ℓ : Module.Dual K (O t)),
    φ = ℓ.comp ((observe t).comp (w.evaluate A))}

/-- The image of the all-words dual observation map. -/
def allObservation (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) : Submodule K (Module.Dual K (E s)) :=
  Submodule.span K (allObservationGenerators O A observe s)

/-- The bounded dual observations lie among the all-words observations. -/
theorem boundedObservation_le_allObservation (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) :
    boundedObservation O A observe s n ≤ allObservation O A observe s := by
  apply Submodule.span_mono
  intro φ hφ
  rcases hφ with ⟨t, w, ℓ, _, rfl⟩
  exact ⟨t, w, ℓ, rfl⟩

/-- The all-words dual observations are the supremum of the bounded ones. -/
theorem iSup_boundedObservation (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) :
    (⨆ n, boundedObservation O A observe s n) = allObservation O A observe s := by
  apply le_antisymm
  · exact iSup_le (boundedObservation_le_allObservation O A observe s)
  · apply Submodule.span_le.mpr
    intro φ hφ
    rcases hφ with ⟨t, w, ℓ, rfl⟩
    apply (le_iSup (boundedObservation O A observe s) w.length)
    apply Submodule.subset_span
    exact ⟨t, w, ℓ, le_rfl, rfl⟩

end Observation

end

end SHIGURE.Minimal
