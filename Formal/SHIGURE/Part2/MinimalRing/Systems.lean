import Formal.SHIGURE.Part2.Minimal.FiniteWords
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Typed linear systems over a commutative ring

The input and named unary operations are actual linear maps. Words are the
same typed paths used by the finite-dimensional field theorem, before any
quotient by Laws.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped DirectSum TensorProduct

noncomputable section

variable {R S : Type*} [CommRing R]
variable (Op : S → S → Type*) (E I : S → Type*)
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]

/-- Inputs and typed unary operations over a commutative ring. -/
structure LinearSystem where
  input : ∀ s, I s →ₗ[R] E s
  operation : ∀ {s t}, Op s t → E s →ₗ[R] E t

variable {Op E I}

/-- Evaluate an actual typed word by composing its named operations. -/
def evaluate (A : LinearSystem (R := R) Op E I) {s t : S} (w : Word Op s t) :
    E s →ₗ[R] E t := by
  induction w with
  | nil => exact LinearMap.id
  | snoc w e ih => exact (A.operation e).comp ih

@[simp] theorem evaluate_nil (A : LinearSystem (R := R) Op E I) (s : S) :
    evaluate A (Word.nil s) = LinearMap.id := rfl

@[simp] theorem evaluate_snoc (A : LinearSystem (R := R) Op E I)
    {s t u : S} (w : Word Op s t) (e : Op t u) :
    evaluate A (Word.snoc w e) = (A.operation e).comp (evaluate A w) := rfl

/-- The all-words input map, from the direct sum of the actual input modules. -/
def allWordReachMap (A : LinearSystem (R := R) Op E I) (s : S) :
    (⨁ w : InputWord Op s, I w.1) →ₗ[R] E s := by
  classical
  exact DirectSum.toModule R _ _ (fun w => (evaluate A w.2).comp (A.input w.1))

/-- The input map restricted to words of length at most `n`. -/
def boundedWordReachMap (A : LinearSystem (R := R) Op E I) (s : S) (n : ℕ) :
    (⨁ w : ShortInputWord Op s n, I w.1.1) →ₗ[R] E s := by
  classical
  exact DirectSum.toModule R _ _ (fun w => (evaluate A w.1.2).comp (A.input w.1.1))

variable {O : S → Type*} [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]

/-- The finite-word observation map into the product of output modules. -/
def boundedObservationMap (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) (n : ℕ) :
    E s →ₗ[R] (∀ w : ShortOutputWord Op s n, O w.1.1) :=
  LinearMap.pi (fun w => (observe w.1.1).comp (evaluate A w.1.2))

/-- The all-words dual-observation map from the direct sum of output duals. -/
def allWordDualObservationMap (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) :
    (⨁ w : OutputWord Op s, Module.Dual R (O w.1)) →ₗ[R] Module.Dual R (E s) := by
  classical
  exact DirectSum.toModule R _ _
    (fun w => (evaluate A w.2).dualMap.comp (observe w.1).dualMap)

/-- Extension of every input and operation along the same algebra map. -/
def baseChangeSystem (T : Type*) [CommRing T] [Algebra R T]
    (A : LinearSystem (R := R) Op E I) :
    LinearSystem (R := T) Op (fun s => T ⊗[R] E s) (fun s => T ⊗[R] I s) where
  input s := (A.input s).baseChange T
  operation e := (A.operation e).baseChange T

/-- Word evaluation commutes with extension of scalars. -/
theorem evaluate_baseChange (T : Type*) [CommRing T] [Algebra R T]
    (A : LinearSystem (R := R) Op E I) {s t : S} (w : Word Op s t) :
    evaluate (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
        (baseChangeSystem T A) w = (evaluate A w).baseChange T := by
  induction w with
  | nil =>
    change LinearMap.id = (LinearMap.id : E s →ₗ[R] E s).baseChange T
    exact (LinearMap.baseChange_id (A := T)).symm
  | snoc w e ih =>
    change ((A.operation e).baseChange T).comp
        (evaluate (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
          (baseChangeSystem T A) w) = ((A.operation e).comp (evaluate A w)).baseChange T
    rw [ih, LinearMap.baseChange_comp]

end
end SHIGURE.MinimalRing
