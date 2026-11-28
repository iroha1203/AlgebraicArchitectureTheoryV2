import Formal.SHIGURE.Part2.MinimalRing.Systems
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Reversing a linear system over a commutative ring

Observation duals become inputs, and every typed operation is reversed and
dualized.  Reversal of the actual typed word computes the dual of its action.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal

variable {R S : Type*} [CommRing R]
variable {Op : S → S → Type*} {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]

/-- Reverse each named operation and use the dual observations as inputs. -/
def reverseSystem (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) :
    LinearSystem (R := R) (fun s t => Op t s)
      (fun s => Module.Dual R (E s)) (fun s => Module.Dual R (O s)) where
  input s := (observe s).dualMap
  operation e := (A.operation e).dualMap

/-- Evaluating concatenated words composes their linear actions. -/
theorem evaluate_append (A : LinearSystem (R := R) Op E I)
    {s t u : S} (w : Word Op s t) (v : Word Op t u) :
    evaluate A (w.append v) = (evaluate A v).comp (evaluate A w) := by
  induction v with
  | nil => ext x; rfl
  | snoc v e ih =>
    change (A.operation e).comp (evaluate A (w.append v)) =
      ((A.operation e).comp (evaluate A v)).comp (evaluate A w)
    rw [ih]
    exact (LinearMap.comp_assoc (evaluate A w) (evaluate A v) (A.operation e)).symm

/-- Evaluating the reversed word in the reversed system is the original
word action's actual dual map. -/
theorem evaluate_reverseSystem (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) {s t : S} (w : Word Op s t) :
    evaluate (E := fun u => Module.Dual R (E u)) (I := fun u => Module.Dual R (O u))
        (reverseSystem (E := E) (I := I) (O := O) A observe) w.reverse =
      (evaluate A w).dualMap := by
  induction w with
  | nil => rfl
  | snoc w e ih =>
    rw [Word.reverse_snoc, evaluate_append, ih]
    change (evaluate A w).dualMap.comp ((A.operation e).dualMap.comp LinearMap.id) =
      ((A.operation e).comp (evaluate A w)).dualMap
    rw [LinearMap.comp_id, LinearMap.dualMap_comp_dualMap]

end SHIGURE.MinimalRing
