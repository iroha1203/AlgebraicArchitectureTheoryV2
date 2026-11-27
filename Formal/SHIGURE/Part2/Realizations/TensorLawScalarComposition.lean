import Formal.SHIGURE.Part2.Realizations.TensorExpressions

/-! # Composition of scalar substitutions in typed tensor Laws -/

namespace SHIGURE

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {sig : Signature.{u}}

/-- Consecutive substitutions in a written tensor expression are substitution along the composite. -/
theorem TensorExpression.mapScalars_comp {X Y : TensorShape sig.SortType}
    (e : TensorExpression R sig X Y) (f : R →+* S) (g : S →+* T) :
    (e.mapScalars f).mapScalars g = e.mapScalars (g.comp f) := by
  induction e <;> simp [TensorExpression.mapScalars, RingHom.comp_apply, *]

/-- The same composition applies to both sides of the original tensor Law. -/
theorem TensorLaw.mapScalars_comp (e : TensorLaw R sig) (f : R →+* S) (g : S →+* T) :
    (e.mapScalars f).mapScalars g = e.mapScalars (g.comp f) := by
  cases e
  simp [TensorLaw.mapScalars, TensorExpression.mapScalars_comp]

end SHIGURE
