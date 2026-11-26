import Formal.SHIGURE.Part2.Quantities.Representation
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# A square-zero quantity with fixed states

Example 5.7 gives an infinitesimal direction by varying a single quantity on a
point. The principal residual ideal is retained in the original polynomial ring.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

variable (k : Type u) [CommRing k] {sig : Signature.{u}} (A : Structure sig)

/-- One quantity at one input with the original equality `t * t = 0`. -/
def nilpotentPresentation : Presentation k A where
  Quantity := PUnit
  Domain _ := PUnit
  Law := PUnit
  Input _ := PUnit
  left _ _ := .mul (.quantity ⟨PUnit.unit, PUnit.unit⟩) (.quantity ⟨PUnit.unit, PUnit.unit⟩)
  right _ _ := .scalar 0

/-- Over a nonzero coefficient ring, the point with coordinate one fails the original
equation of Example 5.7. The nilpotent lifts below do satisfy that same equation. -/
theorem nilpotentConstantOne_not_holds [Nontrivial k] :
    ¬ (nilpotentPresentation k A).Holds (R := k) (fun _ _ => 1) := by
  intro h
  have equality := h PUnit.unit PUnit.unit
  change (1 : k) * 1 = algebraMap k k 0 at equality
  rw [mul_one, map_zero] at equality
  exact one_ne_zero equality

/-- Identify the one universal quantity variable with the univariate indeterminate. -/
def nilpotentCoordinates : (nilpotentPresentation k A).CoordinateAlgebra ≃ₐ[k] Polynomial k :=
  (MvPolynomial.renameEquiv k (show (nilpotentPresentation k A).Coordinate ≃ PUnit.{u + 1} from {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => ⟨PUnit.unit, PUnit.unit⟩
    left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
    right_inv := by rintro ⟨⟩; rfl })).trans (MvPolynomial.pUnitAlgEquiv k)

/-- The universal quantity becomes the distinguished polynomial variable. -/
theorem nilpotentCoordinates_generator :
    nilpotentCoordinates k A ((nilpotentPresentation k A).universalQuantity PUnit.unit PUnit.unit) =
      Polynomial.X := by
  change MvPolynomial.pUnitAlgEquiv k
    (MvPolynomial.rename (fun _ => PUnit.unit)
      (MvPolynomial.X (R := k) (⟨PUnit.unit, PUnit.unit⟩ : (nilpotentPresentation k A).Coordinate))) = _
  rw [MvPolynomial.rename_X]
  exact MvPolynomial.eval₂_X _ _ _

/-- The one named residual becomes the square of the original coordinate. -/
theorem nilpotentCoordinates_residual (l : (nilpotentPresentation k A).Law)
    (e : (nilpotentPresentation k A).Input l) :
    nilpotentCoordinates k A ((nilpotentPresentation k A).residual l e) = Polynomial.X ^ 2 := by
  let f := nilpotentCoordinates k A
  let i : (nilpotentPresentation k A).Coordinate := ⟨PUnit.unit, PUnit.unit⟩
  let x := MvPolynomial.X (R := k) i
  change f (x * x - algebraMap k (nilpotentPresentation k A).CoordinateAlgebra 0) = _
  have hx : f x = Polynomial.X := nilpotentCoordinates_generator k A
  rw [map_zero, sub_zero, map_mul, hx, pow_two]

/-- The original residual ideal becomes the square ideal under the coordinate isomorphism. -/
theorem nilpotentCoordinates_residualIdeal :
    (nilpotentPresentation k A).residualIdeal.map (nilpotentCoordinates k A).toRingHom =
      Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k)) := by
  rw [Presentation.residualIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨⟨l, e⟩, rfl⟩, rfl⟩
    exact nilpotentCoordinates_residual k A l e
  · rintro rfl
    refine ⟨_, ⟨⟨PUnit.unit, PUnit.unit⟩, rfl⟩, ?_⟩
    exact nilpotentCoordinates_residual k A _ _

/-- The residual quotient is the polynomial algebra modulo the original ideal `(t²)`. -/
def nilpotentLawAlgebraEquiv : (nilpotentPresentation k A).LawAlgebra ≃ₐ[k]
    (Polynomial k ⧸ Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k))) :=
  Ideal.quotientEquivAlg _ _ (nilpotentCoordinates k A) (nilpotentCoordinates_residualIdeal k A).symm

/-- Every infinitesimal direction is a lawful model over the dual-number algebra. -/
def nilpotentDualModel (a : k) : (nilpotentPresentation k A).Model (DualNumber k) :=
  ⟨fun _ _ => TrivSqZeroExt.inr a, by
    intro _ _
    change TrivSqZeroExt.inr a * TrivSqZeroExt.inr a = algebraMap k (DualNumber k) 0
    rw [TrivSqZeroExt.inr_mul_inr, map_zero]⟩

/-- All lifts of the zero value are the specified square-zero directions. -/
theorem nilpotentDualModel_fiber
    (q : (nilpotentPresentation k A).Model (DualNumber k)) :
    (q.val PUnit.unit PUnit.unit).fst = 0 ↔ ∃! a : k, q = nilpotentDualModel k A a := by
  constructor
  · intro h
    refine ⟨(q.val PUnit.unit PUnit.unit).snd, ?_, ?_⟩
    · apply Subtype.ext
      funext j x
      have hj : j = PUnit.unit := Subsingleton.elim (α := PUnit) _ _
      subst j
      have hx : x = PUnit.unit := Subsingleton.elim (α := PUnit) _ _
      subst x
      exact TrivSqZeroExt.ext h rfl
    · intro a ha
      exact (congrArg (fun m : (nilpotentPresentation k A).Model (DualNumber k) =>
        (m.val PUnit.unit PUnit.unit).snd) ha).symm
  · rintro ⟨a, rfl, _⟩
    rfl

end SHIGURE.Quantities
