import Formal.SHIGURE.Part2.StackQuantities.NonflatExample
import Formal.SHIGURE.Part2.Quantities.Coordinates

/-! # The non-flat ideal as a written quantity Law

The Law `a * q(c) = 0` has a single fixed quantity input.  Its original
Chapter 5 residual is transported to `a t` by a coordinate equivalence.
-/

noncomputable section

universe u

namespace SHIGURE.StackQuantities.Nonflat

open MvPolynomial SHIGURE.Quantities

variable (k : Type u) [CommRing k] {sig : SHIGURE.Signature.{u}} (A : SHIGURE.Structure sig)

/-- A written scalar coefficient multiplying the unique quantity application. -/
def writtenPresentation : Presentation (Base k) A where
  Quantity := PUnit
  Domain _ := PUnit
  Law := PUnit
  Input _ := PUnit
  left _ _ := .mul (.scalar Polynomial.X) (.quantity ⟨PUnit.unit, PUnit.unit⟩)
  right _ _ := .scalar 0

/-- Identify the one named quantity coordinate with `t`. -/
def writtenCoordinates : (writtenPresentation k A).CoordinateAlgebra ≃ₐ[Base k] Ambient k :=
  MvPolynomial.renameEquiv (Base k) (show (writtenPresentation k A).Coordinate ≃ Unit from {
    toFun := fun _ => ()
    invFun := fun _ => ⟨PUnit.unit, PUnit.unit⟩
    left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
    right_inv := by rintro ⟨⟩; rfl })

/-- The universal quantity is sent to the indeterminate `t`. -/
theorem writtenCoordinates_quantity :
    writtenCoordinates k A ((writtenPresentation k A).universalQuantity PUnit.unit PUnit.unit) = X () := by
  change MvPolynomial.rename (fun _ : (writtenPresentation k A).Coordinate => ()) (MvPolynomial.X _) = _
  rw [MvPolynomial.rename_X]

/-- The residual is computed from the written expression and equals `a t`. -/
theorem writtenCoordinates_residual (l : (writtenPresentation k A).Law)
    (e : (writtenPresentation k A).Input l) :
    writtenCoordinates k A ((writtenPresentation k A).residual l e) = generator k := by
  change writtenCoordinates k A
      (algebraMap (Base k) (writtenPresentation k A).CoordinateAlgebra Polynomial.X *
        (writtenPresentation k A).universalQuantity PUnit.unit PUnit.unit -
        algebraMap (Base k) (writtenPresentation k A).CoordinateAlgebra 0) = _
  rw [map_zero, sub_zero, map_mul, (writtenCoordinates k A).commutes,
    writtenCoordinates_quantity]
  rfl

/-- The fixed-input quantity model's original residual ideal becomes `(a t)`. -/
theorem writtenCoordinates_residualIdeal :
    (writtenPresentation k A).residualIdeal.map (writtenCoordinates k A).toRingHom = residualIdeal k := by
  rw [Presentation.residualIdeal, residualIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨⟨l, e⟩, rfl⟩, rfl⟩
    exact writtenCoordinates_residual k A l e
  · rintro rfl
    refine ⟨_, ⟨⟨PUnit.unit, PUnit.unit⟩, rfl⟩, ?_⟩
    exact writtenCoordinates_residual k A _ _

end SHIGURE.StackQuantities.Nonflat
end
