import Formal.SHIGURE.Part2.Schemes.AffineTripleTensorCoordinates
import Formal.SHIGURE.Part2.Descent.TensorCoordinateCocycle

/-! # The ordered tensor cocycle of the geometric affine overlap

The coordinate calculation uses a module variable. Substituting the module
represented by a geometric datum then uses only the computed comparison maps.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory ModuleCat TensorProduct SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
local notation "D₃" => B ⊗[A] (B ⊗[A] B)

/-- Compare scalar extension maps on the adjunction unit to identify a B.4 coordinate operation. -/
private theorem scalarExtension_hom_ext_at_unit {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) {M : ModuleCat.{u} R} {N : ModuleCat.{u} T}
    {a b : (extendScalars f).obj M ⟶ N}
    (pointwise : ∀ x : M,
      a ((extendRestrictScalarsAdj f).unit.app M x) = b ((extendRestrictScalarsAdj f).unit.app M x)) :
    a = b := by
  let adj := extendRestrictScalarsAdj f
  apply (adj.homEquiv M N).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  exact ModuleCat.hom_ext (LinearMap.ext pointwise)

section Coordinates

variable (M : ModuleCat.{u} B) [Module A M] [IsScalarTower A B M]

attribute [local instance] doubleModule

variable (θ : OverlapIso A B M)

/-- The coefficient action on the three ordered tensor charts of the B.4 cocycle. -/
private abbrev coordinateAction (θ : OverlapIso A B M) := (θ.restrictScalars A).toLinearMap.lTensor B

/-- The scalar extension along the indexed triple projection in Appendix B.3. -/
private abbrev scalarCoordinate (i : Fin 3) := affineTripleScalarModule (A := A) M i
/-- The canonical extension unit for the indexed coordinate in the B.4 cocycle. -/
private abbrev coordinateUnit (i : Fin 3) := affineTripleScalarUnit (A := A) M i
/-- Identify the center extension of the B.3 triple overlap with its B.4 tensor chart. -/
private abbrev middleChart := affineMiddleTensorIso (A := A) (M := M)
/-- Identify the final extension of the B.3 triple overlap with its B.4 tensor chart. -/
private abbrev lastChart := affineLastTensorIso (A := A) (M := M)

variable (q : scalarCoordinate (A := A) M 1 ⟶ scalarCoordinate (A := A) M 2)
  (t : affineMiddleTensor (A := A) M ⟶ affineLastTensor (A := A) M)
  (ht : ∀ z : B ⊗[A] (M ⊗[A] B), t z = coordinateAction M θ z)
  (h₁₂ : ∀ x : M, (lastChart (A := A) M).hom (q (coordinateUnit (A := A) M 1 x)) =
    affineTripleOverlapInsertion (A := A) (M := M) 1 2 (lastChart (A := A) M)
      (θ (x ⊗ₜ[A] (1 : B))))

include ht h₁₂

set_option maxRecDepth 2048 in
set_option maxHeartbeats 450000 in
/-- Calculate the B.4 pair comparison on the scalar extension generators. -/
private theorem pair_generator (x : M) :
    (lastChart (A := A) M).hom (q (coordinateUnit (A := A) M 1 x)) =
      t ((middleChart (A := A) M).hom (coordinateUnit (A := A) M 1 x)) := by
  let y := θ (x ⊗ₜ[A] (1 : B))
  have insertion : affineTripleOverlapInsertion (A := A) (M := M) 1 2 (lastChart (A := A) M) y =
      (1 : B) ⊗ₜ[A] y :=
    affineTripleOverlapInsertion_12 (A := A) (M := M) y
  have unit : (middleChart (A := A) M).hom (coordinateUnit (A := A) M 1 x) =
      (1 : B) ⊗ₜ[A] (x ⊗ₜ[A] (1 : B)) :=
    affineMiddleTensorIso_unit (A := A) x
  let f := (θ.restrictScalars A).toLinearMap
  have tensorValue : coordinateAction M θ ((middleChart (A := A) M).hom (coordinateUnit (A := A) M 1 x)) =
      (1 : B) ⊗ₜ[A] y :=
    (congrArg (fun z : B ⊗[A] (M ⊗[A] B) => coordinateAction M θ z) unit).trans
      (f.lTensor_tmul B (1 : B) (x ⊗ₜ[A] (1 : B)))
  exact (h₁₂ x).trans (insertion.trans ((ht _).trans tensorValue).symm)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 450000 in
/-- Determine a B.4 transition on the whole middle chart from its generator formula. -/
private theorem pair_comparison : q ≫ (lastChart (A := A) M).hom = (middleChart (A := A) M).hom ≫ t :=
  scalarExtension_hom_ext_at_unit (affineTripleRingHom A B 1).hom
    (M := M) (N := affineLastTensor (A := A) M) (pair_generator M θ q t ht h₁₂)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 775000 in
/-- Read the three affine comparison formulas as the ordered B.4 tensor cocycle. -/
private theorem tensor_cocycle_of_affine_coordinates
    (p : scalarCoordinate (A := A) M 0 ⟶ scalarCoordinate (A := A) M 1)
    (r : scalarCoordinate (A := A) M 0 ⟶ scalarCoordinate (A := A) M 2) (cocycle : p ≫ q = r)
    (h₀₁ : ∀ x : M, (middleChart (A := A) M).hom (p (coordinateUnit (A := A) M 0 x)) =
      affineTripleOverlapInsertion (A := A) (M := M) 0 1 (middleChart (A := A) M) (θ (x ⊗ₜ[A] (1 : B))))
    (h₀₂ : ∀ x : M, (lastChart (A := A) M).hom (r (coordinateUnit (A := A) M 0 x)) =
      affineTripleOverlapInsertion (A := A) (M := M) 0 2 (lastChart (A := A) M) (θ (x ⊗ₜ[A] (1 : B)))) :
    (move12 θ).comp (move01 θ) = move02 θ := by
  let e := TensorProduct.assoc A B M B
  let v : scalarCoordinate (A := A) M 1 → (B ⊗[A] M) ⊗[A] B :=
    fun y => e.symm ((middleChart (A := A) M).hom y)
  let w : scalarCoordinate (A := A) M 2 → B ⊗[A] (B ⊗[A] M) :=
    fun y => (lastChart (A := A) M).hom y
  refine coefficientCocycle_of_coordinate_composition θ p q r (coordinateUnit (A := A) M 0) v w cocycle ?_ ?_ ?_
  · intro x
    have first := (h₀₁ x).trans (affineTripleOverlapInsertion_01 (A := A) (M := M) (θ (x ⊗ₜ[A] (1 : B))))
    exact (congrArg (fun z : B ⊗[A] (M ⊗[A] B) => e.symm z) first).trans (e.symm_apply_apply _)
  · intro y
    have eq := congrArg (fun k : scalarCoordinate (A := A) M 1 ⟶ affineLastTensor (A := A) M => k y)
      (pair_comparison M θ q t ht h₁₂)
    exact eq.trans ((ht ((middleChart (A := A) M).hom y)).trans
      (congrArg (fun z : B ⊗[A] (M ⊗[A] B) => coordinateAction M θ z) (e.apply_symm_apply _).symm))
  · intro x
    exact (h₀₂ x).trans
      ((affineTripleOverlapInsertion_02 (A := A) (M := M) (θ (x ⊗ₜ[A] (1 : B)))).trans (move02_unit θ x).symm)

end Coordinates

section GeometricDatum

variable (D : AffineSingletonDescentData A B)

local notation "ℳ" => affineDescentCoefficientModule D
local instance : Module A ℳ := Module.compHom _ (algebraMap A B)
local instance : IsScalarTower A B ℳ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
attribute [local instance] doubleModule

set_option maxRecDepth 2048 in
set_option maxHeartbeats 850000 in
/-- The overlap of the original affine datum satisfies the ordered tensor
cocycle of coefficient descent. -/
theorem affineDescentCoefficientTensorCocycle :
    (move12 (affineDescentCoefficientOverlap D)).comp (move01 (affineDescentCoefficientOverlap D)) =
      move02 (affineDescentCoefficientOverlap D) :=
  tensor_cocycle_of_affine_coordinates (A := A) (B := B) ℳ (affineDescentCoefficientOverlap D)
    (affineDescentPairScalarHom D 1 2) (affineTripleCoordinateMap D) (affineTripleCoordinateMap_apply D)
    (fun x => affineDescentPairScalarHom_unit D 1 2 (lastChart (A := A) ℳ) x)
    (affineDescentPairScalarHom D 0 1) (affineDescentPairScalarHom D 0 2)
    (affineDescentPairScalarHom_cocycle D 0 1 2)
    (fun x => affineDescentPairScalarHom_unit D 0 1 (middleChart (A := A) ℳ) x)
    (fun x => affineDescentPairScalarHom_unit D 0 2 (lastChart (A := A) ℳ) x)

end GeometricDatum

end

end SHIGURE.SchemeDescent
