import Formal.SHIGURE.Part2.Schemes.RelativeSpecBaseChange

/-! # Direct-image comparisons for algebra sheaves

## Implementation notes

The structure map of a test object is recorded in the category of
algebras under the base structure sheaf. Direct image along a composition
uses the original ring on each inverse-image open. The resulting comparisons
have identity components on those rings. This presentation records the
transition of an algebra as an adjoint map; the corresponding pullback
isomorphism is formed using the existing adjunction of B.7.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

/-- Direct image of algebra sheaves along the identity preserves the original algebra. -/
def pushforwardAlgebraId (X : Scheme.{u}) : pushforwardAlgebra (𝟙 X) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (fun D => Under.isoMk (Iso.refl _) ?_) ?_
  · apply Sheaf.hom_ext
    ext1
    funext U
    rfl
  · intro D E m
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    ext1
    funext U
    rfl

/-- Iterated direct images of algebra sheaves give the algebra over the
composite base map, with its actual action of the base structure sheaf. -/
def pushforwardAlgebraComp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    pushforwardAlgebra g ⋙ pushforwardAlgebra f ≅ pushforwardAlgebra (g ≫ f) := by
  refine NatIso.ofComponents (fun D => Under.isoMk (Iso.refl _) ?_) ?_
  · apply Sheaf.hom_ext
    ext1
    funext U
    rfl
  · intro D E m
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    ext1
    funext U
    rfl

/-- The direct image of the structure sheaf on the identity test object is the
unit algebra of the base scheme. -/
def directImageStructure_id (X : Scheme.{u}) :
    directImageStructure (𝟙 X) ≅ Under.mk (𝟙 X.sheaf) :=
  Under.isoMk (Iso.refl _) (by rfl)


end

end SHIGURE.SchemeDescent
