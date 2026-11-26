import Formal.SHIGURE.Part2.Recovery.PresentationRestriction
import Formal.SHIGURE.Part2.Recovery.RelativeSchemeMaps

/-!
# Functorial coefficient change of copying models

Both the local splitting and the sheaf Laws are preserved by restriction.
The coefficient change sends a represented sheaf to the sheaf of points
of the actual fiber product. On the category of sheaf structures the
unit and composition comparisons come from the functor of relative tests.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

noncomputable section

namespace SHIGURE.Copying

private theorem lift_congr {X : Type u} [Category.{v} X] {Y : Type w} [Category* Y]
    (P : ObjectProperty Y) {F G : X ⥤ Y} (e : F = G) (hF : ∀ A, P (F.obj A)) (hG : ∀ A, P (G.obj A)) :
    P.lift F hF = P.lift G hG := by
  subst G
  rfl

/-- Coefficient restriction along the identity is the identity on copying models and arrows. -/
theorem restrictCopyingCoefficients_id (T : Theory.{u}) (S : Scheme.{u}) :
    restrictCopyingCoefficients T (𝟙 S) = 𝟭 _ :=
  lift_congr (zariskiCopyingProperty T S)
    (congrArg (fun F => (zariskiCopyingProperty T S).ι ⋙ F) (restrictStructureFunctor_id T.signature S))
    _ _

/-- Composed coefficient restriction agrees with the iterated restrictions on all models and arrows. -/
theorem restrictCopyingCoefficients_comp (T : Theory.{u}) {S S' S'' : Scheme.{u}}
    (g : S'' ⟶ S') (f : S' ⟶ S) :
    restrictCopyingCoefficients T f ⋙ restrictCopyingCoefficients T g = restrictCopyingCoefficients T (g ≫ f) :=
  lift_congr (zariskiCopyingProperty T S'')
    (congrArg (fun F => (zariskiCopyingProperty T S).ι ⋙ F) (restrictStructureFunctor_comp T.signature g f))
    _ _

/-- Copying model categories form a coefficient functor, with coherent identities and composition. -/
def copyingCoefficients (T : Theory.{u}) : Scheme.{u}ᵒᵖ ⥤ Cat where
  obj S := Cat.of (zariskiCopyingProperty T S.unop).FullSubcategory
  map f := (restrictCopyingCoefficients T f.unop).toCatHom
  map_id S := congrArg Functor.toCatHom (restrictCopyingCoefficients_id T S.unop)
  map_comp f g := congrArg Functor.toCatHom (restrictCopyingCoefficients_comp T g.unop f.unop).symm

end SHIGURE.Copying
