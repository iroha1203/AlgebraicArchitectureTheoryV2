import Formal.SHIGURE.Part1.PullbackComparison
import Mathlib.CategoryTheory.Category.Cat

/-! # Contravariant model semantics of the quotient theory category

## Implementation notes

The strict comparisons of Theorem 2.4 are used in a functor to mathlib
`Cat`. The quotient is the one formed from interpretation equivalence in
Appendix A. A raw representative supplies a pullback, and its equivalence
class determines that functor by the comparison theorem. Keeping raw
interpretations as arrows would depend on the choice of proof trees.
-/

universe u

namespace SHIGURE.Theory

open CategoryTheory

variable {S T U : Theory.{u}}

/-- The model pullback of a theory arrow is independent of its interpretation representative. -/
noncomputable def modelPullback (f : S ⟶ T) : Model T ⥤ Model S :=
  Quotient.lift Interpretation.pullback (fun _ _ same => Interpretation.pullback_eq_of_equivalent same) f

/-- A quotient representative acts by its pullback functor. -/
@[simp] theorem modelPullback_ofInterpretation (f : Interpretation S T) :
    modelPullback (ofInterpretation f) = f.pullback :=
  rfl

/-- The identity theory arrow acts by the identity model functor. -/
@[simp] theorem modelPullback_id (S : Theory.{u}) : modelPullback (𝟙 S) = 𝟭 (Model S) :=
  Interpretation.pullback_identity S

/-- The model functors compose in the reverse order to the arrows of the theory category. -/
theorem modelPullback_comp (f : S ⟶ T) (g : T ⟶ U) :
    modelPullback (f ≫ g) = modelPullback g ⋙ modelPullback f :=
  Quotient.inductionOn₂ f g fun u v => Interpretation.pullback_comp v u

/-- Corollary 2.4a(a): the model functors for an inverse pair compose to the identity on the source. -/
theorem modelPullback_inv_hom (e : S ≅ T) :
    modelPullback e.inv ⋙ modelPullback e.hom = 𝟭 (Model S) := by
  rw [← modelPullback_comp, e.hom_inv_id, modelPullback_id]

/-- Corollary 2.4a(a): the model functors for an inverse pair compose to the identity on the target. -/
theorem modelPullback_hom_inv (e : S ≅ T) :
    modelPullback e.hom ⋙ modelPullback e.inv = 𝟭 (Model T) := by
  rw [← modelPullback_comp, e.inv_hom_id, modelPullback_id]

/-- The contravariant functor of model categories uses the actual quotient category of theories. -/
noncomputable def modelSemantics : Theory.{u}ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj T := Cat.of (Model T.unop)
  map f := (modelPullback f.unop).toCatHom
  map_id X := by
    apply Cat.ext
    exact modelPullback_id X.unop
  map_comp f g := by
    apply Cat.ext
    exact modelPullback_comp g.unop f.unop

/-- The semantic functor assigns the ordinary model category to the input theory. -/
@[simp] theorem modelSemantics_obj (T : Theory.{u}ᵒᵖ) :
    modelSemantics.obj T = Cat.of (Model T.unop) := rfl

/-- The semantic functor reads a theory arrow as the corresponding contravariant pullback. -/
theorem modelSemantics_map_toFunctor {X Y : Theory.{u}ᵒᵖ} (f : X ⟶ Y) :
    (modelSemantics.map f).toFunctor = modelPullback f.unop := rfl

end SHIGURE.Theory
