import Formal.SHIGURE.Part1.LensCoordinates
import Formal.SHIGURE.Part1.LensFixed

/-! # Fixed-view and empty-view lens examples

The same Boolean product has a nonidentity arrow in the fixed-view fiber
and an arrow of the ordinary lens category excluded by that fiber.
An empty view still has an exact semantic model under Theorem 2.9.
-/

namespace SHIGURE.Lens

open CategoryTheory

/-- An empty view gives a lens with an empty state type. -/
def emptyView : Lens.{0} := product Empty Unit

/-- Encoding and reading the lens does not require a chosen view. -/
theorem emptyView_recovered : ofModel emptyView.toModel = emptyView ∧ IsEmpty emptyView.State :=
  ⟨ofModel_toModel _, ⟨fun state => nomatch state.1⟩⟩

namespace BooleanExample

/-- The Boolean product as an object of the fiber over `Bool`. -/
def fixed : Fixed Bool := ⟨lens, rfl⟩

/-- The complement flip has identity view and so lies in the fixed-view fiber. -/
def fixedFlip : fixed ⟶ fixed :=
  ⟨flipComplement, (Fixed.view_lift_iff (A := fixed) (B := fixed) flipComplement).2 fun _ => rfl⟩

/-- On an actual fixed-model arrow the complement flip changes a state. -/
theorem fixedFlip_model_value :
    (FixedModel.Hom.modelHom (Fixed.toFixedHom fixedFlip)).hom.onSort .source (false, false) = (false, true) := by
  rw [Fixed.toFixedHom_modelHom, Lens.toModelHom_source_apply]
  rfl

/-- Flipping the view and leaving the complement unchanged is an ordinary lens arrow. -/
def flipView : lens ⟶ lens :=
  ⟨fun a => (!a.1, a.2), Bool.not, fun _ => rfl, fun _ _ => rfl⟩

/-- The view flip cannot be an arrow of the fiber over the Boolean view. -/
theorem flipView_not_fixed : ¬ viewFunctor.IsHomLift (𝟙 Bool) flipView := by
  intro lifted
  have opposite : true = false := (Fixed.view_lift_iff (A := fixed) (B := fixed) flipView).1 lifted false
  cases opposite

end BooleanExample
end SHIGURE.Lens
