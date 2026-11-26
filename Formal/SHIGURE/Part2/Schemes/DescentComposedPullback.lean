import Formal.SHIGURE.Part2.Schemes.ComposedModulePullback
import Formal.SHIGURE.Part2.Schemes.DescentPullHom

/-! # Pullback of geometric descent maps along specified composites -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u

private abbrev F := quasiCoherentModulesPseudofunctor
private abbrev forget (X : Scheme.{u}) := (quasiCoherentModulesProperty.prop (.mk (op X))).ι

variable {X₀ X₁ Y T : Scheme.{u}} {a₀ : Y ⟶ X₀} {a₁ : Y ⟶ X₁}
  {M : F.obj (.mk (op X₀))} {N : F.obj (.mk (op X₁))}

set_option maxHeartbeats 500000 in
/-- Forgetting to module sheaves identifies the pulled comparison with the
iterated pullback followed by the specified comparisons of composites. -/
theorem quasiCoherentPullHom_forget_composed
    (d : (F.map a₀.op.toLoc).toFunctor.obj M ⟶ (F.map a₁.op.toLoc).toFunctor.obj N)
    (k : T ⟶ Y) (b₀ : T ⟶ X₀) (b₁ : T ⟶ X₁) (e₀ : k ≫ a₀ = b₀) (e₁ : k ≫ a₁ = b₁)
    (y : (pullback a₀).obj M.obj ⟶ (pullback a₁).obj N.obj)
    (equal : (forget Y).map d = y) :
    (forget T).map (pullHom (F := F) d k b₀ b₁ e₀ e₁) =
      (pullbackCompositionFor a₀ k b₀ e₀).inv.app M.obj ≫
        (pullback k).map y ≫ (pullbackCompositionFor a₁ k b₁ e₁).hom.app N.obj := by
  rw [pullbackCompositionFor_inv_app, pullbackCompositionFor_hom_app, ← equal]
  exact quasiCoherentPullHom_forget d k b₀ b₁ e₀ e₁

end

end SHIGURE.SchemeDescent
