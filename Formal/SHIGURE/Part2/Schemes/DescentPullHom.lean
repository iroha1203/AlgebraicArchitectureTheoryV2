import Formal.SHIGURE.Part2.Schemes.DescentComparisons

/-! # Forgetting quasi-coherence in descent maps -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u

/-- The geometric quasi-coherent module pseudofunctor used by Appendix B.3. -/
private abbrev F := quasiCoherentModulesPseudofunctor
/-- The inclusion of the quasi-coherent fiber into all module sheaves in Appendix B.3. -/
private abbrev forget (X : Scheme.{u}) := (quasiCoherentModulesProperty.prop (.mk (op X))).ι

variable {X₀ X₁ Y T : Scheme.{u}} {a₀ : Y ⟶ X₀} {a₁ : Y ⟶ X₁}
  {M : F.obj (.mk (op X₀))} {N : F.obj (.mk (op X₁))}

/-- Forgetting quasi-coherence recovers the original module-sheaf pullback
of a descent map, with its two original composition comparisons. -/
theorem quasiCoherentPullHom_forget
    (d : (F.map a₀.op.toLoc).toFunctor.obj M ⟶ (F.map a₁.op.toLoc).toFunctor.obj N)
    (k : T ⟶ Y) (b₀ : T ⟶ X₀) (b₁ : T ⟶ X₁) (e₀ : k ≫ a₀ = b₀) (e₁ : k ≫ a₁ = b₁) :
    (forget T).map (pullHom (F := F) d k b₀ b₁ e₀ e₁) =
      ((pullbackCongr e₀.symm).hom.app M.obj ≫ (pullbackComp k a₀).inv.app M.obj) ≫
        (pullback k).map ((forget Y).map d) ≫
        ((pullbackComp k a₁).hom.app N.obj ≫ (pullbackCongr e₁).hom.app N.obj) := by
  subst b₀; subst b₁
  change (forget T).map
    ((F.mapComp' a₀.op.toLoc k.op.toLoc (k ≫ a₀).op.toLoc rfl).hom.toNatTrans.app M ≫
      (F.map k.op.toLoc).toFunctor.map d ≫
      (F.mapComp' a₁.op.toLoc k.op.toLoc (k ≫ a₁).op.toLoc rfl).inv.toNatTrans.app N) = _
  rw [Functor.map_comp, Functor.map_comp,
    quasiCoherentMapComp'_hom k a₀ (k ≫ a₀) rfl M,
    quasiCoherentMapComp'_inv k a₁ (k ≫ a₁) rfl N]
  rfl

end

end SHIGURE.SchemeDescent
