import Formal.SHIGURE.Part2.Schemes.DescentComparisons

/-! # Forgetting quasi-coherence in descent maps -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u

private abbrev F := quasiCoherentModulesPseudofunctor
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
  let I := forget T
  let S₀ := F.mapComp' a₀.op.toLoc k.op.toLoc b₀.op.toLoc (congrArg (fun f => f.op.toLoc) e₀)
  let S₁ := F.mapComp' a₁.op.toLoc k.op.toLoc b₁.op.toLoc (congrArg (fun f => f.op.toLoc) e₁)
  let l := S₀.hom.toNatTrans.app M
  let r := S₁.inv.toNatTrans.app N
  let m := (F.map k.op.toLoc).toFunctor.map d
  have lEq : I.map l = (pullbackCongr e₀.symm).hom.app M.obj ≫ (pullbackComp k a₀).inv.app M.obj :=
    quasiCoherentMapComp'_hom k a₀ b₀ e₀ M
  have rEq : I.map r = (pullbackComp k a₁).hom.app N.obj ≫ (pullbackCongr e₁).hom.app N.obj :=
    quasiCoherentMapComp'_inv k a₁ b₁ e₁ N
  have mEq : I.map m = (pullback k).map ((forget Y).map d) := rfl
  change I.map (l ≫ m ≫ r) = _
  rw [I.map_comp, I.map_comp, lEq, mEq, rEq]

end

end SHIGURE.SchemeDescent
