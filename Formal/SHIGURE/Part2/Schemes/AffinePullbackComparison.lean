import Formal.SHIGURE.Part2.Schemes.AffineTildeComposition
import Formal.SHIGURE.Part2.Descent.ScalarCocycle

/-! # Pullback of affine overlap comparisons -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {R S T : CommRingCat.{u}}

/-- Compose affine pullbacks, using the original composite ring morphism. -/
def affinePullbackComposition (f : R ⟶ S) (g : S ⟶ T) :
    pullback (Spec.map f) ⋙ pullback (Spec.map g) ≅ pullback (Spec.map (f ≫ g)) :=
  (pullbackCongr (Spec.map_comp f g) ≪≫ (pullbackComp (Spec.map g) (Spec.map f)).symm).symm

set_option maxHeartbeats 500000 in
/-- The component of affine composition coherence on one coefficient module. -/
theorem tildePullbackIso_comp_at (f : R ⟶ S) (g : S ⟶ T) (M : ModuleCat.{u} R) :
    (affinePullbackComposition f g).hom.app ((tilde.functor R).obj M) ≫
      (tildePullbackIso (f ≫ g)).hom.app M ≫
      (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).hom.app M) =
    (pullback (Spec.map g)).map ((tildePullbackIso f).hom.app M) ≫
      (tildePullbackIso g).hom.app ((ModuleCat.extendScalars f.hom).obj M) := by
  let r := (affinePullbackComposition f g).app ((tilde.functor R).obj M)
  let u := (tildePullbackIso (f ≫ g)).app M
  let s := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let a := (tildePullbackIso f).app M
  let b := (tildePullbackIso g).app ((ModuleCat.extendScalars f.hom).obj M)
  let P := pullback (Spec.map g)
  let E := tilde.functor T
  have equal := congrArg (fun e => e.hom.app M) (tildePullbackIso_comp f g)
  have composed : u.hom ≫ E.map s.hom = r.inv ≫ P.map a.hom ≫ b.hom := by
    change (tildePullbackIso (f ≫ g)).hom.app M ≫
      (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).hom.app M) =
      ((pullbackCongr (Spec.map_comp f g) ≪≫ (pullbackComp (Spec.map g) (Spec.map f)).symm).hom.app
        ((tilde.functor R).obj M)) ≫ P.map a.hom ≫ b.hom
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Category.assoc] using equal
  change r.hom ≫ u.hom ≫ E.map s.hom = P.map a.hom ≫ b.hom
  rw [composed, r.hom_inv_id_assoc]

set_option maxHeartbeats 550000 in
/-- Pulling back an affine overlap comparison is scalar extension along the
same homomorphism of overlap rings, including both composition constraints. -/
theorem tildePullComparison (f₀ f₁ : R ⟶ S) (g : S ⟶ T) {M N : ModuleCat.{u} R}
    (δ : (ModuleCat.extendScalars f₀.hom).obj M ⟶ (ModuleCat.extendScalars f₁.hom).obj N) :
    (affinePullbackComposition f₀ g).inv.app ((tilde.functor R).obj M) ≫
    (pullback (Spec.map g)).map ((tildePullbackIso f₀).hom.app M ≫
      (tilde.functor S).map δ ≫ (tildePullbackIso f₁).inv.app N) ≫
    (affinePullbackComposition f₁ g).hom.app ((tilde.functor R).obj N) =
    (tildePullbackIso (f₀ ≫ g)).hom.app M ≫
      (tilde.functor T).map (scalarExtensionPullHom f₀.hom f₁.hom g.hom δ) ≫
      (tildePullbackIso (f₁ ≫ g)).inv.app N :=
  comparison_through_baseChange (tilde.functor S) (tilde.functor T) (ModuleCat.extendScalars g.hom)
    (pullback (Spec.map g)) (tildePullbackIso g) δ
    ((tildePullbackIso f₀).app M) ((tildePullbackIso f₁).app N)
    ((affinePullbackComposition f₀ g).app ((tilde.functor R).obj M))
    ((affinePullbackComposition f₁ g).app ((tilde.functor R).obj N))
    ((ModuleCat.extendScalarsComp f₀.hom g.hom).app M)
    ((ModuleCat.extendScalarsComp f₁.hom g.hom).app N)
    ((tildePullbackIso (f₀ ≫ g)).app M) ((tildePullbackIso (f₁ ≫ g)).app N)
    (tildePullbackIso_comp_at f₀ g M) (tildePullbackIso_comp_at f₁ g N)

end

end SHIGURE.SchemeDescent
