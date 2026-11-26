import Formal.SHIGURE.Part2.Schemes.AffinePullbackComparison
import Formal.SHIGURE.Part2.Schemes.ComposedModulePullback
import Formal.SHIGURE.Part2.Schemes.AffineQuasiCoherentFiber
import Formal.SHIGURE.Part2.Schemes.DescentComposedPullback
import Formal.SHIGURE.Part2.Descent.ScalarChangeProjection

/-! # Geometric and scalar descent comparisons on spectra -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat SHIGURE.CoefficientDescent

noncomputable section

universe u

private abbrev F := quasiCoherentModulesPseudofunctor
private abbrev forget (X : Scheme.{u}) := (quasiCoherentModulesProperty.prop (.mk (op X))).ι

private theorem affinePullbackComposition_to_generic {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    affinePullbackComposition f g =
      pullbackCompositionFor (Spec.map f) (Spec.map g) (Spec.map (f ≫ g)) (Spec.map_comp f g).symm := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 550000 in
/-- On spectra, the pseudofunctor's pull of a normalized overlap map has the
scalar extension comparison for the composed ring maps. -/
theorem affinePullHom_scalar {R S T : CommRingCat.{u}} (f₀ f₁ : R ⟶ S) (g : S ⟶ T)
    {M N : ModuleCat.{u} R}
    (m : (affinePullbackFunctor f₀).obj ((affineTildeFunctor R).obj M) ⟶
      (affinePullbackFunctor f₁).obj ((affineTildeFunctor R).obj N))
    (δ : (ModuleCat.extendScalars f₀.hom).obj M ⟶ (ModuleCat.extendScalars f₁.hom).obj N)
    (normalized : (forget (Spec S)).map m = (tildePullbackIso f₀).hom.app M ≫
      (tilde.functor S).map δ ≫ (tildePullbackIso f₁).inv.app N) :
    (forget (Spec T)).map (pullHom (F := F) m (Spec.map g) (Spec.map (f₀ ≫ g)) (Spec.map (f₁ ≫ g))
      (Spec.map_comp f₀ g).symm (Spec.map_comp f₁ g).symm) =
    (tildePullbackIso (f₀ ≫ g)).hom.app M ≫
      (tilde.functor T).map (scalarExtensionPullHom f₀.hom f₁.hom g.hom δ) ≫
      (tildePullbackIso (f₁ ≫ g)).inv.app N := by
  let M' := (affineTildeFunctor R).obj M
  let N' := (affineTildeFunctor R).obj N
  let y := (tildePullbackIso f₀).hom.app M ≫ (tilde.functor S).map δ ≫ (tildePullbackIso f₁).inv.app N
  have computed := quasiCoherentPullHom_forget_composed (M := M') (N := N') m (Spec.map g)
    (Spec.map (f₀ ≫ g)) (Spec.map (f₁ ≫ g)) (Spec.map_comp f₀ g).symm (Spec.map_comp f₁ g).symm y normalized
  rw [← affinePullbackComposition_to_generic f₀ g, ← affinePullbackComposition_to_generic f₁ g] at computed
  exact computed.trans (tildePullComparison f₀ f₁ g δ)


set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
/-- The same comparison for independently named ring maps of the triple overlap. -/
theorem affinePullHom_scalar_at {R S T : CommRingCat.{u}} (f₀ f₁ : R ⟶ S) (g : S ⟶ T)
    {r₀ r₁ : R ⟶ T} (h₀ : f₀ ≫ g = r₀) (h₁ : f₁ ≫ g = r₁)
    {M N : ModuleCat.{u} R}
    (m : (affinePullbackFunctor f₀).obj ((affineTildeFunctor R).obj M) ⟶
      (affinePullbackFunctor f₁).obj ((affineTildeFunctor R).obj N))
    (δ : (ModuleCat.extendScalars f₀.hom).obj M ⟶ (ModuleCat.extendScalars f₁.hom).obj N)
    (normalized : (forget (Spec S)).map m = (tildePullbackIso f₀).hom.app M ≫
      (tilde.functor S).map δ ≫ (tildePullbackIso f₁).inv.app N) :
    (forget (Spec T)).map (pullHom (F := F) m (Spec.map g) (Spec.map r₀) (Spec.map r₁)
      ((Spec.map_comp f₀ g).symm.trans (congrArg (fun k : R ⟶ T => Spec.map k) h₀))
      ((Spec.map_comp f₁ g).symm.trans (congrArg (fun k : R ⟶ T => Spec.map k) h₁))) =
    (tildePullbackIso r₀).hom.app M ≫
      (tilde.functor T).map (scalarExtensionPullHomAt f₀.hom f₁.hom g.hom
        (congrArg (fun k : R ⟶ T => k.hom) h₀) (congrArg (fun k : R ⟶ T => k.hom) h₁) δ) ≫
      (tildePullbackIso r₁).inv.app N := by
  subst r₀
  subst r₁
  rw [scalarExtensionPullHomAt_comp]
  exact affinePullHom_scalar f₀ f₁ g m δ normalized

end

end SHIGURE.SchemeDescent
