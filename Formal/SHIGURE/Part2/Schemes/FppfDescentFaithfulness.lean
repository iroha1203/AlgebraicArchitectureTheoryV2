import Formal.SHIGURE.Part2.Schemes.AffineFppfFaithfulness
import Formal.SHIGURE.Part2.Schemes.FppfDescentBaseChange

/-! # Globally detecting module maps by fppf pullback -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

private theorem map_eq_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {x y : C} {f g : x ⟶ y} (equal : F.map f = F.map g) :
    G.map f = G.map g := by
  apply (cancel_epi (e.hom.app x)).1
  rw [← e.hom.naturality f, ← e.hom.naturality g, equal]

set_option maxHeartbeats 725000 in
/-- Equality of fppf descent maps is detected on any Zariski cover where
the pulled-back fppf comparison is faithful. -/
theorem fppfComparison_faithful_of_openCover {X : Scheme.{u}} (cover : FppfCover X) (opens : X.OpenCover)
    (checks : ∀ i, (fppfModuleComparison (cover.pullback₁ (opens.f i))).Faithful) :
    (fppfModuleComparison cover).Faithful where
  map_injective {M N} {f g} eq := by
    let G := Q.toDescentData opens.f
    letI : G.IsEquivalence := openCoverComparison_isEquivalence_anySize opens
    apply G.map_injective
    apply Pseudofunctor.DescentData.Hom.ext
    funext i
    let H := fppfDescentBaseChange cover (opens.f i)
    let e := fppfComparisonBaseChange cover (opens.f i)
    let K := fppfModuleComparison (cover.pullback₁ (opens.f i))
    have localComp := map_eq_of_iso e (congrArg H.map eq)
    letI : K.Faithful := checks i
    exact K.map_injective localComp

set_option maxHeartbeats 725000 in
/-- Pullback to any fppf covering family detects equality of maps of
quasi-coherent modules over an arbitrary scheme. -/
theorem fppfComparison_faithful {X : Scheme.{u}} (cover : FppfCover X) :
    (fppfModuleComparison cover).Faithful := by
  apply fppfComparison_faithful_of_openCover cover X.affineCover
  intro i
  exact affineFppfComparison_faithful (cover.pullback₁ (X.affineCover.f i))

end

end SHIGURE.SchemeDescent
