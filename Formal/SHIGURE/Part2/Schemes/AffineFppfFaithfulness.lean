import Formal.SHIGURE.Part2.Schemes.AffineDescentFaithfulness
import Formal.SHIGURE.Part2.Schemes.FiniteFppfProduct
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentZariskiStack

/-! # Detecting maps by an arbitrary fppf cover of an affine base -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v w

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {R : CommRingCat.{u}} {cover : FppfCover (Spec R)}

set_option maxHeartbeats 650000 in
/-- Faithful flatness of the product and the Zariski cover by its components
make the affine component comparison faithful. -/
theorem AffineRefinement.comparison_faithful (refinement : AffineRefinement cover) :
    (fppfModuleComparison refinement.affine.cover).Faithful := by
  let P := (Q.map (Spec.map refinement.productMap).op.toLoc).toFunctor
  let E := Q.toDescentData refinement.productOpenCover.f
  letI : P.Faithful := affineFaithfullyFlatPullback_faithful (A := R) (B := refinement.productRing)
  letI : E.IsEquivalence := openCoverComparison_isEquivalence_anySize refinement.productOpenCover
  exact Functor.Faithful.of_comp_iso refinement.restrictGlobalComparisonToProduct


section Comparison

variable {X : Scheme.{u}} {original : FppfCover.{u,v} X} {small : FppfCover.{u,w} X}

/-- Restricting to a covering family over the given charts detects maps if
the comparison for that family detects maps. -/
theorem fppfComparison_faithful_of_refinement
    (m : Precoverage.ZeroHypercover.Hom (Scheme.precoverage FppfComponent) small original) (faithful : (fppfModuleComparison small).Faithful) :
    (fppfModuleComparison original).Faithful := by
  let w (i : small.I₀) :
      m.h₀ i ≫ original.f (m.s₀ i) = small.f i ≫ 𝟙 X := by
    rw [Category.comp_id]
    exact m.w₀ i
  let E := fppfModuleComparison small
  letI : E.Faithful := faithful
  let e := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso Q w
  let unit := Cat.Hom.toNatIso (Q.mapId (.mk (op X)))
  exact Functor.Faithful.of_comp_iso
    (e ≪≫ Functor.isoWhiskerRight unit E ≪≫ E.leftUnitor)

/-- Choose one original chart over each point. This puts the indexing type in
the base universe, so the product of the rings in an affine refinement can
be used in the same universe as the base ring. -/
def fppfPointSubcover (cover : FppfCover X) : FppfCover.{u,u} X where
  I₀ := X
  X x := cover.X (cover.idx x)
  f x := cover.f (cover.idx x)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x => ⟨x, cover.covers x⟩, fun x => cover.map_prop (cover.idx x)⟩

/-- The point-indexed cover uses the original charts and original morphisms. -/
def fppfPointSubcoverOver (cover : FppfCover.{u,v} X) :
    Precoverage.ZeroHypercover.Hom (Scheme.precoverage FppfComponent) (fppfPointSubcover cover) cover where
  s₀ := cover.idx
  h₀ _ := 𝟙 _
  w₀ _ := Category.id_comp _

end Comparison

set_option maxHeartbeats 750000 in
/-- Every fppf covering family of a spectrum detects equality of morphisms
of quasi-coherent modules, through the actual affine refinement. -/
theorem affineFppfComparison_faithful (cover : FppfCover (Spec R)) :
    (fppfModuleComparison cover).Faithful := by
  let small := fppfPointSubcover cover
  let refinement := affineRefinement small
  have faithful : (fppfModuleComparison small).Faithful :=
    fppfComparison_faithful_of_refinement refinement.over refinement.comparison_faithful
  exact fppfComparison_faithful_of_refinement (fppfPointSubcoverOver cover) faithful

end

end SHIGURE.SchemeDescent
