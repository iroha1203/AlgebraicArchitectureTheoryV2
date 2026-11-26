import Mathlib.AlgebraicGeometry.Cover.Sigma
import Formal.SHIGURE.Part2.Schemes.FppfDescentData

/-! # The finite affine refinement and its single faithfully flat map -/

namespace SHIGURE.SchemeDescent.AffineRefinement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {R : CommRingCat.{u}} {cover : FppfCover (Spec R)} (F : AffineRefinement cover)

/-- The selected component family generates a subsieve of the original fppf cover. -/
theorem sieve_refines :
    Sieve.ofArrows F.affine.cover.X F.affine.cover.f ≤ Sieve.ofArrows cover.X cover.f :=
  F.over.sieve₀_le_sieve₀

/-- The product-ring morphism underlying affine descent is itself a singleton fppf cover. -/
def productCover : FppfCover (Spec R) := by
  letI : Finite F.affine.I₀ := F.finite
  have property : FppfComponent (Sigma.desc F.affine.f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := FppfComponent) F.affine.cover.map_prop
  have property' : FppfComponent (Spec.map F.productMap) := by
    rw [← F.productSpec_over] at property
    exact (MorphismProperty.cancel_left_of_respectsIso FppfComponent (sigmaSpec F.affine.X) _).mp property
  apply Precoverage.ZeroHypercover.singleton (Spec.map F.productMap)
  exact (Scheme.singleton_mem_precoverage_iff FppfComponent _).2
    ⟨F.product_flat_surjective.2.surj, property'⟩

/-- The component spectra form a refinement of the singleton product cover via
the corresponding open immersions into the spectrum of the product. -/
def toProductCover : F.affine.cover ⟶ F.productCover where
  s₀ _ := PUnit.unit
  h₀ i := Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
  w₀ i := by
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) ≫ Spec.map F.productMap = F.affine.f i
    exact (Spec.map_comp _ _).symm.trans
      ((congrArg (fun a : R ⟶ F.affine.X i => Spec.map a) (F.productMap_eval i)).trans
        (F.spec_componentMap i))

set_option maxHeartbeats 500000 in
/-- Each component enters the product spectrum as an open subscheme. -/
theorem toProductCover_isOpenImmersion (i : F.affine.I₀) :
    IsOpenImmersion (F.toProductCover.h₀ i) := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j : F.affine.I₀ => ↑(F.affine.X j)) i)))
  infer_instance

/-- The component spectra give the actual Zariski cover of the finite product spectrum. -/
def productOpenCover : (Spec F.productRing).OpenCover where
  I₀ := F.affine.I₀
  X i := Spec (F.affine.X i)
  f i := Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => F.toProductCover_isOpenImmersion i⟩
    let e := F.productSpecIso
    let opens := AlgebraicGeometry.sigmaOpenCover (fun i => Spec (F.affine.X i))
    obtain ⟨i, y, hy⟩ := opens.exists_eq (e.inv x)
    refine ⟨i, y, ?_⟩
    change (Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))) y = x
    have factor : Sigma.ι (fun j => Spec (F.affine.X j)) i ≫ e.hom =
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) :=
      ι_sigmaSpec F.affine.X i
    have component : Sigma.ι (fun j => Spec (F.affine.X j)) i y = e.inv x := hy
    calc
      _ = (Sigma.ι (fun j => Spec (F.affine.X j)) i ≫ e.hom) y :=
        congrArg (fun a : Spec (F.affine.X i) ⟶ Spec F.productRing => a y) factor.symm
      _ = e.hom (Sigma.ι (fun j => Spec (F.affine.X j)) i y) := rfl
      _ = e.hom (e.inv x) := congrArg (fun z => e.hom z) component
      _ = x := congrArg (fun a : Spec F.productRing ⟶ Spec F.productRing => a x) e.inv_hom_id

private theorem productChart_square (i : F.affine.I₀) :
    𝟙 (Spec (F.affine.X i)) ≫ F.affine.f i =
      F.productOpenCover.f i ≫ Spec.map F.productMap := by
  rw [Category.id_comp]
  exact (F.toProductCover.w₀ i).symm

/-- Descent data on the affine components restrict to the actual open cover of
the product spectrum. The pullback functor retains all overlap compatibilities. -/
def restrictDescentToProduct :
    FppfModuleDescentData F.affine.cover ⥤
      quasiCoherentModulesPseudofunctor.DescentData F.productOpenCover.f :=
  Pseudofunctor.DescentData.pullFunctor quasiCoherentModulesPseudofunctor
    (f := F.affine.cover.f) (p := Spec.map F.productMap) (f' := F.productOpenCover.f)
    (α := id) (p' := fun i => 𝟙 (Spec (F.affine.X i))) F.productChart_square

/-- The restriction to product charts agrees with the descent comparison of
the actual pullback to the product spectrum. -/
def restrictGlobalComparisonToProduct :
    fppfModuleComparison F.affine.cover ⋙ F.restrictDescentToProduct ≅
      (quasiCoherentModulesPseudofunctor.map (Spec.map F.productMap).op.toLoc).toFunctor ⋙
        quasiCoherentModulesPseudofunctor.toDescentData F.productOpenCover.f :=
  Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    quasiCoherentModulesPseudofunctor F.productChart_square

end

end SHIGURE.SchemeDescent.AffineRefinement
