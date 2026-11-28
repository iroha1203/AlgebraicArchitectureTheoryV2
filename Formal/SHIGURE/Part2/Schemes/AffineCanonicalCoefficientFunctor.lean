import Formal.SHIGURE.Part2.Schemes.AffineCanonicalCoefficientChart
import Formal.SHIGURE.Part2.Schemes.AffineDescentCoefficientMaps

/-! # The coefficient functor on canonical geometric descent data -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

private abbrev targetFiber := quasiCoherentModulesPseudofunctor.obj (.mk (op (Spec (CommRingCat.of B))))

/-- Read the original quasi-coherent chart of a singleton descent datum. -/
def affineChartEvaluation : AffineSingletonDescentData A B ⥤ targetFiber B where
  obj D := D.obj ()
  map f := f.hom ()
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The representing coefficient modules and their actual chart maps. -/
def affineCoefficientFunctor : AffineSingletonDescentData A B ⥤ ModuleCat.{u} B :=
  affineChartEvaluation A B ⋙ (affineTildeEquivalence (CommRingCat.of B)).inverse

/-- The geometric comparison on associated modules over the affine base. -/
def affineCanonicalDatumFunctor : ModuleCat.{u} A ⥤ AffineSingletonDescentData A B :=
  affineTildeFunctor (CommRingCat.of A) ⋙
    quasiCoherentModulesPseudofunctor.toDescentData (fun _ : Unit => affineScalarMap A B)

set_option maxHeartbeats 650000 in
private def affineCanonicalEvaluationIso :
    affineCanonicalDatumFunctor A B ⋙ affineChartEvaluation A B ≅
      affineTildeFunctor (CommRingCat.of A) ⋙ affinePullbackFunctor (CommRingCat.ofHom (algebraMap A B)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl

set_option maxHeartbeats 750000 in
/-- On the canonical geometric datum, the coefficient functor is naturally
the scalar extension from the original affine base. -/
def affineCanonicalCoefficientNatIso :
    affineCanonicalDatumFunctor A B ⋙ affineCoefficientFunctor A B ≅
      ModuleCat.extendScalars.{u,u,u} (R := A) (S := B) (algebraMap A B) := by
  let E := affineTildeEquivalence (CommRingCat.of B)
  let G : ModuleCat.{u} A ⥤ ModuleCat.{u} B := ModuleCat.extendScalars (algebraMap A B)
  let r := CommRingCat.ofHom (algebraMap A B)
  let iso := affineCanonicalEvaluationIso A B ≪≫ affineTildePullbackIso r
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iso E.inverse ≪≫
    Functor.associator G E.functor E.inverse ≪≫ Functor.isoWhiskerLeft G E.unitIso.symm ≪≫ G.rightUnitor

set_option maxHeartbeats 950000 in
/-- The natural coefficient comparison uses the same component as the
comparison obtained by reflecting the canonical associated-module chart. -/
theorem affineCanonicalCoefficientNatIso_app_hom (M : ModuleCat.{u} A) :
    (affineCanonicalCoefficientNatIso A B).hom.app M =
      (affineCanonicalCoefficientIso (B := B) M).hom := by
  let R := CommRingCat.of B
  let E := affineTildeEquivalence R
  let a := (affineTildePullbackIso (CommRingCat.ofHom (algebraMap A B))).app M
  let N := (ModuleCat.extendScalars (algebraMap A B)).obj M
  let K := (affineCanonicalDatum (B := B) M).obj ()
  apply E.fullyFaithfulFunctor.map_injective
  have app : (affineCanonicalCoefficientNatIso A B).hom.app M =
      E.inverse.map a.hom ≫ E.unitInv.app N := by
    simp only [affineCanonicalCoefficientNatIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.rightUnitor_hom_app, Category.id_comp, affineCanonicalEvaluationIso,
      NatIso.ofComponents_hom_app, Iso.refl_hom]
    rfl
  rw [app, E.functor.map_comp, ← E.counit_app_functor]
  have natural : E.functor.map (E.inverse.map a.hom) ≫ E.counit.app (E.functor.obj N) =
      E.counit.app K ≫ a.hom := E.counit.naturality a.hom
  rw [natural]
  exact (affineCanonicalCoefficientIso_tilde_hom (B := B) M).symm

end

end SHIGURE.SchemeDescent
