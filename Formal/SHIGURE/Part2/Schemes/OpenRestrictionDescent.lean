import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentPullback
import Formal.SHIGURE.Part2.Schemes.OpenPullbackCoherence

/-! # Restricting an open-overlap comparison

Identify pulling back a comparison morphism with restricting the corresponding
map of module sheaves along an open immersion.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u

private theorem restrictFunctorIsoPullback_comp_app {T V U : Scheme.{u}}
    (k : T ⟶ V) (p : V ⟶ U) [IsOpenImmersion k] [IsOpenImmersion p] (M : U.Modules) :
    (restrictFunctorIsoPullback (k ≫ p)).hom.app M =
      (restrictFunctorComp k p).hom.app M ≫
      (restrictFunctor k).map ((restrictFunctorIsoPullback p).hom.app M) ≫
      (restrictFunctorIsoPullback k).hom.app ((pullback p).obj M) ≫
      (pullbackComp k p).hom.app M := by
  have h := congrArg (fun e => e.hom.app M) (restrictFunctorIsoPullback_comp k p)
  have eq : (restrictFunctorComp k p).inv.app M ≫ (restrictFunctorIsoPullback (k ≫ p)).hom.app M =
      (restrictFunctor k).map ((restrictFunctorIsoPullback p).hom.app M) ≫
      (restrictFunctorIsoPullback k).hom.app ((pullback p).obj M) ≫ (pullbackComp k p).hom.app M := by
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using h
  rw [← eq, ← Category.assoc]
  exact (((restrictFunctorComp k p).app M).hom_inv_id_assoc _).symm

set_option maxRecDepth 1600 in
set_option maxHeartbeats 1500000 in
/-- The comparison on an open test scheme is the ordinary restriction of the
comparison on a larger scheme, after identifying the iterated restrictions. -/
theorem openRestriction_pullHom {T V U₁ U₂ : Scheme.{u}}
    (k : T ⟶ V) (p : V ⟶ U₁) (q : V ⟶ U₂)
    [IsOpenImmersion k] [IsOpenImmersion p] [IsOpenImmersion q]
    {M : quasiCoherentModulesPseudofunctor.obj (.mk (op U₁))}
    {N : quasiCoherentModulesPseudofunctor.obj (.mk (op U₂))}
    (φ : (quasiCoherentModulesPseudofunctor.map p.op.toLoc).toFunctor.obj M ⟶
      (quasiCoherentModulesPseudofunctor.map q.op.toLoc).toFunctor.obj N)
    (a : T ⟶ U₁) (b : T ⟶ U₂) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : k ≫ p = a) (hb : k ≫ q = b) :
    (restrictFunctorIsoPullback a).hom.app M.obj ≫
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map (pullHom φ k a b ha hb) ≫
      (restrictFunctorIsoPullback b).inv.app N.obj =
    (restrictFunctorCongr ha).inv.app M.obj ≫
      (restrictFunctorComp k p).hom.app M.obj ≫
      (restrictFunctor k).map
        ((restrictFunctorIsoPullback p).hom.app M.obj ≫
          (quasiCoherentModulesProperty.prop (.mk (op V))).ι.map φ ≫
          (restrictFunctorIsoPullback q).inv.app N.obj) ≫
      (restrictFunctorComp k q).inv.app N.obj ≫
      (restrictFunctorCongr hb).hom.app N.obj := by
  subst a
  subst b
  let h := (quasiCoherentModulesProperty.prop (.mk (op V))).ι.map φ
  let ep := (restrictFunctorComp k p).app M.obj
  let eq := (restrictFunctorComp k q).app N.obj
  let pp := (pullbackComp k p).app M.obj
  let pq := (pullbackComp k q).app N.obj
  let rp := (restrictFunctorIsoPullback p).app M.obj
  let rq := (restrictFunctorIsoPullback q).app N.obj
  let ra := (restrictFunctorIsoPullback (k ≫ p)).app M.obj
  let rb := (restrictFunctorIsoPullback (k ≫ q)).app N.obj
  let rk := restrictFunctorIsoPullback k
  have pull : (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
      (pullHom φ k (k ≫ p) (k ≫ q) rfl rfl) =
      pp.inv ≫ (pullback k).map h ≫ pq.hom := by
    let F := quasiCoherentModulesPseudofunctor
    have exactComp {U : Scheme.{u}} (l : V ⟶ U) :
        F.mapComp' l.op.toLoc k.op.toLoc (k ≫ l).op.toLoc rfl = F.mapComp l.op.toLoc k.op.toLoc :=
      F.mapComp'_eq_mapComp l.op.toLoc k.op.toLoc
    rw [pullHom, exactComp p, exactComp q]
    rfl
  have refl (U : Scheme.{u}) (l : T ⟶ U) [IsOpenImmersion l] :
      restrictFunctorCongr (rfl : l = l) = Iso.refl _ := by
    apply Iso.ext
    ext M' W x
    rw [restrictFunctorCongr_hom_app_app]
    have same : eqToHom (show l ''ᵁ W = l ''ᵁ W by rfl) = 𝟙 _ := Subsingleton.elim _ _
    rw [same, op_id, M'.presheaf.map_id]
    rfl
  rw [pull, refl, refl]
  change ra.hom ≫ (pp.inv ≫ (pullback k).map h ≫ pq.hom) ≫ rb.inv =
    𝟙 _ ≫ ep.hom ≫ (restrictFunctor k).map (rp.hom ≫ h ≫ rq.inv) ≫ eq.inv ≫ 𝟙 _
  have ha' : ra.hom = ep.hom ≫ (restrictFunctor k).map rp.hom ≫ rk.hom.app _ ≫ pp.hom :=
    restrictFunctorIsoPullback_comp_app k p M.obj
  have hb' : rb.hom = eq.hom ≫ (restrictFunctor k).map rq.hom ≫ rk.hom.app _ ≫ pq.hom :=
    restrictFunctorIsoPullback_comp_app k q N.obj
  apply (cancel_mono rb.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  rw [ha', hb']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Functor.map_comp,
    ← NatTrans.naturality_assoc]
  have cancel := ((restrictFunctor k).mapIso rq).inv_hom_id_assoc
    (rk.hom.app ((pullback q).obj N.obj) ≫ pq.hom)
  rw [Functor.mapIso_inv, Functor.mapIso_hom] at cancel
  rw [cancel]
  rfl

end

end SHIGURE.SchemeDescent
