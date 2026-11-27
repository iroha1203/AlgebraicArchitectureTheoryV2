import Formal.SHIGURE.Part2.Schemes.DescentComparisons
import Formal.SHIGURE.Part2.Schemes.OpenPullbackCoherence

/-! # Canonical comparisons for open-cover descent

The chart pullbacks of a global module induce the ordinary restriction
comparisons on the overlaps.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules

noncomputable section

universe u

private theorem openRestrictionComp_app {T V U : Scheme.{u}} (k : T ⟶ V) (p : V ⟶ U)
    [IsOpenImmersion k] [IsOpenImmersion p] (M : U.Modules) :
    (restrictFunctor k).map ((restrictFunctorIsoPullback p).hom.app M) ≫
      (restrictFunctorIsoPullback k).hom.app ((pullback p).obj M) ≫
      (pullbackComp k p).hom.app M =
    (restrictFunctorComp k p).inv.app M ≫ (restrictFunctorIsoPullback (k ≫ p)).hom.app M := by
  have eq := congrArg (fun e => e.hom.app M) (restrictFunctorIsoPullback_comp k p)
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using eq.symm

private theorem ofObj_map_abstract
    {C : Type*} [Category C]
    {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {X T : C} {U : ι → C} {f : ∀ i, U i ⟶ X}
    (M : G.obj (.mk (op X))) (c : T ⟶ X) {i j : ι}
    (a : T ⟶ U i) (b : T ⟶ U j) (ha : a ≫ f i = c) (hb : b ≫ f j = c)
    {D : Type*} [Category D] (I : G.obj (.mk (op T)) ⥤ D) :
    I.map ((DescentData.ofObj (F := G) (f := f) M).hom c a b ha hb) =
      I.map ((G.mapComp' (f i).op.toLoc a.op.toLoc c.op.toLoc (congrArg (fun g => g.op.toLoc) ha)).inv.toNatTrans.app M) ≫
      I.map ((G.mapComp' (f j).op.toLoc b.op.toLoc c.op.toLoc (congrArg (fun g => g.op.toLoc) hb)).hom.toNatTrans.app M) := by
  simp only [DescentData.ofObj_hom, Functor.map_comp]

private theorem pullbackCongr_rfl_app {T X : Scheme.{u}} (c : T ⟶ X) (N : X.Modules) :
    (pullbackCongr (rfl : c = c)).hom.app N = 𝟙 _ := by
  simp [pullbackCongr]

private theorem openCanonicalComparison_diag {C : Type*} [Category C]
    {X₁ X₂ X₃ X₄ X₅ X₆ Y₁ Y₁' Y₂' Y₂ : C}
    (fP : X₁ ⟶ X₂) (A : X₂ ⟶ X₃) (L : X₃ ⟶ X₄) (pullCongr : X₄ ⟶ X₅) (R : X₆ ≅ X₅)
    (B : Y₂ ≅ X₆) (Cinv : X₁ ⟶ Y₁) (S : Y₁ ⟶ Y₁') (D : Y₁' ≅ Y₂') (fQ : Y₂' ⟶ Y₂)
    (EA : Y₁ ⟶ X₄) (EB : Y₁' ⟶ X₅)
    (compA : fP ≫ A ≫ L = Cinv ≫ EA)
    (compB : fQ ≫ B.hom ≫ R.hom = D.inv ≫ EB)
    (congr' : S ≫ EB = EA ≫ pullCongr) :
    fP ≫ A ≫ (L ≫ pullCongr ≫ R.inv) ≫ B.inv = Cinv ≫ S ≫ D.hom ≫ fQ := by
  apply (cancel_mono (B.hom ≫ R.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [compB, Iso.hom_inv_id_assoc, ← Category.assoc A, ← Category.assoc, compA]
  simpa only [Category.assoc] using congrArg (Cinv ≫ ·) congr'.symm

/-- The canonical comparison of pullbacks of a global module induces the
canonical comparison of its ordinary restrictions on an open overlap. -/
theorem openCanonicalComparison {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ X} [∀ i, IsOpenImmersion (f i)] (i j : ι)
    (a : T ⟶ U i) (b : T ⟶ U j) [IsOpenImmersion a] [IsOpenImmersion b]
    (equal : a ≫ f i = b ≫ f j)
    (M : quasiCoherentModulesPseudofunctor.obj (.mk (op X))) :
    (restrictFunctor a).map ((restrictFunctorIsoPullback (f i)).hom.app M.obj) ≫
      (restrictFunctorIsoPullback a).hom.app ((pullback (f i)).obj M.obj) ≫
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
        ((DescentData.ofObj (F := quasiCoherentModulesPseudofunctor) (f := f) M).hom (a ≫ f i) a b rfl equal.symm) ≫
      (restrictFunctorIsoPullback b).inv.app ((pullback (f j)).obj M.obj) =
    (restrictFunctorComp a (f i)).inv.app M.obj ≫
      (restrictFunctorCongr equal).hom.app M.obj ≫
      (restrictFunctorComp b (f j)).hom.app M.obj ≫
      (restrictFunctor b).map ((restrictFunctorIsoPullback (f j)).hom.app M.obj) := by
  have hL :
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
        ((quasiCoherentModulesPseudofunctor.mapComp' (f i).op.toLoc a.op.toLoc (a ≫ f i).op.toLoc rfl).inv.toNatTrans.app M) =
      (pullbackComp a (f i)).hom.app M.obj :=
    (quasiCoherentMapComp'_inv a (f i) (a ≫ f i) rfl M).trans
      ((congrArg ((pullbackComp a (f i)).hom.app M.obj ≫ ·) (pullbackCongr_rfl_app (a ≫ f i) M.obj)).trans
        (Category.comp_id _))
  have hR :
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
        ((quasiCoherentModulesPseudofunctor.mapComp' (f j).op.toLoc b.op.toLoc (a ≫ f i).op.toLoc
          (congrArg (fun g => g.op.toLoc) equal.symm)).hom.toNatTrans.app M) =
      (pullbackCongr equal.symm.symm).hom.app M.obj ≫ (pullbackComp b (f j)).inv.app M.obj :=
    quasiCoherentMapComp'_hom b (f j) (a ≫ f i) equal.symm M
  have h1 := ofObj_map_abstract (G := quasiCoherentModulesPseudofunctor) (f := f) M (a ≫ f i) a b rfl equal.symm
    (quasiCoherentModulesProperty.prop (.mk (op T))).ι
  have compare := h1.trans (congrArg₂ (· ≫ ·) hL hR)
  have congr' :
      (restrictFunctorCongr equal).hom.app M.obj ≫ (restrictFunctorIsoPullback (b ≫ f j)).hom.app M.obj =
      (restrictFunctorIsoPullback (a ≫ f i)).hom.app M.obj ≫ (pullbackCongr equal.symm.symm).hom.app M.obj := by
    have h0 :
        (restrictFunctorCongr equal).hom.app M.obj ≫ (restrictFunctorIsoPullback (b ≫ f j)).hom.app M.obj =
        (restrictFunctorIsoPullback (a ≫ f i)).hom.app M.obj ≫ (pullbackCongr equal).hom.app M.obj := by
      simpa only [Iso.trans_hom, NatTrans.comp_app] using
        congrArg (fun e => e.hom.app M.obj) (restrictFunctorIsoPullback_congr equal)
    exact h0.trans (congrArg (fun h => (restrictFunctorIsoPullback (a ≫ f i)).hom.app M.obj ≫
      (pullbackCongr h).hom.app M.obj) (Subsingleton.elim equal equal.symm.symm))
  have main := openCanonicalComparison_diag
    ((restrictFunctor a).map ((restrictFunctorIsoPullback (f i)).hom.app M.obj))
    ((restrictFunctorIsoPullback a).hom.app ((pullback (f i)).obj M.obj))
    ((pullbackComp a (f i)).hom.app M.obj)
    ((pullbackCongr equal.symm.symm).hom.app M.obj)
    ((pullbackComp b (f j)).app M.obj)
    ((restrictFunctorIsoPullback b).app ((pullback (f j)).obj M.obj))
    ((restrictFunctorComp a (f i)).inv.app M.obj)
    ((restrictFunctorCongr equal).hom.app M.obj)
    ((restrictFunctorComp b (f j)).app M.obj)
    ((restrictFunctor b).map ((restrictFunctorIsoPullback (f j)).hom.app M.obj))
    ((restrictFunctorIsoPullback (a ≫ f i)).hom.app M.obj)
    ((restrictFunctorIsoPullback (b ≫ f j)).hom.app M.obj)
    (openRestrictionComp_app a (f i) M.obj)
    (openRestrictionComp_app b (f j) M.obj)
    congr'
  exact (congrArg (fun mid =>
    (restrictFunctor a).map ((restrictFunctorIsoPullback (f i)).hom.app M.obj) ≫
      (restrictFunctorIsoPullback a).hom.app ((pullback (f i)).obj M.obj) ≫
      mid ≫ (restrictFunctorIsoPullback b).inv.app ((pullback (f j)).obj M.obj)) compare).trans main

end

end SHIGURE.SchemeDescent
