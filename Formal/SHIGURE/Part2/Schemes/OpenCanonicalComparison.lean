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

set_option maxHeartbeats 950000 in
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
  let N := M.obj
  let P := (restrictFunctorIsoPullback (f i)).app N
  let Q := (restrictFunctorIsoPullback (f j)).app N
  let A := (restrictFunctorIsoPullback a).app ((pullback (f i)).obj N)
  let B := (restrictFunctorIsoPullback b).app ((pullback (f j)).obj N)
  let C := (restrictFunctorComp a (f i)).app N
  let D := (restrictFunctorComp b (f j)).app N
  let L := (pullbackComp a (f i)).app N
  let R := (pullbackComp b (f j)).app N
  let EA := (restrictFunctorIsoPullback (a ≫ f i)).app N
  let EB := (restrictFunctorIsoPullback (b ≫ f j)).app N
  let S := (restrictFunctorCongr equal).app N
  let pullCongr := (pullbackCongr equal).app N
  let I := (quasiCoherentModulesProperty.prop (.mk (op T))).ι
  have compare : I.map ((DescentData.ofObj (F := quasiCoherentModulesPseudofunctor) (f := f) M).hom (a ≫ f i) a b rfl equal.symm) =
      L.hom ≫ pullCongr.hom ≫ R.inv := by
    simp only [DescentData.ofObj_hom, I.map_comp]
    rw [quasiCoherentMapComp'_inv a (f i) (a ≫ f i) rfl M,
      quasiCoherentMapComp'_hom b (f j) (a ≫ f i) equal.symm M]
    change (L.hom ≫ 𝟙 _) ≫ pullCongr.hom ≫ R.inv = _
    rw [Category.comp_id]
  change (restrictFunctor a).map P.hom ≫ A.hom ≫
      I.map ((DescentData.ofObj (F := quasiCoherentModulesPseudofunctor) (f := f) M).hom (a ≫ f i) a b rfl equal.symm) ≫ B.inv =
    C.inv ≫ S.hom ≫ D.hom ≫ (restrictFunctor b).map Q.hom
  rw [compare]
  apply (cancel_mono (B.hom ≫ R.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have compA : (restrictFunctor a).map P.hom ≫ A.hom ≫ L.hom = C.inv ≫ EA.hom :=
    openRestrictionComp_app a (f i) N
  have compB : (restrictFunctor b).map Q.hom ≫ B.hom ≫ R.hom = D.inv ≫ EB.hom :=
    openRestrictionComp_app b (f j) N
  have congr := congrArg (fun e => e.hom.app N) (restrictFunctorIsoPullback_congr equal)
  have congr' : S.hom ≫ EB.hom = EA.hom ≫ pullCongr.hom := congr
  rw [compB, Iso.hom_inv_id_assoc, ← Category.assoc A.hom, ← Category.assoc, compA]
  simpa only [Category.assoc] using congrArg (C.inv ≫ ·) congr'.symm

end

end SHIGURE.SchemeDescent
