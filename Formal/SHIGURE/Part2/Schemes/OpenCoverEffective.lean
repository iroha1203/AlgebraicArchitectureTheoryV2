import Formal.SHIGURE.Part2.Schemes.OpenCoverDescentTest
import Formal.SHIGURE.Part2.Schemes.OpenGluedRecovery
import Formal.SHIGURE.Part2.Schemes.DescentRebase
import Formal.SHIGURE.Part2.Schemes.OpenDescentMaps

/-! # Effective gluing on the original open cover -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules

noncomputable section

universe u

variable {X : Scheme.{u}} (cover : Scheme.OpenCover.{u} X)
  (data : quasiCoherentModulesPseudofunctor.DescentData cover.f)

private abbrev QCoh := quasiCoherentModulesPseudofunctor

private abbrev dataOnGlue : QCoh.DescentData cover.gluedCover.ι :=
  rebaseDatum cover.fromGlued (fun i => (cover.ι_fromGlued i).symm) data

set_option maxHeartbeats 425000 in
private theorem rebase_open_transition (i j : cover.I₀) :
    (openDataRestrictIso (dataOnGlue cover data) (cover.gluedCover.f i j ≫ cover.gluedCover.ι i)
      (cover.gluedCover.f i j) (overlapRight cover.gluedCover i j) rfl
      (overlapRight_comp_chart cover.gluedCover i j)).hom =
      ((openDescentGlueData cover data).transition i j).hom := by
  let D := cover.gluedCover
  let p := D.f i j
  let q := overlapRight D i j
  let I := (quasiCoherentModulesProperty.prop (.mk (op (D.V (i, j))))).ι
  let a := (restrictFunctorIsoPullback p).app (data.obj i).obj
  let b := (restrictFunctorIsoPullback q).app (data.obj j).obj
  let x := (p ≫ D.ι i) ≫ cover.fromGlued
  let y := p ≫ cover.f i
  have xy : x = y := (Category.assoc p (D.ι i) cover.fromGlued).trans
    (congrArg (p ≫ ·) (cover.ι_fromGlued i))
  have px : p ≫ cover.f i = x := xy.symm
  have qy : q ≫ cover.f j = y := calc
    _ = q ≫ D.ι j ≫ cover.fromGlued := congrArg (q ≫ ·) (cover.ι_fromGlued j).symm
    _ = (q ≫ D.ι j) ≫ cover.fromGlued := (Category.assoc _ _ _).symm
    _ = x := congrArg (· ≫ cover.fromGlued) (overlapRight_comp_chart D i j)
    _ = y := xy
  have qx : q ≫ cover.f j = x := qy.trans xy.symm
  have sameBase {x' y' : D.V (i, j) ⟶ X} (eq : x' = y')
      (pa : p ≫ cover.f i = x') (qa : q ≫ cover.f j = x')
      (pb : p ≫ cover.f i = y') (qb : q ≫ cover.f j = y') :
      data.hom x' p q pa qa = data.hom y' p q pb qb := by
    subst y'
    rfl
  have h : data.hom x p q px qx = data.hom y p q rfl qy := sameBase xy px qx rfl qy
  have hi : I.map (data.hom x p q px qx) = I.map (data.hom y p q rfl qy) := congrArg I.map h
  change a.hom ≫ I.map (data.hom x p q px qx) ≫ b.inv =
    a.hom ≫ I.map (data.hom y p q rfl qy) ≫ b.inv
  exact congrArg (fun m : (pullback p).obj (data.obj i).obj ⟶ (pullback q).obj (data.obj j).obj =>
    a.hom ≫ m ≫ b.inv) hi

set_option maxHeartbeats 500000 in
private theorem openGluedRestriction_agrees :
    openGluedRestrictionData cover.gluedCover (dataOnGlue cover data) = openDescentGlueData cover data := by
  let D := cover.gluedCover
  let charts (i : D.J) := (data.obj i).obj
  let a := openGluedRestrictionData D (dataOnGlue cover data)
  let b := openDescentGlueData cover data
  have matchTransitions : (fun i j => a.transition i j) = (fun i j => b.transition i j) := by
    funext i j
    exact Iso.ext (rebase_open_transition cover data i j)
  exact congrArg (ModuleGluingData.mk (D := D) charts) matchTransitions

private theorem dataOnGlue_cocycle :
    (openGluedRestrictionData cover.gluedCover (dataOnGlue cover data)).Cocycle := by
  rw [openGluedRestriction_agrees]
  exact openDescentGlueData_cocycle cover data

/-- Glue the chart modules via compatible sections, then identify the glued
scheme with the original base of the cover. -/
def openCoverGluedObject : QCoh.obj (.mk (op X)) :=
  (QCoh.map (asIso cover.fromGlued).inv.op.toLoc).toFunctor.obj
    (openGluedRestrictionObject cover.gluedCover (dataOnGlue cover data) (dataOnGlue_cocycle cover data))

set_option maxHeartbeats 800000 in
/-- The glued object recovers the original datum on its original charts. -/
def openCoverGluedIso : (QCoh.toDescentData cover.f).obj (openCoverGluedObject cover data) ≅ data := by
  let D := cover.gluedCover
  let e := asIso cover.fromGlued
  let desc := dataOnGlue cover data
  let coherent := dataOnGlue_cocycle cover data
  let origin := openGluedRestrictionObject D desc coherent
  let onX := openCoverGluedObject cover data
  have orientation : ∀ i : cover.I₀, cover.f i = D.ι i ≫ e.hom :=
    fun i => (cover.ι_fromGlued i).symm
  have w (i : cover.I₀) : 𝟙 (cover.X i) ≫ cover.f i = D.ι i ≫ e.hom :=
    (Category.id_comp (cover.f i)).trans (orientation i)
  have w' (i : cover.I₀) : 𝟙 (cover.X i) ≫ D.ι i = cover.f i ≫ e.inv := by
    rw [Category.id_comp, orientation i, Category.assoc, e.hom_inv_id, Category.comp_id]
  let comp := DescentData.pullFunctorEquivalence (p' := fun i => 𝟙 (cover.X i))
    (q' := fun i => 𝟙 (cover.X i)) (α := id) (β := id) QCoh e w w'
  have inverseLaw : e.inv.op.toLoc ≫ e.hom.op.toLoc = 𝟙 (LocallyDiscrete.mk (op D.glued)) :=
    congrArg (fun k => k.op.toLoc) e.hom_inv_id
  let identified : (QCoh.map e.hom.op.toLoc).toFunctor.obj onX ≅ origin :=
    ((Cat.Hom.toNatIso (QCoh.mapComp' e.inv.op.toLoc e.hom.op.toLoc _ inverseLaw)).app origin).symm ≪≫
      (Cat.Hom.toNatIso (QCoh.mapId _)).app origin
  let ra := (DescentData.toDescentDataCompPullFunctorIso QCoh (p := e.hom) (f' := D.ι)
    (p' := fun i => 𝟙 (cover.X i)) (α := id) w).app onX
  let rb := (QCoh.toDescentData D.ι).mapIso identified
  let rc := openGluedRestrictionDescentIso D desc coherent
  let rd := (pullFunctorRebaseIso e.hom orientation data).symm
  exact comp.fullyFaithfulFunctor.preimageIso (ra ≪≫ rb ≪≫ rc ≪≫ rd)

/-- Every quasi-coherent module descent datum on an open cover is the
restriction of a quasi-coherent module on the original scheme. -/
theorem openCoverComparison_essSurj (X : Scheme.{u}) (cover : Scheme.OpenCover.{u} X) :
    (QCoh.toDescentData cover.f).EssSurj :=
  ⟨fun data => ⟨openCoverGluedObject cover data, ⟨openCoverGluedIso cover data⟩⟩⟩

set_option maxHeartbeats 850000 in
/-- Pullback along an arbitrary original open cover gives an equivalence of
quasi-coherent modules with their compatible geometric descent data. -/
theorem openCoverComparison_isEquivalence {X : Scheme.{u}} (cover : Scheme.OpenCover.{u} X) :
    (QCoh.toDescentData cover.f).IsEquivalence := by
  let D := cover.gluedCover
  let e := asIso cover.fromGlued
  let onGlue := QCoh.toDescentData D.ι
  let pb := (QCoh.map e.hom.op.toLoc).toFunctor
  let comparison := QCoh.toDescentData cover.f
  have orientation : ∀ i : cover.I₀, cover.f i = D.ι i ≫ e.hom :=
    fun i => (cover.ι_fromGlued i).symm
  have w (i : cover.I₀) : 𝟙 (cover.X i) ≫ cover.f i = D.ι i ≫ e.hom :=
    (Category.id_comp (cover.f i)).trans (orientation i)
  have w' (i : cover.I₀) : 𝟙 (cover.X i) ≫ D.ι i = cover.f i ≫ e.inv := by
    rw [Category.id_comp, orientation i, Category.assoc, e.hom_inv_id, Category.comp_id]
  let transfer := DescentData.pullFunctorEquivalence (p' := fun i => 𝟙 (cover.X i))
    (q' := fun i => 𝟙 (cover.X i)) (α := id) (β := id) QCoh e w w'
  let equal : comparison ⋙ transfer.functor ≅ pb ⋙ onGlue :=
    DescentData.toDescentDataCompPullFunctorIso QCoh w
  letI : pb.IsEquivalence := descentPullbackIso_isEquivalence QCoh e
  letI : onGlue.EssSurj := openCoverComparison_essSurj D.glued D.openCover
  letI : onGlue.Full := (openGlueComparison_fullyFaithful D).full
  letI : onGlue.Faithful := (openGlueComparison_fullyFaithful D).faithful
  letI : onGlue.IsEquivalence := {}
  letI : (comparison ⋙ transfer.functor).IsEquivalence := Functor.isEquivalence_of_iso equal.symm
  exact Functor.isEquivalence_of_comp_right comparison transfer.functor

end

end SHIGURE.SchemeDescent
