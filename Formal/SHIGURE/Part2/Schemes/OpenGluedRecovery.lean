import Formal.SHIGURE.Part2.Schemes.OpenCanonicalComparison
import Formal.SHIGURE.Part2.Schemes.OpenGluingChartTransition
import Formal.SHIGURE.Part2.Schemes.DescentComparisons
import Formal.SHIGURE.Part2.Schemes.OpenDescentMorphisms

/-! # Recovering descent data from the glued module -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor

variable (D : Scheme.GlueData.{u}) (data : Q.DescentData D.ι)

/-- Read the descent comparisons on the chosen geometric chart overlaps. -/
def openGluedRestrictionData : ModuleGluingData D where
  module i := (data.obj i).obj
  transition i j := openDataRestrictIso data (D.f i j ≫ D.ι i) (D.f i j) (overlapRight D i j)
    rfl (overlapRight_comp_chart D i j)

variable (C : (openGluedRestrictionData D data).Cocycle)

/-- The glued coherent module, formed from the compatible sections of the existing charts. -/
def openGluedRestrictionObject : Q.obj (.mk (op D.glued)) :=
  ⟨(openGluedRestrictionData D data).compatibleModule,
    (openGluedRestrictionData D data).compatibleModule_quasiCoherent C
      (fun i => (data.obj i).property)⟩

private abbrev canon := (Q.toDescentData D.ι).obj (openGluedRestrictionObject D data C)

private def chartRecoveryIso (i : D.J) : (canon D data C).obj i ≅ data.obj i :=
  ObjectProperty.isoMk (quasiCoherentModulesProperty.prop (.mk (op (D.U i))))
    (((restrictFunctorIsoPullback (D.ι i)).app (openGluedRestrictionObject D data C).obj).symm ≪≫
      (openGluedRestrictionData D data).chartIso C i)

private theorem chartRecoveryHom (i : D.J) :
    (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι.map (chartRecoveryIso D data C i).hom =
      ((restrictFunctorIsoPullback (D.ι i)).app (openGluedRestrictionObject D data C).obj).inv ≫
      ((openGluedRestrictionData D data).chartIso C i).hom := rfl

private theorem gluedChartSquare {K : Type*} [Category K] {A A' B B' M N : K}
    (a : A ≅ A') (b : B ≅ B') (m : A ⟶ M) (n : B ⟶ N)
    (e : A ⟶ B) (h : A' ⟶ B') (t : M ⟶ N)
    (canonical : a.hom ≫ h = e ≫ b.hom) (glue : m ≫ t = e ≫ n) :
    (a.inv ≫ m) ≫ t = h ≫ (b.inv ≫ n) := by
  have invert : a.inv ≫ e = h ≫ b.inv := by
    apply (cancel_epi a.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc a.hom, canonical, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, glue, ← Category.assoc, invert, Category.assoc]

set_option maxHeartbeats 350000 in
private theorem chartRecoveryIso_comm (i j : D.J) :
    let p := D.f i j
    let q := overlapRight D i j
    (Q.map p.op.toLoc).toFunctor.map (chartRecoveryIso D data C i).hom ≫
      data.hom (p ≫ D.ι i) p q rfl (overlapRight_comp_chart D i j) =
    (canon D data C).hom (p ≫ D.ι i) p q rfl (overlapRight_comp_chart D i j) ≫
      (Q.map q.op.toLoc).toFunctor.map (chartRecoveryIso D data C j).hom := by
  let G := openGluedRestrictionData D data
  let p := D.f i j
  let q := overlapRight D i j
  let N := openGluedRestrictionObject D data C
  let A := restrictFunctor p
  let B := restrictFunctor q
  let a := (restrictFunctorIsoPullback (D.ι i)).app N.obj
  let b := (restrictFunctorIsoPullback (D.ι j)).app N.obj
  let m := (G.chartIso C i).hom
  let n := (G.chartIso C j).hom
  let h := (openDataRestrictIso (canon D data C) (p ≫ D.ι i) p q rfl
    (overlapRight_comp_chart D i j)).hom
  let e := ((ModuleGluingData.ofModule N.obj).transition i j).hom
  let t := (G.transition i j).hom
  have canonical : A.map a.hom ≫ h = e ≫ B.map b.hom :=
    openCanonicalComparison (f := D.ι) i j p q (overlapRight_comp_chart D i j).symm N
  have glue : A.map m ≫ t = e ≫ B.map n := G.chartIso_transition C i j
  have leftMap : A.map (a.inv ≫ m) = (A.mapIso a).inv ≫ A.map m := A.map_comp _ _
  have rightMap : B.map (b.inv ≫ n) = (B.mapIso b).inv ≫ B.map n := B.map_comp _ _
  have compare := gluedChartSquare (A.mapIso a) (B.mapIso b) (A.map m) (B.map n) e h t
    canonical glue
  have square : A.map (a.inv ≫ m) ≫ t = h ≫ B.map (b.inv ≫ n) :=
    (congrArg (· ≫ t) leftMap).trans (compare.trans (congrArg (h ≫ ·) rightMap.symm))
  apply (openDescentHom_comm_iff (D₁ := canon D data C) (D₂ := data)
    (p ≫ D.ι i) p q rfl (overlapRight_comp_chart D i j)
    (chartRecoveryIso D data C i).hom (chartRecoveryIso D data C j).hom).2
  rw [chartRecoveryHom, chartRecoveryHom]
  exact square

set_option maxHeartbeats 450000 in
/-- The actual compatible-section gluing recovers the full descent datum
on the chosen scheme gluing. -/
def openGluedRestrictionDescentIso : canon D data C ≅ data :=
  DescentData.isoMk (chartRecoveryIso D data C) (by
    intro Y base i j p q hp hq
    exact descentHom_comm_of_pullbacks (overlap_isPullback D)
      (fun i => (chartRecoveryIso D data C i).hom) (chartRecoveryIso_comm D data C)
      base p q hp hq)

end

end SHIGURE.SchemeDescent
