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

private theorem openDataRestrictIso_hom_eq {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ X} (d : Q.DescentData f) {i j : ι} (base : T ⟶ X)
    (a : T ⟶ U i) (b : T ⟶ U j) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ f i = base) (hb : b ≫ f j = base) :
    (openDataRestrictIso d base a b ha hb).hom =
      (restrictFunctorIsoPullback a).hom.app (d.obj i).obj ≫
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map (d.hom base a b ha hb) ≫
      (restrictFunctorIsoPullback b).inv.app (d.obj j).obj := rfl

private theorem ofModule_transition_hom (D : Scheme.GlueData.{u}) (M : D.glued.Modules) (i j : D.J) :
    ((ModuleGluingData.ofModule M).transition i j).hom =
      (restrictFunctorComp (D.f i j) (D.ι i)).inv.app M ≫
      (restrictFunctorCongr (overlapRight_comp_chart D i j).symm).hom.app M ≫
      (restrictFunctorComp (overlapRight D i j) (D.ι j)).hom.app M := by
  simp only [ModuleGluingData.ofModule, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]

private theorem assoc4_left {K : Type*} [Category K] {A B E F G : K}
    (u : A ⟶ B) (v : B ⟶ E) (w : E ⟶ F) (x : F ⟶ G) :
    (u ≫ v ≫ w) ≫ x = u ≫ v ≫ w ≫ x := by
  simp only [Category.assoc]

private theorem openCanonicalComparison_exact {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ X} [∀ i, IsOpenImmersion (f i)] (i j : ι) (p : T ⟶ U i) (q : T ⟶ U j)
    [IsOpenImmersion p] [IsOpenImmersion q]
    (hq : q ≫ f j = p ≫ f i) (P : Q.obj (.mk (op X))) :
    (restrictFunctor p).map ((restrictFunctorIsoPullback (f i)).hom.app P.obj) ≫
      (openDataRestrictIso ((Q.toDescentData f).obj P) (p ≫ f i) p q rfl hq).hom =
    ((restrictFunctorComp p (f i)).inv.app P.obj ≫
      (restrictFunctorCongr hq.symm).hom.app P.obj ≫
      (restrictFunctorComp q (f j)).hom.app P.obj) ≫
      (restrictFunctor q).map ((restrictFunctorIsoPullback (f j)).hom.app P.obj) := by
  rw [openDataRestrictIso_hom_eq, assoc4_left]
  have h0 := openCanonicalComparison (f := f) i j p q hq.symm P
  exact (congrArg (fun hb =>
    (restrictFunctor p).map ((restrictFunctorIsoPullback (f i)).hom.app P.obj) ≫
      (restrictFunctorIsoPullback p).hom.app ((pullback (f i)).obj P.obj) ≫
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
        ((DescentData.ofObj (F := quasiCoherentModulesPseudofunctor) (f := f) P).hom
          (p ≫ f i) p q rfl hb) ≫
      (restrictFunctorIsoPullback q).inv.app ((pullback (f j)).obj P.obj))
    (Subsingleton.elim hq hq.symm.symm)).trans h0

private theorem chartRecovery_core {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ X} [∀ i, IsOpenImmersion (f i)] (data : Q.DescentData f)
    (N : Q.obj (.mk (op X))) {i j : ι} (p : T ⟶ U i) (q : T ⟶ U j)
    [IsOpenImmersion p] [IsOpenImmersion q] (hq : q ≫ f j = p ≫ f i)
    (mi : N.obj.restrict (f i) ⟶ (data.obj i).obj)
    (mj : N.obj.restrict (f j) ⟶ (data.obj j).obj)
    (ci : ((Q.toDescentData f).obj N).obj i ⟶ data.obj i)
    (cj : ((Q.toDescentData f).obj N).obj j ⟶ data.obj j)
    (hci : (quasiCoherentModulesProperty.prop (.mk (op (U i)))).ι.map ci =
      ((restrictFunctorIsoPullback (f i)).app N.obj).inv ≫ mi)
    (hcj : (quasiCoherentModulesProperty.prop (.mk (op (U j)))).ι.map cj =
      ((restrictFunctorIsoPullback (f j)).app N.obj).inv ≫ mj)
    (e : (N.obj.restrict (f i)).restrict p ⟶ (N.obj.restrict (f j)).restrict q)
    (he : e = (restrictFunctorComp p (f i)).inv.app N.obj ≫
      (restrictFunctorCongr hq.symm).hom.app N.obj ≫
      (restrictFunctorComp q (f j)).hom.app N.obj)
    (glue : (restrictFunctor p).map mi ≫ (openDataRestrictIso data (p ≫ f i) p q rfl hq).hom =
      e ≫ (restrictFunctor q).map mj) :
    (Q.map p.op.toLoc).toFunctor.map ci ≫ data.hom (p ≫ f i) p q rfl hq =
    ((Q.toDescentData f).obj N).hom (p ≫ f i) p q rfl hq ≫ (Q.map q.op.toLoc).toFunctor.map cj := by
  subst e
  let A := restrictFunctor p
  let B := restrictFunctor q
  let a := (restrictFunctorIsoPullback (f i)).app N.obj
  let b := (restrictFunctorIsoPullback (f j)).app N.obj
  let h := (openDataRestrictIso ((Q.toDescentData f).obj N) (p ≫ f i) p q rfl hq).hom
  let t := (openDataRestrictIso data (p ≫ f i) p q rfl hq).hom
  let e' := (restrictFunctorComp p (f i)).inv.app N.obj ≫
      (restrictFunctorCongr hq.symm).hom.app N.obj ≫
      (restrictFunctorComp q (f j)).hom.app N.obj
  have canonical : (A.mapIso a).hom ≫ h = e' ≫ (B.mapIso b).hom :=
    openCanonicalComparison_exact i j p q hq N
  have leftMap : A.map (a.inv ≫ mi) = (A.mapIso a).inv ≫ A.map mi := A.map_comp _ _
  have rightMap : B.map (b.inv ≫ mj) = (B.mapIso b).inv ≫ B.map mj := B.map_comp _ _
  have compare := gluedChartSquare (A.mapIso a) (B.mapIso b) (A.map mi) (B.map mj) e' h t
    canonical glue
  have square : A.map (a.inv ≫ mi) ≫ t = h ≫ B.map (b.inv ≫ mj) :=
    (congrArg (· ≫ t) leftMap).trans (compare.trans (congrArg (h ≫ ·) rightMap.symm))
  apply (openDescentHom_comm_iff (D₁ := (Q.toDescentData f).obj N) (D₂ := data)
    (p ≫ f i) p q rfl hq ci cj).2
  rw [hci, hcj]
  exact square

private theorem chartRecoveryIso_comm (i j : D.J) :
    (Q.map (D.f i j).op.toLoc).toFunctor.map (chartRecoveryIso D data C i).hom ≫
      data.hom (D.f i j ≫ D.ι i) (D.f i j) (overlapRight D i j) rfl (overlap_isPullback D i j).w.symm =
    (canon D data C).hom (D.f i j ≫ D.ι i) (D.f i j) (overlapRight D i j) rfl (overlap_isPullback D i j).w.symm ≫
      (Q.map (overlapRight D i j).op.toLoc).toFunctor.map (chartRecoveryIso D data C j).hom := by
  have hq : (overlap_isPullback D i j).w.symm = overlapRight_comp_chart D i j := Subsingleton.elim _ _
  exact (congrArg (fun h =>
    (Q.map (D.f i j).op.toLoc).toFunctor.map (chartRecoveryIso D data C i).hom ≫
      data.hom (D.f i j ≫ D.ι i) (D.f i j) (overlapRight D i j) rfl h =
    (canon D data C).hom (D.f i j ≫ D.ι i) (D.f i j) (overlapRight D i j) rfl h ≫
      (Q.map (overlapRight D i j).op.toLoc).toFunctor.map (chartRecoveryIso D data C j).hom) hq).mpr
    (chartRecovery_core data (openGluedRestrictionObject D data C) (D.f i j) (overlapRight D i j)
      (overlapRight_comp_chart D i j)
      ((openGluedRestrictionData D data).chartIso C i).hom
      ((openGluedRestrictionData D data).chartIso C j).hom
      (chartRecoveryIso D data C i).hom
      (chartRecoveryIso D data C j).hom
      (chartRecoveryHom D data C i)
      (chartRecoveryHom D data C j)
      ((ModuleGluingData.ofModule (openGluedRestrictionObject D data C).obj).transition i j).hom
      (ofModule_transition_hom D (openGluedRestrictionObject D data C).obj i j)
      ((openGluedRestrictionData D data).chartIso_transition C i j))

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
