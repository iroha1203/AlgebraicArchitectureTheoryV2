import Formal.SHIGURE.Part2.Schemes.OpenCanonicalComparison
import Formal.SHIGURE.Part2.Schemes.OpenGluingChartTransition
import Formal.SHIGURE.Part2.Schemes.OpenDescentMorphisms

/-! # Descent of quasi-coherent module maps over open charts -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor
variable {D : Scheme.GlueData.{u}} {M N : Q.obj (.mk (op D.glued))}
  (φ : (Q.toDescentData D.ι).obj M ⟶ (Q.toDescentData D.ι).obj N)

private def chartRestrictionMap (i : D.J) :
    M.obj.restrict (D.ι i) ⟶ N.obj.restrict (D.ι i) :=
  (restrictFunctorIsoPullback (D.ι i)).hom.app M.obj ≫
    (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι.map (φ.hom i) ≫
    (restrictFunctorIsoPullback (D.ι i)).inv.app N.obj

private theorem restrict_morphism_square {C : Type*} [Category C]
    {X X' Y Y' U U' V V' : C}
    (a : X ≅ X') (b : Y ≅ Y') (c : U ≅ U') (d : V ≅ V')
    (t₁ : X ⟶ Y) (t₂ : U ⟶ V) (s₁ : X' ⟶ Y') (s₂ : U' ⟶ V')
    (m : X' ⟶ U') (n : Y' ⟶ V')
    (h₁ : a.hom ≫ s₁ = t₁ ≫ b.hom) (h₂ : c.hom ≫ s₂ = t₂ ≫ d.hom)
    (comm : m ≫ s₂ = s₁ ≫ n) :
    (a.hom ≫ m ≫ c.inv) ≫ t₂ = t₁ ≫ b.hom ≫ n ≫ d.inv := by
  have inv : c.inv ≫ t₂ = s₂ ≫ d.inv := by
    apply (cancel_epi c.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc c.hom, h₂,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc, inv]
  rw [← Category.assoc m, comm, Category.assoc, ← Category.assoc a.hom, h₁, Category.assoc]

private theorem openDataRestrictIso_hom_eq {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ X} (d : Q.DescentData f) {i j : ι} (base : T ⟶ X)
    (a : T ⟶ U i) (b : T ⟶ U j) [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ f i = base) (hb : b ≫ f j = base) :
    (openDataRestrictIso d base a b ha hb).hom =
      (restrictFunctorIsoPullback a).hom.app (d.obj i).obj ≫
      (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map (d.hom base a b ha hb) ≫
      (restrictFunctorIsoPullback b).inv.app (d.obj j).obj := rfl

private theorem ofModule_transition_hom (D : Scheme.GlueData.{u}) (P : D.glued.Modules) (i j : D.J) :
    ((ModuleGluingData.ofModule P).transition i j).hom =
      (restrictFunctorComp (D.f i j) (D.ι i)).inv.app P ≫
      (restrictFunctorCongr (overlapRight_comp_chart D i j).symm).hom.app P ≫
      (restrictFunctorComp (overlapRight D i j) (D.ι j)).hom.app P := by
  simp only [ModuleGluingData.ofModule, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]

private theorem assoc4_left {C : Type*} [Category C] {A B E F G : C}
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

private theorem openDescentHom_comm_of_hom {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ X} {D₁ D₂ : Q.DescentData f} (φ : D₁ ⟶ D₂)
    {i j : ι} (base : T ⟶ X) (p : T ⟶ U i) (q : T ⟶ U j)
    [IsOpenImmersion p] [IsOpenImmersion q] (hp : p ≫ f i = base) (hq : q ≫ f j = base) :
    (restrictFunctor p).map ((quasiCoherentModulesProperty.prop (.mk (op (U i)))).ι.map (φ.hom i)) ≫
      (openDataRestrictIso D₂ base p q hp hq).hom =
    (openDataRestrictIso D₁ base p q hp hq).hom ≫
      (restrictFunctor q).map ((quasiCoherentModulesProperty.prop (.mk (op (U j)))).ι.map (φ.hom j)) :=
  (openDescentHom_comm_iff base p q hp hq (φ.hom i) (φ.hom j)).1 (φ.comm base p q hp hq)

private theorem map_comp3 {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  rw [F.map_comp, F.map_comp]

private theorem chartRestriction_core {ι : Type u} {X T : Scheme.{u}} {U : ι → Scheme.{u}}
    {f : ∀ i, U i ⟶ X} [∀ i, IsOpenImmersion (f i)] {M N : Q.obj (.mk (op X))}
    (φ : (Q.toDescentData f).obj M ⟶ (Q.toDescentData f).obj N)
    {i j : ι} (p : T ⟶ U i) (q : T ⟶ U j)
    [IsOpenImmersion p] [IsOpenImmersion q] (hq : q ≫ f j = p ≫ f i)
    (tM : (M.obj.restrict (f i)).restrict p ⟶ (M.obj.restrict (f j)).restrict q)
    (tN : (N.obj.restrict (f i)).restrict p ⟶ (N.obj.restrict (f j)).restrict q)
    (htM : tM = (restrictFunctorComp p (f i)).inv.app M.obj ≫
      (restrictFunctorCongr hq.symm).hom.app M.obj ≫
      (restrictFunctorComp q (f j)).hom.app M.obj)
    (htN : tN = (restrictFunctorComp p (f i)).inv.app N.obj ≫
      (restrictFunctorCongr hq.symm).hom.app N.obj ≫
      (restrictFunctorComp q (f j)).hom.app N.obj)
    (ci : M.obj.restrict (f i) ⟶ N.obj.restrict (f i))
    (cj : M.obj.restrict (f j) ⟶ N.obj.restrict (f j))
    (hci : ci = (restrictFunctorIsoPullback (f i)).hom.app M.obj ≫
      (quasiCoherentModulesProperty.prop (.mk (op (U i)))).ι.map (φ.hom i) ≫
      (restrictFunctorIsoPullback (f i)).inv.app N.obj)
    (hcj : cj = (restrictFunctorIsoPullback (f j)).hom.app M.obj ≫
      (quasiCoherentModulesProperty.prop (.mk (op (U j)))).ι.map (φ.hom j) ≫
      (restrictFunctorIsoPullback (f j)).inv.app N.obj) :
    (restrictFunctor p).map ci ≫ tN = tM ≫ (restrictFunctor q).map cj := by
  subst tM; subst tN; subst ci; subst cj
  let A := restrictFunctor p
  let B := restrictFunctor q
  let compM := (openDataRestrictIso ((Q.toDescentData f).obj M) (p ≫ f i) p q rfl hq).hom
  let compN := (openDataRestrictIso ((Q.toDescentData f).obj N) (p ≫ f i) p q rfl hq).hom
  let aM := (restrictFunctorIsoPullback (f i)).app M.obj
  let aN := (restrictFunctorIsoPullback (f i)).app N.obj
  let bM := (restrictFunctorIsoPullback (f j)).app M.obj
  let bN := (restrictFunctorIsoPullback (f j)).app N.obj
  let m := (quasiCoherentModulesProperty.prop (.mk (op (U i)))).ι.map (φ.hom i)
  let n := (quasiCoherentModulesProperty.prop (.mk (op (U j)))).ι.map (φ.hom j)
  let eM := (restrictFunctorComp p (f i)).inv.app M.obj ≫
      (restrictFunctorCongr hq.symm).hom.app M.obj ≫
      (restrictFunctorComp q (f j)).hom.app M.obj
  let eN := (restrictFunctorComp p (f i)).inv.app N.obj ≫
      (restrictFunctorCongr hq.symm).hom.app N.obj ≫
      (restrictFunctorComp q (f j)).hom.app N.obj
  have left : (A.mapIso aM).hom ≫ compM = eM ≫ (B.mapIso bM).hom :=
    openCanonicalComparison_exact i j p q hq M
  have right : (A.mapIso aN).hom ≫ compN = eN ≫ (B.mapIso bN).hom :=
    openCanonicalComparison_exact i j p q hq N
  have compare : A.map m ≫ compN = compM ≫ B.map n :=
    openDescentHom_comm_of_hom φ (p ≫ f i) p q rfl hq
  have l : A.map (aM.hom ≫ m ≫ aN.inv) = (A.mapIso aM).hom ≫ A.map m ≫ (A.mapIso aN).inv :=
    map_comp3 A aM.hom m aN.inv
  have r : B.map (bM.hom ≫ n ≫ bN.inv) = (B.mapIso bM).hom ≫ B.map n ≫ (B.mapIso bN).inv :=
    map_comp3 B bM.hom n bN.inv
  have sq := restrict_morphism_square (A.mapIso aM) (B.mapIso bM) (A.mapIso aN) (B.mapIso bN)
    eM eN compM compN (A.map m) (B.map n) left right compare
  exact (congrArg (· ≫ eN) l).trans (sq.trans (congrArg (eM ≫ ·) r.symm))

private theorem chartRestrictionMap_comm (i j : D.J) :
    (restrictFunctor (D.f i j)).map (chartRestrictionMap φ i) ≫
      ((ModuleGluingData.ofModule N.obj).transition i j).hom =
    ((ModuleGluingData.ofModule M.obj).transition i j).hom ≫
      (restrictFunctor (overlapRight D i j)).map (chartRestrictionMap φ j) :=
  chartRestriction_core φ (D.f i j) (overlapRight D i j) (overlapRight_comp_chart D i j)
    _ _ (ofModule_transition_hom D M.obj i j) (ofModule_transition_hom D N.obj i j)
    (chartRestrictionMap φ i) (chartRestrictionMap φ j) rfl rfl

private def openGluedHom : M ⟶ N :=
  ObjectProperty.homMk
    (ModuleGluingData.glueGlobalMap
      { map := chartRestrictionMap φ
        naturality := chartRestrictionMap_comm φ })

private theorem openGluedHom_map :
    (Q.toDescentData D.ι).map (openGluedHom φ) = φ := by
  apply DescentData.hom_ext
  intro i
  let I := (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι
  let J := (quasiCoherentModulesProperty.prop (.mk (op D.glued))).ι
  let R := restrictFunctor (D.ι i)
  let P := pullback (D.ι i)
  let e := restrictFunctorIsoPullback (D.ι i)
  let m := J.map (openGluedHom φ)
  let chart := I.map (φ.hom i)
  apply I.map_injective
  change P.map m = chart
  have lifted : R.map m = chartRestrictionMap φ i :=
    ModuleGluingData.glueGlobalMap_chart
      { map := chartRestrictionMap φ
        naturality := chartRestrictionMap_comm φ } i
  have natural : R.map m ≫ e.hom.app N.obj = e.hom.app M.obj ≫ P.map m :=
    e.hom.naturality m
  rw [lifted] at natural
  have same : (e.app M.obj).hom ≫ chart ≫ (e.app N.obj).inv ≫ (e.app N.obj).hom =
      (e.app M.obj).hom ≫ P.map m := by
    change (chartRestrictionMap φ i) ≫ (e.hom.app N.obj) = _
    exact natural
  exact ((cancel_epi (e.app M.obj).hom).1 (by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using same)).symm

private theorem openGluedHom_faithful (M N : Q.obj (.mk (op D.glued)))
    {m n : M ⟶ N} (same : (Q.toDescentData D.ι).map m = (Q.toDescentData D.ι).map n) : m = n := by
  let J := (quasiCoherentModulesProperty.prop (.mk (op D.glued))).ι
  apply J.map_injective
  apply ModuleGluingData.hom_ext_of_restrictCharts
  intro i
  let I := (quasiCoherentModulesProperty.prop (.mk (op (D.U i)))).ι
  let e := restrictFunctorIsoPullback (D.ι i)
  have chart := congrArg (fun h : (Q.toDescentData D.ι).obj M ⟶ (Q.toDescentData D.ι).obj N =>
    I.map (h.hom i)) same
  have equal : (pullback (D.ι i)).map (J.map m) = (pullback (D.ι i)).map (J.map n) := chart
  apply (cancel_mono (e.hom.app N.obj)).1
  let R := restrictFunctor (D.ι i)
  let P := pullback (D.ι i)
  have mNatural : R.map (J.map m) ≫ e.hom.app N.obj = e.hom.app M.obj ≫ P.map (J.map m) :=
    e.hom.naturality (J.map m)
  have nNatural : R.map (J.map n) ≫ e.hom.app N.obj = e.hom.app M.obj ≫ P.map (J.map n) :=
    e.hom.naturality (J.map n)
  exact mNatural.trans ((congrArg (e.hom.app M.obj ≫ ·) equal).trans nNatural.symm)

/-- The ordinary chart gluing recovers all maps of quasi-coherent modules. -/
def openGlueComparison_fullyFaithful (D : Scheme.GlueData.{u}) :
    (Q.toDescentData D.ι).FullyFaithful where
  preimage := openGluedHom
  map_preimage := openGluedHom_map
  preimage_map := fun m => openGluedHom_faithful _ _ (openGluedHom_map ((Q.toDescentData D.ι).map m))

end

end SHIGURE.SchemeDescent
