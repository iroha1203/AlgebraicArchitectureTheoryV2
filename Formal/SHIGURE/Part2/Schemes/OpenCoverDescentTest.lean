import Formal.SHIGURE.Part2.Schemes.OpenCoverDescentTransitions

/-! # Comparing the open-cover descent datum on one test open -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Scheme.Modules

noncomputable section

universe u

variable {X : Scheme.{u}} (cover : Scheme.OpenCover.{u} X)
  (data : quasiCoherentModulesPseudofunctor.DescentData cover.f)
  (W : cover.gluedCover.glued.Opens)

private theorem openChartLift_toBase (i : cover.I₀) (hi : W ≤ (cover.gluedCover.ι i).opensRange) :
    openChartLift i W hi ≫ cover.f i = W.ι ≫ cover.fromGlued := by
  rw [← cover.ι_fromGlued i, ← Category.assoc, openChartLift_fac]

/-- On an open shared by two charts, the datum identifies their actual restrictions. -/
def openDescentTestIso (i j : cover.I₀)
    (hi : W ≤ (cover.gluedCover.ι i).opensRange) (hj : W ≤ (cover.gluedCover.ι j).opensRange) :
    ((openDescentGlueData cover data).module i).restrict (openChartLift i W hi) ≅
      ((openDescentGlueData cover data).module j).restrict (openChartLift j W hj) := by
  let a := openChartLift i W hi
  let b := openChartLift j W hj
  let base := W.ι ≫ cover.fromGlued
  exact openDataRestrictIso data base a b
    (openChartLift_toBase cover W i hi) (openChartLift_toBase cover W j hj)

/-- On an open contained in three charts, the restriction comparisons satisfy the Čech cocycle. -/
theorem openDescentTestIso_comp (i j k : cover.I₀)
    (hi : W ≤ (cover.gluedCover.ι i).opensRange) (hj : W ≤ (cover.gluedCover.ι j).opensRange)
    (hk : W ≤ (cover.gluedCover.ι k).opensRange) :
    (openDescentTestIso cover data W i j hi hj).hom ≫ (openDescentTestIso cover data W j k hj hk).hom =
      (openDescentTestIso cover data W i k hi hk).hom := by
  let F := (quasiCoherentModulesProperty.prop (.mk (op (W : Scheme)))).ι
  let a := openChartLift i W hi
  let b := openChartLift j W hj
  let c := openChartLift k W hk
  let base := W.ι ≫ cover.fromGlued
  let ha := openChartLift_toBase cover W i hi
  let hb := openChartLift_toBase cover W j hj
  let hc := openChartLift_toBase cover W k hk
  let ea := (restrictFunctorIsoPullback a).app (data.obj i).obj
  let eb := (restrictFunctorIsoPullback b).app (data.obj j).obj
  let ec := (restrictFunctorIsoPullback c).app (data.obj k).obj
  let h₁ := data.hom base a b ha hb
  let h₂ := data.hom base b c hb hc
  let h₃ := data.hom base a c ha hc
  change (ea.hom ≫ F.map h₁ ≫ eb.inv) ≫ (eb.hom ≫ F.map h₂ ≫ ec.inv) =
    ea.hom ≫ F.map h₃ ≫ ec.inv
  have cocycle : h₁ ≫ h₂ = h₃ := data.hom_comp base a b c ha hb hc
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, cocycle]

/-- The comparison on a test open within one chart is the identity. -/
theorem openDescentTestIso_id (i : cover.I₀) (hi : W ≤ (cover.gluedCover.ι i).opensRange) :
    (openDescentTestIso cover data W i i hi hi).hom = 𝟙 _ := by
  let F := (quasiCoherentModulesProperty.prop (.mk (op (W : Scheme)))).ι
  let a := openChartLift i W hi
  let base := W.ι ≫ cover.fromGlued
  let ha := openChartLift_toBase cover W i hi
  let ea := (restrictFunctorIsoPullback a).app (data.obj i).obj
  change ea.hom ≫ F.map (data.hom base a a ha ha) ≫ ea.inv = 𝟙 _
  rw [data.hom_self base a ha, F.map_id]
  change ea.hom ≫ 𝟙 ((Scheme.Modules.pullback a).obj (data.obj i).obj) ≫ ea.inv = 𝟙 _
  rw [Category.id_comp, Iso.hom_inv_id]

private theorem chartRead_topSections {T V U X : Scheme.{u}}
    (k : T ⟶ V) (p : V ⟶ U) (a : T ⟶ U) (i : U ⟶ X) (c : V ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion p] [IsOpenImmersion a]
    (ha : k ≫ p = a) (hc : p ≫ i = c) (W : X.Opens)
    (hV : k ''ᵁ ⊤ = c ⁻¹ᵁ W) (hU : a ''ᵁ ⊤ = i ⁻¹ᵁ W)
    (M : U.Modules) :
    (((pushforward i).map ((restrictAdjunction p).unit.app M) ≫
      (pushforwardComp p i).hom.app (M.restrict p) ≫
      (pushforwardCongr hc).hom.app (M.restrict p)).app W) ≫
      (openTopSectionsIso (M.restrict p) k _ hV).hom =
    (openTopSectionsIso M a _ hU).hom ≫
      ((restrictFunctorCongr ha).inv.app M ≫
        (restrictFunctorComp k p).hom.app M).app ⊤ := by
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    restrictAdjunction_unit_app_app, pushforwardCongr_hom_app_app, restrictFunctorCongr_inv_app_app,
    restrictFunctorComp_hom_app_app, openTopSectionsIso, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    restrict_map, ← Category.assoc, ← Functor.map_comp]
  erw [Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

private theorem pushforwardCongr_refl_hom {V X : Scheme.{u}} (c : V ⟶ X) (M : V.Modules) :
    (pushforwardCongr (rfl : c = c)).hom.app M = 𝟙 _ := by
  ext W x
  rw [pushforwardCongr_hom_app_app]
  have same : eqToHom (show c ⁻¹ᵁ W = c ⁻¹ᵁ W by rfl) = 𝟙 _ := Subsingleton.elim _ _
  rw [same, op_id, M.presheaf.map_id]
  rfl

private theorem openTopSections_naturality {T V : Scheme.{u}} {A B : V.Modules} (m : A ⟶ B)
    (k : T ⟶ V) [IsOpenImmersion k] (U : V.Opens) (image : k ''ᵁ ⊤ = U) :
    m.app U ≫ (openTopSectionsIso B k U image).hom =
      (openTopSectionsIso A k U image).hom ≫ ((restrictFunctor k).map m).app ⊤ :=
  (m.mapPresheaf.naturality ((eqToHom image).op)).symm

private abbrev moduleTopSections (T : Scheme.{u}) :=
  toPresheaf T ⋙ (CategoryTheory.evaluation T.Opensᵒᵖ Ab.{u}).obj (op ⊤)

set_option maxHeartbeats 650000 in
private def openDescentSectionIso (i j : cover.I₀)
    (hi : W ≤ (cover.gluedCover.ι i).opensRange) (hj : W ≤ (cover.gluedCover.ι j).opensRange) :
    Γ((openDescentGlueData cover data).chartPushforward i, W) ≅
      Γ((openDescentGlueData cover data).chartPushforward j, W) :=
  by
    let G := openDescentGlueData cover data
    let left := openChartTopSectionsIso i W hi (G.module i)
    let right := openChartTopSectionsIso j W hj (G.module j)
    let middle := (moduleTopSections (W : Scheme)).mapIso (openDescentTestIso cover data W i j hi hj)
    exact left ≪≫ middle ≪≫ right.symm


section Gluing

variable {D : Scheme.GlueData.{u}} (G : ModuleGluingData D)
  (W : D.glued.Opens) (i j : D.J)
  (hi : W ≤ (D.ι i).opensRange) (hj : W ≤ (D.ι j).opensRange)

private theorem openOverlapLift_condition :
    openChartLift i W hi ≫ D.ι i = openChartLift j W hj ≫ D.ι j :=
  (openChartLift_fac i W hi).trans (openChartLift_fac j W hj).symm

private def openOverlapLift : (W : Scheme) ⟶ D.V (i, j) :=
  (overlap_isPullback D i j).lift _ _ (openOverlapLift_condition W i j hi hj)

private theorem openOverlapLift_left : openOverlapLift W i j hi hj ≫ D.f i j = openChartLift i W hi :=
  (overlap_isPullback D i j).lift_fst _ _ _

private theorem openOverlapLift_right :
    openOverlapLift W i j hi hj ≫ overlapRight D i j = openChartLift j W hj :=
  (overlap_isPullback D i j).lift_snd _ _ _

private instance : IsOpenImmersion (openOverlapLift W i j hi hj) := by
  haveI : IsOpenImmersion (openOverlapLift W i j hi hj ≫ D.f i j) := by
    rw [openOverlapLift_left]
    infer_instance
  exact IsOpenImmersion.of_comp _ (D.f i j)

private theorem openOverlapLift_image :
    openOverlapLift W i j hi hj ''ᵁ ⊤ = (D.f i j ≫ D.ι i) ⁻¹ᵁ W := by
  let c := D.f i j ≫ D.ι i
  let k := openOverlapLift W i j hi hj
  have fac : k ≫ c = W.ι := by
    rw [show c = D.f i j ≫ D.ι i from rfl, ← Category.assoc]
    rw [show k ≫ D.f i j = openChartLift i W hi from openOverlapLift_left W i j hi hj,
      openChartLift_fac]
  apply openLift_image_top c W k fac
  intro x hx
  obtain ⟨y, hy⟩ := (show x ∈ Set.range W.ι from W.range_ι.symm ▸ hx)
  exact ⟨k y, (congrArg (fun l : (W : Scheme) ⟶ D.glued => l y) fac).trans hy⟩

private def leftTestRestrictIso (M : (D.U i).Modules) :
    M.restrict (openChartLift i W hi) ≅
      (M.restrict (D.f i j)).restrict (openOverlapLift W i j hi hj) :=
  ((restrictFunctorCongr (openOverlapLift_left W i j hi hj)).symm ≪≫
    restrictFunctorComp (openOverlapLift W i j hi hj) (D.f i j)).app M

private def rightTestRestrictIso (M : (D.U j).Modules) :
    M.restrict (openChartLift j W hj) ≅
      (M.restrict (overlapRight D i j)).restrict (openOverlapLift W i j hi hj) :=
  ((restrictFunctorCongr (openOverlapLift_right W i j hi hj)).symm ≪≫
    restrictFunctorComp (openOverlapLift W i j hi hj) (overlapRight D i j)).app M

private def openGluingTestIso :
    (G.module i).restrict (openChartLift i W hi) ≅ (G.module j).restrict (openChartLift j W hj) :=
  leftTestRestrictIso W i j hi hj (G.module i) ≪≫
    (restrictFunctor (openOverlapLift W i j hi hj)).mapIso (G.transition i j) ≪≫
    (rightTestRestrictIso W i j hi hj (G.module j)).symm

set_option maxHeartbeats 850000 in
private theorem openGluingSectionTransport :
    (openChartTopSectionsIso i W hi (G.module i)).hom ≫
      (moduleTopSections (W : Scheme)).map (openGluingTestIso G W i j hi hj).hom ≫
      (openChartTopSectionsIso j W hj (G.module j)).inv = G.transport i j W hi := by
  let a := openChartLift i W hi
  let b := openChartLift j W hj
  let p := D.f i j
  let q := overlapRight D i j
  let c := p ≫ D.ι i
  let ea := openChartTopSectionsIso i W hi (G.module i)
  let eb := openChartTopSectionsIso j W hj (G.module j)
  let E := moduleTopSections (W : Scheme)
  let t := G.transition i j
  let k := openOverlapLift W i j hi hj
  have ha : k ≫ p = a := openOverlapLift_left W i j hi hj
  have hb : k ≫ q = b := openOverlapLift_right W i j hi hj
  let il := leftTestRestrictIso W i j hi hj (G.module i)
  let ir := rightTestRestrictIso W i j hi hj (G.module j)
  let image := openOverlapLift_image W i j hi hj
  let e := openTopSectionsIso ((G.module i).restrict p) k _ image
  let e' := openTopSectionsIso ((G.module j).restrict q) k _ image
  have hleft : (G.restrictLeft i j).app W ≫ e.hom = ea.hom ≫ E.map il.hom := by
    have comparison := chartRead_topSections k p a (D.ι i) c ha rfl W image
      (openChartLift_image_top i W hi) (G.module i)
    rw [pushforwardCongr_refl_hom, Category.comp_id] at comparison
    exact comparison
  have hright : (G.restrictRight i j).app W ≫ e.hom =
      eb.hom ≫ E.map ir.hom ≫ E.map ((restrictFunctor k).map t.inv) := by
    let r := (pushforward (D.ι j)).map ((restrictAdjunction q).unit.app (G.module j)) ≫
      (pushforwardComp q (D.ι j)).hom.app ((G.module j).restrict q) ≫
      (pushforwardCongr (overlapRight_comp_chart D i j)).hom.app ((G.module j).restrict q)
    change (r ≫ (pushforward c).map t.inv).app W ≫ e.hom = _
    rw [Hom.comp_app, Category.assoc, pushforward_map_app]
    rw [openTopSections_naturality t.inv k _ image]
    rw [← Category.assoc]
    have compare : r.app W ≫ e'.hom = eb.hom ≫ E.map ir.hom :=
      chartRead_topSections k q b (D.ι j) c hb (overlapRight_comp_chart D i j) W image
        (openChartLift_image_top j W hj) (G.module j)
    rw [compare, Category.assoc]
    rfl
  letI := G.restrictRight_app_isIso i j W hi
  apply (cancel_mono ((G.restrictRight i j).app W ≫ e.hom)).1
  change (ea.hom ≫ E.map (il.hom ≫ (restrictFunctor k).map t.hom ≫ ir.inv) ≫ eb.inv) ≫
      ((G.restrictRight i j).app W ≫ e.hom) = G.transport i j W hi ≫ (G.restrictRight i j).app W ≫ e.hom
  rw [G.transport_restrictRight_assoc, hleft, hright]
  simp only [E.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  have cancelChart : E.map ir.inv ≫ E.map ir.hom ≫ E.map ((restrictFunctor k).map t.inv) =
      E.map ((restrictFunctor k).map t.inv) :=
    (E.mapIso ir).inv_hom_id_assoc (E.map ((restrictFunctor k).map t.inv))
  have cancelTransition : E.map ((restrictFunctor k).map t.hom) ≫
      E.map ((restrictFunctor k).map t.inv) = 𝟙 _ :=
    (E.mapIso ((restrictFunctor k).mapIso t)).hom_inv_id
  have cancel : E.map ((restrictFunctor k).map t.hom) ≫ E.map ir.inv ≫
      E.map ir.hom ≫ E.map ((restrictFunctor k).map t.inv) = 𝟙 _ := by
    rw [cancelChart, cancelTransition]
  exact congrArg (fun m => ea.hom ≫ E.map il.hom ≫ m) cancel |>.trans (by rw [Category.comp_id])

end Gluing

set_option maxHeartbeats 700000 in
private theorem openDescentTestIso_eq_gluing (i j : cover.I₀)
    (hi : W ≤ (cover.gluedCover.ι i).opensRange) (hj : W ≤ (cover.gluedCover.ι j).opensRange) :
    openDescentTestIso cover data W i j hi hj =
      openGluingTestIso (openDescentGlueData cover data) W i j hi hj := by
  let D := cover.gluedCover
  let a := openChartLift i W hi
  let b := openChartLift j W hj
  let p := D.f i j
  let q := overlapRight D i j
  let k := openOverlapLift W i j hi hj
  have ha : k ≫ p = a := openOverlapLift_left W i j hi hj
  have hb : k ≫ q = b := openOverlapLift_right W i j hi hj
  have hq : q ≫ cover.f j = p ≫ cover.f i := by
    rw [← cover.ι_fromGlued j, ← cover.ι_fromGlued i, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun l => l ≫ cover.fromGlued) (overlapRight_comp_chart D i j)
  have hkbase : k ≫ p ≫ cover.f i = W.ι ≫ cover.fromGlued :=
    (Category.assoc k p (cover.f i)).symm.trans
      ((congrArg (· ≫ cover.f i) ha).trans (openChartLift_toBase cover W i hi))
  exact openDataRestrictIso_naturality data k (p ≫ cover.f i) (W.ι ≫ cover.fromGlued)
    hkbase p q rfl hq a b ha hb (openChartLift_toBase cover W i hi) (openChartLift_toBase cover W j hj)

set_option maxHeartbeats 750000 in
private theorem openDescentSectionIso_hom (i j : cover.I₀)
    (hi : W ≤ (cover.gluedCover.ι i).opensRange) (hj : W ≤ (cover.gluedCover.ι j).opensRange) :
    (openDescentSectionIso cover data W i j hi hj).hom =
      (openDescentGlueData cover data).transport i j W hi := by
  let G := openDescentGlueData cover data
  let E := moduleTopSections (W : Scheme)
  let A := (G.module i).restrict (openChartLift i W hi)
  let B := (G.module j).restrict (openChartLift j W hj)
  let ei := openChartTopSectionsIso i W hi (G.module i)
  let ej := openChartTopSectionsIso j W hj (G.module j)
  let useOnSections (t : A ≅ B) := ei ≪≫ E.mapIso t ≪≫ ej.symm
  let test := openDescentTestIso cover data W i j hi hj
  let glued := openGluingTestIso G W i j hi hj
  have compare : test = glued := openDescentTestIso_eq_gluing cover data W i j hi hj
  have sections : (useOnSections test).hom = (useOnSections glued).hom :=
    congrArg (fun t : A ≅ B => (useOnSections t).hom) compare
  exact sections.trans (openGluingSectionTransport G W i j hi hj)

set_option maxHeartbeats 900000 in
/-- The actual overlaps of an open-cover datum satisfy the compatible-section
cocycle used to construct its glued quasi-coherent module. -/
theorem openDescentGlueData_cocycle : (openDescentGlueData cover data).Cocycle := by
  apply ModuleGluingData.Cocycle.ofTripleOpen
  · intro i W hi
    rw [← openDescentSectionIso_hom cover data W i i hi hi]
    let G := openDescentGlueData cover data
    let e := openChartTopSectionsIso i W hi (G.module i)
    let E := moduleTopSections (W : Scheme)
    change e.hom ≫ E.map (openDescentTestIso cover data W i i hi hi).hom ≫ e.inv = 𝟙 _
    rw [openDescentTestIso_id, E.map_id]
    exact (congrArg (e.hom ≫ ·) (Category.id_comp e.inv)).trans e.hom_inv_id
  · intro i j k W hi hj hk
    rw [← openDescentSectionIso_hom cover data W i j hi hj,
      ← openDescentSectionIso_hom cover data W j k hj hk,
      ← openDescentSectionIso_hom cover data W i k hi hk]
    let G := openDescentGlueData cover data
    let ei := openChartTopSectionsIso i W hi (G.module i)
    let ej := openChartTopSectionsIso j W hj (G.module j)
    let ek := openChartTopSectionsIso k W hk (G.module k)
    let E := moduleTopSections (W : Scheme)
    let a := (openDescentTestIso cover data W i j hi hj).hom
    let b := (openDescentTestIso cover data W j k hj hk).hom
    let c := (openDescentTestIso cover data W i k hi hk).hom
    change (ei.hom ≫ E.map a ≫ ej.inv) ≫ (ej.hom ≫ E.map b ≫ ek.inv) =
      ei.hom ≫ E.map c ≫ ek.inv
    have eq : a ≫ b = c := openDescentTestIso_comp cover data W i j k hi hj hk
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← E.map_comp_assoc, eq]


/-- The compatible-section module of an open-cover datum is quasi-coherent. -/
theorem openDescentGluedModule_quasiCoherent :
    IsQuasiCoherentModule (openDescentGlueData cover data).compatibleModule :=
  (openDescentGlueData cover data).compatibleModule_quasiCoherent
    (openDescentGlueData_cocycle cover data) (fun i => (data.obj i).property)

end
end SHIGURE.SchemeDescent
