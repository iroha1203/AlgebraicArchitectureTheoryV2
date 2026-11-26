import Formal.SHIGURE.Part2.Schemes.OpenPullbackCoherence

/-! # Transitions of the compatible-section gluing

The adjoint characterizations of chart projections recover the prescribed
transition as an actual map on every double overlap.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules

noncomputable section

universe u

private theorem homEquiv_comp_conjugate {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {P : C} {Q : D} (f : L₁.obj P ⟶ Q) :
    b.homEquiv P Q (α.app P ≫ f) =
      a.homEquiv P Q f ≫ (conjugateEquiv a b α).app Q := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← unit_conjugateEquiv a b α P, Category.assoc,
    (conjugateEquiv a b α).naturality]

private theorem restrictComp_homEquiv {Y U X : Scheme.{u}} (p : Y ⟶ U) (i : U ⟶ X)
    [IsOpenImmersion p] [IsOpenImmersion i] {N : X.Modules} {M : U.Modules}
    (m : N.restrict i ⟶ M) :
    (restrictAdjunction (p ≫ i)).homEquiv _ _
      ((restrictFunctorComp p i).hom.app N ≫ (restrictFunctor p).map m) =
    (restrictAdjunction i).homEquiv _ _ m ≫
      (pushforward i).map ((restrictAdjunction p).unit.app M) ≫
      (pushforwardComp p i).hom.app (M.restrict p) := by
  rw [homEquiv_comp_conjugate, restrictFunctorComp_conjugate, Adjunction.comp_homEquiv]
  change (restrictAdjunction i).homEquiv N _
    ((restrictAdjunction p).homEquiv (N.restrict i) (M.restrict p) ((restrictFunctor p).map m)) ≫
    (pushforwardComp p i).hom.app (M.restrict p) = _
  rw [Adjunction.homEquiv_unit (restrictAdjunction p), Adjunction.unit_naturality,
    Adjunction.homEquiv_naturality_right, Category.assoc]

private theorem restrictCongr_homEquiv {Y X : Scheme.{u}} {c d : Y ⟶ X}
    [IsOpenImmersion c] [IsOpenImmersion d] (same : d = c)
    {N : X.Modules} {M : Y.Modules} (m : N.restrict d ⟶ M) :
    (restrictAdjunction c).homEquiv _ _ ((restrictFunctorCongr same.symm).hom.app N ≫ m) =
      (restrictAdjunction d).homEquiv _ _ m ≫ (pushforwardCongr same).hom.app M := by
  subst d
  have left : (restrictFunctorCongr (rfl : c = c)).hom.app N = 𝟙 _ := by
    ext W x
    rw [restrictFunctorCongr_hom_app_app]
    have equal : eqToHom (show c ''ᵁ W = c ''ᵁ W by rfl) = 𝟙 _ := Subsingleton.elim _ _
    rw [equal, op_id, N.presheaf.map_id]
    rfl
  have right : (pushforwardCongr (rfl : c = c)).hom.app M = 𝟙 _ := by
    ext W x
    rw [pushforwardCongr_hom_app_app]
    have equal : eqToHom (show c ⁻¹ᵁ W = c ⁻¹ᵁ W by rfl) = 𝟙 _ := Subsingleton.elim _ _
    rw [equal, op_id, M.presheaf.map_id]
    rfl
  rw [left, right, Category.id_comp, Category.comp_id]

set_option maxRecDepth 1600 in
set_option maxHeartbeats 900000 in
/-- The recovered charts of the compatible-section module intertwine the
actual restriction maps on each geometric overlap. -/
theorem ModuleGluingData.chartIso_transition {D : Scheme.GlueData.{u}} (G : ModuleGluingData D)
    (C : G.Cocycle) (i j : D.J) :
    (restrictFunctor (D.f i j)).map (G.chartIso C i).hom ≫ (G.transition i j).hom =
      ((ModuleGluingData.ofModule G.compatibleModule).transition i j).hom ≫
        (restrictFunctor (overlapRight D i j)).map (G.chartIso C j).hom := by
  let N := G.compatibleModule
  let p := D.f i j
  let q := overlapRight D i j
  let c := p ≫ D.ι i
  let d := q ≫ D.ι j
  let equal : d = c := overlapRight_comp_chart D i j
  let t := G.transition i j
  let e := (restrictFunctorComp p (D.ι i)).app N
  let f := (restrictFunctorComp q (D.ι j)).app N
  let g := (restrictFunctorCongr equal.symm).app N
  let mi := (G.chartIso C i).hom
  let mj := (G.chartIso C j).hom
  let ai := (restrictAdjunction (D.ι i)).homEquiv _ _ mi
  let aj := (restrictAdjunction (D.ι j)).homEquiv _ _ mj
  change (restrictFunctor p).map mi ≫ t.hom = (e.inv ≫ g.hom ≫ f.hom) ≫ (restrictFunctor q).map mj
  apply (cancel_epi e.hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply ((restrictAdjunction c).homEquiv N _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  show (restrictAdjunction (p ≫ D.ι i)).homEquiv N _
      ((restrictFunctorComp p (D.ι i)).hom.app N ≫ (restrictFunctor p).map mi) ≫
      (pushforward c).map t.hom = _
  rw [restrictComp_homEquiv]
  change (ai ≫ G.restrictLeft i j) ≫ (pushforward c).map t.hom =
    (restrictAdjunction c).homEquiv N _ (g.hom ≫ f.hom ≫ (restrictFunctor q).map mj)
  have mate := restrictCongr_homEquiv equal (f.hom ≫ (restrictFunctor q).map mj)
  have mate' : (restrictAdjunction c).homEquiv N _ (g.hom ≫ f.hom ≫ (restrictFunctor q).map mj) =
      (restrictAdjunction d).homEquiv N _ (f.hom ≫ (restrictFunctor q).map mj) ≫
        (pushforwardCongr equal).hom.app _ := mate
  rw [G.chartIso_overlap C i j, mate']
  show (aj ≫ G.restrictRight i j) ≫ (pushforward c).map t.hom =
    (restrictAdjunction (q ≫ D.ι j)).homEquiv N _
      ((restrictFunctorComp q (D.ι j)).hom.app N ≫ (restrictFunctor q).map mj) ≫
      (pushforwardCongr equal).hom.app _
  rw [restrictComp_homEquiv]
  simp only [ModuleGluingData.restrictRight, Category.assoc]
  change aj ≫ (pushforward (D.ι j)).map ((restrictAdjunction q).unit.app (G.module j)) ≫
    (pushforwardComp q (D.ι j)).hom.app ((G.module j).restrict q) ≫
    (pushforwardCongr equal).hom.app ((G.module j).restrict q) ≫
    (pushforward c).map t.inv ≫ (pushforward c).map t.hom = _
  rw [← (pushforward c).map_comp, t.inv_hom_id, (pushforward c).map_id, Category.comp_id]


section GlobalMaps

variable {D : Scheme.GlueData.{u}} {M N : D.glued.Modules}

/-- Restrict a map of global modules to the canonical chart data. -/
def ModuleGluingData.restrictGlobalMap (m : M ⟶ N) :
    (ModuleGluingData.ofModule M).CompatibleMorphisms (ModuleGluingData.ofModule N) where
  map i := (restrictFunctor (D.ι i)).map m
  naturality i j := by
    let p := D.f i j
    let q := overlapRight D i j
    let comparison := (restrictFunctorComp p (D.ι i)).symm ≪≫
      restrictFunctorCongr (overlapRight_comp_chart D i j).symm ≪≫ restrictFunctorComp q (D.ι j)
    exact comparison.hom.naturality m

private theorem map_reglueIso_inv (P : D.glued.Modules) (i : D.J) :
    (restrictFunctor (D.ι i)).map (ModuleGluingData.reglueIso P).inv =
      (ModuleGluingData.ofModule P).chartMap i := by
  let R := restrictFunctor (D.ι i)
  let e := ModuleGluingData.reglueIso P
  apply (cancel_epi (R.map e.hom)).1
  exact (R.mapIso e).hom_inv_id.trans (ModuleGluingData.reglueIso_chart P i).symm

/-- Recover a global module morphism from its compatible chart maps. -/
def ModuleGluingData.glueGlobalMap
    (m : (ModuleGluingData.ofModule M).CompatibleMorphisms (ModuleGluingData.ofModule N)) : M ⟶ N :=
  (ModuleGluingData.reglueIso M).hom ≫ ModuleGluingData.glueMorphism m ≫
    (ModuleGluingData.reglueIso N).inv

/-- The recovered global morphism has the prescribed local maps. -/
theorem ModuleGluingData.glueGlobalMap_chart
    (m : (ModuleGluingData.ofModule M).CompatibleMorphisms (ModuleGluingData.ofModule N))
    (i : D.J) :
    (restrictFunctor (D.ι i)).map (ModuleGluingData.glueGlobalMap m) = m.map i := by
  let R := restrictFunctor (D.ι i)
  let e := ModuleGluingData.reglueIso M
  let f := ModuleGluingData.reglueIso N
  change R.map (e.hom ≫ ModuleGluingData.glueMorphism m ≫ f.inv) = m.map i
  rw [R.map_comp, R.map_comp, map_reglueIso_inv, ModuleGluingData.glueMorphism_chart,
    ← Category.assoc, ModuleGluingData.reglueIso_chart, Category.id_comp]

/-- Recovering the compatible restrictions of a global morphism returns the
original morphism. -/
theorem ModuleGluingData.glueGlobalMap_restrictGlobalMap (m : M ⟶ N) :
    ModuleGluingData.glueGlobalMap (ModuleGluingData.restrictGlobalMap m) = m := by
  let G := ModuleGluingData.ofModule M
  let H := ModuleGluingData.ofModule N
  let e := ModuleGluingData.reglueIso M
  let f := ModuleGluingData.reglueIso N
  let charts := ModuleGluingData.restrictGlobalMap m
  let analogue := e.inv ≫ m ≫ f.hom
  have onCharts (i : D.J) :
      (restrictFunctor (D.ι i)).map analogue ≫ H.chartMap i = G.chartMap i ≫ charts.map i := by
    let R := restrictFunctor (D.ι i)
    change R.map (e.inv ≫ m ≫ f.hom) ≫ H.chartMap i = G.chartMap i ≫ R.map m
    rw [R.map_comp, R.map_comp, Category.assoc, Category.assoc,
      ModuleGluingData.reglueIso_chart, Category.comp_id, map_reglueIso_inv]
  obtain ⟨u, _, unique⟩ := ModuleGluingData.existsUnique_glueMorphism charts
  have equal : ModuleGluingData.glueMorphism charts = analogue :=
    (unique _ (ModuleGluingData.glueMorphism_chart charts)).trans (unique _ onCharts).symm
  change e.hom ≫ ModuleGluingData.glueMorphism charts ≫ f.inv = m
  rw [equal]
  change e.hom ≫ (e.inv ≫ m ≫ f.hom) ≫ f.inv = m
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem compatibleMorphisms_ext {G H : ModuleGluingData D}
    {m n : G.CompatibleMorphisms H} (h : m.map = n.map) : m = n := by
  cases m with
  | mk left hl =>
    cases n with
    | mk right hr =>
      change left = right at h
      subst right
      rfl

/-- Two global morphisms that agree on every chart are equal. -/
theorem ModuleGluingData.hom_ext_of_restrictCharts {m n : M ⟶ N}
    (h : ∀ i : D.J, (restrictFunctor (D.ι i)).map m = (restrictFunctor (D.ι i)).map n) : m = n := by
  have same : ModuleGluingData.restrictGlobalMap m = ModuleGluingData.restrictGlobalMap n := by
    exact compatibleMorphisms_ext (funext h)
  rw [← ModuleGluingData.glueGlobalMap_restrictGlobalMap m, same,
    ModuleGluingData.glueGlobalMap_restrictGlobalMap]

end GlobalMaps

end

end SHIGURE.SchemeDescent
