import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Gluing module sheaves on scheme charts

For the scheme glued by Lemma B.6, a module is formed as the equalizer of
the two maps from the product of chart sheaves to the product of overlap
sheaves. Each chart and overlap is pushed forward along its actual open
immersion, so the equalizer consists of compatible local sections.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules

noncomputable section

universe u

variable (D : Scheme.GlueData.{u})

/-- The right chart map from the overlap written in the left chart. -/
def overlapRight (i j : D.J) : D.V (i, j) ⟶ D.U j :=
  D.t i j ≫ D.f j i

/-- The right chart map is an open immersion. -/
instance overlapRight_isOpenImmersion (i j : D.J) : IsOpenImmersion (overlapRight D i j) :=
  inferInstanceAs (IsOpenImmersion (D.t i j ≫ D.f j i))

/-- Both descriptions of the overlap define the same open in the glued scheme. -/
theorem overlapRight_comp_chart (i j : D.J) :
    overlapRight D i j ≫ D.ι j = D.f i j ≫ D.ι i := by
  simpa only [overlapRight, Category.assoc] using D.glue_condition i j

/-- The overlap maps are a pullback of the original chart inclusions. -/
theorem overlap_isPullback (i j : D.J) :
    IsPullback (D.f i j) (overlapRight D i j) (D.ι i) (D.ι j) :=
  IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)

/-- The image of an overlap open in the right chart is the preimage of
the corresponding open in the left chart. -/
theorem overlapRight_image_preimage (i j : D.J) (W : D.glued.Opens) :
    (overlapRight D i j) ''ᵁ ((D.f i j ≫ D.ι i) ⁻¹ᵁ W) =
      (D.ι j) ⁻¹ᵁ ((D.ι i).opensRange ⊓ W) := by
  rw [Scheme.Hom.comp_preimage,
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (overlap_isPullback D i j),
    Scheme.Hom.image_preimage_eq_opensRange_inf]

/-- The left chart sees the same open intersection as the right chart. -/
theorem overlapLeft_image_preimage (i j : D.J) (W : D.glued.Opens) :
    D.f i j ''ᵁ ((D.f i j ≫ D.ι i) ⁻¹ᵁ W) =
      (D.ι i) ⁻¹ᵁ ((D.ι j).opensRange ⊓ W) := by
  rw [← overlapRight_comp_chart, Scheme.Hom.comp_preimage,
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (overlap_isPullback D i j).flip,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

/-- A module map is invertible when its restrictions along all chart inclusions are invertible. -/
theorem isIso_of_restrictCharts {M N : D.glued.Modules} (f : M ⟶ N)
    (localIso : ∀ i, IsIso ((restrictFunctor (D.ι i)).map f)) : IsIso f := by
  let F : TopCat.Sheaf Ab D.glued := ⟨M.presheaf, M.isSheaf⟩
  let K : TopCat.Sheaf Ab D.glued := ⟨N.presheaf, N.isSheaf⟩
  let m : F ⟶ K := ⟨f.mapPresheaf⟩
  haveI : IsIso m := (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso m).2 fun x => by
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
    letI := localIso i
    exact (NatIso.isIso_map_iff (restrictStalkNatIso (D.ι i) y) f).1
      (Functor.map_isIso (toPresheaf (D.U i) ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y) ((restrictFunctor (D.ι i)).map f))
  haveI : IsIso ((toPresheaf D.glued).map f) :=
    (TopCat.Sheaf.forget Ab _).map_isIso m
  exact isIso_of_reflects_iso f (toPresheaf D.glued)

/-- Local modules and their comparison maps on the actual scheme overlaps. -/
structure ModuleGluingData where
  /-- Each module lives on its original scheme chart. -/
  module (i : D.J) : (D.U i).Modules
  /-- The comparison is an isomorphism of modules on the same overlap. -/
  transition (i j : D.J) : (module i).restrict (D.f i j) ≅ (module j).restrict (overlapRight D i j)

namespace ModuleGluingData

variable {D} (G : ModuleGluingData D)

/-- The chart sheaf viewed on the glued scheme. -/
abbrev chartPushforward (i : D.J) : D.glued.Modules :=
  (pushforward (D.ι i)).obj (G.module i)

/-- Restrict a global module and transport it along the two actual overlap maps. -/
def ofModule (N : D.glued.Modules) : ModuleGluingData D where
  module i := N.restrict (D.ι i)
  transition i j :=
    ((restrictFunctorComp (D.f i j) (D.ι i)).app N).symm ≪≫
      (restrictFunctorCongr (overlapRight_comp_chart D i j).symm).app N ≪≫
      (restrictFunctorComp (overlapRight D i j) (D.ι j)).app N

private abbrev chartUnit (N : D.glued.Modules) (i : D.J) :
    N ⟶ (ofModule N : ModuleGluingData D).chartPushforward i :=
  (restrictAdjunction (D.ι i)).unit.app N

/-- The overlap sheaf viewed on the glued scheme. -/
abbrev overlapPushforward (i j : D.J) : D.glued.Modules :=
  (pushforward (D.f i j ≫ D.ι i)).obj ((G.module i).restrict (D.f i j))

/-- Restrict the left chart's sections to the overlap. -/
def restrictLeft (i j : D.J) : G.chartPushforward i ⟶ G.overlapPushforward i j :=
  (pushforward (D.ι i)).map ((restrictAdjunction (D.f i j)).unit.app (G.module i)) ≫
    (pushforwardComp (D.f i j) (D.ι i)).hom.app _

/-- Restrict the right chart and read its sections in the left chart's coordinates. -/
def restrictRight (i j : D.J) : G.chartPushforward j ⟶ G.overlapPushforward i j :=
  (pushforward (D.ι j)).map ((restrictAdjunction (overlapRight D i j)).unit.app (G.module j)) ≫
    (pushforwardComp (overlapRight D i j) (D.ι j)).hom.app _ ≫
    (pushforwardCongr (overlapRight_comp_chart D i j)).hom.app _ ≫
    (pushforward (D.f i j ≫ D.ι i)).map (G.transition i j).inv

private theorem chartUnit_agree (N : D.glued.Modules) (i j : D.J) :
    chartUnit N i ≫ (ofModule N : ModuleGluingData D).restrictLeft i j =
      chartUnit N j ≫ (ofModule N : ModuleGluingData D).restrictRight i j := by
  apply Scheme.Modules.hom_ext
  intro W
  simp only [restrictLeft, restrictRight, Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, restrict_map, ofModule, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app, restrictFunctorCongr_inv_app_app]
  repeat erw [Category.comp_id]
  simp only [← Category.assoc, ← Functor.map_comp]
  erw [Category.comp_id]
  rw [← Functor.map_comp]
  exact congrArg N.presheaf.map (Subsingleton.elim _ _)

private theorem isIso_pushforward_restrict_unit_app {Z Y X : Scheme.{u}} (f : Z ⟶ Y)
    (g : Y ⟶ X) [IsOpenImmersion f] (M : Y.Modules) (W : X.Opens)
    (equal : f ''ᵁ (f ⁻¹ᵁ (g ⁻¹ᵁ W)) = g ⁻¹ᵁ W) :
    IsIso (((pushforward g).map ((restrictAdjunction f).unit.app M)).app W) := by
  rw [pushforward_map_app, restrictAdjunction_unit_app_app]
  have same : homOfLE (f.image_preimage_le (g ⁻¹ᵁ W)) = eqToHom equal := Subsingleton.elim _ _
  rw [same]
  infer_instance

/-- Over an open of the left chart, every right-chart section is already
a section on that overlap. -/
theorem restrictRight_app_isIso (i j : D.J) (W : D.glued.Opens) (h : W ≤ (D.ι i).opensRange) :
    IsIso ((G.restrictRight i j).app W) := by
  have equal : (overlapRight D i j) ''ᵁ ((overlapRight D i j) ⁻¹ᵁ ((D.ι j) ⁻¹ᵁ W)) = (D.ι j) ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, overlapRight_comp_chart, overlapRight_image_preimage, inf_eq_right.mpr h]
  letI := isIso_pushforward_restrict_unit_app (overlapRight D i j) (D.ι j) (G.module j) W equal
  simp only [restrictRight, Hom.comp_app]
  infer_instance

/-- Over an open of the right chart, every left-chart section is already
a section on that overlap. -/
theorem restrictLeft_app_isIso (i j : D.J) (W : D.glued.Opens) (h : W ≤ (D.ι j).opensRange) :
    IsIso ((G.restrictLeft i j).app W) := by
  have equal : D.f i j ''ᵁ (D.f i j ⁻¹ᵁ ((D.ι i) ⁻¹ᵁ W)) = (D.ι i) ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, overlapLeft_image_preimage, inf_eq_right.mpr h]
  letI := isIso_pushforward_restrict_unit_app (D.f i j) (D.ι i) (G.module i) W equal
  simp only [restrictLeft, Hom.comp_app]
  infer_instance

/-- Over an open contained in chart `i`, a section of chart `i` yields a
section of chart `j` on its intersection with that open. -/
def transport (i j : D.J) (W : D.glued.Opens) (hi : W ≤ (D.ι i).opensRange) :
    Γ(G.chartPushforward i, W) ⟶ Γ(G.chartPushforward j, W) :=
  letI := G.restrictRight_app_isIso i j W hi
  (G.restrictLeft i j).app W ≫ inv ((G.restrictRight i j).app W)

@[reassoc (attr := simp)]
theorem transport_restrictRight (i j : D.J) (W : D.glued.Opens) (hi : W ≤ (D.ι i).opensRange) :
    G.transport i j W hi ≫ (G.restrictRight i j).app W = (G.restrictLeft i j).app W := by
  letI := G.restrictRight_app_isIso i j W hi
  simp [transport]

private theorem section_naturality {M N : D.glued.Modules} (f : M ⟶ N)
    {W V : D.glued.Opens} (a : V ⟶ W) :
    M.presheaf.map a.op ≫ f.app V = f.app W ≫ N.presheaf.map a.op :=
  f.mapPresheaf.naturality a.op

/-- The transition on a shared open commutes with restricting that open. -/
@[reassoc]
theorem transport_naturality (i j : D.J) {W V : D.glued.Opens} (a : V ⟶ W)
    (hW : W ≤ (D.ι i).opensRange) :
    (G.chartPushforward i).presheaf.map a.op ≫ G.transport i j V (a.le.trans hW) =
      G.transport i j W hW ≫ (G.chartPushforward j).presheaf.map a.op := by
  letI := G.restrictRight_app_isIso i j V (a.le.trans hW)
  apply (cancel_mono ((G.restrictRight i j).app V)).1
  rw [Category.assoc, G.transport_restrictRight,
    Category.assoc, section_naturality (G.restrictRight i j) a]
  rw [G.transport_restrictRight_assoc]
  exact section_naturality (G.restrictLeft i j) a

/-- Identity and triple-overlap coherence of the given local isomorphisms.
In the composition law the target sections are on the intersection with
the third chart, so the equation is evaluated on the actual triple overlap. -/
structure Cocycle : Prop where
  /-- The transition on one chart identifies it with itself. -/
  identity (i : D.J) (W : D.glued.Opens) (h : W ≤ (D.ι i).opensRange) :
    G.transport i i W h = 𝟙 _
  /-- On a triple overlap, the direct and composed transitions agree. -/
  composition (i j k : D.J) (W : D.glued.Opens)
    (hi : W ≤ (D.ι i).opensRange) (hj : W ≤ (D.ι j).opensRange) :
    G.transport i j W hi ≫ G.transport j k W hj = G.transport i k W hi

/-- The reverse transition is inverse on every shared open. -/
theorem Cocycle.inverse (C : G.Cocycle) (i j : D.J) (W : D.glued.Opens)
    (hi : W ≤ (D.ι i).opensRange) (hj : W ≤ (D.ι j).opensRange) :
    G.transport i j W hi ≫ G.transport j i W hj = 𝟙 _ :=
  (C.composition i j i W hi hj).trans (C.identity i W hi)

private theorem chartUnit_transport (N : D.glued.Modules) (i j : D.J) (W : D.glued.Opens)
    (hi : W ≤ (D.ι i).opensRange) :
    (chartUnit N i).app W ≫ (ofModule N : ModuleGluingData D).transport i j W hi = (chartUnit N j).app W := by
  let G : ModuleGluingData D := ofModule N
  letI := G.restrictRight_app_isIso i j W hi
  apply (cancel_mono ((G.restrictRight i j).app W)).1
  rw [Category.assoc, G.transport_restrictRight]
  exact congrArg (fun m => m.app W) (chartUnit_agree N i j)

private theorem chartUnit_isIso (N : D.glued.Modules) (i : D.J) (W : D.glued.Opens)
    (hi : W ≤ (D.ι i).opensRange) : IsIso ((chartUnit N i).app W) := by
  rw [restrictAdjunction_unit_app_app]
  have eq := ((D.ι i).image_preimage_eq_opensRange_inf W).trans (inf_eq_right.mpr hi)
  have same : homOfLE ((D.ι i).image_preimage_le W) = eqToHom eq := Subsingleton.elim _ _
  rw [same]
  infer_instance

/-- Restrictions of a global sheaf satisfy the identity and triple-overlap laws. -/
theorem ofModule_cocycle (N : D.glued.Modules) : (ofModule N : ModuleGluingData D).Cocycle where
  identity i W hi := by
    letI := chartUnit_isIso N i W hi
    apply (cancel_epi ((chartUnit N i).app W)).1
    rw [chartUnit_transport, Category.comp_id]
  composition i j k W hi hj := by
    letI := chartUnit_isIso N i W hi
    apply (cancel_epi ((chartUnit N i).app W)).1
    rw [← Category.assoc, chartUnit_transport, chartUnit_transport, chartUnit_transport]

private theorem overlapRestrict_isIso (i j : D.J) (W : D.glued.Opens) :
    IsIso ((G.overlapPushforward i j).presheaf.map
      (homOfLE (inf_le_right : (D.ι i).opensRange ⊓ W ≤ W)).op) := by
  rw [pushforward_obj_presheaf_map]
  have same : (D.f i j ≫ D.ι i) ⁻¹ᵁ ((D.ι i).opensRange ⊓ W) =
      (D.f i j ≫ D.ι i) ⁻¹ᵁ W := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.comp_preimage, (D.ι i).preimage_opensRange,
      Scheme.Hom.preimage_top, top_inf_eq]
  have equal : (TopologicalSpace.Opens.map (D.f i j ≫ D.ι i).base).map
      (homOfLE (inf_le_right : (D.ι i).opensRange ⊓ W ≤ W)) = eqToHom same :=
    Subsingleton.elim _ _
  rw [equal]
  infer_instance

private theorem transport_agree (C : G.Cocycle) (i j k : D.J) (W : D.glued.Opens)
    (hi : W ≤ (D.ι i).opensRange) :
    G.transport i j W hi ≫ (G.restrictLeft j k).app W =
      G.transport i k W hi ≫ (G.restrictRight j k).app W := by
  let V := (D.ι j).opensRange ⊓ W
  let a : V ⟶ W := homOfLE inf_le_right
  have hj : V ≤ (D.ι j).opensRange := inf_le_left
  letI : IsIso ((G.overlapPushforward j k).presheaf.map a.op) := G.overlapRestrict_isIso j k W
  apply (cancel_mono ((G.overlapPushforward j k).presheaf.map a.op)).1
  simp only [Category.assoc]
  rw [← section_naturality (G.restrictLeft j k) a, ← section_naturality (G.restrictRight j k) a,
    ← G.transport_naturality_assoc i j a hi, ← G.transport_naturality_assoc i k a hi,
    ← G.transport_restrictRight j k V hj]
  simp only [← Category.assoc]
  rw [Category.assoc ((G.chartPushforward i).presheaf.map a.op), C.composition i j k V]

/-- Compatible maps to the chart sheaves agree after restricting to either side of every overlap. -/
def CompatibleMaps (N : D.glued.Modules) :=
  {m : ∀ i, N ⟶ G.chartPushforward i //
    ∀ i j, m i ≫ G.restrictLeft i j = m j ≫ G.restrictRight i j}

private abbrev chartProduct := ∏ᶜ G.chartPushforward

private abbrev overlapFamily (ij : D.J × D.J) := G.overlapPushforward ij.1 ij.2

private def leftMap : G.chartProduct ⟶ ∏ᶜ G.overlapFamily :=
  Pi.lift fun ij => Pi.π _ ij.1 ≫ G.restrictLeft ij.1 ij.2

private def rightMap : G.chartProduct ⟶ ∏ᶜ G.overlapFamily :=
  Pi.lift fun ij => Pi.π _ ij.2 ≫ G.restrictRight ij.1 ij.2

/-- The sheaf of compatible sections is a genuine limit in the category of module sheaves. -/
def compatibleModule : D.glued.Modules := equalizer G.leftMap G.rightMap

/-- Send a compatible section to its component on the given chart. -/
def projectChart (i : D.J) : G.compatibleModule ⟶ G.chartPushforward i :=
  equalizer.ι G.leftMap G.rightMap ≫ Pi.π _ i

/-- The two restrictions of compatible sections to each overlap agree. -/
@[reassoc]
theorem projectChart_agree (i j : D.J) :
    G.projectChart i ≫ G.restrictLeft i j = G.projectChart j ≫ G.restrictRight i j := by
  have equal := congrArg (· ≫ Pi.π G.overlapFamily (i,j)) (equalizer.condition G.leftMap G.rightMap)
  simpa only [Category.assoc, leftMap, rightMap, Pi.lift_π, projectChart] using equal

/-- The glued sheaf represents all compatible maps into the actual chart sheaves. -/
def compatibleMapsEquiv (N : D.glued.Modules) :
    (N ⟶ G.compatibleModule) ≃ G.CompatibleMaps N where
  toFun f := ⟨fun i => f ≫ G.projectChart i, fun i j => by
    simp only [Category.assoc, G.projectChart_agree]⟩
  invFun m := equalizer.lift (Pi.lift m.val) (by
    apply Pi.hom_ext
    intro ij
    rcases ij with ⟨i, j⟩
    simpa only [Category.assoc, leftMap, rightMap, Pi.lift_π, Pi.lift_π_assoc] using m.property i j)
  left_inv f := by
    apply (cancel_mono (equalizer.ι G.leftMap G.rightMap)).1
    apply Pi.hom_ext
    intro i
    simp only [equalizer.lift_ι, Pi.lift_π, Category.assoc, projectChart]
  right_inv m := by
    apply Subtype.ext
    funext i
    simp only [projectChart, equalizer.lift_ι_assoc, Pi.lift_π]

private abbrev sections (W : D.glued.Opens) : D.glued.Modules ⥤ Type u :=
  toPresheaf D.glued ⋙ (CategoryTheory.evaluation _ Ab).obj (.op W) ⋙ CategoryTheory.forget Ab

private instance sections_preservesLimits (W : D.glued.Opens) :
    PreservesLimitsOfSize.{u, u} (sections W) := by
  let E := (CategoryTheory.evaluation D.glued.Opensᵒᵖ Ab.{u}).obj (.op W)
  letI : PreservesLimitsOfSize.{u, u} E :=
    ⟨evaluation_preservesLimitsOfShape (Opposite.op W)⟩
  letI : PreservesLimitsOfSize.{u, u} (E ⋙ CategoryTheory.forget Ab.{u}) :=
    comp_preservesLimits E (CategoryTheory.forget Ab.{u})
  exact comp_preservesLimits (toPresheaf D.glued) (E ⋙ CategoryTheory.forget Ab.{u})

private def sectionProductIso (W : D.glued.Opens) {J : Type u} (F : J → D.glued.Modules) :
    (sections W).obj (∏ᶜ F) ≅ (∀ j, (sections W).obj (F j)) :=
  (isLimitOfHasProductOfPreservesLimit (sections W) F).conePointUniqueUpToIso
    (Types.productLimitCone (fun j => (sections W).obj (F j))).isLimit

private theorem sectionProductIso_apply (W : D.glued.Opens) {J : Type u}
    (F : J → D.glued.Modules) (x : (sections W).obj (∏ᶜ F)) (j : J) :
    (sectionProductIso W F).hom x j = (Pi.π F j).app W x :=
  congr_fun
    (IsLimit.conePointUniqueUpToIso_hom_comp (isLimitOfHasProductOfPreservesLimit (sections W) F)
      (Types.productLimitCone (fun j => (sections W).obj (F j))).isLimit ⟨j⟩) x

/-- A chart section on each preimage of an open, agreeing on the actual double overlaps. -/
def CompatibleSections (W : D.glued.Opens) :=
  {s : ∀ i, Γ(G.chartPushforward i, W) //
    ∀ i j, (G.restrictLeft i j).app W (s i) = (G.restrictRight i j).app W (s j)}

/-- Sections of the equalizer on any open are precisely the compatible chart sections. -/
def compatibleSectionsEquiv (W : D.glued.Opens) :
    Γ(G.compatibleModule, W) ≃ G.CompatibleSections W := by
  let f (x : Γ(G.compatibleModule, W)) : G.CompatibleSections W :=
    ⟨fun i => (G.projectChart i).app W x, fun i j => by
      simpa only [Hom.comp_app] using congrArg (fun h => h.app W x) (G.projectChart_agree i j)⟩
  have eqLimit := isLimitOfHasEqualizerOfPreservesLimit (sections W) G.leftMap G.rightMap
  let e := (sectionProductIso W G.chartPushforward).toEquiv
  have project (x : (sections W).obj G.chartProduct) (i : D.J) :
      e x i = (Pi.π G.chartPushforward i).app W x :=
    sectionProductIso_apply W _ _ _
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b eq
    have proj : (sections W).map (equalizer.ι G.leftMap G.rightMap) a =
        (sections W).map (equalizer.ι G.leftMap G.rightMap) b := by
      apply e.injective
      funext i
      rw [project, project]
      exact congrArg (fun x : G.CompatibleSections W => x.val i) eq
    have same : (sections W).map G.leftMap ((sections W).map (equalizer.ι G.leftMap G.rightMap) a) =
        (sections W).map G.rightMap ((sections W).map (equalizer.ι G.leftMap G.rightMap) a) :=
      congr_fun (show (sections W).map (equalizer.ι G.leftMap G.rightMap) ≫
          (sections W).map G.leftMap = (sections W).map (equalizer.ι G.leftMap G.rightMap) ≫
          (sections W).map G.rightMap by
        rw [← Functor.map_comp, ← Functor.map_comp, equalizer.condition]) a
    obtain ⟨_, _, unique⟩ := Types.unique_of_type_equalizer _ _ eqLimit _ same
    exact (unique a rfl).trans (unique b proj.symm).symm
  · intro s
    let x := e.symm s.val
    have value (i : D.J) : (Pi.π G.chartPushforward i).app W x = s.val i :=
      (project x i).symm.trans (congrFun (e.apply_symm_apply s.val) i)
    have same : (sections W).map G.leftMap x = (sections W).map G.rightMap x := by
      apply (sectionProductIso W G.overlapFamily).toEquiv.injective
      funext ij
      rcases ij with ⟨i, j⟩
      change (sectionProductIso W G.overlapFamily).hom ((sections W).map G.leftMap x) (i, j) =
        (sectionProductIso W G.overlapFamily).hom ((sections W).map G.rightMap x) (i, j)
      rw [sectionProductIso_apply, sectionProductIso_apply]
      change (Pi.π G.overlapFamily (i, j)).app W (G.leftMap.app W x) =
        (Pi.π G.overlapFamily (i, j)).app W (G.rightMap.app W x)
      rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, ← Hom.comp_app, ← Hom.comp_app]
      simp only [leftMap, rightMap, Pi.lift_π, Hom.comp_app, AddCommGrpCat.comp_apply, value]
      exact s.property i j
    obtain ⟨y, hy, _⟩ := Types.unique_of_type_equalizer _ _ eqLimit _ same
    refine ⟨y, Subtype.ext (funext fun i => ?_)⟩
    change (Pi.π G.chartPushforward i).app W
      ((sections W).map (equalizer.ι G.leftMap G.rightMap) y) = s.val i
    rw [hy, value]

@[simp]
theorem compatibleSectionsEquiv_apply (W : D.glued.Opens) (s : Γ(G.compatibleModule, W)) (i : D.J) :
    (G.compatibleSectionsEquiv W s).val i = (G.projectChart i).app W s := rfl

/-- On an open of a given chart, a compatible family is freely and uniquely
determined by its section on that chart. -/
def compatibleSectionsOnChart (C : G.Cocycle) (i : D.J) (W : D.glued.Opens)
    (hi : W ≤ (D.ι i).opensRange) : G.CompatibleSections W ≃ Γ(G.chartPushforward i, W) where
  toFun s := s.val i
  invFun x := ⟨fun j => G.transport i j W hi x,
    fun j k => congrArg (fun f => f x) (G.transport_agree C i j k W hi)⟩
  left_inv s := by
    apply Subtype.ext
    funext j
    letI := G.restrictRight_app_isIso i j W hi
    change G.transport i j W hi (s.val i) = s.val j
    apply ((ConcreteCategory.isIso_iff_bijective ((G.restrictRight i j).app W)).mp inferInstance).injective
    exact (congrArg (fun f => f (s.val i)) (G.transport_restrictRight i j W hi)).trans (s.property i j)
  right_inv x := by
    change G.transport i i W hi x = x
    rw [C.identity]
    rfl

/-- The projection of the glued module onto a chart is an isomorphism on each
open contained in that chart. -/
theorem projectChart_app_isIso (C : G.Cocycle) (i : D.J) (W : D.glued.Opens)
    (hi : W ≤ (D.ι i).opensRange) : IsIso ((G.projectChart i).app W) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ((G.compatibleSectionsEquiv W).trans (G.compatibleSectionsOnChart C i W hi)).bijective

/-- The comparison from the restriction of the glued module to its original chart module. -/
def chartMap (i : D.J) : G.compatibleModule.restrict (D.ι i) ⟶ G.module i :=
  ((restrictAdjunction (D.ι i)).homEquiv _ _).symm (G.projectChart i)

private theorem restrictFunctor_map_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (m : M ⟶ N) (V : X.Opens) :
    ((restrictFunctor f).map m).app V = m.app (f ''ᵁ V) := rfl

/-- Pulling back the glued module to an original chart recovers its prescribed module. -/
def chartIso (C : G.Cocycle) (i : D.J) : G.compatibleModule.restrict (D.ι i) ≅ G.module i := by
  haveI : IsIso (G.chartMap i) := Hom.isIso_iff_isIso_app.mpr fun V => by
    rw [chartMap, Adjunction.homEquiv_symm_apply, Hom.comp_app, restrictFunctor_map_app]
    letI := G.projectChart_app_isIso C i ((D.ι i) ''ᵁ V) ((D.ι i).image_le_opensRange V)
    infer_instance
  exact asIso (G.chartMap i)

/-- The chart recovery isomorphisms satisfy the prescribed overlap
comparisons, written using the adjunctions of the open inclusions. -/
theorem chartIso_overlap (C : G.Cocycle) (i j : D.J) :
    ((restrictAdjunction (D.ι i)).homEquiv _ _ (G.chartIso C i).hom) ≫ G.restrictLeft i j =
      ((restrictAdjunction (D.ι j)).homEquiv _ _ (G.chartIso C j).hom) ≫ G.restrictRight i j := by
  change ((restrictAdjunction (D.ι i)).homEquiv _ _ (G.chartMap i)) ≫ G.restrictLeft i j =
    ((restrictAdjunction (D.ι j)).homEquiv _ _ (G.chartMap j)) ≫ G.restrictRight i j
  simpa only [chartMap, Equiv.apply_symm_apply] using G.projectChart_agree i j

private def fromGlobalHom (N : D.glued.Modules) : N ⟶ (ofModule N).compatibleModule :=
  ((ofModule N).compatibleMapsEquiv N).symm ⟨chartUnit N, chartUnit_agree N⟩

private theorem fromGlobalHom_project (N : D.glued.Modules) (i : D.J) :
    fromGlobalHom N ≫ (ofModule N).projectChart i = chartUnit N i :=
  congrArg (fun v : (ofModule N).CompatibleMaps N => v.val i)
    (((ofModule N).compatibleMapsEquiv N).apply_symm_apply ⟨chartUnit N, chartUnit_agree N⟩)

private theorem fromGlobalHom_chart (N : D.glued.Modules) (i : D.J) :
    (restrictFunctor (D.ι i)).map (fromGlobalHom N) ≫ (ofModule N).chartMap i = 𝟙 _ := by
  let adj := restrictAdjunction (D.ι i)
  apply (adj.homEquiv N _).injective
  rw [adj.homEquiv_naturality_left, chartMap, Equiv.apply_symm_apply, fromGlobalHom_project]
  simp [Adjunction.homEquiv_apply, adj]

/-- Gluing the restricted modules from a global module recovers the original module. -/
def reglueIso (N : D.glued.Modules) : N ≅ (ofModule N).compatibleModule := by
  haveI : IsIso (fromGlobalHom N) := isIso_of_restrictCharts D _ fun i => by
    let e := (ofModule N).chartIso (ofModule_cocycle N) i
    have equal : (restrictFunctor (D.ι i)).map (fromGlobalHom N) = e.inv := by
      apply (cancel_mono e.hom).1
      exact (fromGlobalHom_chart N i).trans e.inv_hom_id.symm
    rw [equal]
    infer_instance
  exact asIso (fromGlobalHom N)

/-- A morphism between local modules that intertwines the two overlap transitions. -/
structure CompatibleMorphisms (H : ModuleGluingData D) where
  /-- The morphism on each original chart. -/
  map (i : D.J) : G.module i ⟶ H.module i
  /-- The original left and right restrictions give a commuting square. -/
  naturality (i j : D.J) :
    (restrictFunctor (D.f i j)).map (map i) ≫ (H.transition i j).hom =
      (G.transition i j).hom ≫ (restrictFunctor (overlapRight D i j)).map (map j)

variable {G} {H : ModuleGluingData D}

private theorem CompatibleMorphisms.naturality_inv (m : G.CompatibleMorphisms H) (i j : D.J) :
    (restrictFunctor (overlapRight D i j)).map (m.map j) ≫ (H.transition i j).inv =
      (G.transition i j).inv ≫ (restrictFunctor (D.f i j)).map (m.map i) := by
  apply (cancel_mono (H.transition i j).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, m.naturality, Iso.inv_hom_id_assoc]

private theorem CompatibleMorphisms.restrictLeft_naturality (m : G.CompatibleMorphisms H) (i j : D.J) :
    (pushforward (D.ι i)).map (m.map i) ≫ H.restrictLeft i j =
      G.restrictLeft i j ≫ (pushforward (D.f i j ≫ D.ι i)).map
        ((restrictFunctor (D.f i j)).map (m.map i)) := by
  simp only [restrictLeft, Category.assoc]
  have unit := (restrictAdjunction (D.f i j)).unit.naturality (m.map i)
  simp only [Functor.id_map] at unit
  have push := (pushforwardComp (D.f i j) (D.ι i)).hom.naturality
    ((restrictFunctor (D.f i j)).map (m.map i))
  simp only [Functor.comp_map] at unit push
  rw [← Functor.map_comp_assoc, unit, Functor.map_comp, Category.assoc, push]

private theorem CompatibleMorphisms.restrictRight_naturality (m : G.CompatibleMorphisms H) (i j : D.J) :
    (pushforward (D.ι j)).map (m.map j) ≫ H.restrictRight i j =
      G.restrictRight i j ≫ (pushforward (D.f i j ≫ D.ι i)).map
        ((restrictFunctor (D.f i j)).map (m.map i)) := by
  let h := overlapRight D i j
  simp only [restrictRight, Category.assoc]
  have unit := (restrictAdjunction h).unit.naturality (m.map j)
  have push := (pushforwardComp h (D.ι j)).hom.naturality_assoc
    ((restrictFunctor h).map (m.map j))
    ((pushforwardCongr (overlapRight_comp_chart D i j)).hom.app ((H.module j).restrict h) ≫
      (pushforward (D.f i j ≫ D.ι i)).map (H.transition i j).inv)
  simp only [Functor.id_map, Functor.comp_map] at unit push
  rw [← Functor.map_comp_assoc, unit, Functor.map_comp, Category.assoc, push,
    (pushforwardCongr (overlapRight_comp_chart D i j)).hom.naturality_assoc,
    ← Functor.map_comp, m.naturality_inv, Functor.map_comp]

/-- Compatible local morphisms assemble into a morphism of glued modules. -/
def glueMorphism (m : G.CompatibleMorphisms H) : G.compatibleModule ⟶ H.compatibleModule :=
  (H.compatibleMapsEquiv G.compatibleModule).symm
    ⟨fun i => G.projectChart i ≫ (pushforward (D.ι i)).map (m.map i), fun i j => by
      simp only [Category.assoc, m.restrictLeft_naturality, m.restrictRight_naturality]
      exact G.projectChart_agree_assoc i j _⟩

@[reassoc (attr := simp)]
theorem glueMorphism_project (m : G.CompatibleMorphisms H) (i : D.J) :
    glueMorphism m ≫ H.projectChart i = G.projectChart i ≫ (pushforward (D.ι i)).map (m.map i) := by
  simpa only [compatibleMapsEquiv] using congrArg (fun t : H.CompatibleMaps G.compatibleModule => t.val i)
    ((H.compatibleMapsEquiv G.compatibleModule).apply_symm_apply
      ⟨fun i => G.projectChart i ≫ (pushforward (D.ι i)).map (m.map i), _⟩)

private theorem chartMap_square_iff (g : G.compatibleModule ⟶ H.compatibleModule)
    (i : D.J) (m : G.module i ⟶ H.module i) :
    (restrictFunctor (D.ι i)).map g ≫ H.chartMap i = G.chartMap i ≫ m ↔
      g ≫ H.projectChart i = G.projectChart i ≫ (pushforward (D.ι i)).map m := by
  simp only [chartMap, ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    Equiv.symm_apply_eq, Equiv.apply_symm_apply]

/-- The assembled morphism restricts to the specified morphism on each chart. -/
theorem glueMorphism_chart (m : G.CompatibleMorphisms H) (i : D.J) :
    (restrictFunctor (D.ι i)).map (glueMorphism m) ≫ H.chartMap i = G.chartMap i ≫ m.map i :=
  (chartMap_square_iff (glueMorphism m) i (m.map i)).2 (glueMorphism_project m i)

/-- Chosen chart morphisms determine the glued morphism uniquely. -/
theorem existsUnique_glueMorphism (m : G.CompatibleMorphisms H) :
    ∃! g : G.compatibleModule ⟶ H.compatibleModule,
      ∀ i, (restrictFunctor (D.ι i)).map g ≫ H.chartMap i = G.chartMap i ≫ m.map i := by
  refine ⟨glueMorphism m, glueMorphism_chart m, fun g hg => ?_⟩
  apply (H.compatibleMapsEquiv G.compatibleModule).injective
  apply Subtype.ext
  funext i
  change g ≫ H.projectChart i = glueMorphism m ≫ H.projectChart i
  rw [glueMorphism_project]
  exact (chartMap_square_iff g i (m.map i)).1 (hg i)

end ModuleGluingData

end

end SHIGURE.SchemeDescent
