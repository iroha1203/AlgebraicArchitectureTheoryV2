import Formal.SHIGURE.Part2.Recovery.SheafTransitions

/-!
# Compatible local sheaf sections on a Zariski cover

The two maps from the product of chart direct images record the two
restrictions to each overlap. Their equalizer represents the sections
that match under the prescribed transition isomorphisms.

## Implementation notes

Taking the equalizer in sheaves supplies the sheaf condition before
computing any section. A sectionwise construction would repeat the
gluing proof on the relative site. Here the sectionwise matching
equations and the comparison on each chart follow from the equalizer.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} (C : Scheme.OpenCover.{u} S)

namespace SheafCharts

variable {C} (D : SheafCharts C)

/-- Sections of a chart on the original relative tests after taking the inverse-image open. -/
def chartImage (i : C.I₀) : ZariskiSheaf S := (relativeSheafDirectImage (C.f i)).obj (D.chart i)

private def overlapToBase (i j : C.I₀) : CoverOverlap C i j ⟶ S :=
  pullback.fst (C.f i) (C.f j) ≫ C.f i

private abbrev overlapAt (T : Over S) (i j : C.I₀) :=
  (relativeSchemePullback (overlapToBase i j)).obj T

private abbrev commonTest (T : Over S) (i j : C.I₀) : Over S :=
  (Over.map (overlapToBase i j)).obj (overlapAt T i j)

private def commonInclusion (T : Over S) (i j : C.I₀) : commonTest T i j ⟶ T :=
  (relativeSchemePullbackAdj (overlapToBase i j)).counit.app T

private def commonLeft (T : Over S) (i j : C.I₀) : CoverLift C i (commonTest T i j) :=
  ⟨(overlapAt T i j).hom ≫ pullback.fst (C.f i) (C.f j), Category.assoc _ _ _⟩

private def commonRight (T : Over S) (i j : C.I₀) : CoverLift C j (commonTest T i j) :=
  ⟨(overlapAt T i j).hom ≫ pullback.snd (C.f i) (C.f j), by
    rw [Category.assoc, ← pullback.condition]
    rfl⟩

private def commonMap {T U : Over S} (g : U ⟶ T) (i j : C.I₀) : commonTest U i j ⟶ commonTest T i j :=
  (Over.map (overlapToBase i j)).map ((relativeSchemePullback (overlapToBase i j)).map g)

private theorem commonMap_inclusion {T U : Over S} (g : U ⟶ T) (i j : C.I₀) :
    commonMap g i j ≫ commonInclusion T i j = commonInclusion U i j ≫ g :=
  (relativeSchemePullbackAdj (overlapToBase i j)).counit.naturality g

private theorem commonChartMap {T U : Over S} (g : U ⟶ T) (i j k : C.I₀)
    (a : CoverLift C k (commonTest T i j)) (b : CoverLift C k (commonTest U i j)) :
    b.toChartTest (commonInclusion U i j) ≫ CoverLift.chartTestMap g k =
      a.map b (commonMap g i j) ≫ a.toChartTest (commonInclusion T i j) := by
  rw [← CoverLift.toChartTest_comp_target, ← CoverLift.toChartTest_comp_source, commonMap_inclusion]

/-- Sections of the overlap read in the second chart. -/
def overlapImage (i j : C.I₀) : ZariskiSheaf S :=
  (relativeSheafDirectImage (overlapToBase i j)).obj
    ((Scheme.zariskiTopology.overMapPullback (Type u) (pullback.snd (C.f i) (C.f j))).obj (D.chart j))

/-- Restrict from the first chart to the overlap and apply its transition. -/
def leftRestriction (i j : C.I₀) : D.chartImage i ⟶ D.overlapImage i j :=
  ⟨{ app := fun T => ↾fun x =>
        D.transitionAt (commonLeft T.unop i j) (commonRight T.unop i j)
          ((D.chart i).val.map ((commonLeft T.unop i j).toChartTest (commonInclusion T.unop i j)).op x)
     naturality := by
       intro X Y f
       ext x
       let T := X.unop
       let U := Y.unop
       let g := f.unop
       let a := commonLeft T i j
       let b := commonRight T i j
       let a' := commonLeft U i j
       let b' := commonRight U i j
       change D.transitionAt a' b' ((D.chart i).val.map (a'.toChartTest (commonInclusion U i j)).op
         ((D.chart i).val.map (CoverLift.chartTestMap g i).op x)) =
         (D.chart j).val.map (b.map b' (commonMap g i j)).op
           (D.transitionAt a b ((D.chart i).val.map (a.toChartTest (commonInclusion T i j)).op x))
       rw [← D.transitionAt_natural, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
         ← op_comp, ← op_comp, commonChartMap g i j i a a'] }⟩

/-- Restrict from the second chart to the common overlap. -/
def rightRestriction (i j : C.I₀) : D.chartImage j ⟶ D.overlapImage i j :=
  ⟨{ app := fun T => ↾fun x =>
        (D.chart j).val.map ((commonRight T.unop i j).toChartTest (commonInclusion T.unop i j)).op x
     naturality := by
       intro X Y f
       ext x
       let T := X.unop
       let U := Y.unop
       let g := f.unop
       let a := commonRight T i j
       let b := commonRight U i j
       change (D.chart j).val.map (b.toChartTest (commonInclusion U i j)).op
           ((D.chart j).val.map (CoverLift.chartTestMap g j).op x) =
         (D.chart j).val.map (a.map b (commonMap g i j)).op
           ((D.chart j).val.map (a.toChartTest (commonInclusion T i j)).op x)
       rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
         commonChartMap g i j j a b] }⟩

private def leftMap : ∏ᶜ D.chartImage ⟶ ∏ᶜ (fun p : C.I₀ × C.I₀ => D.overlapImage p.1 p.2) :=
  Pi.lift (fun p => Pi.π D.chartImage p.1 ≫ D.leftRestriction p.1 p.2)

private def rightMap : ∏ᶜ D.chartImage ⟶ ∏ᶜ (fun p : C.I₀ × C.I₀ => D.overlapImage p.1 p.2) :=
  Pi.lift (fun p => Pi.π D.chartImage p.2 ≫ D.rightRestriction p.1 p.2)

/-- The sheaf of sections of the local charts that agree on every overlap. -/
def matchingSheaf : ZariskiSheaf S := equalizer D.leftMap D.rightMap

/-- An arrow into the matching sheaf projects to a specified chart. -/
def matchingProjection (i : C.I₀) : D.matchingSheaf ⟶ D.chartImage i :=
  equalizer.ι D.leftMap D.rightMap ≫ Pi.π D.chartImage i

/-- The chart projections of the matching sheaf satisfy the overlap equations. -/
theorem matchingProjection_agrees (i j : C.I₀) :
    D.matchingProjection i ≫ D.leftRestriction i j = D.matchingProjection j ≫ D.rightRestriction i j := by
  have h := congrArg (fun f => f ≫ Pi.π (fun p : C.I₀ × C.I₀ => D.overlapImage p.1 p.2) (i, j))
    (equalizer.condition D.leftMap D.rightMap)
  simpa [matchingProjection, leftMap, rightMap, Category.assoc] using h

/-- Equalizer maps are exactly families of arrows with compatible restrictions. -/
def matchingHomEquiv (F : ZariskiSheaf S) : (F ⟶ D.matchingSheaf) ≃
    {m : ∀ i, F ⟶ D.chartImage i // ∀ i j, m i ≫ D.leftRestriction i j = m j ≫ D.rightRestriction i j} where
  toFun f := ⟨fun i => f ≫ D.matchingProjection i, fun i j => by
    rw [Category.assoc, Category.assoc, D.matchingProjection_agrees]⟩
  invFun m := equalizer.lift (Pi.lift m.val) (by
    apply Pi.hom_ext
    intro ij
    simpa [leftMap, rightMap, Category.assoc] using m.property ij.1 ij.2)
  left_inv f := by
    apply equalizer.hom_ext
    apply Pi.hom_ext
    intro i
    simp [matchingProjection, Category.assoc]
  right_inv m := by
    apply Subtype.ext
    funext i
    simp [matchingProjection]

private def relativeSectionEquiv (T : Over S) (F : ZariskiSheaf S) :
    (relativePoints S T ⟶ F) ≃ F.val.obj (op T) where
  toFun f := yonedaEquiv ((relativePointsPresheafIso T).inv ≫ f.val)
  invFun x := ⟨(relativePointsPresheafIso T).hom ≫ yonedaEquiv.symm x⟩
  left_inv f := by
    apply Sheaf.Hom.ext
    dsimp
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv x := by
    dsimp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Equiv.apply_symm_apply]

private theorem relativeSectionEquiv_comp (T : Over S) {F G : ZariskiSheaf S}
    (f : relativePoints S T ⟶ F) (g : F ⟶ G) :
    relativeSectionEquiv T G (f ≫ g) = g.val.app (op T) (relativeSectionEquiv T F f) := by
  simp only [relativeSectionEquiv, Equiv.coe_fn_mk, yonedaEquiv_comp]
  rfl

/-- A section on any relative test is an actual family of sections satisfying all overlap equations. -/
def matchingSectionsEquiv (T : Over S) : D.matchingSheaf.val.obj (op T) ≃
    {x : ∀ i, (D.chartImage i).val.obj (op T) // ∀ i j,
      (D.leftRestriction i j).val.app (op T) (x i) = (D.rightRestriction i j).val.app (op T) (x j)} :=
  (relativeSectionEquiv T D.matchingSheaf).symm.trans ((D.matchingHomEquiv (relativePoints S T)).trans
    { toFun m := ⟨fun i => relativeSectionEquiv T _ (m.val i), fun i j => by
        have h := congrArg (relativeSectionEquiv T _) (m.property i j)
        simpa only [relativeSectionEquiv_comp] using h⟩
      invFun x := ⟨fun i => (relativeSectionEquiv T _).symm (x.val i), fun i j => by
        apply (relativeSectionEquiv T _).injective
        simpa only [relativeSectionEquiv_comp, Equiv.apply_symm_apply] using x.property i j⟩
      left_inv m := Subtype.ext (funext fun i => (relativeSectionEquiv T _).symm_apply_apply (m.val i))
      right_inv x := Subtype.ext (funext fun i => (relativeSectionEquiv T _).apply_symm_apply (x.val i)) })

/-- The tuple of matching sections reads the actual sheaf projection at each chart. -/
theorem matchingSectionsEquiv_val (T : Over S) (x : D.matchingSheaf.val.obj (op T)) (i : C.I₀) :
    (D.matchingSectionsEquiv T x).val i = (D.matchingProjection i).val.app (op T) x := by
  change relativeSectionEquiv T _
    ((relativeSectionEquiv T _).symm x ≫ D.matchingProjection i) = _
  rw [relativeSectionEquiv_comp, Equiv.apply_symm_apply]

private def commonLift {U T : Over S} {i j : C.I₀} (a : CoverLift C i U) (b : CoverLift C j U)
    (g : U ⟶ T) : U ⟶ commonTest T i j := by
  let r := (a.overlapTest b).hom
  have hr : r ≫ overlapToBase i j = U.hom := by
    change pullback.lift a.val b.val (a.property.trans b.property.symm) ≫
      (pullback.fst (C.f i) (C.f j) ≫ C.f i) = U.hom
    rw [← Category.assoc, pullback.lift_fst, a.property]
  refine Over.homMk (pullback.lift g.left r ((Over.w g).trans hr.symm)) ?_
  change pullback.lift g.left r _ ≫ (pullback.snd T.hom (overlapToBase i j) ≫ overlapToBase i j) = U.hom
  rw [← Category.assoc, pullback.lift_snd, hr]

private theorem commonLift_inclusion {U T : Over S} {i j : C.I₀} (a : CoverLift C i U) (b : CoverLift C j U)
    (g : U ⟶ T) : commonLift a b g ≫ commonInclusion T i j = g := by
  apply Over.OverMorphism.ext
  change (commonLift a b g).left ≫ _ = _
  simpa only [commonInclusion, relativeSchemePullbackAdj, Over.mapPullbackAdj_counit_app, Over.homMk_left,
    Category.id_comp, commonLift] using (pullback.lift_fst g.left (a.overlapTest b).hom _)

/-- The overlap equations of a matching section hold on every common test. -/
theorem matchingSections_agree {T U : Over S} {i j : C.I₀} (x : D.matchingSheaf.val.obj (op T))
    (a : CoverLift C i U) (b : CoverLift C j U) (g : U ⟶ T) :
    D.transitionAt a b ((D.chart i).val.map (a.toChartTest g).op ((D.matchingSectionsEquiv T x).val i)) =
      (D.chart j).val.map (b.toChartTest g).op ((D.matchingSectionsEquiv T x).val j) := by
  let a₀ := commonLeft T i j
  let b₀ := commonRight T i j
  let h := commonLift a b g
  let v := commonInclusion T i j
  have hx := (D.matchingSectionsEquiv T x).property i j
  change D.transitionAt a₀ b₀ ((D.chart i).val.map (a₀.toChartTest v).op ((D.matchingSectionsEquiv T x).val i)) =
    (D.chart j).val.map (b₀.toChartTest v).op ((D.matchingSectionsEquiv T x).val j) at hx
  have e := congrArg ((D.chart j).val.map (b₀.map b h).op) hx
  rw [← D.transitionAt_natural a₀ b₀ a b h, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← CoverLift.toChartTest_comp_source, ← CoverLift.toChartTest_comp_source,
    commonLift_inclusion] at e
  exact e

/-- Read a matching section on a test that already factors through one chart. -/
def readChart {T : Over S} {i : C.I₀} (a : CoverLift C i T) (x : D.matchingSheaf.val.obj (op T)) :
    (D.chart i).val.obj (op a.test) :=
  (D.chart i).val.map (a.toChartTest (𝟙 T)).op ((D.matchingSectionsEquiv T x).val i)

/-- The chart comparisons of a glued section recover the given transition on each common test. -/
theorem readChart_agrees {T : Over S} {i j : C.I₀} (a : CoverLift C i T) (b : CoverLift C j T)
    (x : D.matchingSheaf.val.obj (op T)) :
    D.transitionAt a b (D.readChart a x) = D.readChart b x :=
  D.matchingSections_agree x a b (𝟙 T)

private def fromChart (hD : D.Coherent) {T : Over S} {i : C.I₀} (a : CoverLift C i T)
    (x : (D.chart i).val.obj (op a.test)) : D.matchingSheaf.val.obj (op T) :=
  (D.matchingSectionsEquiv T).symm ⟨D.extendChartSection a x, fun j k =>
    D.extendChartSection_agrees hD a x (commonLeft T j k) (commonRight T j k) (commonInclusion T j k)⟩

private theorem fromChart_val (hD : D.Coherent) {T : Over S} {i : C.I₀} (a : CoverLift C i T)
    (x : (D.chart i).val.obj (op a.test)) (j : C.I₀) :
    (D.matchingSectionsEquiv T (D.fromChart hD a x)).val j = D.extendChartSection a x j := by
  rw [fromChart, Equiv.apply_symm_apply]

private theorem readChart_fromChart (hD : D.Coherent) {T : Over S} {i : C.I₀} (a : CoverLift C i T)
    (x : (D.chart i).val.obj (op a.test)) : D.readChart a (D.fromChart hD a x) = x := by
  rw [readChart, D.fromChart_val, D.restrict_extendChartSection]
  have e (b : CoverLift C i T) :
      D.transitionAt b a ((D.chart i).val.map (a.map b (𝟙 T)).op x) = x := by
    have hb : b = a := Subsingleton.elim _ _
    subst b
    rw [CoverLift.map_id, op_id, FunctorToTypes.map_id_apply]
    exact hD.unit a x
  exact e _

private theorem fromChart_readChart (hD : D.Coherent) {T : Over S} {i : C.I₀} (a : CoverLift C i T)
    (x : D.matchingSheaf.val.obj (op T)) : D.fromChart hD a (D.readChart a x) = x := by
  apply (D.matchingSectionsEquiv T).injective
  apply Subtype.ext
  funext j
  let v := coefficientCoverTestInclusion C T j
  let b := a.pullback v
  let c := CoverLift.chartLift C T j
  rw [D.fromChart_val]
  have hb : b.toChartTest v = a.map b v ≫ a.toChartTest (𝟙 T) :=
    (congrArg b.toChartTest (Category.comp_id v)).symm.trans (CoverLift.toChartTest_comp_source a b v (𝟙 T))
  have e := D.matchingSections_agree x b c v
  rw [hb, op_comp, FunctorToTypes.map_comp_apply, CoverLift.toChartTest_inclusion, op_id] at e
  exact e.trans (FunctorToTypes.map_id_apply (D.chart j).val (X := op c.test) ((D.matchingSectionsEquiv T x).val j))

/-- Reading on a test that factors through one chart is a bijection onto its chart sections. -/
theorem readChart_bijective (hD : D.Coherent) {T : Over S} {i : C.I₀} (a : CoverLift C i T) :
    Function.Bijective (D.readChart a) :=
  ⟨Function.LeftInverse.injective (D.fromChart_readChart hD a),
    Function.RightInverse.surjective (D.readChart_fromChart hD a)⟩

/-- Reading matching sections on a chart respects every map of lifted tests. -/
theorem readChart_natural {T U : Over S} {i : C.I₀} (a : CoverLift C i T) (b : CoverLift C i U)
    (g : U ⟶ T) (x : D.matchingSheaf.val.obj (op T)) :
    D.readChart b (D.matchingSheaf.val.map g.op x) =
      (D.chart i).val.map (a.map b g).op (D.readChart a x) := by
  simp only [readChart, D.matchingSectionsEquiv_val]
  rw [FunctorToTypes.naturality _ _ (D.matchingProjection i).val]
  change (D.chart i).val.map (b.toChartTest (𝟙 U)).op
      ((D.chart i).val.map (CoverLift.chartTestMap g i).op _) =
    (D.chart i).val.map (a.map b g).op ((D.chart i).val.map (a.toChartTest (𝟙 T)).op _)
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp]
  rw [← CoverLift.toChartTest_comp_target, ← CoverLift.toChartTest_comp_source, Category.id_comp, Category.comp_id]

/-- The sheaf obtained by gluing restricts to each of the prescribed local sheaves. -/
def restrictMatchingIso (hD : D.Coherent) (i : C.I₀) :
    (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj D.matchingSheaf ≅ D.chart i :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun T =>
    let a := CoverLift.ofTest T.unop
    (show D.matchingSheaf.val.obj (op ((Over.map (C.f i)).obj T.unop)) ≃
        (D.chart i).val.obj (op T.unop) from
      ⟨D.readChart a, D.fromChart hD a, D.fromChart_readChart hD a, D.readChart_fromChart hD a⟩).toIso) (by
    intro U T g
    ext x
    exact D.readChart_natural (CoverLift.ofTest U.unop) (CoverLift.ofTest T.unop) ((Over.map (C.f i)).map g.unop) x))

/-- Local maps of chart sheaves that commute with the transition on their overlaps. -/
structure Arrow (E : SheafCharts C) where
  /-- The arrow on each chart. -/
  onChart (i : C.I₀) : D.chart i ⟶ E.chart i
  /-- The two routes on every common lifted test coincide. -/
  commute {i j : C.I₀} {T : Over S} (a : CoverLift C i T) (b : CoverLift C j T) (x : (D.chart i).val.obj (op a.test)) :
    E.transitionAt a b ((onChart i).val.app (op a.test) x) =
      (onChart j).val.app (op b.test) (D.transitionAt a b x)

namespace Arrow

/-- A square of sheaf arrows on each actual overlap gives a map of chart data. -/
def ofOverlap {E : SheafCharts C} (maps : ∀ i, D.chart i ⟶ E.chart i)
    (commutes : ∀ i j,
      (Scheme.zariskiTopology.overMapPullback (Type u) (pullback.fst (C.f i) (C.f j))).map (maps i) ≫
          (E.transition i j).hom =
        (D.transition i j).hom ≫
          (Scheme.zariskiTopology.overMapPullback (Type u) (pullback.snd (C.f i) (C.f j))).map (maps j)) :
    D.Arrow E where
  onChart := maps
  commute {i j T} a b x := by
    unfold transitionAt
    rw [← FunctorToTypes.naturality _ _ (maps i).val, FunctorToTypes.naturality _ _ (maps j).val]
    let U := op (a.overlapTest b)
    have h := congrArg (fun f => f.val.app U ((D.chart i).val.map (a.overlapLeft b).hom.op x)) (commutes i j)
    exact congrArg ((E.chart j).val.map (a.overlapRight b).inv.op) h

variable {D} {E : SheafCharts C} (f : D.Arrow E)

private def chartMap (i : C.I₀) : D.chartImage i ⟶ E.chartImage i :=
  (relativeSheafDirectImage (C.f i)).map (f.onChart i)

private theorem projectMap_agrees (i j : C.I₀) :
    D.matchingProjection i ≫ f.chartMap i ≫ E.leftRestriction i j =
      D.matchingProjection j ≫ f.chartMap j ≫ E.rightRestriction i j := by
  ext T x
  let U := T.unop
  let a := commonLeft U i j
  let b := commonRight U i j
  let g := commonInclusion U i j
  let xᵢ := (D.matchingProjection i).val.app T x
  let xⱼ := (D.matchingProjection j).val.app T x
  change E.transitionAt a b ((E.chart i).val.map (a.toChartTest g).op
    ((f.onChart i).val.app _ xᵢ)) = (E.chart j).val.map (b.toChartTest g).op ((f.onChart j).val.app _ xⱼ)
  rw [← FunctorToTypes.naturality _ _ (f.onChart i).val, ← FunctorToTypes.naturality _ _ (f.onChart j).val, f.commute]
  have h := D.matchingSections_agree x a b g
  rw [D.matchingSectionsEquiv_val, D.matchingSectionsEquiv_val] at h
  exact congrArg ((f.onChart j).val.app (op b.test)) h

private def matchingData :=
  (⟨fun i => D.matchingProjection i ≫ f.chartMap i, fun i j => by
    rw [Category.assoc, Category.assoc, f.projectMap_agrees]⟩ :
    {m : ∀ i, D.matchingSheaf ⟶ E.chartImage i // ∀ i j, m i ≫ E.leftRestriction i j = m j ≫ E.rightRestriction i j})

/-- Glue a compatible family of local sheaf maps. -/
def glue : D.matchingSheaf ⟶ E.matchingSheaf :=
  (E.matchingHomEquiv D.matchingSheaf).symm f.matchingData

/-- The glued map commutes with all matching projections. -/
theorem glue_projection (i : C.I₀) : f.glue ≫ E.matchingProjection i = D.matchingProjection i ≫ f.chartMap i :=
  congrArg (fun m => m.val i) ((E.matchingHomEquiv D.matchingSheaf).apply_symm_apply f.matchingData)

/-- The glued map on a lifted test reads as the indicated original local map. -/
theorem glue_readChart {T : Over S} {i : C.I₀} (a : CoverLift C i T) (x : D.matchingSheaf.val.obj (op T)) :
    E.readChart a (f.glue.val.app (op T) x) = (f.onChart i).val.app (op a.test) (D.readChart a x) := by
  have h := congrArg (fun m : D.matchingSheaf ⟶ E.chartImage i => m.val.app (op T) x) (f.glue_projection i)
  change (E.matchingProjection i).val.app (op T) (f.glue.val.app (op T) x) =
    (f.onChart i).val.app _ ((D.matchingProjection i).val.app (op T) x) at h
  simp only [readChart, matchingSectionsEquiv_val, h]
  exact (FunctorToTypes.naturality _ _ (f.onChart i).val (a.toChartTest (𝟙 T)).op _).symm

/-- Pointwise injections on all charts glue to a pointwise injection. -/
theorem glue_injective (h : ∀ i (U : (Over (C.X i))ᵒᵖ), Function.Injective ((f.onChart i).val.app U))
    (T : Over S) : Function.Injective (f.glue.val.app (op T)) := by
  intro x y e
  apply (D.matchingSectionsEquiv T).injective
  apply Subtype.ext
  funext i
  rw [D.matchingSectionsEquiv_val, D.matchingSectionsEquiv_val]
  apply h i (op (coefficientCoverTest C T i))
  exact (congrArg (fun m : D.matchingSheaf ⟶ E.chartImage i => m.val.app (op T) x) (f.glue_projection i)).symm.trans
    ((congrArg ((E.matchingProjection i).val.app (op T)) e).trans
      (congrArg (fun m : D.matchingSheaf ⟶ E.chartImage i => m.val.app (op T) y) (f.glue_projection i)))

end Arrow

end SheafCharts
end SHIGURE.Copying
