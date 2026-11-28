import Formal.SHIGURE.Part2.Schemes.Effective.Examples
import Formal.SHIGURE.Part2.Schemes.AffineQuasiCoherentFiber

/-! # Independent local modules on two rational components

The two components are disjoint. We specify rank one on the true component
and rank two on the false component, then define the test-overlap maps
without choosing a module on the base. The general fppf comparison constructs
a global module from this datum and preserves distinct endomorphisms.
-/

namespace SHIGURE.SchemeDescent.EffectiveExamples

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

private abbrev Q := quasiCoherentModulesPseudofunctor.{0}
private abbrev C := rationalAffineCover.cover
private def rings (_ : Bool) : CommRingCat := .of ℚ

private instance component_open (i : Bool) : IsOpenImmersion (C.f i) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Bool => ℚ) i)))
  infer_instance

private theorem component_tag {i j : Bool} {x : C.X i} {y : C.X j}
    (h : C.f i x = C.f j y) : i = j := by
  have first : sigmaSpec rings (sigmaMk (fun i => Spec (rings i)) ⟨i, x⟩) = C.f i x := by
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec]
    rfl
  have second : sigmaSpec rings (sigmaMk (fun i => Spec (rings i)) ⟨j, y⟩) = C.f j y := by
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec]
    rfl
  exact congrArg Sigma.fst ((sigmaMk (fun i => Spec (rings i))).injective
    ((sigmaSpec rings).homeomorph.injective (first.trans (h.trans second.symm))))

private theorem empty_of_ne {Y : Scheme.{0}} {i j : Bool} (hne : i ≠ j)
    (a : Y ⟶ C.X i) (b : Y ⟶ C.X j) (h : a ≫ C.f i = b ≫ C.f j) : IsEmpty Y :=
  ⟨fun y => hne (component_tag (i := i) (j := j) (x := a y) (y := b y)
    (congrArg (fun f : Y ⟶ Spec rationalProduct => f y) h))⟩

private def emptyCover (Y : Scheme.{0}) [IsEmpty Y] : FppfCover.{0,0} Y where
  I₀ := Empty
  X := fun i => nomatch i
  f := fun i => nomatch i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun y => isEmptyElim y, fun i => nomatch i⟩

private theorem empty_hom_ext (Y : Scheme.{0}) [IsEmpty Y]
    {M N : Q.obj (.mk (op Y))} (a b : M ⟶ N) : a = b := by
  let E := emptyCover Y
  let G := fppfModuleComparison E
  letI : G.Faithful := fppfComparison_faithful E
  apply G.map_injective
  apply Pseudofunctor.DescentData.Hom.ext
  funext i
  exact Empty.elim i

/-- The two independently specified coefficient modules are ℚ and ℚ². -/
def independentChartModule (i : Bool) : ModuleCat (CommRingCat.of ℚ) :=
  if i then ModuleCat.of ℚ ℚ else ModuleCat.of ℚ (Bool → ℚ)

/-- The quasi-coherent module prescribed on each actual affine component. -/
def independentChart (i : Bool) : Q.obj (.mk (op (C.X i))) :=
  (affineTildeFunctor (CommRingCat.of ℚ)).obj (independentChartModule i)

private def zeroHom (Y : Scheme.{0})
    (M N : ObjectProperty.FullSubcategory (IsQuasiCoherentModule (X := Y))) : M ⟶ N :=
  ObjectProperty.homMk (0 : M.obj ⟶ N.obj)

private def independentOverlap {Y : Scheme.{0}} (q : Y ⟶ Spec rationalProduct) {i j : Bool}
    (a : Y ⟶ C.X i) (b : Y ⟶ C.X j) (ha : a ≫ C.f i = q) (hb : b ≫ C.f j = q) :
    (Q.map a.op.toLoc).toFunctor.obj (independentChart i) ⟶
      (Q.map b.op.toLoc).toFunctor.obj (independentChart j) := by
  by_cases equal : i = j
  · subst j
    have same : a = b := (cancel_mono (C.f i)).1 (ha.trans hb.symm)
    subst b
    exact 𝟙 _
  · exact zeroHom Y _ _

private theorem independentOverlap_self {Y : Scheme.{0}} {i : Bool} (a : Y ⟶ C.X i) :
    independentOverlap (i := i) (j := i) (a ≫ C.f i) a a rfl rfl = 𝟙 _ := by
  simp [independentOverlap]

private theorem independentOverlap_diag {Y : Scheme.{0}} {i : Bool}
    (q : Y ⟶ Spec rationalProduct) (a : Y ⟶ C.X i) (ha : a ≫ C.f i = q) :
    independentOverlap (i := i) (j := i) q a a ha ha = 𝟙 _ := by
  subst q
  exact independentOverlap_self a

private theorem conjugate_id {K : Type*} [Category K] {A B : K}
    (c : A ≅ B) (f : B ⟶ B) (h : f = 𝟙 B) : c.hom ≫ f ≫ c.inv = 𝟙 A := by
  subst f
  simp only [Category.id_comp, Iso.hom_inv_id]

private theorem pullHom_identity {K : Type*} [Category K]
    {F : Pseudofunctor (LocallyDiscrete Kᵒᵖ) Cat.{0,1}}
    {X Y Z : K} {M : F.obj (.mk (op X))} (a : Y ⟶ X) (p : Z ⟶ Y) (b : Z ⟶ X)
    (h : p ≫ a = b) :
    pullHom (F := F) (M₁ := M) (M₂ := M) (𝟙 ((F.map a.op.toLoc).toFunctor.obj M))
      p b b h h = 𝟙 _ := by
  let c := Cat.Hom.toNatIso (F.mapComp' a.op.toLoc p.op.toLoc b.op.toLoc
    (congrArg (fun k => k.op.toLoc) h))
  change (c.app M).hom ≫ (F.map p.op.toLoc).toFunctor.map (𝟙 _) ≫ (c.app M).inv = 𝟙 _
  exact conjugate_id (c.app M) _
    ((F.map p.op.toLoc).toFunctor.map_id ((F.map a.op.toLoc).toFunctor.obj M))

/-- The original datum is built from the two independent local modules.
Same-component comparisons are identities; mixed-component comparisons are
the unique maps on the empty overlaps. -/
def independentRationalDatum : Q.DescentData C.f where
  obj i := independentChart i
  hom _ q i j a b ha hb := independentOverlap (i := i) (j := j) q a b ha hb
  pullHom_hom _ _ p q q' hq i j a b ha hb a' b' ea eb := by
    by_cases equal : i = j
    · subst j
      have same : a = b := (cancel_mono (C.f i)).1 (ha.trans hb.symm)
      subst b
      cases ea
      cases eb
      rw [independentOverlap_diag, independentOverlap_diag]
      exact pullHom_identity (F := Q) (M := independentChart i) a p (p ≫ a) rfl
    · have overlap : a' ≫ C.f i = b' ≫ C.f j := by
        rw [← ea, ← eb, Category.assoc, Category.assoc, ha, hb]
      letI : IsEmpty _ := empty_of_ne equal a' b' overlap
      exact empty_hom_ext _ _ _
  hom_self _ q i a ha := by
    subst q
    exact independentOverlap_self a
  hom_comp _ q i j k a b c ha hb hc := by
    by_cases first : i = j
    · subst j
      by_cases second : i = k
      · subst k
        have ab : a = b := (cancel_mono (C.f i)).1 (ha.trans hb.symm)
        have ac : a = c := (cancel_mono (C.f i)).1 (ha.trans hc.symm)
        subst b c
        subst q
        simp only [independentOverlap_self, Category.id_comp]
      · letI : IsEmpty _ := empty_of_ne second a c (ha.trans hc.symm)
        exact empty_hom_ext _ _ _
    · letI : IsEmpty _ := empty_of_ne first a b (ha.trans hb.symm)
      exact empty_hom_ext _ _ _

/-- The specified local modules are the actual components of the datum. -/
theorem independentRationalDatum_obj (i : Bool) : independentRationalDatum.obj i = independentChart i := rfl

private def componentwiseEnd (D : Q.DescentData C.f) (φ : ∀ i, D.obj i ⟶ D.obj i) : D ⟶ D where
  hom := φ
  comm := by
    intro Y q i j a b ha hb
    by_cases same : i = j
    · subst j
      have equal : a = b := (cancel_mono (C.f i)).1 (ha.trans hb.symm)
      subst b
      subst q
      simp only [D.hom_self, Category.comp_id, Category.id_comp]
    · letI : IsEmpty Y := empty_of_ne same a b (ha.trans hb.symm)
      exact empty_hom_ext Y _ _

/-- The zero coefficient map on each independently chosen component gives a
descent endomorphism, including on their empty mixed overlaps. -/
def independentZeroEnd : independentRationalDatum ⟶ independentRationalDatum :=
  componentwiseEnd independentRationalDatum (fun i =>
    (affineTildeFunctor (CommRingCat.of ℚ)).map
      (0 : independentChartModule i ⟶ independentChartModule i))

/-- The datum is nonzero: its identity and the independently specified zero
endomorphism differ already on the rank-one rational component. -/
theorem independentRationalDatum_distinguishes_maps :
    (𝟙 independentRationalDatum : independentRationalDatum ⟶ independentRationalDatum) ≠ independentZeroEnd := by
  intro same
  have atTrue := congrArg (fun f : independentRationalDatum ⟶ independentRationalDatum => f.hom true) same
  let T := affineTildeFunctor (CommRingCat.of ℚ)
  let V := ModuleCat.of ℚ ℚ
  change (𝟙 (T.obj V) : T.obj V ⟶ T.obj V) = T.map (0 : V ⟶ V) at atTrue
  have mapped : T.map (𝟙 V) = T.map (0 : V ⟶ V) :=
    (T.map_id V).trans atTrue
  have equal : (𝟙 V : V ⟶ V) = 0 :=
    (affineTildeEquivalence (CommRingCat.of ℚ)).fullyFaithfulFunctor.map_injective mapped
  have value := congrArg (fun f : V ⟶ V => f (1 : ℚ)) equal
  change (1 : ℚ) = 0 at value
  exact one_ne_zero value

/-- The final comparison equivalence constructs a global quasi-coherent module
and recovers the independent datum on the original fppf cover. -/
def independentRationalGlobalization :
    Σ M : Q.obj (.mk (op (Spec rationalProduct))),
      (fppfModuleComparison C).obj M ≅ independentRationalDatum := by
  let F := fppfModuleComparison C
  letI : F.IsEquivalence := fppfModuleComparison_isEquivalence C
  let E := F.asEquivalence
  exact ⟨E.inverse.obj independentRationalDatum, E.counitIso.app independentRationalDatum⟩

/-- The recovered global object also has distinct endomorphisms, obtained
from the identity and zero endomorphisms of the independent datum. -/
theorem independentRationalGlobalization_distinguishes_maps :
    let F := fppfModuleComparison C
    letI : F.IsEquivalence := fppfModuleComparison_isEquivalence C
    let E := F.asEquivalence
    E.inverse.map (𝟙 independentRationalDatum) ≠ E.inverse.map independentZeroEnd := by
  dsimp only
  let F := fppfModuleComparison C
  letI : F.IsEquivalence := fppfModuleComparison_isEquivalence C
  let E := F.asEquivalence
  intro same
  exact independentRationalDatum_distinguishes_maps (E.fullyFaithfulInverse.map_injective same)

end

end SHIGURE.SchemeDescent.EffectiveExamples
