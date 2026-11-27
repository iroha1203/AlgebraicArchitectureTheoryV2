import Formal.SHIGURE.Part2.Schemes.AffineFppfRingEqualizer
import Formal.SHIGURE.Part2.Schemes.FiniteFppfProduct
import Formal.SHIGURE.Part2.Schemes.FppfSchemeMapSeparated
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! # Fppf descent of maps between affine schemes

The selected finite affine charts give an open cover of the product
spectrum. The faithfully flat ring equalizer descends the map from that
spectrum, and joint faithfulness recovers each original component.

## Implementation notes

The local arrows form a family for the actual fppf cover. Mathlib's
`Presieve.Arrows.Compatible` on the Yoneda presheaf expresses agreement
on every test object, which is used to move between the original family
and the finite affine refinement. The pairwise pullback criterion can
supply the same hypothesis via `Presieve.Arrows.pullbackCompatible_iff`.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

section AffineRefinementMaps

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} {cover : FppfCover.{u,u} (Spec R)}
  (F : AffineRefinement cover) (m : ∀ i, cover.X i ⟶ Y)

/-- Restrict the original maps along the morphism of covering families. -/
private def refinedMap (i : F.affine.I₀) : Spec (F.affine.X i) ⟶ Y :=
  F.over.h₀ i ≫ m (F.over.s₀ i)

variable (compatible : Presieve.Arrows.Compatible (yoneda.obj Y) cover.f m)

include compatible in
/-- Agreement on the original family implies agreement for the refined maps. -/
private theorem refinedMap_agree {V : Scheme.{u}} {i j : F.affine.I₀}
    (p : V ⟶ Spec (F.affine.X i)) (q : V ⟶ Spec (F.affine.X j))
    (same : p ≫ F.affine.f i = q ≫ F.affine.f j) :
    p ≫ refinedMap F m i = q ≫ refinedMap F m j := by
  have comm : (p ≫ F.over.h₀ i) ≫ cover.f (F.over.s₀ i) =
      (q ≫ F.over.h₀ j) ≫ cover.f (F.over.s₀ j) := by
    rw [Category.assoc, Category.assoc, F.over.w₀, F.over.w₀]
    exact same
  simpa only [refinedMap, Category.assoc] using
    compatible (F.over.s₀ i) (F.over.s₀ j) V (p ≫ F.over.h₀ i) (q ≫ F.over.h₀ j) comm

/-- The product-chart inclusion factors the refined cover map. -/
private theorem productChart_over (i : F.affine.I₀) :
    F.productOpenCover.f i ≫ Spec.map F.productMap = F.affine.f i :=
  F.toProductCover.w₀ i

include compatible in
/-- The refined maps agree on the overlaps of the open product charts. -/
private theorem productLocalMap_glues (i j : F.affine.I₀) :
    pullback.fst (F.productOpenCover.f i) (F.productOpenCover.f j) ≫ refinedMap F m i =
      pullback.snd (F.productOpenCover.f i) (F.productOpenCover.f j) ≫ refinedMap F m j := by
  apply refinedMap_agree F m compatible
  rw [← productChart_over F i, ← productChart_over F j, ← Category.assoc, ← Category.assoc,
    pullback.condition]

/-- Glue the refined charts into a map from the actual finite product spectrum. -/
private def productLocalMap : Spec F.productRing ⟶ Y :=
  F.productOpenCover.glueMorphisms (refinedMap F m) (productLocalMap_glues F m compatible)

/-- The glued product map restricts to each refined map. -/
private theorem productLocalMap_chart (i : F.affine.I₀) :
    F.productOpenCover.f i ≫ productLocalMap F m compatible = refinedMap F m i :=
  F.productOpenCover.ι_glueMorphisms _ _ i

/-- Check agreement on a test overlap by taking two pulled-back covers of the product charts. -/
private theorem productLocalMap_agrees_on_test {V : Scheme.{u}} (p q : V ⟶ Spec F.productRing)
    (same : p ≫ Spec.map F.productMap = q ≫ Spec.map F.productMap) :
    p ≫ productLocalMap F m compatible = q ≫ productLocalMap F m compatible := by
  let W : V.OpenCover := F.productOpenCover.pullback₁ p
  apply W.hom_ext
  intro i
  let t := W.f i
  let a := F.productOpenCover.pullbackHom p i
  have left : a ≫ F.productOpenCover.f i = t ≫ p :=
    F.productOpenCover.pullbackHom_map p i
  let U : (W.X i).OpenCover := F.productOpenCover.pullback₁ (t ≫ q)
  apply U.hom_ext
  intro j
  let s := U.f j
  let b := F.productOpenCover.pullbackHom (t ≫ q) j
  have right : b ≫ F.productOpenCover.f j = s ≫ (t ≫ q) :=
    F.productOpenCover.pullbackHom_map (t ≫ q) j
  have left' : (s ≫ t) ≫ p = (s ≫ a) ≫ F.productOpenCover.f i := by
    simpa only [Category.assoc] using congrArg (s ≫ ·) left.symm
  have right' : (s ≫ t) ≫ q = b ≫ F.productOpenCover.f j := by
    simpa only [Category.assoc] using right.symm
  have onBase : (s ≫ a) ≫ F.affine.f i = b ≫ F.affine.f j := calc
    _ = ((s ≫ a) ≫ F.productOpenCover.f i) ≫ Spec.map F.productMap := by
      simp only [Category.assoc, productChart_over]
    _ = ((s ≫ t) ≫ p) ≫ Spec.map F.productMap := congrArg (· ≫ Spec.map F.productMap) left'.symm
    _ = ((s ≫ t) ≫ q) ≫ Spec.map F.productMap := by simp only [Category.assoc, same]
    _ = (b ≫ F.productOpenCover.f j) ≫ Spec.map F.productMap := congrArg (· ≫ Spec.map F.productMap) right'
    _ = _ := by simp only [Category.assoc, productChart_over]
  change s ≫ t ≫ p ≫ productLocalMap F m compatible = s ≫ t ≫ q ≫ productLocalMap F m compatible
  calc
    _ = ((s ≫ t) ≫ p) ≫ productLocalMap F m compatible := by simp only [Category.assoc]
    _ = (s ≫ a) ≫ refinedMap F m i := by simp only [left', Category.assoc, productLocalMap_chart F m compatible]
    _ = b ≫ refinedMap F m j := refinedMap_agree F m compatible _ _ onBase
    _ = ((s ≫ t) ≫ q) ≫ productLocalMap F m compatible := by simp only [right', Category.assoc, productLocalMap_chart F m compatible]
    _ = _ := by simp only [Category.assoc]

include compatible in
/-- Recover the original component by pulling back the finite refinement. -/
private theorem originalMap_eq_of_refinedMap {g : Spec R ⟶ Y}
    (hg : ∀ i, F.affine.f i ≫ g = refinedMap F m i) (j : cover.I₀) :
    cover.f j ≫ g = m j := by
  let W := F.affine.cover.pullback₁ (cover.f j)
  apply fppfCover_hom_ext W
  intro i
  let p := W.f i
  let q := F.affine.cover.pullbackHom (cover.f j) i
  have w : q ≫ F.affine.f i = p ≫ cover.f j :=
    F.affine.cover.pullbackHom_map (cover.f j) i
  have relation : (q ≫ F.over.h₀ i) ≫ cover.f (F.over.s₀ i) = p ≫ cover.f j := by
    rw [Category.assoc, F.over.w₀]
    exact w
  change p ≫ cover.f j ≫ g = p ≫ m j
  rw [← Category.assoc, ← w, Category.assoc, hg, refinedMap, ← Category.assoc]
  exact compatible (F.over.s₀ i) j (W.X i) (q ≫ F.over.h₀ i) p relation

end AffineRefinementMaps

set_option maxHeartbeats 360000 in
/-- Every compatible family of maps between the schemes of an arbitrary
fppf cover of an affine base and an affine target descends uniquely. -/
theorem fppfAffineTargetMaps_existUnique_onAffineBase
    {R : CommRingCat.{u}} (C : Type u) [CommRing C]
    (cover : FppfCover.{u,v} (Spec R))
    (m : ∀ i, cover.X i ⟶ Spec (CommRingCat.of C))
    (compatible : Presieve.Arrows.Compatible (yoneda.obj (Spec (CommRingCat.of C))) cover.f m) :
    ∃! g : Spec R ⟶ Spec (CommRingCat.of C), ∀ j, cover.f j ≫ g = m j := by
  let small := fppfPointSubcover cover
  let m' (x : small.I₀) : small.X x ⟶ Spec (CommRingCat.of C) := m (cover.idx x)
  have compatible' : Presieve.Arrows.Compatible (yoneda.obj (Spec (CommRingCat.of C))) small.f m' :=
    fun i j Z p q eq => compatible (cover.idx i) (cover.idx j) Z p q eq
  let F := affineRefinement small
  letI : Algebra R F.productRing := F.productAlgebra
  letI : Module.FaithfullyFlat R F.productRing := F.productFaithfullyFlat
  let q := productLocalMap F m' compatible'
  have a : affineScalarMap R F.productRing = Spec.map F.productMap := rfl
  have agrees : affineDoubleProjection R F.productRing 0 ≫ q =
      affineDoubleProjection R F.productRing 1 ≫ q := by
    apply productLocalMap_agrees_on_test F m' compatible'
    rw [← a, affineDoubleProjection_base, affineDoubleProjection_base]
  obtain ⟨g, hg, _⟩ := affineCover_descendsMap (A := R) (B := F.productRing) C q agrees
  have gOnProduct : Spec.map F.productMap ≫ g = q := a ▸ hg
  have gOnSmall (x : small.I₀) : small.f x ≫ g = m' x := by
    apply originalMap_eq_of_refinedMap F m' compatible' _ x
    intro i
    rw [← productChart_over F i, Category.assoc, gOnProduct]
    exact productLocalMap_chart F m' compatible' i
  have gOnAll (j : cover.I₀) : cover.f j ≫ g = m j := by
    let W := small.pullback₁ (cover.f j)
    apply fppfCover_hom_ext W
    intro i
    let p := W.f i
    let r := small.pullbackHom (cover.f j) i
    have w : r ≫ small.f i = p ≫ cover.f j := small.pullbackHom_map (cover.f j) i
    change p ≫ cover.f j ≫ g = p ≫ m j
    rw [← Category.assoc, ← w, Category.assoc, gOnSmall]
    exact compatible (cover.idx i) j (W.X i) r p w
  refine ⟨g, gOnAll, fun h hh => fppfCover_hom_ext cover (fun j => (hh j).trans (gOnAll j).symm)⟩

set_option maxHeartbeats 360000 in
/-- The affine descent construction transfers through the canonical affine
scheme identifications. -/
theorem fppfAffineTargetMaps_existUnique
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (cover : FppfCover.{u,v} X)
    (m : ∀ i, cover.X i ⟶ Y)
    (compatible : Presieve.Arrows.Compatible (yoneda.obj Y) cover.f m) :
    ∃! g : X ⟶ Y, ∀ i, cover.f i ≫ g = m i := by
  letI : MorphismProperty.IsMultiplicative (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    { id_mem := fun X => inferInstanceAs (LocallyOfFinitePresentation (𝟙 X)) }
  let ex := X.isoSpec
  let ey := Y.isoSpec
  let P := cover.pushforwardIso ex.hom
  have cf (i : cover.I₀) : P.f i = cover.f i ≫ ex.hom := rfl
  let m' (i : P.I₀) : P.X i ⟶ Spec (Γ(Y, ⊤)) := m i ≫ ey.hom
  have compatible' : Presieve.Arrows.Compatible (yoneda.obj (Spec (Γ(Y, ⊤)))) P.f m' := by
    intro i j T p q w
    have w' : p ≫ cover.f i ≫ ex.hom = q ≫ cover.f j ≫ ex.hom := by
      rw [← cf, ← cf]
      exact w
    have equal : p ≫ cover.f i = q ≫ cover.f j :=
      (cancel_mono ex.hom).1 (by simpa only [Category.assoc] using w')
    change p ≫ m i ≫ ey.hom = q ≫ m j ≫ ey.hom
    simpa only [← Category.assoc] using congrArg (· ≫ ey.hom) (compatible i j T p q equal)
  obtain ⟨k, hk, _⟩ := fppfAffineTargetMaps_existUnique_onAffineBase (Γ(Y, ⊤)) P m' compatible'
  let g := ex.hom ≫ k ≫ ey.inv
  have f (i : cover.I₀) : cover.f i ≫ g = m i := by
    change cover.f i ≫ ex.hom ≫ k ≫ ey.inv = m i
    rw [← Category.assoc, ← cf, ← Category.assoc, hk]
    change (m i ≫ ey.hom) ≫ ey.inv = m i
    rw [Category.assoc, ey.hom_inv_id, Category.comp_id]
  exact ⟨g, f, fun k' hk' => fppfCover_hom_ext cover (fun i => (hk' i).trans (f i).symm)⟩

end

end SHIGURE.SchemeDescent
