import Formal.SHIGURE.Part2.Schemes.AffineFppfRingEqualizer
import Formal.SHIGURE.Part2.Schemes.FiniteFppfProduct
import Formal.SHIGURE.Part2.Schemes.FppfSchemeMapSeparated

/-! # Fppf descent of maps between affine schemes

The selected finite affine charts give an open cover of the product
spectrum. The faithfully flat ring equalizer descends the map from that
spectrum, and joint faithfulness recovers each original component.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

/-- Maps on an original fppf family that agree on every test overlap. -/
structure CompatibleSchemeMapFamily {X : Scheme.{u}} (cover : FppfCover.{u,v} X)
    (Y : Scheme.{u}) where
  map (i : cover.I₀) : cover.X i ⟶ Y
  agree ⦃T : Scheme.{u}⦄ ⦃i j : cover.I₀⦄ (p : T ⟶ cover.X i) (q : T ⟶ cover.X j)
    (same : p ≫ cover.f i = q ≫ cover.f j) : p ≫ map i = q ≫ map j

section AffineRefinementMaps

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} {cover : FppfCover.{u,u} (Spec R)}
  (F : AffineRefinement cover) (m : CompatibleSchemeMapFamily cover Y)

private def refinedMap (i : F.affine.I₀) : Spec (F.affine.X i) ⟶ Y :=
  F.over.h₀ i ≫ m.map (F.over.s₀ i)

private theorem refinedMap_agree {V : Scheme.{u}} {i j : F.affine.I₀}
    (p : V ⟶ Spec (F.affine.X i)) (q : V ⟶ Spec (F.affine.X j))
    (same : p ≫ F.affine.f i = q ≫ F.affine.f j) :
    p ≫ refinedMap F m i = q ≫ refinedMap F m j := by
  have comm : (p ≫ F.over.h₀ i) ≫ cover.f (F.over.s₀ i) =
      (q ≫ F.over.h₀ j) ≫ cover.f (F.over.s₀ j) := by
    rw [Category.assoc, Category.assoc, F.over.w₀, F.over.w₀]
    exact same
  simpa only [refinedMap, Category.assoc] using
    m.agree (p ≫ F.over.h₀ i) (q ≫ F.over.h₀ j) comm

private theorem productChart_over (i : F.affine.I₀) :
    F.productOpenCover.f i ≫ Spec.map F.productMap = F.affine.f i :=
  F.toProductCover.w₀ i

private theorem productLocalMap_glues (i j : F.affine.I₀) :
    pullback.fst (F.productOpenCover.f i) (F.productOpenCover.f j) ≫ refinedMap F m i =
      pullback.snd (F.productOpenCover.f i) (F.productOpenCover.f j) ≫ refinedMap F m j := by
  apply refinedMap_agree
  rw [← productChart_over F i, ← productChart_over F j, ← Category.assoc, ← Category.assoc,
    pullback.condition]

private def productLocalMap : Spec F.productRing ⟶ Y :=
  F.productOpenCover.glueMorphisms (refinedMap F m) (productLocalMap_glues F m)

private theorem productLocalMap_chart (i : F.affine.I₀) :
    F.productOpenCover.f i ≫ productLocalMap F m = refinedMap F m i :=
  F.productOpenCover.ι_glueMorphisms _ _ i

private theorem productLocalMap_agrees_on_test {V : Scheme.{u}} (p q : V ⟶ Spec F.productRing)
    (same : p ≫ Spec.map F.productMap = q ≫ Spec.map F.productMap) :
    p ≫ productLocalMap F m = q ≫ productLocalMap F m := by
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
  change s ≫ t ≫ p ≫ productLocalMap F m = s ≫ t ≫ q ≫ productLocalMap F m
  calc
    _ = ((s ≫ t) ≫ p) ≫ productLocalMap F m := by simp only [Category.assoc]
    _ = (s ≫ a) ≫ refinedMap F m i := by simp only [left', Category.assoc, productLocalMap_chart]
    _ = b ≫ refinedMap F m j := refinedMap_agree F m _ _ onBase
    _ = ((s ≫ t) ≫ q) ≫ productLocalMap F m := by simp only [right', Category.assoc, productLocalMap_chart]
    _ = _ := by simp only [Category.assoc]

private theorem originalMap_eq_of_refinedMap {g : Spec R ⟶ Y}
    (hg : ∀ i, F.affine.f i ≫ g = refinedMap F m i) (j : cover.I₀) :
    cover.f j ≫ g = m.map j := by
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
  change p ≫ cover.f j ≫ g = p ≫ m.map j
  rw [← Category.assoc, ← w, Category.assoc, hg, refinedMap, ← Category.assoc]
  exact m.agree (q ≫ F.over.h₀ i) p relation

end AffineRefinementMaps

set_option maxHeartbeats 360000 in
/-- Every compatible family of maps between the schemes of an arbitrary
fppf cover of an affine base and an affine target descends uniquely. -/
theorem fppfAffineTargetMaps_existUnique_onAffineBase
    {R : CommRingCat.{u}} (C : Type u) [CommRing C]
    (cover : FppfCover.{u,v} (Spec R))
    (m : CompatibleSchemeMapFamily cover (Spec (CommRingCat.of C))) :
    ∃! g : Spec R ⟶ Spec (CommRingCat.of C), ∀ j, cover.f j ≫ g = m.map j := by
  let small := fppfPointSubcover cover
  let m' : CompatibleSchemeMapFamily small (Spec (CommRingCat.of C)) :=
    ⟨fun x => m.map (cover.idx x), fun _ _ _ p q eq => m.agree p q eq⟩
  let F := affineRefinement small
  letI : Algebra R F.productRing := F.productAlgebra
  letI : Module.FaithfullyFlat R F.productRing := F.productFaithfullyFlat
  let q := productLocalMap F m'
  have a : affineScalarMap R F.productRing = Spec.map F.productMap := rfl
  have agrees : affineDoubleProjection R F.productRing 0 ≫ q =
      affineDoubleProjection R F.productRing 1 ≫ q := by
    apply productLocalMap_agrees_on_test
    rw [← a, affineDoubleProjection_base, affineDoubleProjection_base]
  obtain ⟨g, hg, _⟩ := affineCover_descendsMap (A := R) (B := F.productRing) C q agrees
  have gOnProduct : Spec.map F.productMap ≫ g = q := a ▸ hg
  have gOnSmall (x : small.I₀) : small.f x ≫ g = m'.map x := by
    apply originalMap_eq_of_refinedMap F m' _ x
    intro i
    rw [← productChart_over F i, Category.assoc, gOnProduct]
    exact productLocalMap_chart F m' i
  have gOnAll (j : cover.I₀) : cover.f j ≫ g = m.map j := by
    let W := small.pullback₁ (cover.f j)
    apply fppfCover_hom_ext W
    intro i
    let p := W.f i
    let r := small.pullbackHom (cover.f j) i
    have w : r ≫ small.f i = p ≫ cover.f j := small.pullbackHom_map (cover.f j) i
    change p ≫ cover.f j ≫ g = p ≫ m.map j
    rw [← Category.assoc, ← w, Category.assoc, gOnSmall]
    exact m.agree r p w
  refine ⟨g, gOnAll, fun h hh => fppfCover_hom_ext cover (fun j => (hh j).trans (gOnAll j).symm)⟩

set_option maxHeartbeats 360000 in
/-- The affine descent construction transfers through the canonical affine
scheme identifications. -/
theorem fppfAffineTargetMaps_existUnique
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (cover : FppfCover.{u,v} X)
    (m : CompatibleSchemeMapFamily cover Y) :
    ∃! g : X ⟶ Y, ∀ i, cover.f i ≫ g = m.map i := by
  letI : MorphismProperty.IsMultiplicative (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    { id_mem := fun X => inferInstanceAs (LocallyOfFinitePresentation (𝟙 X)) }
  let ex := X.isoSpec
  let ey := Y.isoSpec
  let P := cover.pushforwardIso ex.hom
  have cf (i : cover.I₀) : P.f i = cover.f i ≫ ex.hom := rfl
  let m' : CompatibleSchemeMapFamily P (Spec (Γ(Y, ⊤))) :=
    { map := fun i => m.map i ≫ ey.hom
      agree := fun T i j p q w => by
        have w' : p ≫ cover.f i ≫ ex.hom = q ≫ cover.f j ≫ ex.hom := by
          rw [← cf, ← cf]
          exact w
        have a : p ≫ cover.f i = q ≫ cover.f j :=
          (cancel_mono ex.hom).1 (by simpa only [Category.assoc] using w')
        simpa only [← Category.assoc] using congrArg (· ≫ ey.hom) (m.agree p q a) }
  obtain ⟨k, hk, _⟩ := fppfAffineTargetMaps_existUnique_onAffineBase (Γ(Y, ⊤)) P m'
  let g := ex.hom ≫ k ≫ ey.inv
  have f (i : cover.I₀) : cover.f i ≫ g = m.map i := by
    change cover.f i ≫ ex.hom ≫ k ≫ ey.inv = m.map i
    rw [← Category.assoc, ← cf, ← Category.assoc, hk]
    change (m.map i ≫ ey.hom) ≫ ey.inv = m.map i
    rw [Category.assoc, ey.hom_inv_id, Category.comp_id]
  exact ⟨g, f, fun k' hk' => fppfCover_hom_ext cover (fun i => (hk' i).trans (f i).symm)⟩

end

end SHIGURE.SchemeDescent
