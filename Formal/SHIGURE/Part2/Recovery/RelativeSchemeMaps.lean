import Formal.SHIGURE.Part2.Realizations.ZariskiConstants
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Whiskering
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Relative schemes and their Zariski point sheaves

A sheaf of relative points remembers all the relative scheme morphisms.
The pullback comparison comes from the actual adjunction between
postcomposition and the fiber product of relative schemes.

## Implementation notes

The comparisons have the types of mathlib's `Over.pullbackId` and
`Over.pullbackComp`. We use the limiting cones to give their components
directly, so that the projection equations and the comparison of the
represented points can use the same morphisms. The counit formula for
adjoint mates identifies these comparisons with the mathlib isomorphisms.
-/

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S S' : Scheme.{u}}

/-- The sheaf of relative points has the usual relative Yoneda presheaf. -/
def relativePointsPresheafIso (Y : Over S) :
    (relativePoints S Y).val ≅ yoneda.obj Y :=
  NatIso.ofComponents (fun T => (relativePointsEquiv S T.unop Y).toIso) (by
    intro U V g
    ext p
    apply Over.OverMorphism.ext
    rfl)

/-- A relative scheme morphism is postcomposition on all relative points. -/
def relativePointsMap {Y Z : Over S} (f : Y ⟶ Z) :
    relativePoints S Y ⟶ relativePoints S Z :=
  ⟨(relativePointsPresheafIso Y).hom ≫ yoneda.map f ≫ (relativePointsPresheafIso Z).inv⟩

/-- Postcomposition by an identity induces the identity on relative points. -/
theorem relativePointsMap_id (Y : Over S) : relativePointsMap (𝟙 Y) = 𝟙 (relativePoints S Y) := by
  apply Sheaf.Hom.ext
  simp [relativePointsMap]

/-- Postcomposition on represented relative points respects composition. -/
theorem relativePointsMap_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativePointsMap (f ≫ g) = relativePointsMap f ≫ relativePointsMap g := by
  apply Sheaf.Hom.ext
  simp [relativePointsMap, Category.assoc]

/-- Postcomposition of relative points computes the actual morphism in the slice. -/
theorem relativePointsMap_app {T Y Z : Over S} (f : Y ⟶ Z)
    (p : (relativePoints S Y).val.obj (op T)) :
    relativePointsEquiv S T Z ((relativePointsMap f).val.app (op T) p) =
      relativePointsEquiv S T Y p ≫ f := by
  exact (relativePointsEquiv S T Z).apply_symm_apply _

/-- Read a morphism of relative point sheaves at the identity point of the source. -/
def readRelativePointsMap {Y Z : Over S} (f : relativePoints S Y ⟶ relativePoints S Z) : Y ⟶ Z :=
  relativePointsEquiv S Y Z (f.val.app (op Y) ((relativePointsEquiv S Y Y).symm (𝟙 Y)))

/-- Maps between represented relative sheaves are exactly maps of their representing schemes. -/
def relativePointsHomEquiv (Y Z : Over S) :
    (Y ⟶ Z) ≃ (relativePoints S Y ⟶ relativePoints S Z) where
  toFun := relativePointsMap
  invFun := readRelativePointsMap
  left_inv f := by
    rw [readRelativePointsMap, relativePointsMap_app, Equiv.apply_symm_apply, Category.id_comp]
  right_inv f := by
    ext T p
    let r := relativePointsEquiv S T.unop Y p
    let idPoint := (relativePointsEquiv S Y Y).symm (𝟙 Y)
    let img := f.val.app (op Y) idPoint
    have hn := FunctorToTypes.naturality _ _ f.val r.op idPoint
    have hp : (relativePoints S Y).val.map r.op idPoint = p := by
      apply (relativePointsEquiv S T.unop Y).injective
      apply Over.OverMorphism.ext
      change r.left ≫ 𝟙 Y.left = p.val
      rw [Category.comp_id]
      rfl
    rw [hp] at hn
    have hh := congrArg (relativePointsEquiv S T.unop Z) hn
    apply (relativePointsEquiv S T.unop Z).injective
    rw [relativePointsMap_app, hh]
    apply Over.OverMorphism.ext
    rfl

/-- Fiber-product base change in the two slice categories of schemes. -/
def relativeSchemePullback (f : S' ⟶ S) : Over S ⥤ Over S' :=
  @Over.pullback Scheme.{u} _ S' S f (fun g => inferInstanceAs (HasPullback g f))

/-- The slice fiber product is right adjoint to composition of structure maps. -/
def relativeSchemePullbackAdj (f : S' ⟶ S) : Over.map f ⊣ relativeSchemePullback f :=
  @Over.mapPullbackAdj Scheme.{u} _ S' S f (fun g => inferInstanceAs (HasPullback g f))

/-- The projection back to the original relative scheme. -/
abbrev relativeSchemeProjection (f : S' ⟶ S) (Y : Over S) :
    ((relativeSchemePullback f).obj Y).left ⟶ Y.left :=
  pullback.fst Y.hom f

/-- Projecting after a fiber-product map reduces to projecting before the original map. -/
@[reassoc (attr := simp)]
theorem relativeSchemeProjection_map (f : S' ⟶ S) {Y Z : Over S} (g : Y ⟶ Z) :
    ((relativeSchemePullback f).map g).left ≫ relativeSchemeProjection f Z =
      relativeSchemeProjection f Y ≫ g.left :=
  pullback.lift_fst _ _ _

/-- The map of fiber products itself fits into a pullback square over the original scheme map. -/
theorem relativeSchemePullbackMap_isPullback (f : S' ⟶ S) {Y Z : Over S} (g : Y ⟶ Z) :
    IsPullback ((relativeSchemePullback f).map g).left (relativeSchemeProjection f Y)
      (relativeSchemeProjection f Z) g.left := by
  have outer : IsPullback (((relativeSchemePullback f).map g).left ≫ ((relativeSchemePullback f).obj Z).hom)
      (relativeSchemeProjection f Y) f (g.left ≫ Z.hom) := by
    rw [Over.w ((relativeSchemePullback f).map g), Over.w g]
    exact (IsPullback.of_hasPullback Y.hom f).flip
  exact outer.of_right (relativeSchemeProjection_map f g) (IsPullback.of_hasPullback Z.hom f).flip

/-- Pullback along the coefficient identity keeps the same relative test by the first projection. -/
def relativeSchemePullbackId (S : Scheme.{u}) : relativeSchemePullback (𝟙 S) ≅ 𝟭 (Over S) :=
  NatIso.ofComponents (fun Y =>
    Over.isoMk (asIso (relativeSchemeProjection (𝟙 S) Y))
      (pullback.condition.trans (Category.comp_id _))) (by
    intro Y Z g
    apply Over.OverMorphism.ext
    exact relativeSchemeProjection_map (𝟙 S) g)

private theorem iteratedRelativePullback {S'' : Scheme.{u}} (g : S'' ⟶ S') (f : S' ⟶ S) (Y : Over S) :
    IsPullback (relativeSchemeProjection g ((relativeSchemePullback f).obj Y) ≫ relativeSchemeProjection f Y)
      ((relativeSchemePullback g).obj ((relativeSchemePullback f).obj Y)).hom Y.hom (g ≫ f) :=
  (IsPullback.of_hasPullback ((relativeSchemePullback f).obj Y).hom g).paste_horiz (IsPullback.of_hasPullback Y.hom f)

private theorem overPullbackHomExt {B X V : Scheme.{u}} {Y Z : Over B} {p : Y.left ⟶ X}
    {x : X ⟶ V} {b : B ⟶ V} (P : IsPullback p Y.hom x b) {g h : Z ⟶ Y}
    (e : g.left ≫ p = h.left ≫ p) : g = h :=
  Over.OverMorphism.ext (P.hom_ext e ((Over.w g).trans (Over.w h).symm))

private def relativeSchemePullbackCompAt {S'' : Scheme.{u}} (g : S'' ⟶ S') (f : S' ⟶ S) (Y : Over S) :
    (relativeSchemePullback (g ≫ f)).obj Y ≅ (relativeSchemePullback g).obj ((relativeSchemePullback f).obj Y) :=
  let w := IsPullback.of_hasPullback Y.hom (g ≫ f)
  let h := iteratedRelativePullback g f Y
  Over.isoMk (w.isoIsPullback _ _ h) (IsPullback.isoIsPullback_hom_snd _ _ w h)

@[reassoc (attr := simp)]
private theorem relativeSchemePullbackCompAt_fst {S'' : Scheme.{u}} (g : S'' ⟶ S') (f : S' ⟶ S) (Y : Over S) :
    (relativeSchemePullbackCompAt g f Y).hom.left ≫
        relativeSchemeProjection g ((relativeSchemePullback f).obj Y) ≫ relativeSchemeProjection f Y =
      relativeSchemeProjection (g ≫ f) Y :=
  IsPullback.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback Y.hom (g ≫ f)) (iteratedRelativePullback g f Y)

/-- The iterated fiber-product comparison preserves both projections. -/
def relativeSchemePullbackComp {S'' : Scheme.{u}} (g : S'' ⟶ S') (f : S' ⟶ S) :
    relativeSchemePullback (g ≫ f) ≅ relativeSchemePullback f ⋙ relativeSchemePullback g :=
  NatIso.ofComponents (relativeSchemePullbackCompAt g f) (by
    intro Y Z r
    apply overPullbackHomExt (iteratedRelativePullback g f Z)
    change (((relativeSchemePullback (g ≫ f)).map r).left ≫ (relativeSchemePullbackCompAt g f Z).hom.left) ≫
        relativeSchemeProjection g ((relativeSchemePullback f).obj Z) ≫ relativeSchemeProjection f Z =
      ((relativeSchemePullbackCompAt g f Y).hom.left ≫
        ((relativeSchemePullback g).map ((relativeSchemePullback f).map r)).left) ≫
          relativeSchemeProjection g ((relativeSchemePullback f).obj Z) ≫ relativeSchemeProjection f Z
    simp only [Category.assoc, relativeSchemePullbackCompAt_fst, relativeSchemeProjection_map,
      relativeSchemeProjection_map_assoc, relativeSchemePullbackCompAt_fst_assoc])

/-- Projecting an iterated comparison back to the original scheme reduces to the direct projection. -/
@[reassoc (attr := simp)]
theorem relativeSchemePullbackComp_fst {S'' : Scheme.{u}} (g : S'' ⟶ S') (f : S' ⟶ S) (Y : Over S) :
    ((relativeSchemePullbackComp g f).hom.app Y).left ≫
      relativeSchemeProjection g ((relativeSchemePullback f).obj Y) ≫ relativeSchemeProjection f Y =
      relativeSchemeProjection (g ≫ f) Y :=
  relativeSchemePullbackCompAt_fst g f Y

/-- The underlying map of a unit comparison reduces to the first projection. -/
@[reassoc (attr := simp)]
theorem relativeSchemePullbackId_fst (Y : Over S) :
    ((relativeSchemePullbackId S).hom.app Y).left = relativeSchemeProjection (𝟙 S) Y := rfl

/-- The first-projection unit is the standard unit comparison for slice pullback. -/
theorem relativeSchemePullbackId_eq_mathlib (S : Scheme.{u}) :
    relativeSchemePullbackId S = (Over.pullbackId (X := S)) := by
  apply Iso.ext
  ext1
  funext Y
  apply Over.OverMorphism.ext
  rw [relativeSchemePullbackId_fst]
  have h := conjugateEquiv_counit
    (relativeSchemePullbackAdj (𝟙 S)) (Adjunction.id (C := Over S)) (Over.mapId S).inv Y
  have hleft := congrArg (fun (r : (relativeSchemePullback (𝟙 S)).obj Y ⟶ Y) => r.left) h
  change ((Over.pullbackId (X := S)).hom.app Y).left ≫ 𝟙 Y.left =
    𝟙 _ ≫ relativeSchemeProjection (𝟙 S) Y at hleft
  simpa only [Category.comp_id, Category.id_comp] using hleft.symm

/-- The two-projection composition comparison is the standard composition comparison for slice pullback. -/
theorem relativeSchemePullbackComp_eq_mathlib {S'' : Scheme.{u}} (g : S'' ⟶ S') (f : S' ⟶ S) :
    relativeSchemePullbackComp g f = Over.pullbackComp g f := by
  apply Iso.ext
  ext1
  funext Y
  apply overPullbackHomExt (iteratedRelativePullback g f Y)
  rw [relativeSchemePullbackComp_fst]
  have h := conjugateEquiv_counit (relativeSchemePullbackAdj (g ≫ f))
    ((relativeSchemePullbackAdj g).comp (relativeSchemePullbackAdj f)) (Over.mapComp g f).inv Y
  rw [Adjunction.comp_counit_app] at h
  have hleft := congrArg (fun r => (Over.forget S).map r) h
  change ((Over.pullbackComp g f).hom.app Y).left ≫
      (𝟙 _ ≫ relativeSchemeProjection g ((relativeSchemePullback f).obj Y)) ≫
        (𝟙 _ ≫ relativeSchemeProjection f Y) =
    𝟙 _ ≫ (𝟙 _ ≫ relativeSchemeProjection (g ≫ f) Y) at hleft
  simpa only [Category.id_comp] using hleft.symm

/-- After identifying equal coefficient maps, the projection reduces to the untransported projection. -/
@[reassoc (attr := simp)]
theorem relativeSchemePullback_congr_fst {f g : S' ⟶ S} (e : f = g) (Y : Over S) :
    (eqToHom (congrArg (fun a => (relativeSchemePullback a).obj Y) e)).left ≫ relativeSchemeProjection g Y =
      relativeSchemeProjection f Y := by
  subst g
  simp only [eqToHom_refl, Over.id_left, Category.id_comp]

/-- The two ways of comparing a triple iterated fiber product agree on both projections. -/
theorem relativeSchemePullback_assoc {S'' S''' : Scheme.{u}} (h : S''' ⟶ S'') (g : S'' ⟶ S') (f : S' ⟶ S)
    (Y : Over S) :
    ((relativeSchemePullbackComp (h ≫ g) f).hom.app Y) ≫
        ((relativeSchemePullbackComp h g).hom.app ((relativeSchemePullback f).obj Y)) =
      eqToHom (congrArg (fun a => (relativeSchemePullback a).obj Y) (Category.assoc h g f)) ≫
        ((relativeSchemePullbackComp h (g ≫ f)).hom.app Y) ≫
          (relativeSchemePullback h).map ((relativeSchemePullbackComp g f).hom.app Y) := by
  let P := (relativeSchemePullback f).obj Y
  let Q := (relativeSchemePullback g).obj P
  have pull := (IsPullback.of_hasPullback Q.hom h).paste_horiz (iteratedRelativePullback g f Y)
  apply overPullbackHomExt pull
  change _ ≫ relativeSchemeProjection h Q ≫ relativeSchemeProjection g P ≫ relativeSchemeProjection f Y =
    _ ≫ relativeSchemeProjection h Q ≫ relativeSchemeProjection g P ≫ relativeSchemeProjection f Y
  dsimp only [Q, P]
  simp only [Over.comp_left, Category.assoc, relativeSchemePullbackComp_fst, relativeSchemePullbackComp_fst_assoc]
  rw [relativeSchemeProjection_map_assoc (Y := (relativeSchemePullback (g ≫ f)).obj Y)
      (Z := (relativeSchemePullback g).obj ((relativeSchemePullback f).obj Y))
      h ((relativeSchemePullbackComp g f).hom.app Y),
    relativeSchemePullbackComp_fst g f Y, relativeSchemePullbackComp_fst h (g ≫ f) Y]
  exact (relativeSchemePullback_congr_fst (Category.assoc h g f) Y).symm

/-- The left unit comparison for a fiber product is the comparison along equality of the base maps. -/
theorem relativeSchemePullback_leftUnit (f : S' ⟶ S) (Y : Over S) :
    (relativeSchemePullbackComp (𝟙 S') f).hom.app Y ≫
      (relativeSchemePullbackId S').hom.app ((relativeSchemePullback f).obj Y) =
        eqToHom (congrArg (fun a => (relativeSchemePullback a).obj Y) (Category.id_comp f)) := by
  apply overPullbackHomExt (IsPullback.of_hasPullback Y.hom f)
  change _ ≫ relativeSchemeProjection f Y = _ ≫ relativeSchemeProjection f Y
  simp only [Over.comp_left, Category.assoc, relativeSchemePullbackId_fst, relativeSchemePullbackComp_fst]
  exact (relativeSchemePullback_congr_fst (Category.id_comp f) Y).symm

/-- The right unit comparison agrees with the composition of the identity and fiber-product maps. -/
theorem relativeSchemePullback_rightUnit (f : S' ⟶ S) (Y : Over S) :
    (relativeSchemePullbackComp f (𝟙 S)).hom.app Y ≫
      (relativeSchemePullback f).map ((relativeSchemePullbackId S).hom.app Y) =
        eqToHom (congrArg (fun a => (relativeSchemePullback a).obj Y) (Category.comp_id f)) := by
  apply overPullbackHomExt (IsPullback.of_hasPullback Y.hom f)
  change _ ≫ relativeSchemeProjection f Y = _ ≫ relativeSchemeProjection f Y
  simp only [Over.comp_left, Category.assoc]
  rw [relativeSchemeProjection_map (Y := (relativeSchemePullback (𝟙 S)).obj Y) (Z := Y)
      f ((relativeSchemePullbackId S).hom.app Y), relativeSchemePullbackId_fst,
    relativeSchemePullbackComp_fst]
  exact (relativeSchemePullback_congr_fst (Category.comp_id f) Y).symm

/-- Pulling back a represented carrier is represented by the actual fiber product in the slice. -/
def relativePointsPullbackIso (f : S' ⟶ S) (Y : Over S) :
    ((Scheme.zariskiTopology.overMapPullback (Type u) f).obj (relativePoints S Y)) ≅
      relativePoints S' ((relativeSchemePullback f).obj Y) := by
  let adj := relativeSchemePullbackAdj f
  let n := CategoryTheory.Functor.isoWhiskerLeft (Over.map f).op (relativePointsPresheafIso Y) ≪≫
    (adj.compYonedaIso.app Y).symm ≪≫ (relativePointsPresheafIso ((relativeSchemePullback f).obj Y)).symm
  exact ⟨⟨n.hom⟩, ⟨n.inv⟩, Sheaf.Hom.ext n.hom_inv_id, Sheaf.Hom.ext n.inv_hom_id⟩

/-- The representing isomorphism evaluates by the fiber-product adjunction. -/
theorem relativePointsPullbackIso_app (f : S' ⟶ S) (Y : Over S) (T : Over S')
    (x : (relativePoints S Y).val.obj (op ((Over.map f).obj T))) :
    relativePointsEquiv S' T ((relativeSchemePullback f).obj Y)
        ((relativePointsPullbackIso f Y).hom.val.app (op T) x) =
      (relativeSchemePullbackAdj f).homEquiv T Y (relativePointsEquiv S ((Over.map f).obj T) Y x) :=
  (relativePointsEquiv S' T ((relativeSchemePullback f).obj Y)).apply_symm_apply _

/-- The comparison carries a morphism of represented sheaves to the actual fiber-product map. -/
theorem relativePointsPullbackIso_naturality (f : S' ⟶ S) {Y Z : Over S} (g : Y ⟶ Z) :
    (Scheme.zariskiTopology.overMapPullback (Type u) f).map (relativePointsMap g) ≫ (relativePointsPullbackIso f Z).hom =
      (relativePointsPullbackIso f Y).hom ≫ relativePointsMap ((relativeSchemePullback f).map g) := by
  ext T x
  let U := T.unop
  apply (relativePointsEquiv S' U ((relativeSchemePullback f).obj Z)).injective
  change relativePointsEquiv S' U ((relativeSchemePullback f).obj Z)
      ((relativePointsPullbackIso f Z).hom.val.app (op U) ((relativePointsMap g).val.app (op ((Over.map f).obj U)) x)) =
    relativePointsEquiv S' U ((relativeSchemePullback f).obj Z)
      ((relativePointsMap ((relativeSchemePullback f).map g)).val.app (op U)
        ((relativePointsPullbackIso f Y).hom.val.app (op U) x))
  rw [relativePointsMap_app, relativePointsPullbackIso_app, relativePointsPullbackIso_app, relativePointsMap_app]
  exact (relativeSchemePullbackAdj f).homEquiv_naturality_right _ g

private theorem relativePointsEquiv_restrict {T U Y : Over S} (g : U ⟶ T)
    (x : (relativePoints S Y).val.obj (op T)) :
    relativePointsEquiv S U Y ((relativePoints S Y).val.map g.op x) =
      g ≫ relativePointsEquiv S T Y x :=
  Over.OverMorphism.ext rfl

@[reassoc (attr := simp)]
private theorem relativeSchemePullbackHomEquiv_fst (f : S' ⟶ S) {T : Over S'} {Y : Over S}
    (g : (Over.map f).obj T ⟶ Y) :
    ((relativeSchemePullbackAdj f).homEquiv T Y g).left ≫ relativeSchemeProjection f Y = g.left := by
  unfold relativeSchemePullbackAdj Over.mapPullbackAdj
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

/-- For coefficient change in Chapter 4, §4.5, the comparison of represented points commutes
with the unit of slice pullback. The input is an arbitrary relative scheme over the given base. -/
theorem relativePointsPullbackIso_id (Y : Over S) :
    (relativePointsPullbackIso (𝟙 S) Y).hom ≫ relativePointsMap ((relativeSchemePullbackId S).hom.app Y) =
      (Scheme.zariskiTopology.overMapPullbackId (Type u) S).hom.app (relativePoints S Y) := by
  ext T x
  let V := T.unop
  let U := (Over.map (𝟙 S)).obj V
  let e : V ⟶ U := (Over.mapId S).inv.app V
  change ((relativePointsMap ((relativeSchemePullbackId S).hom.app Y)).val.app (op V))
    ((relativePointsPullbackIso (𝟙 S) Y).hom.val.app (op V) x) =
    (relativePoints S Y).val.map e.op x
  apply (relativePointsEquiv S V Y).injective
  rw [relativePointsMap_app, relativePointsPullbackIso_app, relativePointsEquiv_restrict]
  apply Over.OverMorphism.ext
  change ((relativeSchemePullbackAdj (𝟙 S)).homEquiv V Y (relativePointsEquiv S U Y x)).left ≫
    relativeSchemeProjection (𝟙 S) Y = e.left ≫ (relativePointsEquiv S U Y x).left
  rw [relativeSchemePullbackHomEquiv_fst]
  exact (Category.id_comp _).symm

/-- For coefficient change in Chapter 4, §4.5, the comparison of represented points commutes
with composition of slice pullbacks along the two given coefficient maps. -/
theorem relativePointsPullbackIso_comp {S'' : Scheme.{u}} (g : S'' ⟶ S') (f : S' ⟶ S) (Y : Over S) :
    (Scheme.zariskiTopology.overMapPullback (Type u) g).map (relativePointsPullbackIso f Y).hom ≫
        (relativePointsPullbackIso g ((relativeSchemePullback f).obj Y)).hom =
      (Scheme.zariskiTopology.overMapPullbackComp (Type u) g f).hom.app (relativePoints S Y) ≫
        (relativePointsPullbackIso (g ≫ f) Y).hom ≫ relativePointsMap ((relativeSchemePullbackComp g f).hom.app Y) := by
  ext T x
  let V := T.unop
  let U := (Over.map g).obj V
  let W := (Over.map f).obj U
  let K := (Over.map (g ≫ f)).obj V
  let e : K ⟶ W := (Over.mapComp g f).hom.app V
  let P := (relativeSchemePullback f).obj Y
  let Q := (relativeSchemePullback g).obj P
  let r := relativePointsEquiv S W Y x
  let m := ((relativeSchemePullbackComp g f).hom.app Y)
  change (relativePointsPullbackIso g P).hom.val.app (op V)
      ((relativePointsPullbackIso f Y).hom.val.app (op U) x) =
    (relativePointsMap m).val.app (op V)
      ((relativePointsPullbackIso (g ≫ f) Y).hom.val.app (op V) ((relativePoints S Y).val.map e.op x))
  apply (relativePointsEquiv S'' V Q).injective
  rw [relativePointsMap_app, relativePointsPullbackIso_app, relativePointsPullbackIso_app,
    relativePointsPullbackIso_app, relativePointsEquiv_restrict]
  apply overPullbackHomExt (iteratedRelativePullback g f Y)
  change ((relativeSchemePullbackAdj g).homEquiv V P ((relativeSchemePullbackAdj f).homEquiv U Y r)).left ≫
    relativeSchemeProjection g P ≫ relativeSchemeProjection f Y =
      (((relativeSchemePullbackAdj (g ≫ f)).homEquiv V Y (e ≫ r)).left ≫ m.left) ≫
        relativeSchemeProjection g P ≫ relativeSchemeProjection f Y
  rw [relativeSchemePullbackHomEquiv_fst_assoc, relativeSchemePullbackHomEquiv_fst, Category.assoc,
    relativeSchemePullbackComp_fst, relativeSchemePullbackHomEquiv_fst]
  exact (Category.id_comp _).symm

end SHIGURE.Copying
