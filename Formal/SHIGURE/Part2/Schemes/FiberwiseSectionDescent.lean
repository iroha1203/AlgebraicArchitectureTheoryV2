import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Cat

/-! # Families of sections on the fibers of a pseudofunctor -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v a b c

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b})

/-- A family of types of sections, with functorial change of the object and
coherent restriction along the maps of the site. -/
structure FiberwiseSections where
  fiber (X : LocallyDiscrete Cᵒᵖ) : F.obj X ⥤ Type c
  restrict {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) :
    fiber X ⟶ (F.map f).toFunctor ⋙ fiber Y
  restrict_id (X : LocallyDiscrete Cᵒᵖ) (M : F.obj X) (s : (fiber X).obj M) :
    (fiber X).map ((F.mapId X).hom.toNatTrans.app M) ((restrict (𝟙 X)).app M s) = s
  restrict_comp {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
      (M : F.obj X) (s : (fiber X).obj M) :
    (fiber Z).map ((F.mapComp f g).hom.toNatTrans.app M) ((restrict (f ≫ g)).app M s) =
      (restrict g).app ((F.map f).toFunctor.obj M) ((restrict f).app M s)

namespace FiberwiseSections

variable {F} (A : FiberwiseSections F)

private def pull {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) :
    (A.fiber X).Elements ⥤ (A.fiber Y).Elements where
  obj S := ⟨(F.map f).toFunctor.obj S.1, (A.restrict f).app S.1 S.2⟩
  map {S T} m := ⟨(F.map f).toFunctor.map m.1, by
    have h := congrFun ((A.restrict f).naturality m.1) S.2
    exact h.symm.trans (congrArg ((A.restrict f).app T.1) m.2)⟩
  map_id _ := Subtype.ext ((F.map f).toFunctor.map_id _)
  map_comp _ _ := Subtype.ext ((F.map f).toFunctor.map_comp _ _)

private def pullId (X : LocallyDiscrete Cᵒᵖ) : A.pull (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun S => CategoryOfElements.isoMk _ _
    ((Cat.Hom.toNatIso (F.mapId X)).app S.1) (A.restrict_id X S.1 S.2)) (by
      intro S T m
      apply Subtype.ext
      exact (F.mapId X).hom.toNatTrans.naturality m.1)

private def pullComp {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    A.pull (f ≫ g) ≅ A.pull f ⋙ A.pull g :=
  NatIso.ofComponents (fun S => CategoryOfElements.isoMk _ _
    ((Cat.Hom.toNatIso (F.mapComp f g)).app S.1) (A.restrict_comp f g S.1 S.2)) (by
      intro S T m
      apply Subtype.ext
      exact (F.mapComp f g).hom.toNatTrans.naturality m.1)

private theorem pull_eqToHom {X Y : LocallyDiscrete Cᵒᵖ} {f g : X ⟶ Y}
    (eq : f = g) (S : (A.fiber X).Elements) :
    ((eqToHom (congrArg (fun k => (A.pull k).toCatHom) eq)).toNatTrans.app S).val =
      (eqToHom (congrArg F.map eq)).toNatTrans.app S.1 := by
  subst g
  rfl

/-- The elements of every section functor, with actual transport of the
underlying objects and their sections. -/
def pseudofunctor : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,max b c} := by
  refine pseudofunctorOfIsLocallyDiscrete (fun X => Cat.of (A.fiber X).Elements)
    (fun f => (A.pull f).toCatHom) (fun X => Cat.Hom.isoMk (A.pullId X))
    (fun f g => Cat.Hom.isoMk (A.pullComp f g)) ?_ ?_ ?_
  · intro X Y Z W f g h
    let eq : (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext S
    apply Subtype.ext
    have law := (F.map₂_associator f g h).symm.trans (F.toPrelaxFunctor.map₂_eqToHom _ _ eq)
    have component := congrArg (fun t => t.toNatTrans.app S.1) law
    exact component.trans (A.pull_eqToHom eq S).symm
  · intro X Y f
    let eq : 𝟙 X ≫ f = f := Category.id_comp f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext S
    apply Subtype.ext
    have law := (F.map₂_left_unitor f).symm.trans (F.toPrelaxFunctor.map₂_eqToHom _ _ eq)
    have component := congrArg (fun t => t.toNatTrans.app S.1) law
    exact component.trans (A.pull_eqToHom eq S).symm
  · intro X Y f
    let eq : f ≫ 𝟙 Y = f := Category.comp_id f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext S
    apply Subtype.ext
    have law := (F.map₂_right_unitor f).symm.trans (F.toPrelaxFunctor.map₂_eqToHom _ _ eq)
    have component := congrArg (fun t => t.toNatTrans.app S.1) law
    exact component.trans (A.pull_eqToHom eq S).symm

private theorem mapComp'_hom_projects {X Y Z : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (r : f ≫ g = k) (S : (A.fiber X).Elements) :
    ((A.pseudofunctor.mapComp' f g k r).hom.toNatTrans.app S).val =
      (F.mapComp' f g k r).hom.toNatTrans.app S.1 := by
  subst k
  rw [mapComp'_eq_mapComp, mapComp'_eq_mapComp]
  rfl

private theorem mapComp'_inv_projects {X Y Z : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (r : f ≫ g = k) (S : (A.fiber X).Elements) :
    ((A.pseudofunctor.mapComp' f g k r).inv.toNatTrans.app S).val =
      (F.mapComp' f g k r).inv.toNatTrans.app S.1 := by
  subst k
  rw [mapComp'_eq_mapComp, mapComp'_eq_mapComp]
  rfl

private theorem pullHom_projects {X₁ X₂ Y Y' : C}
    {M : (A.fiber (.mk (op X₁))).Elements} {N : (A.fiber (.mk (op X₂))).Elements}
    {p : Y ⟶ X₁} {q : Y ⟶ X₂}
    (e : (A.pseudofunctor.map p.op.toLoc).toFunctor.obj M ⟶
      (A.pseudofunctor.map q.op.toLoc).toFunctor.obj N) (r : Y' ⟶ Y)
    (p' : Y' ⟶ X₁) (q' : Y' ⟶ X₂) (hp : r ≫ p = p') (hq : r ≫ q = q') :
    (pullHom (F := A.pseudofunctor) e r p' q' hp hq).val =
      pullHom (F := F) e.val r p' q' hp hq := by
  let ep := congrArg (fun m : Y' ⟶ X₁ => m.op.toLoc) hp
  let eq := congrArg (fun m : Y' ⟶ X₂ => m.op.toLoc) hq
  change ((A.pseudofunctor.mapComp' p.op.toLoc r.op.toLoc p'.op.toLoc ep).hom.toNatTrans.app M).val ≫
    (F.map r.op.toLoc).toFunctor.map e.val ≫
    ((A.pseudofunctor.mapComp' q.op.toLoc r.op.toLoc q'.op.toLoc eq).inv.toNatTrans.app N).val = _
  rw [A.mapComp'_hom_projects, A.mapComp'_inv_projects]
  rfl

section Descent

variable {X : C} {I : Type*} {U : I → C} (f : ∀ i, U i ⟶ X)

/-- Discard a section and its preservation condition from the actual
descent datum in every original component and on every test object. -/
def underlyingDatum (D : A.pseudofunctor.DescentData f) : F.DescentData f where
  obj i := (D.obj i).1
  hom _ q i j p r hp hr := (D.hom q (i₁ := i) (i₂ := j) p r hp hr).val
  pullHom_hom Y' Y g q q' hq i j p r hp hr p' r' hp' hr' := by
    have equal := D.pullHom_hom g q q' hq (i₁ := i) (i₂ := j) p r hp hr p' r' hp' hr'
    exact (A.pullHom_projects _ g p' r' hp' hr').symm.trans (congrArg Subtype.val equal)
  hom_self _ q i p hp := congrArg Subtype.val (D.hom_self q (i := i) p hp)
  hom_comp _ q i j k p r s hp hr hs :=
    congrArg Subtype.val (D.hom_comp q (i₁ := i) (i₂ := j) (i₃ := k) p r s hp hr hs)

private theorem canonical_hom_projects (M : (A.fiber (.mk (op X))).Elements)
    {Y : C} (q : Y ⟶ X) {i j : I} (p : Y ⟶ U i) (r : Y ⟶ U j)
    (hp : p ≫ f i = q) (hr : r ≫ f j = q) :
    (((A.pseudofunctor.toDescentData f).obj M).hom q p r hp hr).val =
      ((F.toDescentData f).obj M.1).hom q p r hp hr := by
  let ep := congrArg (fun a : Y ⟶ X => a.op.toLoc) hp
  let er := congrArg (fun a : Y ⟶ X => a.op.toLoc) hr
  change ((A.pseudofunctor.mapComp' (f i).op.toLoc p.op.toLoc q.op.toLoc ep).inv.toNatTrans.app M).val ≫
    ((A.pseudofunctor.mapComp' (f j).op.toLoc r.op.toLoc q.op.toLoc er).hom.toNatTrans.app M).val = _
  rw [A.mapComp'_inv_projects, A.mapComp'_hom_projects]
  rfl

/-- A section of the restriction of the global object on each cover component. -/
abbrev localSections (M : F.obj (.mk (op X))) :=
  ∀ i, (A.fiber (.mk (op (U i)))).obj ((F.map (f i).op.toLoc).toFunctor.obj M)

/-- Restrict a section of a global object to every covering component. -/
def canonicalLocal (M : F.obj (.mk (op X))) (s : (A.fiber (.mk (op X))).obj M) :
    A.localSections f M :=
  fun i => (A.restrict (f i).op.toLoc).app M s

private theorem canonicalLocal_compatible (M : (A.fiber (.mk (op X))).Elements) {Y : C}
    (q : Y ⟶ X) {i j : I} (p : Y ⟶ U i) (r : Y ⟶ U j)
    (hp : p ≫ f i = q) (hr : r ≫ f j = q) :
    (A.fiber (.mk (op Y))).map (((F.toDescentData f).obj M.1).hom q p r hp hr)
      ((A.restrict p.op.toLoc).app _ (A.canonicalLocal f M.1 M.2 i)) =
    (A.restrict r.op.toLoc).app _ (A.canonicalLocal f M.1 M.2 j) := by
  rw [← A.canonical_hom_projects f M q p r hp hr]
  exact (((A.pseudofunctor.toDescentData f).obj M).hom q p r hp hr).property

/-- The section descent condition for one actual family over a fixed global
object: compatible local sections have a unique global preimage. -/
def HasSectionDescent : Prop :=
  ∀ (M : F.obj (.mk (op X))) (s : A.localSections f M),
    (∀ (Y : C) (q : Y ⟶ X) (i j : I) (p : Y ⟶ U i) (r : Y ⟶ U j)
      (hp : p ≫ f i = q) (hr : r ≫ f j = q),
      (A.fiber (.mk (op Y))).map (((F.toDescentData f).obj M).hom q p r hp hr)
        ((A.restrict p.op.toLoc).app _ (s i)) = (A.restrict r.op.toLoc).app _ (s j)) →
    ∃! t, ∀ i, A.canonicalLocal f M t i = s i

private theorem canonicalLocal_injective (sections : A.HasSectionDescent f)
    (M : F.obj (.mk (op X))) : Function.Injective (A.canonicalLocal f M) := by
  intro s t eq
  obtain ⟨x, _, unique⟩ := sections M (A.canonicalLocal f M t) fun _ q _ _ p r hp hr =>
    A.canonicalLocal_compatible f ⟨M, t⟩ q p r hp hr
  exact (unique s (congrFun eq)).trans (unique t (fun _ => rfl)).symm

private def underlyingCanonicalMap (M N : (A.fiber (.mk (op X))).Elements)
    (m : (A.pseudofunctor.toDescentData f).obj M ⟶ (A.pseudofunctor.toDescentData f).obj N) :
    (F.toDescentData f).obj M.1 ⟶ (F.toDescentData f).obj N.1 where
  hom i := (m.hom i).val
  comm Y q i j p r hp hr := by
    rw [← A.canonical_hom_projects f M q p r hp hr, ← A.canonical_hom_projects f N q p r hp hr]
    exact congrArg Subtype.val (m.comm q p r hp hr)

private def comparisonFullyFaithful (sections : A.HasSectionDescent f)
    (ff : (F.toDescentData f).FullyFaithful) :
    (A.pseudofunctor.toDescentData f).FullyFaithful where
  preimage {M N} m := by
    let h := A.underlyingCanonicalMap f M N m
    let k := ff.preimage h
    have proj (i : I) : (F.map (f i).op.toLoc).toFunctor.map k = (m.hom i).val :=
      congrArg (fun a => a.hom i) (ff.map_preimage h)
    refine ⟨k, A.canonicalLocal_injective f sections N.1 ?_⟩
    funext i
    have natural := congrFun ((A.restrict (f i).op.toLoc).naturality k) M.2
    change (A.canonicalLocal f N.1 ((A.fiber (.mk (op X))).map k M.2)) i = _
    change (A.canonicalLocal f N.1 ((A.fiber (.mk (op X))).map k M.2)) i =
      (A.fiber (.mk (op (U i)))).map ((F.map (f i).op.toLoc).toFunctor.map k)
        (A.canonicalLocal f M.1 M.2 i) at natural
    exact natural.trans ((congrArg (fun a => (A.fiber (.mk (op (U i)))).map a
      (A.canonicalLocal f M.1 M.2 i)) (proj i)).trans (m.hom i).property)
  map_preimage {M N} m := by
    apply DescentData.hom_ext
    intro i
    apply Subtype.ext
    exact congrArg (fun a => a.hom i) (ff.map_preimage (A.underlyingCanonicalMap f M N m))
  preimage_map {M N} m := by
    apply Subtype.ext
    let h := A.underlyingCanonicalMap f M N ((A.pseudofunctor.toDescentData f).map m)
    have same : h = (F.toDescentData f).map m.val := by
      apply DescentData.hom_ext
      intro i
      rfl
    change ff.preimage h = m.val
    rw [same, ff.preimage_map]

private def transportedLocal {D : A.pseudofunctor.DescentData f} {M : F.obj (.mk (op X))}
    (e : A.underlyingDatum f D ≅ (F.toDescentData f).obj M) : A.localSections f M :=
  fun i => (A.fiber (.mk (op (U i)))).map (e.hom.hom i) (D.obj i).2

private theorem transportedLocal_compatible
    {D : A.pseudofunctor.DescentData f} {M : F.obj (.mk (op X))}
    (e : A.underlyingDatum f D ≅ (F.toDescentData f).obj M)
    (Y : C) (q : Y ⟶ X) (i j : I) (p : Y ⟶ U i) (r : Y ⟶ U j)
    (hp : p ≫ f i = q) (hr : r ≫ f j = q) :
    (A.fiber (.mk (op Y))).map (((F.toDescentData f).obj M).hom q p r hp hr)
      ((A.restrict p.op.toLoc).app _ (A.transportedLocal f e i)) =
      (A.restrict r.op.toLoc).app _ (A.transportedLocal f e j) := by
  let P := A.fiber (.mk (op Y))
  let pi := e.hom.hom i
  let pj := e.hom.hom j
  let a := (A.restrict p.op.toLoc).app _ (D.obj i).2
  let b := (A.restrict r.op.toLoc).app _ (D.obj j).2
  have natural_p : (A.restrict p.op.toLoc).app _ (A.transportedLocal f e i) =
      P.map ((F.map p.op.toLoc).toFunctor.map pi) a :=
    congrFun ((A.restrict p.op.toLoc).naturality pi) (D.obj i).2
  have natural_r : (A.restrict r.op.toLoc).app _ (A.transportedLocal f e j) =
      P.map ((F.map r.op.toLoc).toFunctor.map pj) b :=
    congrFun ((A.restrict r.op.toLoc).naturality pj) (D.obj j).2
  have compatible : P.map ((A.underlyingDatum f D).hom q p r hp hr) a = b :=
    (D.hom q p r hp hr).property
  let d := ((F.toDescentData f).obj M).hom q p r hp hr
  let k := (A.underlyingDatum f D).hom q p r hp hr
  let pm := (F.map p.op.toLoc).toFunctor.map pi
  let rm := (F.map r.op.toLoc).toFunctor.map pj
  have comm : pm ≫ d = k ≫ rm := e.hom.comm q p r hp hr
  change P.map d ((A.restrict p.op.toLoc).app ((F.map (f i).op.toLoc).toFunctor.obj M)
    (A.transportedLocal f e i)) =
    (A.restrict r.op.toLoc).app ((F.map (f j).op.toLoc).toFunctor.obj M) (A.transportedLocal f e j)
  calc
    _ = P.map d (P.map pm a) := congrArg (P.map d) natural_p
    _ = P.map (pm ≫ d) a := (FunctorToTypes.map_comp_apply P pm d a).symm
    _ = P.map (k ≫ rm) a := congrArg (fun l => P.map l a) comm
    _ = P.map rm (P.map k a) := FunctorToTypes.map_comp_apply P k rm a
    _ = P.map rm b := congrArg (P.map rm) compatible
    _ = _ := natural_r.symm

private def componentIso {D D' : F.DescentData f} (e : D ≅ D') (i : I) : D.obj i ≅ D'.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := congrArg (fun k => k.hom i) e.hom_inv_id
  inv_hom_id := congrArg (fun k => k.hom i) e.inv_hom_id

private theorem comparison_essentiallySurjective (sections : A.HasSectionDescent f)
    (base : (F.toDescentData f).EssSurj) : (A.pseudofunctor.toDescentData f).EssSurj where
  mem_essImage D := by
    obtain ⟨M, ⟨e⟩⟩ := base.mem_essImage (A.underlyingDatum f D)
    obtain ⟨t, ht, _⟩ := sections M (A.transportedLocal f e.symm)
      (A.transportedLocal_compatible f e.symm)
    let N : (A.fiber (.mk (op X))).Elements := ⟨M, t⟩
    let E : ∀ i, D.obj i ≅ ((A.pseudofunctor.toDescentData f).obj N).obj i :=
      fun i => CategoryOfElements.isoMk _ _ (componentIso f e.symm i) (ht i).symm
    have agrees (Y : C) (q : Y ⟶ X) (i j : I) (p : Y ⟶ U i) (r : Y ⟶ U j)
        (hp : p ≫ f i = q) (hr : r ≫ f j = q) :
        (A.pseudofunctor.map p.op.toLoc).toFunctor.map (E i).hom ≫
          ((A.pseudofunctor.toDescentData f).obj N).hom q p r hp hr =
        D.hom q p r hp hr ≫ (A.pseudofunctor.map r.op.toLoc).toFunctor.map (E j).hom := by
      apply Subtype.ext
      change (F.map p.op.toLoc).toFunctor.map (e.inv.hom i) ≫
          (((A.pseudofunctor.toDescentData f).obj N).hom q p r hp hr).val =
        (D.hom q p r hp hr).val ≫ (F.map r.op.toLoc).toFunctor.map (e.inv.hom j)
      rw [A.canonical_hom_projects f N q p r hp hr]
      exact e.inv.comm q p r hp hr
    exact ⟨N, ⟨(DescentData.isoMk E agrees).symm⟩⟩

/-- When objects and their sections satisfy effective descent, pairs
of an object and a section satisfy the comparison equivalence. -/
theorem comparison_isEquivalence (sections : A.HasSectionDescent f)
    [(F.toDescentData f).IsEquivalence] : (A.pseudofunctor.toDescentData f).IsEquivalence := by
  let ff := A.comparisonFullyFaithful f sections
    (Functor.FullyFaithful.ofFullyFaithful (F.toDescentData f))
  haveI := ff.full
  haveI := ff.faithful
  haveI := A.comparison_essentiallySurjective f sections (inferInstanceAs (F.toDescentData f).EssSurj)
  exact { }

end Descent

end FiberwiseSections

end

end SHIGURE.SchemeDescent
