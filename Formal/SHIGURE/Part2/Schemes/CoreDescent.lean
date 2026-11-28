import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-! # Maximal subgroupoids and effective descent

Lemma 6.2 first descends realizations and all structure-preserving maps.
Its groupoid statement is obtained by applying the actual categorical
core, retaining the category with noninvertible maps as the source theory.

## Implementation notes

We use mathlib's `Core`, `Functor.core`, `Iso.core`, and `Equivalence.core`.
The equivalence of descent categories uses the transition isomorphisms
already constructed by `Pseudofunctor.DescentData.iso`; no invertibility
of arbitrary maps in the original fibers is assumed.
-/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe t u v a b

variable {C : Type u} [Category.{v} C]

private theorem core_eqToHom_hom {D : Type b} [Category.{a} D]
    {M N : Core D} (h : M = N) :
    (eqToHom h).iso.hom = eqToHom (congrArg Core.of h) := by
  cases h
  rfl

/-- Taking maximal subgroupoids fiberwise, with the actual core functors
and the core images of the original scalar-change coherences. -/
def corePseudofunctor
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b}) :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Core (F.obj (.mk X))))
    (fun f => (F.map f.toLoc).toFunctor.core.toCatHom)
    (fun X => Cat.Hom.isoMk
      ((Cat.Hom.toNatIso (F.mapId (.mk X))).core ≪≫ Functor.coreId _))
    (fun f g => Cat.Hom.isoMk
      ((Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).core ≪≫
        Functor.coreComp (F.map f.toLoc).toFunctor (F.map g.toLoc).toFunctor))
    ?_ ?_ ?_
  · intro X Y Z W f g h
    ext1
    apply NatTrans.ext
    funext M
    apply Core.hom_ext
    dsimp
    rw [Cat.eqToHom_app, core_eqToHom_hom]
    simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      Cat.associator_hom_app, Strict.associator_eqToIso, eqToIso.hom,
      PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app, eqToHom_refl,
      Category.comp_id, Category.id_comp, core_eqToHom_hom] using congrArg
      (fun z => z.toNatTrans.app M.of) (F.map₂_associator f.toLoc g.toLoc h.toLoc).symm
  · intro X Y f
    ext1
    apply NatTrans.ext
    funext M
    apply Core.hom_ext
    dsimp
    rw [Cat.eqToHom_app, core_eqToHom_hom]
    simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.leftUnitor_hom_app,
      Strict.leftUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
      Cat.eqToHom_app, eqToHom_refl, Category.comp_id, core_eqToHom_hom] using congrArg
      (fun z => z.toNatTrans.app M.of) (F.map₂_left_unitor f.toLoc).symm
  · intro X Y f
    ext1
    apply NatTrans.ext
    funext M
    apply Core.hom_ext
    dsimp
    rw [Cat.eqToHom_app, core_eqToHom_hom]
    simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.rightUnitor_hom_app,
      Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
      Cat.eqToHom_app, eqToHom_refl, Category.comp_id, core_eqToHom_hom] using congrArg
      (fun z => z.toNatTrans.app M.of) (F.map₂_right_unitor f.toLoc).symm

private theorem core_mapComp'_hom_hom
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b})
    {A B D : LocallyDiscrete Cᵒᵖ} (f : A ⟶ B) (g : B ⟶ D) (fg : A ⟶ D)
    (hfg : f ≫ g = fg) (M : Core (F.obj A)) :
    (((corePseudofunctor F).mapComp' f g fg hfg).hom.toNatTrans.app M).iso.hom =
      (F.mapComp' f g fg hfg).hom.toNatTrans.app M.of := by
  subst fg
  simp only [mapComp'_eq_mapComp]
  dsimp [corePseudofunctor]
  simp
  cases f
  cases g
  rfl

private theorem core_mapComp'_inv_hom
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b})
    {A B D : LocallyDiscrete Cᵒᵖ} (f : A ⟶ B) (g : B ⟶ D) (fg : A ⟶ D)
    (hfg : f ≫ g = fg) (M : Core (F.obj A)) :
    (((corePseudofunctor F).mapComp' f g fg hfg).inv.toNatTrans.app M).iso.hom =
      (F.mapComp' f g fg hfg).inv.toNatTrans.app M.of := by
  subst fg
  simp only [mapComp'_eq_mapComp]
  dsimp [corePseudofunctor]
  simp
  cases f
  cases g
  rfl

private theorem core_pullHom_hom
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b})
    {X₁ X₂ Y Y' : C} {M₁ : Core (F.obj (.mk (op X₁)))}
    {M₂ : Core (F.obj (.mk (op X₂)))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : ((corePseudofunctor F).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((corePseudofunctor F).map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).iso.hom =
      pullHom (F := F) φ.iso.hom g gf₁ gf₂ hgf₁ hgf₂ := by
  change
    (((corePseudofunctor F).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc _).hom.toNatTrans.app M₁).iso.hom ≫
      (F.map g.op.toLoc).toFunctor.map φ.iso.hom ≫
        (((corePseudofunctor F).mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc _).inv.toNatTrans.app M₂).iso.hom = _
  rw [core_mapComp'_hom_hom, core_mapComp'_inv_hom]
  rfl

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b})
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- An ordinary descent object supplies a core descent object: its
transition morphisms are the actual isomorphisms forced by the cocycle. -/
def coreDescentOfObj (D : F.DescentData f) : (corePseudofunctor F).DescentData f where
  obj i := ⟨D.obj i⟩
  hom _ q _ _ a b ha hb := ⟨D.iso q a b ha hb⟩
  pullHom_hom Y' Y g q q' hq i j a b ha hb ga gb hga hgb := by
    apply Core.hom_ext
    rw [core_pullHom_hom]
    exact D.pullHom_hom g q q' hq a b ha hb ga gb hga hgb
  hom_self Y q i a ha := by
    apply Core.hom_ext
    exact D.hom_self q a ha
  hom_comp Y q i j k a b c ha hb hc := by
    apply Core.hom_ext
    exact D.hom_comp q a b c ha hb hc

/-- Forget the core wrappers on a descent object, retaining its actual
objects and the underlying transition morphisms. -/
def forgetCoreDescentObj (D : (corePseudofunctor F).DescentData f) : F.DescentData f where
  obj i := (D.obj i).of
  hom _ q _ _ a b ha hb := (D.hom q a b ha hb).iso.hom
  pullHom_hom Y' Y g q q' hq i j a b ha hb ga gb hga hgb := by
    have equal := congrArg (fun z => z.iso.hom)
      (D.pullHom_hom g q q' hq a b ha hb ga gb hga hgb)
    dsimp only at equal
    rw [core_pullHom_hom] at equal
    exact equal
  hom_self Y q i a ha := congrArg (fun z => z.iso.hom) (D.hom_self q a ha)
  hom_comp Y q i j k a b c ha hb hc :=
    congrArg (fun z => z.iso.hom) (D.hom_comp q a b c ha hb hc)

/-- Evaluation at one member of a descent covering family. This connects
core morphisms of descent data to their actual component isomorphisms. -/
def descentEvaluation (i : ι) : F.DescentData f ⥤ F.obj (.mk (op (X i))) where
  obj D := D.obj i
  map a := a.hom i

/-- Core morphisms of ordinary descent objects induce descent morphisms
whose components are the actual component isomorphisms. -/
def coreDescentFunctor : Core (F.DescentData f) ⥤ (corePseudofunctor F).DescentData f where
  obj D := coreDescentOfObj F f D.of
  map a :=
    { hom i := ⟨(descentEvaluation F f i).mapIso a.iso⟩
      comm Y q i j p r hp hr := by
        apply Core.hom_ext
        exact a.iso.hom.comm q p r hp hr }
  map_id D := by
    apply DescentData.hom_ext
    intro i
    apply Core.hom_ext
    rfl
  map_comp a b := by
    apply DescentData.hom_ext
    intro i
    apply Core.hom_ext
    rfl

/-- A morphism of core descent data gives an isomorphism of ordinary
descent data, using its component isomorphisms and their commuting squares. -/
def coreDescentInverse : (corePseudofunctor F).DescentData f ⥤ Core (F.DescentData f) where
  obj D := ⟨forgetCoreDescentObj F f D⟩
  map a := ⟨DescentData.isoMk (fun i => (a.hom i).iso) (by
    intro Y q i j p r hp hr
    exact congrArg (fun z => z.iso.hom) (a.comm q p r hp hr))⟩
  map_id D := by
    apply Core.hom_ext
    apply DescentData.hom_ext
    intro i
    rfl
  map_comp a b := by
    apply Core.hom_ext
    apply DescentData.hom_ext
    intro i
    rfl

/-- The ordinary descent object is recovered with the identity at every
cover component after passing to core descent data and back. -/
def coreDescentUnitIso :
    𝟭 (Core (F.DescentData f)) ≅ coreDescentFunctor F f ⋙ coreDescentInverse F f :=
  NatIso.ofComponents (fun D => Core.isoMk
    (DescentData.isoMk (fun i => Iso.refl (D.of.obj i)) (by
      intro Y q i j p r hp hr
      simp only [Iso.refl_hom]
      erw [(F.map p.op.toLoc).toFunctor.map_id, (F.map r.op.toLoc).toFunctor.map_id,
        Category.id_comp, Category.comp_id]
      rfl))) (by
        intro D E a
        apply Core.hom_ext
        apply DescentData.hom_ext
        intro i
        simp [coreDescentFunctor, coreDescentInverse, coreDescentOfObj, forgetCoreDescentObj,
          descentEvaluation])

/-- Core descent data are recovered with the identity at every cover
component. The transition isomorphisms agree because their hom maps agree. -/
def coreDescentCounitIso :
    coreDescentInverse F f ⋙ coreDescentFunctor F f ≅
      𝟭 ((corePseudofunctor F).DescentData f) :=
  NatIso.ofComponents (fun D => DescentData.isoMk (fun i => Iso.refl (D.obj i)) (by
    intro Y q i j p r hp hr
    simp only [Iso.refl_hom]
    erw [((corePseudofunctor F).map p.op.toLoc).toFunctor.map_id,
      ((corePseudofunctor F).map r.op.toLoc).toFunctor.map_id,
      Category.id_comp, Category.comp_id]
    apply Core.hom_ext
    rfl)) (by
      intro D E a
      apply DescentData.hom_ext
      intro i
      apply Core.hom_ext
      change (a.hom i).iso.hom ≫ 𝟙 _ = 𝟙 _ ≫ (a.hom i).iso.hom
      simp)

/-- Actual core descent data are equivalent to the core of the original
descent category. The equivalence retains every original object and the
actual invertible morphisms; it imposes no invertibility on other maps. -/
def coreDescentEquivalence : Core (F.DescentData f) ≌ (corePseudofunctor F).DescentData f where
  functor := coreDescentFunctor F f
  inverse := coreDescentInverse F f
  unitIso := coreDescentUnitIso F f
  counitIso := coreDescentCounitIso F f
  functor_unitIso_comp D := by
    apply DescentData.hom_ext
    intro i
    apply Core.hom_ext
    dsimp [coreDescentFunctor, coreDescentInverse, coreDescentUnitIso, coreDescentCounitIso,
      coreDescentOfObj, forgetCoreDescentObj, descentEvaluation]
    simp
    rfl

/-- The actual comparison for core-valued descent agrees with the core
of the ordinary comparison followed by the explicit descent equivalence.
Every component over the covering family is the identity. -/
def coreComparisonIso :
    (F.toDescentData f).core ⋙ (coreDescentEquivalence F f).functor ≅
      (corePseudofunctor F).toDescentData f :=
  NatIso.ofComponents (fun M => DescentData.isoMk
    (fun i => Iso.refl (((corePseudofunctor F).map (f i).op.toLoc).toFunctor.obj M)) (by
      intro Y q i j p r hp hr
      simp only [Iso.refl_hom]
      erw [((corePseudofunctor F).map p.op.toLoc).toFunctor.map_id,
        ((corePseudofunctor F).map r.op.toLoc).toFunctor.map_id,
        Category.id_comp, Category.comp_id]
      apply Core.hom_ext
      change
        (((corePseudofunctor F).mapComp' (f i).op.toLoc p.op.toLoc q.op.toLoc _).inv.toNatTrans.app M).iso.hom ≫
          (((corePseudofunctor F).mapComp' (f j).op.toLoc r.op.toLoc q.op.toLoc _).hom.toNatTrans.app M).iso.hom =
        (F.mapComp' (f i).op.toLoc p.op.toLoc q.op.toLoc _).inv.toNatTrans.app M.of ≫
          (F.mapComp' (f j).op.toLoc r.op.toLoc q.op.toLoc _).hom.toNatTrans.app M.of
      rw [core_mapComp'_inv_hom, core_mapComp'_hom_hom])) (by
        intro M N a
        apply DescentData.hom_ext
        intro i
        apply Core.hom_ext
        change (F.map (f i).op.toLoc).toFunctor.map a.iso.hom ≫ 𝟙 _ =
          𝟙 _ ≫ (F.map (f i).op.toLoc).toFunctor.map a.iso.hom
        simp)

/-- Effective descent of all objects and morphisms implies effective
descent of the actual maximal subgroupoids, via mathlib's core equivalence.
The sole premise is the corresponding ordinary comparison equivalence. -/
theorem coreComparison_isEquivalence [(F.toDescentData f).IsEquivalence] :
    ((corePseudofunctor F).toDescentData f).IsEquivalence := by
  let e := (F.toDescentData f).asEquivalence.core
  letI : ((F.toDescentData f).core).IsEquivalence := e.isEquivalence_functor
  letI : ((coreDescentEquivalence F f).functor).IsEquivalence :=
    (coreDescentEquivalence F f).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (coreComparisonIso F f)

/-- The maximal subgroupoids of a category-valued stack form a stack for
the same topology. This is the final groupoid step in Lemma 6.2. -/
theorem corePseudofunctor_isStack (J : GrothendieckTopology C) [F.IsStack J] :
    (corePseudofunctor F).IsStack J := by
  apply IsStack.of_isStackFor
  intro S R hR
  have ordinary := F.isStackFor' R hR
  rw [isStackFor_iff] at ordinary ⊢
  letI := ordinary
  exact coreComparison_isEquivalence F (fun (a : R.arrows.category) => a.obj.hom)

end

end SHIGURE.SchemeDescent
