import Formal.SHIGURE.Part2.Recovery.CoverLifts
import Formal.SHIGURE.Part2.Recovery.StructureArrowDescent

/-!
# Overlap equations for descent of arrows

The equation for local arrows is imposed on tests over the actual
fiber product of two chart opens. Naturality then gives the matching
condition for arbitrary sections restricted from those two charts.

## Implementation notes

The equation is evaluated on a test mapping to the intersection.
This lets the two chart restrictions be compared on the same test
scheme, using identities of its underlying scheme to transport
sections. Equalities between the iterated site functors give the
same equations after evaluation.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {C : Scheme.OpenCover.{u} S} {F G : ZariskiSheaf S}

/-- The value of a local arrow on a global test that factors through the chart. -/
def chartApply {i : C.I₀} {T : Over S}
    (f : (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F ⟶
      (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj G)
    (a : CoverLift C i T) (x : F.val.obj (op T)) : G.val.obj (op T) :=
  G.val.map a.toBase.inv.op (f.val.app (op a.test) (F.val.map a.toBase.hom.op x))

private theorem chartApply_natural {i : C.I₀} {T U : Over S}
    (f : (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F ⟶
      (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj G)
    (a : CoverLift C i T) (b : CoverLift C i U) (g : U ⟶ T) (x : F.val.obj (op T)) :
    G.val.map g.op (chartApply f a x) = chartApply f b (F.val.map g.op x) := by
  let v := a.map b g
  let p := (Over.map (C.f i)).map v
  have h₁ : p ≫ a.toBase.hom = b.toBase.hom ≫ g := by
    apply Over.OverMorphism.ext
    change g.left ≫ 𝟙 T.left = 𝟙 U.left ≫ g.left
    rw [Category.comp_id, Category.id_comp]
  have h₂ : g ≫ a.toBase.inv = b.toBase.inv ≫ p := by
    apply Over.OverMorphism.ext
    change g.left ≫ 𝟙 T.left = 𝟙 U.left ≫ g.left
    rw [Category.comp_id, Category.id_comp]
  have hF : F.val.map b.toBase.hom.op (F.val.map g.op x) = F.val.map p.op (F.val.map a.toBase.hom.op x) := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, h₁]
  have hN := FunctorToTypes.naturality _ _ f.val v.op (F.val.map a.toBase.hom.op x)
  change f.val.app (op b.test) (F.val.map p.op (F.val.map a.toBase.hom.op x)) =
    G.val.map p.op (f.val.app (op a.test) (F.val.map a.toBase.hom.op x)) at hN
  unfold chartApply
  rw [hF, hN, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, h₂]

private theorem chartApply_ofTest {i : C.I₀} (T : Over (C.X i))
    (f : (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F ⟶
      (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj G)
    (x : F.val.obj (op ((Over.map (C.f i)).obj T))) :
    chartApply f (CoverLift.ofTest T) x = f.val.app (op T) x := by
  obtain ⟨W, p, rfl⟩ := Over.mk_surjective T
  let T := Over.mk p
  let V := (Over.map (C.f i)).obj T
  let a := CoverLift.ofTest T
  have hh : a.toBase.hom = 𝟙 V := Over.OverMorphism.ext rfl
  have hi : a.toBase.inv = 𝟙 V := Over.OverMorphism.ext rfl
  change G.val.map a.toBase.inv.op (f.val.app (op T) (F.val.map a.toBase.hom.op x)) = _
  rw [hh, hi, op_id, FunctorToTypes.map_id_apply]
  exact FunctorToTypes.map_id_apply G.val (X := op V) (f.val.app (op T) x)

private def firstOverlapLift {i j : C.I₀} {T : Over S}
    (p : T.left ⟶ pullback (C.f i) (C.f j)) (h : p ≫ pullback.fst _ _ ≫ C.f i = T.hom) : CoverLift C i T :=
  ⟨p ≫ pullback.fst _ _, (Category.assoc _ _ _).trans h⟩

private def secondOverlapLift {i j : C.I₀} {T : Over S}
    (p : T.left ⟶ pullback (C.f i) (C.f j)) (h : p ≫ pullback.fst _ _ ≫ C.f i = T.hom) : CoverLift C j T :=
  ⟨p ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition]; exact h⟩

/-- Local arrows agree on all relative tests over each actual chart intersection. -/
def SheafArrowsAgreeOnOverlaps
    (f : ∀ i, (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F ⟶
      (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj G) : Prop :=
  ∀ (i j : C.I₀) (T : Over S) (p : T.left ⟶ pullback (C.f i) (C.f j))
    (hp : p ≫ pullback.fst _ _ ≫ C.f i = T.hom) (x : F.val.obj (op T)),
    chartApply (f i) (firstOverlapLift p hp) x = chartApply (f j) (secondOverlapLift p hp) x

private theorem chartApply_restrictGlobal {i : C.I₀} {T : Over S} (f : F ⟶ G)
    (a : CoverLift C i T) (x : F.val.obj (op T)) :
    chartApply ((Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map f) a x =
      f.val.app (op T) x := by
  change G.val.map a.toBase.inv.op (f.val.app _ (F.val.map a.toBase.hom.op x)) = _
  rw [FunctorToTypes.naturality _ _ f.val, ← FunctorToTypes.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
    FunctorToTypes.map_id_apply]

/-- Restrictions of a single global arrow satisfy the overlap equations. -/
theorem sheafArrowsAgreeOnOverlaps_ofGlobal (f : F ⟶ G) :
    SheafArrowsAgreeOnOverlaps (fun i => (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map f) := by
  intro i j T p hp x
  rw [chartApply_restrictGlobal, chartApply_restrictGlobal]

/-- The overlap equations imply the matching conditions for gluing local sheaf maps. -/
def LocalSheafMaps.ofOverlaps
    (f : ∀ i, (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F ⟶
      (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj G)
    (w : SheafArrowsAgreeOnOverlaps f) : LocalSheafMaps C F G where
  onOpen := f
  agree i j T U V a b x y e := by
    let a₀ := CoverLift.ofTest U
    let b₀ := CoverLift.ofTest V
    let a₁ := a₀.pullback a
    let b₁ := b₀.pullback b
    let p := (a₁.overlapTest b₁).hom
    have hp : p ≫ pullback.fst (C.f i) (C.f j) ≫ C.f i = T.hom := by
      change pullback.lift a₁.val b₁.val (a₁.property.trans b₁.property.symm) ≫
        pullback.fst (C.f i) (C.f j) ≫ C.f i = T.hom
      rw [← Category.assoc, pullback.lift_fst, a₁.property]
    have ha := chartApply_natural (f i) a₀ a₁ a x
    have hb := chartApply_natural (f j) b₀ b₁ b y
    rw [chartApply_ofTest] at ha hb
    have he := w i j T p hp (F.val.map b.op y)
    have h₁ : firstOverlapLift p hp = a₁ := Subsingleton.elim _ _
    have h₂ : secondOverlapLift p hp = b₁ := Subsingleton.elim _ _
    rw [h₁, h₂] at he
    exact ha.trans ((congrArg (chartApply (f i) a₁) e).trans (he.trans hb.symm))

/-- A family of local structure maps matching on all chart intersections has a unique global extension. -/
theorem existsUnique_structureMap_ofOverlaps {sig : Signature.{u}}
    {A B : SheafStructure sig (Scheme.zariskiTopology.over S)}
    (f : ∀ i, restrictStructure (C.f i) A ⟶ restrictStructure (C.f i) B)
    (w : ∀ s, SheafArrowsAgreeOnOverlaps (fun i => (f i).onSort s)) :
    ∃! m : A ⟶ B, ∀ i, restrictStructureMap (C.f i) m = f i :=
  (show LocalStructureMaps C A B from
      ⟨f, fun s => (LocalSheafMaps.ofOverlaps (fun i => (f i).onSort s) (w s)).agree⟩).existsUnique_glue

end SHIGURE.Copying
