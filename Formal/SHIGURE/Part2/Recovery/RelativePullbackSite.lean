import Formal.SHIGURE.Part2.Recovery.RelativeSchemeMaps

/-!
# Direct images along maps of coefficient schemes

The inverse image of a relative test is its fiber product. Pulling back
a Zariski covering gives a covering of this new test, so composing a sheaf
with this operation on tests defines its direct image.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S S' : Scheme.{u}} (f : S' ⟶ S)

/-- Taking fiber products of relative tests preserves covering sieves. -/
theorem relativeSchemePullback_coverPreserving :
    CoverPreserving (Scheme.zariskiTopology.over S) (Scheme.zariskiTopology.over S')
      (relativeSchemePullback f) where
  cover_preserve {T Q} cover := by
    rw [GrothendieckTopology.mem_over_iff] at cover ⊢
    obtain ⟨C, sub⟩ := Scheme.mem_grothendieckTopology_iff.mp cover
    let F := relativeSchemePullback f
    let T' := F.obj T
    let π : T'.left ⟶ T.left := pullback.fst T.hom f
    let D := C.pullback₁ π
    refine Scheme.mem_grothendieckTopology_iff.mpr ⟨D, ?_⟩
    rintro _ _ ⟨i⟩
    let Qi := Over.mk (C.f i ≫ T.hom)
    let gi : Qi ⟶ T := Over.homMk (C.f i)
    have hi : Q gi := (Sieve.overEquiv_iff Q (C.f i)).mp (sub _ (Presieve.ofArrows.mk i))
    let p : D.X i ⟶ T'.left := D.f i
    let q : D.X i ⟶ C.X i := C.pullbackHom π i
    have eq : q ≫ (C.f i ≫ T.hom) = (p ≫ T'.hom) ≫ f := by
      rw [← Category.assoc, C.pullbackHom_map, Category.assoc, Category.assoc]
      exact congrArg (p ≫ ·) (pullback.condition (f := T.hom) (g := f))
    let r : D.X i ⟶ (F.obj Qi).left := pullback.lift q (p ≫ T'.hom) eq
    let a : Over.mk (p ≫ T'.hom) ⟶ F.obj Qi := Over.homMk r (pullback.lift_snd _ _ _)
    apply (Sieve.overEquiv_iff (Q.functorPushforward F) p).mpr
    refine ⟨Qi, gi, a, hi, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · symm
      change (r ≫ (F.map gi).left) ≫ π = p ≫ π
      have map_fst : (F.map gi).left ≫ π = pullback.fst Qi.hom f ≫ gi.left :=
        pullback.lift_fst _ _ _
      have lift_fst : r ≫ pullback.fst Qi.hom f = q := pullback.lift_fst _ _ _
      rw [Category.assoc, map_fst, ← Category.assoc, lift_fst]
      exact C.pullbackHom_map π i
    · exact (Over.w (a ≫ F.map gi)).symm

/-- The fiber-product functor on tests can pull sheaves back by composition. -/
instance relativeSchemePullback_isContinuous :
    (relativeSchemePullback f).IsContinuous (Scheme.zariskiTopology.over S) (Scheme.zariskiTopology.over S') := by
  letI : (relativeSchemePullback f).IsRightAdjoint := (relativeSchemePullbackAdj f).isRightAdjoint
  exact CategoryTheory.Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat (Scheme.zariskiTopology.over S') (relativeSchemePullback f))
    (relativeSchemePullback_coverPreserving f)

/-- The direct image of a relative Zariski sheaf has its sections on inverse-image tests. -/
def relativeSheafDirectImage : ZariskiSheaf S' ⥤ ZariskiSheaf S :=
  (relativeSchemePullback f).sheafPushforwardContinuous _ _ _

end SHIGURE.Copying
