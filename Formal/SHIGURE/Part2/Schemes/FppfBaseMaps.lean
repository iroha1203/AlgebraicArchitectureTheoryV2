import Formal.SHIGURE.Part2.Schemes.FppfRelativeAffineSections
import Mathlib.AlgebraicGeometry.Limits

/-! # Descent of the coefficient-scheme map

Definition 6.1 regards a realization over a scheme as including a map to
the spectrum of the fixed coefficient ring. Such maps descend on arbitrary
fppf covers, including covers of nonaffine schemes.

## Implementation notes

A map from `X` to an affine scheme `Y` is the same as a section of the
projection `Y × X → X`. This projection is affine: it is the base change
of the map from `Y` to the terminal scheme `Spec ℤ`. We use the existing
effective descent theorem for sections of affine morphisms. That theorem
already performs the finite affine refinements and compatible-open gluing,
so this construction uses the same descent of actual scheme morphisms.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

/-- Compatible maps from an arbitrary fppf cover to an affine target
descend uniquely. This supplies the structural map needed in Lemma 6.2
when realizations are treated as fibers over all schemes. -/
theorem fppfAffineTargetMaps_existUnique_onAnyBase
    {X Y : Scheme.{u}} [IsAffine Y] (cover : FppfCover.{u,v} X)
    (m : ∀ i, cover.X i ⟶ Y)
    (compatible : Presieve.Arrows.Compatible (yoneda.obj Y) cover.f m) :
    ∃! g : X ⟶ Y, ∀ i, cover.f i ≫ g = m i := by
  let pX := specULiftZIsTerminal.{u}.from X
  let pY := specULiftZIsTerminal.{u}.from Y
  let h := pullback.snd pY pX
  letI : IsAffineHom pY := inferInstance
  letI : IsAffineHom h := MorphismProperty.pullback_snd _ _ inferInstance
  let localSection (i : cover.I₀) : cover.X i ⟶ pullback pY pX :=
    pullback.lift (m i) (cover.f i) (specULiftZIsTerminal.hom_ext _ _)
  have over (i : cover.I₀) : localSection i ≫ h = cover.f i :=
    pullback.lift_snd _ _ _
  have compatibleSections : Presieve.Arrows.Compatible
      (yoneda.obj (pullback pY pX)) cover.f localSection := by
    intro i j T a b w
    change a ≫ localSection i = b ≫ localSection j
    apply pullback.hom_ext
    · simp only [Category.assoc, localSection, pullback.lift_fst]
      exact compatible i j T a b w
    · simpa only [Category.assoc, localSection, pullback.lift_snd] using w
  obtain ⟨s, hs, _⟩ := relativeAffineSection_descent h localSection over compatibleSections
  let g := s ≫ pullback.fst pY pX
  have recovers (i : cover.I₀) : cover.f i ≫ g = m i := by
    change cover.f i ≫ s ≫ pullback.fst pY pX = m i
    rw [← Category.assoc, hs.2 i]
    exact pullback.lift_fst _ _ _
  exact ⟨g, recovers, fun g' hg' =>
    fppfCover_hom_ext cover (fun i => (hg' i).trans (recovers i).symm)⟩

/-- The coefficient-scheme maps in Definition 6.1 descend on every fppf
cover of every scheme. The cover and its compatible local structural maps
are the complete input data; an affine base is not required. -/
theorem fppfBaseMaps_existUnique {k : Type u} [CommRing k] {X : Scheme.{u}}
    (cover : FppfCover.{u,v} X) (m : ∀ i, cover.X i ⟶ Spec (CommRingCat.of k))
    (compatible : Presieve.Arrows.Compatible (yoneda.obj (Spec (CommRingCat.of k)))
      cover.f m) :
    ∃! g : X ⟶ Spec (CommRingCat.of k), ∀ i, cover.f i ≫ g = m i :=
  fppfAffineTargetMaps_existUnique_onAnyBase cover m compatible

end

end SHIGURE.SchemeDescent
