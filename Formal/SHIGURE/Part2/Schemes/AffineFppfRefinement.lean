import Formal.SHIGURE.Part2.CoefficientDescent
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Finite faithfully flat refinements over an affine scheme

The open images of the affine pieces of an fppf cover have a finite
subcover of an affine base. The coproduct of those pieces is the spectrum
of their product ring. Its structural map is faithfully flat.

## Implementation notes

The refinement retains the actual factorizations into the given cover.
The coproduct comparison identifies the actual component maps to the
affine base. This gives the coefficient algebra for Lemma B.4.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

/-- The component condition for an fppf cover. -/
abbrev FppfComponent : MorphismProperty Scheme.{u} :=
  @Flat ⊓ @LocallyOfFinitePresentation

/-- A jointly surjective family of flat, locally finitely presented morphisms. -/
abbrev FppfCover (X : Scheme.{u}) := X.Cover (Scheme.precoverage FppfComponent)

variable {R : CommRingCat.{u}} {cover : FppfCover (Spec R)}

/-- A finite affine refinement with its factorization into the original cover. -/
structure AffineRefinement (cover : FppfCover (Spec R)) where
  /-- An affine cover with the same component condition. -/
  affine : Scheme.AffineCover.{u} FppfComponent (Spec R)
  /-- The selected map into the original cover. -/
  over : affine.cover ⟶ cover
  /-- There are finitely many affine pieces. -/
  finite : Finite affine.I₀
  /-- Each comparison into the original component is an open immersion. -/
  openImmersion (i : affine.I₀) : IsOpenImmersion (over.h₀ i)

/-- Universal openness and compactness give a finite affine refinement of an fppf cover of a spectrum. -/
theorem affineRefinement_exists (cover : FppfCover (Spec R)) : Nonempty (AffineRefinement cover) := by
  have openMaps (i : cover.I₀) : IsOpenMap (cover.f i) := by
    letI : Flat (cover.f i) := (cover.map_prop i).1
    letI : LocallyOfFinitePresentation (cover.f i) := (cover.map_prop i).2
    exact (cover.f i).isOpenMap
  letI : QuasiCompactCover cover.toPreZeroHypercover := QuasiCompactCover.of_isOpenMap openMaps
  obtain ⟨affine, over, finite, isOpen⟩ := QuasiCompactCover.exists_hom cover
  exact ⟨⟨affine, over, finite, isOpen⟩⟩

/-- A chosen finite affine refinement, retaining the original cover maps. -/
def affineRefinement (cover : FppfCover (Spec R)) : AffineRefinement cover :=
  Classical.choice (affineRefinement_exists cover)

namespace AffineRefinement

variable (F : AffineRefinement cover)

/-- The ring map of an individual affine piece. -/
def componentMap (i : F.affine.I₀) : R ⟶ F.affine.X i :=
  (Scheme.Spec.preimage (F.affine.f i)).unop

/-- Taking Spec recovers the selected component map. -/
theorem spec_componentMap (i : F.affine.I₀) :
    Spec.map (F.componentMap i) = F.affine.f i :=
  Scheme.Spec.map_preimage _

/-- The coefficient ring is the product of the selected affine rings. -/
abbrev productRing : CommRingCat.{u} := .of (∀ i, F.affine.X i)

/-- The structural ring map of the product has the selected component maps as projections. -/
def productMap : R ⟶ F.productRing :=
  CommRingCat.ofHom (Pi.ringHom (fun i => (F.componentMap i).hom))

/-- Projection gives the chosen component's coefficient map. -/
theorem productMap_eval (i : F.affine.I₀) :
    F.productMap ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) = F.componentMap i := by
  ext x
  rfl

/-- The finite coproduct of affine pieces is the spectrum of their product. -/
def productSpecIso : (∐ fun i => Spec (F.affine.X i)) ≅ Spec F.productRing :=
  letI : Finite F.affine.I₀ := F.finite
  asIso (sigmaSpec F.affine.X)

/-- The finite coproduct comparison commutes with the structural maps to the base. -/
theorem productSpec_over :
    sigmaSpec F.affine.X ≫ Spec.map F.productMap = Sigma.desc F.affine.f := by
  apply Sigma.hom_ext
  intro i
  rw [ι_sigmaSpec_assoc, Sigma.ι_desc, ← Spec.map_comp, F.productMap_eval, F.spec_componentMap]

private theorem sigma_surjective : Surjective (Sigma.desc F.affine.f) := by
  constructor
  intro x
  obtain ⟨y, hy⟩ := F.affine.covers x
  refine ⟨Sigma.ι (fun i => Spec (F.affine.X i)) (F.affine.idx x) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, hy]

/-- Flatness is local on the coproduct source, and the selected components cover the base. -/
theorem product_flat_surjective :
    Flat (Spec.map F.productMap) ∧ Surjective (Spec.map F.productMap) := by
  letI : Finite F.affine.I₀ := F.finite
  have flat : Flat (Sigma.desc F.affine.f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Flat) fun i => (F.affine.map_prop i).1
  rw [← F.productSpec_over] at flat
  have surjective := F.sigma_surjective
  rw [← F.productSpec_over] at surjective
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso @Flat (sigmaSpec F.affine.X) _).1 flat,
    Surjective.of_comp (sigmaSpec F.affine.X) _⟩

/-- The finite product carries its actual simultaneous algebra structure. -/
instance productAlgebra : Algebra R F.productRing := F.productMap.hom.toAlgebra

/-- The selected product is faithfully flat over the base. -/
instance productFaithfullyFlat : Module.FaithfullyFlat R F.productRing :=
  RingHom.faithfullyFlat_algebraMap_iff.1 ((flat_and_surjective_SpecMap_iff F.productMap).1 F.product_flat_surjective)

/-- The finite coefficient algebra supplies the effective descent equivalence. -/
def descentEquivalence :=
  CoefficientDescent.DescentModule.equivalence (A := R) (B := F.productRing)

/-- The geometric double overlap is the spectrum of the double coefficient algebra. -/
def overlapIso :
    pullback (Spec.map F.productMap) (Spec.map F.productMap) ≅
      Spec (CommRingCat.of (TensorProduct R F.productRing F.productRing)) :=
  pullbackSpecIso R F.productRing F.productRing

/-- The first projection of the overlap is induced by the first coefficient embedding. -/
theorem overlapIso_fst :
    F.overlapIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F.productRing
      (TensorProduct R F.productRing F.productRing))) = pullback.fst _ _ :=
  pullbackSpecIso_hom_fst' R F.productRing F.productRing

/-- The second projection is induced by the second coefficient embedding. -/
theorem overlapIso_snd :
    F.overlapIso.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := F.productRing)
        (B := F.productRing)).toRingHom) = pullback.snd _ _ :=
  pullbackSpecIso_hom_snd R F.productRing F.productRing

end AffineRefinement

end

end SHIGURE.SchemeDescent
