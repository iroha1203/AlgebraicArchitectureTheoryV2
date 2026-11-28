import Formal.SHIGURE.Part2.Schemes.FppfGlobalFromAffineSingleton
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentZariskiStack

/-! # Effectivity after pullback to the finite product chart

The components of a finite affine refinement cover the spectrum of the
product ring by open immersions. Each component factors through the pullback
of the original family to that spectrum. Thus Zariski descent and the fppf
prestack property give effective descent on that pulled-back family.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

/-- An open covering family is also an fppf covering family, with unchanged
components and maps. -/
def effectiveOpenCoverAsFppf {X : Scheme.{u}} (opens : Scheme.OpenCover X) : FppfCover X :=
  opens.changeProp fun i => by
    letI : IsOpenImmersion (opens.f i) := opens.map_prop i
    exact ⟨inferInstanceAs (Flat (opens.f i)),
      inferInstanceAs (LocallyOfFinitePresentation (opens.f i))⟩

namespace AffineRefinement

variable {R : CommRingCat.{u}} {cover : FppfCover (Spec R)} (F : AffineRefinement cover)

/-- The product components refine the original family after its base change
along the product-ring map. -/
def productOpenCoverToPullback :
    effectiveOpenCoverAsFppf F.productOpenCover ⟶
      cover.pullback₁ (Spec.map F.productMap) where
  s₀ i := F.over.s₀ i
  h₀ i := pullback.lift (F.productOpenCover.f i) (F.over.h₀ i) (by
    calc
      F.productOpenCover.f i ≫ Spec.map F.productMap = F.affine.f i :=
        (F.toProductCover.w₀ i)
      _ = F.over.h₀ i ≫ cover.f (F.over.s₀ i) := (F.over.w₀ i).symm)
  w₀ i := pullback.lift_fst _ _ _

set_option maxHeartbeats 700000 in
/-- The finite product map is itself an effective fppf singleton: its
coefficient algebra is the actual faithfully flat product algebra. -/
theorem productCover_isEquivalence :
    (fppfModuleComparison F.productCover).IsEquivalence := by
  letI : Algebra R F.productRing := F.productAlgebra
  letI : Module.FaithfullyFlat R F.productRing := F.productFaithfullyFlat
  have single : Q.IsStackFor (Presieve.singleton (Spec.map F.productMap)) := by
    have h := (Q.isStackFor_ofArrows_iff
      (fun _ : Unit => affineScalarMap R F.productRing)).2
        (affineSingletonFaithfullyFlatDescent (A := R) (B := F.productRing))
    rw [Presieve.ofArrows_of_unique] at h
    exact h
  letI : Unique F.productCover.I₀ := by
    change Unique PUnit
    infer_instance
  apply (Q.isStackFor_ofArrows_iff F.productCover.f).1
  rw [Presieve.ofArrows_of_unique]
  exact single

set_option maxHeartbeats 700000 in
/-- The original fppf comparison becomes an equivalence after pullback to
its selected product spectrum. The proof uses the actual open refinement. -/
theorem productPullback_isEquivalence :
    (fppfModuleComparison (cover.pullback₁ (Spec.map F.productMap))).IsEquivalence := by
  letI : Q.IsPrestack fppfTopology := quasiCoherentModules_isFppfPrestack
  let O := effectiveOpenCoverAsFppf F.productOpenCover
  let P := cover.pullback₁ (Spec.map F.productMap)
  have openStack : Q.IsStackFor (Sieve.ofArrows O.X O.f).arrows := by
    rw [IsStackFor_generate_iff]
    exact (Q.isStackFor_ofArrows_iff O.f).2
      (openCoverComparison_isEquivalence_anySize F.productOpenCover)
  have refined : Sieve.ofArrows O.X O.f ≤ Sieve.ofArrows P.X P.f :=
    F.productOpenCoverToPullback.sieve₀_le_sieve₀
  have result := IsStackFor.of_le' Q openStack (fppfCover_sieve_mem O) refined
  rw [IsStackFor_generate_iff, Q.isStackFor_ofArrows_iff] at result
  exact result

end AffineRefinement

end

end SHIGURE.SchemeDescent
