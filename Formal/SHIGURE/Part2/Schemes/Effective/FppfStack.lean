import Formal.SHIGURE.Part2.Schemes.Effective.CombinedRecovery
import Formal.SHIGURE.Part2.Schemes.Effective.ProductRefinement

/-! # Effective fppf descent of quasi-coherent modules

A finite affine refinement of a cover of a spectrum produces a single
faithfully flat product map. Its pullback of the original family is refined
by the product's component open cover. The local-to-global theorem then gives
effectivity on affine bases, and affine open covers give it on all schemes.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

set_option maxHeartbeats 750000 in
private theorem affineFppfComparison_small {R : CommRingCat.{u}}
    (cover : FppfCover.{u,u} (Spec R)) : (fppfModuleComparison cover).IsEquivalence := by
  let F := affineRefinement cover
  let E : FppfCover.{u,u} (Spec R) := F.productCover
  apply fppfComparison_isEquivalence_of_local E cover F.productCover_isEquivalence
  intro i
  change PUnit at i
  cases i
  exact F.productPullback_isEquivalence

set_option maxHeartbeats 750000 in
/-- Every fppf covering family of an affine base has effective descent for
quasi-coherent modules and all compatible module maps. -/
theorem affineFppfModuleComparison_isEquivalence {R : CommRingCat.{u}}
    (cover : FppfCover.{u,v} (Spec R)) : (fppfModuleComparison cover).IsEquivalence := by
  letI : Q.IsPrestack fppfTopology := quasiCoherentModules_isFppfPrestack
  let small := fppfPointSubcover cover
  have smallStack : Q.IsStackFor (Sieve.ofArrows small.X small.f).arrows := by
    rw [IsStackFor_generate_iff, Q.isStackFor_ofArrows_iff]
    exact affineFppfComparison_small small
  have stack := IsStackFor.of_le' Q smallStack (fppfCover_sieve_mem small)
    (fppfPointSubcoverOver cover).sieve₀_le_sieve₀
  rw [IsStackFor_generate_iff, Q.isStackFor_ofArrows_iff] at stack
  exact stack

set_option maxHeartbeats 750000 in
/-- The actual comparison for any fppf covering family of any scheme is an
equivalence, on all quasi-coherent modules and all compatible module maps. -/
theorem fppfModuleComparison_isEquivalence {X : Scheme.{u}}
    (cover : FppfCover.{u,v} X) : (fppfModuleComparison cover).IsEquivalence := by
  let A := X.affineOpenCover
  let Z := A.openCover
  let E := effectiveOpenCoverAsFppf Z
  apply fppfComparison_isEquivalence_of_local E cover
  · exact openCoverComparison_isEquivalence_anySize Z
  · intro i
    exact affineFppfModuleComparison_isEquivalence (cover.pullback₁ (Z.f i))

set_option maxHeartbeats 750000 in
/-- Quasi-coherent modules and all their maps form a stack for the fppf
topology on arbitrary schemes. -/
theorem quasiCoherentModules_isFppfStack : Q.{u}.IsStack fppfTopology := by
  letI : MorphismProperty.IsMultiplicative
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    { id_mem := fun X => inferInstanceAs (LocallyOfFinitePresentation (𝟙 X)) }
  apply IsStack.of_precoverage (J := Scheme.precoverage FppfComponent)
  intro X R hR
  let cover : FppfCover.{u,u+1} X := ⟨R.preZeroHypercover, R.presieve₀_preZeroHypercover.symm ▸ hR⟩
  have eq : cover.presieve₀ = R := R.presieve₀_preZeroHypercover
  rw [← eq]
  exact (Q.isStackFor_ofArrows_iff cover.f).2 (fppfModuleComparison_isEquivalence cover)

end

end SHIGURE.SchemeDescent
