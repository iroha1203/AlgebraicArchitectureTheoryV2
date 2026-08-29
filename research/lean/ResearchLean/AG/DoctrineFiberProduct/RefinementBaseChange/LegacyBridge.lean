import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.RealizedSupport

/-!
# Bridge to the existing relative-hom mate machinery

The revision-1 relative interface already derives reverse functors and mates
from factorization uniqueness.  This module supplies that interface from the
revision-3 selected-family package and its genuine strongly cartesian lift.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- The selected-family lift satisfies the earlier explicit factor interface. -/
noncomputable def legacyRefinementLiftOfRealizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (target : CoreFiber Y) : LegacyRefinementCartesianLift r target := by
  rcases target with ⟨Q, hQ⟩
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition ⟨Q, rfl⟩
  let P := SelectedRefinementTransport.inverseCorePackage Q data
  let forward := SelectedRefinementTransport.inverseCorePackageForwardUpper Q data
  let backward := SelectedRefinementTransport.inverseCorePackageBackwardUpper Q data
  let domain : CoreFiber X :=
    ⟨P, SelectedRefinementTransport.inverseCorePackage_point Q data⟩
  let hom : RefinementOverHom r domain ⟨Q, rfl⟩ := {
    lower := r
    lower_eq := rfl
    upper := forward
    atomEquiv_eq := rfl
  }
  let factor : ∀ {sourcePackage : CoreFiber X},
      RefinementOverHom r sourcePackage ⟨Q, rfl⟩ → (sourcePackage ⟶ domain) := by
    intro sourcePackage candidate
    let total : PackageTotalHom sourcePackage.1 P := {
      base := eqToHom (sourcePackage.2.trans domain.2.symm)
      upper := candidate.upper.comp backward
      atomEquiv_eq := by
        apply Equiv.ext
        intro atom
        calc
          (candidate.upper.comp backward).atomEquiv atom =
              backward.atomEquiv (candidate.upper.atomEquiv atom) := rfl
          _ = atom := by
            rw [candidate.atomEquiv_eq, candidate.lower_eq]
            exact data.atomEquiv.symm_apply_apply atom
          _ = (eqToHom (sourcePackage.2.trans domain.2.symm)).doctrineHom.atomEquiv atom := by
            rw [ExtInstHom.eqToHom_atomEquiv]
            rfl
    }
    refine ⟨total, ?_⟩
    apply CategoryTheory.IsHomLift.of_fac'
      (packageProjection U) (𝟙 X) total sourcePackage.2 domain.2
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  exact {
    domain := domain
    hom := hom
    factor := factor
    factor_fac := by
      intro source candidate
      apply RefinementOverHom.ext
      change (candidate.upper.comp backward).comp forward = candidate.upper
      rw [PackageTotalHom.upper_comp_assoc,
        SelectedRefinementTransport.inverseCorePackageBackward_comp_forward,
        PackageTotalHom.upper_comp_id]
    factor_unique := by
      intro source candidate vertical hfac
      apply CategoryTheory.Functor.Fiber.hom_ext
      apply PackageTotalHom.ext
      · letI : (packageProjection U).IsHomLift (𝟙 X) vertical.1 := vertical.2
        let generated := factor candidate
        letI : (packageProjection U).IsHomLift (𝟙 X) generated.1 := generated.2
        exact (CategoryTheory.IsHomLift.fac'
          (packageProjection U) (𝟙 X) vertical.1).trans
            (CategoryTheory.IsHomLift.fac'
              (packageProjection U) (𝟙 X) generated.1).symm
      · have hupper := congrArg RefinementOverHom.upper hfac
        change vertical.1.upper.comp forward = candidate.upper at hupper
        change vertical.1.upper = candidate.upper.comp backward
        calc
          vertical.1.upper = vertical.1.upper.comp
              (SignedExactCoreReadingHom.refl P) :=
            (PackageTotalHom.upper_comp_id _).symm
          _ = vertical.1.upper.comp (forward.comp backward) := by
            rw [SelectedRefinementTransport.inverseCorePackageForward_comp_backward]
          _ = (vertical.1.upper.comp forward).comp backward := by
            rw [PackageTotalHom.upper_comp_assoc]
          _ = candidate.upper.comp backward := by rw [hupper]
  }

/-- Objectwise legacy cleavage generated from the fixed condition. -/
noncomputable def legacyRefinementCleavageOfRealizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r) :
    LegacyRefinementCartesianCleavage r where
  lift target := legacyRefinementLiftOfRealizedReflection r condition target

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
