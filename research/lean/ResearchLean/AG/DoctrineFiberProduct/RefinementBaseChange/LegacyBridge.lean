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

@[simp]
theorem exactPointedToRefinement_map_eqToHom
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U} (h : X = Y) :
    (exactPointedToRefinement U).map (eqToHom h) =
      (eqToHom (congrArg (fun Z => PointedRefinementObject.mk Z) h) :
        PointedRefinementObject.mk X ⟶ PointedRefinementObject.mk Y) := by
  subst h
  rfl

/--
An exact vertical fiber map remains vertical after the exact-to-refinement total
comparison.  The proof explicitly transports the exact fiber equation through
the commuting projection square.
-/
theorem exactVerticalComparison_isHomLift
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {source target : CoreFiber X} (vertical : source ⟶ target) :
    (refinementPackageProjection U).IsHomLift
      (PointedRefinementHom.id X)
      ((exactPackageToRefinement U).map vertical.1) := by
  let hsource := congrArg (fun Z => PointedRefinementObject.mk Z) source.2
  let htarget := congrArg (fun Z => PointedRefinementObject.mk Z) target.2
  apply CategoryTheory.IsHomLift.of_fac'
    (refinementPackageProjection U) (PointedRefinementHom.id X)
      ((exactPackageToRefinement U).map vertical.1) hsource htarget
  have hcomparison :
      (refinementPackageProjection U).map
          ((exactPackageToRefinement U).map vertical.1) =
        (exactPointedToRefinement U).map
          ((packageProjection U).map vertical.1) := by
    simpa using CategoryTheory.Functor.congr_hom
      (exact_refinement_projection_square U) vertical.1
  letI : (packageProjection U).IsHomLift (𝟙 X) vertical.1 := vertical.2
  have hexact := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (𝟙 X) vertical.1
  rw [hcomparison, hexact]
  simp only [CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id,
    exactPointedToRefinement_map_eqToHom]
  change eqToHom hsource ≫ PointedRefinementHom.id X ≫
      eqToHom htarget.symm = _
  rfl

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
  have factor_triangle : ∀ {source : CoreFiber X}
      (candidate : RefinementOverHom r source ⟨Q, rfl⟩),
      RefinementOverHom.precomp (factor candidate) hom = candidate := by
    intro source candidate
    apply RefinementOverHom.ext
    change (candidate.upper.comp backward).comp forward = candidate.upper
    rw [PackageTotalHom.upper_comp_assoc,
      SelectedRefinementTransport.inverseCorePackageBackward_comp_forward,
      PackageTotalHom.upper_comp_id]
  exact {
    domain := domain
    hom := hom
    factor := factor
    factor_fac := factor_triangle
    factor_unique := by
      intro source candidate vertical hfac
      let generated := factor candidate
      let actual := refinementLiftOfRealizedReflection r condition ⟨Q, rfl⟩
      letI : (refinementPackageProjection U).IsHomLift
          (PointedRefinementHom.id X)
          ((exactPackageToRefinement U).map vertical.1) :=
        exactVerticalComparison_isHomLift vertical
      letI : (refinementPackageProjection U).IsHomLift
          (PointedRefinementHom.id X)
          ((exactPackageToRefinement U).map generated.1) :=
        exactVerticalComparison_isHomLift generated
      letI := actual.isStronglyCartesian
      have hbase : vertical.1.base = generated.1.base := by
        letI : (packageProjection U).IsHomLift (𝟙 X) vertical.1 := vertical.2
        letI : (packageProjection U).IsHomLift (𝟙 X) generated.1 := generated.2
        exact (CategoryTheory.IsHomLift.fac'
          (packageProjection U) (𝟙 X) vertical.1).trans
            (CategoryTheory.IsHomLift.fac'
              (packageProjection U) (𝟙 X) generated.1).symm
      have hcomp :
          (exactPackageToRefinement U).map vertical.1 ≫ actual.hom =
            (exactPackageToRefinement U).map generated.1 ≫ actual.hom := by
        apply RefinementPackageHom.ext
        · change
            (PointedRefinementHom.ofExact vertical.1.base).comp r =
              (PointedRefinementHom.ofExact generated.1.base).comp r
          exact congrArg (fun base => (PointedRefinementHom.ofExact base).comp r) hbase
        · have hvertical := congrArg RefinementOverHom.upper hfac
          have hgenerated := congrArg RefinementOverHom.upper (factor_triangle candidate)
          simpa [actual, hom, generated, RefinementOverHom.precomp,
            RefinementPackageHom.comp] using hvertical.trans hgenerated.symm
      have hcomparison :
          (exactPackageToRefinement U).map vertical.1 =
            (exactPackageToRefinement U).map generated.1 := by
        apply CategoryTheory.Functor.IsStronglyCartesian.ext
          (refinementPackageProjection U) r actual.hom
          (PointedRefinementHom.id X)
        exact hcomp
      apply CategoryTheory.Functor.Fiber.hom_ext
      apply PackageTotalHom.ext
      · exact hbase
      · exact congrArg RefinementPackageHom.upper hcomparison
  }

/-- Objectwise legacy cleavage generated from the fixed condition. -/
noncomputable def legacyRefinementCleavageOfRealizedReflection
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r) :
    LegacyRefinementCartesianCleavage r where
  lift target := legacyRefinementLiftOfRealizedReflection r condition target

/-- The relative bridge selects the same authored package as the public lift. -/
theorem legacyRefinementLift_domain_coherence
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (target : CoreFiber Y) :
    (legacyRefinementLiftOfRealizedReflection r condition target).domain.1 =
      (refinementLiftOfRealizedReflection r condition target).domain := by
  rcases target with ⟨Q, hQ⟩
  subst Y
  rfl

/-- The relative bridge uses the public lift's complete upper edge. -/
theorem legacyRefinementLift_upper_coherence
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (target : CoreFiber Y) :
    HEq (legacyRefinementLiftOfRealizedReflection r condition target).hom.upper
      (refinementLiftOfRealizedReflection r condition target).hom.upper := by
  rcases target with ⟨Q, hQ⟩
  subst Y
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
