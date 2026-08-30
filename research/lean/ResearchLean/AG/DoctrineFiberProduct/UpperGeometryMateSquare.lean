import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateComparison

/-!
# Cartesian qualification for the upper geometry mate comparison

The geometry-compatible routes and the completed G-114 routes use independent
cartesian choices. This module proves that the completed G-114 route composites
retain strong cartesianness in the G-115 refinement-package category, supplying
the universal-property input for the later comparison square. Completed
predecessor APIs remain immutable inputs.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

/-- A legacy realized-refinement lift, read as a package morphism, remains
strongly cartesian because its complete upper map has the generated inverse. -/
theorem legacyRefinementPackageLift_isStronglyCartesian
    {X Y : ExtractionInstance U} (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r) (target : CoreFiber Y) :
    (refinementPackageProjection U).IsStronglyCartesian
      (refinementPackageHomOfOver
        (legacyRefinementLiftOfRealizedReflection r condition target).hom).base
      (refinementPackageHomOfOver
        (legacyRefinementLiftOfRealizedReflection r condition target).hom) := by
  rcases target with ⟨Q, hQ⟩
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition ⟨Q, rfl⟩
  apply refinementPackageHom_isStronglyCartesian_of_upper_inverse
    (refinementPackageHomOfOver
      (legacyRefinementLiftOfRealizedReflection r condition ⟨Q, rfl⟩).hom)
    (SelectedRefinementTransport.inverseCorePackageBackwardUpper Q data)
  · exact SelectedRefinementTransport.inverseCorePackageForward_comp_backward Q data
  · exact SelectedRefinementTransport.inverseCorePackageBackward_comp_forward Q data

/-- A G-112-selected exact lift remains strongly cartesian after embedding in
the lax refinement-package category. -/
theorem selectedExactRefinementLift_isStronglyCartesian
    {X Y : ExtractionInstance U} (g : X ⟶ Y) (target : CoreFiber Y) :
    (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map
        (exact_bottom_semantic_global_selected_lift g target).hom).base)
      ((exactPackageToRefinement U).map
        (exact_bottom_semantic_global_selected_lift g target).hom) := by
  let inverse := exact_bottom_semantic_global_selected_lift_upperInverse g target
  apply refinementPackageHom_isStronglyCartesian_of_upper_inverse
    ((exactPackageToRefinement U).map
      (exact_bottom_semantic_global_selected_lift g target).hom)
    inverse.inv
  · exact inverse.hom_inv
  · exact inverse.inv_hom

/-- The retargeted G-114 base-first composite is strongly cartesian. -/
theorem retargetedBaseComposite_isStronglyCartesian
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsStronglyCartesian
      (retargetedContext ctx target).baseCompositeLeg.base
      (retargetedContext ctx target).baseCompositeLeg := by
  unfold ActiveRefinementBCContext.baseCompositeLeg
  letI hexact := selectedExactRefinementLift_isStronglyCartesian
    ((retargetedContext ctx target).configuration.pointedConfigurationAt
      (retargetedContext ctx target).source).pulledFst
    (((retargetedContext ctx target).legacyRegime).reverseBase.obj
      (retargetedContext ctx target).targetPackage)
  letI hrefinement : (refinementPackageProjection U).IsStronglyCartesian
      (refinementPackageHomOfOver
        (((retargetedContext ctx target).legacyRegime).baseCleavage.lift
          (retargetedContext ctx target).targetPackage).hom).base
      (refinementPackageHomOfOver
        (((retargetedContext ctx target).legacyRegime).baseCleavage.lift
          (retargetedContext ctx target).targetPackage).hom) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (refinementPackageHomOfOver
        (legacyRefinementLiftOfRealizedReflection
          ((retargetedContext ctx target).configuration.baseRefinementAt
            (retargetedContext ctx target).source)
          (retargetedContext ctx target).condition
          (retargetedContext ctx target).targetPackage).hom).base
      (refinementPackageHomOfOver
        (legacyRefinementLiftOfRealizedReflection
          ((retargetedContext ctx target).configuration.baseRefinementAt
            (retargetedContext ctx target).source)
          (retargetedContext ctx target).condition
          (retargetedContext ctx target).targetPackage).hom)
    exact legacyRefinementPackageLift_isStronglyCartesian _ _ _
  exact CategoryTheory.Functor.IsStronglyCartesian.comp
    (refinementPackageProjection U)

/-- The retargeted G-114 pulled-first composite is strongly cartesian. -/
theorem retargetedPulledComposite_isStronglyCartesian
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsStronglyCartesian
      (retargetedContext ctx target).pulledCompositeLeg.base
      (retargetedContext ctx target).pulledCompositeLeg := by
  unfold ActiveRefinementBCContext.pulledCompositeLeg
  letI hrefinement : (refinementPackageProjection U).IsStronglyCartesian
      (refinementPackageHomOfOver
        (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
          (retargetedContext ctx target).pullbackTargetPackage).hom).base
      (refinementPackageHomOfOver
        (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
          (retargetedContext ctx target).pullbackTargetPackage).hom) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (refinementPackageHomOfOver
        (legacyRefinementLiftOfRealizedReflection
          ((retargetedContext ctx target).configuration.pulledRefinementAt
            (retargetedContext ctx target).source)
          (pulledRealizedReflection (retargetedContext ctx target).configuration
            (retargetedContext ctx target).source
            (retargetedContext ctx target).condition)
          (retargetedContext ctx target).pullbackTargetPackage).hom).base
      (refinementPackageHomOfOver
        (legacyRefinementLiftOfRealizedReflection
          ((retargetedContext ctx target).configuration.pulledRefinementAt
            (retargetedContext ctx target).source)
          (pulledRealizedReflection (retargetedContext ctx target).configuration
            (retargetedContext ctx target).source
            (retargetedContext ctx target).condition)
          (retargetedContext ctx target).pullbackTargetPackage).hom)
    exact legacyRefinementPackageLift_isStronglyCartesian _ _ _
  letI hexact := selectedExactRefinementLift_isStronglyCartesian
    ((retargetedContext ctx target).configuration.pointedConfigurationAt
      (retargetedContext ctx target).source).pullbackFst
    (retargetedContext ctx target).targetPackage
  exact CategoryTheory.Functor.IsStronglyCartesian.comp
    (refinementPackageProjection U)

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
