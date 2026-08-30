import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCochains
import ResearchLean.AG.CrossStageCoherence.PathGaugeEffectivity

/-!
# Canonical comparators on compatible routes

The generated base-first and pulled-first canonical two-cell comparators are
identified with the Cartesian pullbacks of the single source canonical
comparator.  The proof first compares the two composites after the route leg
by its geometry-level Cartesian uniqueness, then uses the route path's
composite strong cocartesianness to identify the endpoint automorphisms.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The base-route canonical comparator is the two-level Cartesian pullback
of the source canonical comparator. -/
theorem generatedBaseRouteCanonicalComparator_eq_pullback
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    upperCanonicalTwoCellComparator input.generatedBaseRouteData 1 cell =
      input.generatedBaseCompositeFiberAutAt (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.compatibleSourceRouteData 1 cell) := by
  let routeLeft := input.generatedBaseRouteData.lift.pathLift (P.twoLeft cell)
  let routeRight := input.generatedBaseRouteData.lift.pathLift (P.twoRight cell)
  let sourceCanonical :=
    upperCanonicalTwoCellComparator input.compatibleSourceRouteData 1 cell
  let pulledCanonical := input.generatedBaseCompositeFiberAutAt
    (P.twoTarget cell) sourceCanonical
  have hsource :
      (input.compatibleSourceRouteData.lift.pathLift (P.twoLeft cell)).comp
          (CompositeFiberAut.hom sourceCanonical) =
        input.compatibleSourceRouteData.lift.pathLift (P.twoRight cell) := by
    simpa only [upperReselectedPathLift_one] using
      upperCanonicalTwoCellComparator_fac
        input.compatibleSourceRouteData 1 cell
  have hroute : routeLeft.comp
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator input.generatedBaseRouteData 1 cell)) =
      routeRight := by
    simpa only [upperReselectedPathLift_one] using
      upperCanonicalTwoCellComparator_fac input.generatedBaseRouteData 1 cell
  have hafterLeg :
      ((exactGeometryToRefinementGeometry U).map
          (routeLeft.comp (CompositeFiberAut.hom pulledCanonical))) ≫
            input.generatedBaseRouteLegAt (P.twoTarget cell) =
        ((exactGeometryToRefinementGeometry U).map routeRight) ≫
            input.generatedBaseRouteLegAt (P.twoTarget cell) := by
    change (((exactGeometryToRefinementGeometry U).map routeLeft) ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom pulledCanonical))) ≫
          input.generatedBaseRouteLegAt (P.twoTarget cell) = _
    rw [Category.assoc]
    change ((exactGeometryToRefinementGeometry U).map routeLeft).comp
        (((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom pulledCanonical)).comp
            (input.generatedBaseRouteLegAt (P.twoTarget cell))) = _
    rw [input.generatedBaseCompositeFiberAutAt_fac]
    change ((exactGeometryToRefinementGeometry U).map routeLeft).comp
        ((input.generatedBaseRouteLegAt (P.twoTarget cell)).comp
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom sourceCanonical))) = _
    rw [← UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
      input.generatedBaseRoutePath_fac (P.twoLeft cell),
      UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
    change input.generatedBaseRouteLegAt (P.twoSource cell) ≫
        (exactGeometryToRefinementGeometry U).map
          ((input.compatibleSourceRouteData.lift.pathLift
            (P.twoLeft cell)).comp (CompositeFiberAut.hom sourceCanonical)) = _
    rw [hsource]
    exact (input.generatedBaseRoutePath_fac (P.twoRight cell)).symm
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      routeLeft.base.base routeLeft :=
    input.generatedBaseRouteData.lift.pathLift_compositeStrong (P.twoLeft cell)
  apply CompositeFiberAut.ext_of_strong_fac routeLeft
  have hpull : routeLeft.comp (CompositeFiberAut.hom pulledCanonical) =
      routeRight := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    let left := (exactGeometryToRefinementGeometry U).map
      (routeLeft.comp (CompositeFiberAut.hom pulledCanonical))
    let right := (exactGeometryToRefinementGeometry U).map routeRight
    have hleftBase : left.base = right.base := by
      let packageLeft := left.base
      let packageRight := right.base
      have hpackageBase : packageLeft.base = packageRight.base := by
        change (exactPointedToRefinement U).map
            ((routeLeft.comp
              (CompositeFiberAut.hom pulledCanonical)).base.base) =
          (exactPointedToRefinement U).map routeRight.base.base
        apply congrArg (exactPointedToRefinement U).map
        change routeLeft.base.base.comp
            (CompositeFiberAut.hom pulledCanonical).base.base =
          routeRight.base.base
        rw [CompositeFiberAut.hom_base_base_eq]
        simpa only [Category.comp_id] using
          input.generatedBaseRouteData.twoCellBase cell
      letI hpackageLeftLift :=
        UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
          packageRight.base packageLeft hpackageBase
      letI hpackageRightLift :=
        UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
          packageRight.base packageRight rfl
      letI : (refinementPackageProjection U).IsStronglyCartesian
          (input.generatedBaseRouteLegAt (P.twoTarget cell)).base.base
          (input.generatedBaseRouteLegAt (P.twoTarget cell)).base :=
        UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨P.twoTarget cell⟩))
          (input.sourceTargetGeometryAt (P.twoTarget cell))
      apply CategoryTheory.Functor.IsStronglyCartesian.ext
        (refinementPackageProjection U)
        (input.generatedBaseRouteLegAt (P.twoTarget cell)).base.base
        (input.generatedBaseRouteLegAt (P.twoTarget cell)).base
        packageRight.base
      change left.base.comp
          (input.generatedBaseRouteLegAt (P.twoTarget cell)).base =
        right.base.comp
          (input.generatedBaseRouteLegAt (P.twoTarget cell)).base
      exact congrArg RefinementGeometryHom.base hafterLeg
    letI hleftLift :=
      UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
        right.base left hleftBase
    letI hrightLift :=
      UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
        right.base right rfl
    letI := input.generatedBaseRouteLegAt_isStronglyCartesian (P.twoTarget cell)
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementGeometryProjection U)
      (input.generatedBaseRouteLegAt (P.twoTarget cell)).base
      (input.generatedBaseRouteLegAt (P.twoTarget cell))
      right.base
    exact hafterLeg
  exact hroute.trans hpull.symm

/-- The pulled-route canonical comparator is the two-level Cartesian pullback
of the source canonical comparator. -/
theorem generatedPulledRouteCanonicalComparator_eq_pullback
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    upperCanonicalTwoCellComparator input.generatedPulledRouteData 1 cell =
      input.generatedPulledCompositeFiberAutAt (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.compatibleSourceRouteData 1 cell) := by
  let routeLeft := input.generatedPulledRouteData.lift.pathLift (P.twoLeft cell)
  let routeRight := input.generatedPulledRouteData.lift.pathLift (P.twoRight cell)
  let sourceCanonical :=
    upperCanonicalTwoCellComparator input.compatibleSourceRouteData 1 cell
  let pulledCanonical := input.generatedPulledCompositeFiberAutAt
    (P.twoTarget cell) sourceCanonical
  have hsource :
      (input.compatibleSourceRouteData.lift.pathLift (P.twoLeft cell)).comp
          (CompositeFiberAut.hom sourceCanonical) =
        input.compatibleSourceRouteData.lift.pathLift (P.twoRight cell) := by
    simpa only [upperReselectedPathLift_one] using
      upperCanonicalTwoCellComparator_fac
        input.compatibleSourceRouteData 1 cell
  have hroute : routeLeft.comp
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator input.generatedPulledRouteData 1 cell)) =
      routeRight := by
    simpa only [upperReselectedPathLift_one] using
      upperCanonicalTwoCellComparator_fac input.generatedPulledRouteData 1 cell
  have hafterLeg :
      ((exactGeometryToRefinementGeometry U).map
          (routeLeft.comp (CompositeFiberAut.hom pulledCanonical))) ≫
            input.generatedPulledRouteLegAt (P.twoTarget cell) =
        ((exactGeometryToRefinementGeometry U).map routeRight) ≫
            input.generatedPulledRouteLegAt (P.twoTarget cell) := by
    change (((exactGeometryToRefinementGeometry U).map routeLeft) ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom pulledCanonical))) ≫
          input.generatedPulledRouteLegAt (P.twoTarget cell) = _
    rw [Category.assoc]
    change ((exactGeometryToRefinementGeometry U).map routeLeft).comp
        (((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom pulledCanonical)).comp
            (input.generatedPulledRouteLegAt (P.twoTarget cell))) = _
    rw [input.generatedPulledCompositeFiberAutAt_fac]
    change ((exactGeometryToRefinementGeometry U).map routeLeft).comp
        ((input.generatedPulledRouteLegAt (P.twoTarget cell)).comp
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom sourceCanonical))) = _
    rw [← UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
      input.generatedPulledRoutePath_fac (P.twoLeft cell),
      UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
    change input.generatedPulledRouteLegAt (P.twoSource cell) ≫
        (exactGeometryToRefinementGeometry U).map
          ((input.compatibleSourceRouteData.lift.pathLift
            (P.twoLeft cell)).comp (CompositeFiberAut.hom sourceCanonical)) = _
    rw [hsource]
    exact (input.generatedPulledRoutePath_fac (P.twoRight cell)).symm
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      routeLeft.base.base routeLeft :=
    input.generatedPulledRouteData.lift.pathLift_compositeStrong (P.twoLeft cell)
  apply CompositeFiberAut.ext_of_strong_fac routeLeft
  have hpull : routeLeft.comp (CompositeFiberAut.hom pulledCanonical) =
      routeRight := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    let left := (exactGeometryToRefinementGeometry U).map
      (routeLeft.comp (CompositeFiberAut.hom pulledCanonical))
    let right := (exactGeometryToRefinementGeometry U).map routeRight
    have hleftBase : left.base = right.base := by
      let packageLeft := left.base
      let packageRight := right.base
      have hpackageBase : packageLeft.base = packageRight.base := by
        change (exactPointedToRefinement U).map
            ((routeLeft.comp
              (CompositeFiberAut.hom pulledCanonical)).base.base) =
          (exactPointedToRefinement U).map routeRight.base.base
        apply congrArg (exactPointedToRefinement U).map
        change routeLeft.base.base.comp
            (CompositeFiberAut.hom pulledCanonical).base.base =
          routeRight.base.base
        rw [CompositeFiberAut.hom_base_base_eq]
        simpa only [Category.comp_id] using
          input.generatedPulledRouteData.twoCellBase cell
      letI hpackageLeftLift :=
        UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
          packageRight.base packageLeft hpackageBase
      letI hpackageRightLift :=
        UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
          packageRight.base packageRight rfl
      letI : (refinementPackageProjection U).IsStronglyCartesian
          (input.generatedPulledRouteLegAt (P.twoTarget cell)).base.base
          (input.generatedPulledRouteLegAt (P.twoTarget cell)).base :=
        UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨P.twoTarget cell⟩))
          (input.sourceTargetGeometryAt (P.twoTarget cell))
      apply CategoryTheory.Functor.IsStronglyCartesian.ext
        (refinementPackageProjection U)
        (input.generatedPulledRouteLegAt (P.twoTarget cell)).base.base
        (input.generatedPulledRouteLegAt (P.twoTarget cell)).base
        packageRight.base
      change left.base.comp
          (input.generatedPulledRouteLegAt (P.twoTarget cell)).base =
        right.base.comp
          (input.generatedPulledRouteLegAt (P.twoTarget cell)).base
      exact congrArg RefinementGeometryHom.base hafterLeg
    letI hleftLift :=
      UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
        right.base left hleftBase
    letI hrightLift :=
      UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
        right.base right rfl
    letI := input.generatedPulledRouteLegAt_isStronglyCartesian (P.twoTarget cell)
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementGeometryProjection U)
      (input.generatedPulledRouteLegAt (P.twoTarget cell)).base
      (input.generatedPulledRouteLegAt (P.twoTarget cell))
      right.base
    exact hafterLeg
  exact hroute.trans hpull.symm

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
