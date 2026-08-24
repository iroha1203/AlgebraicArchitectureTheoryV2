import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComponentFactorization

/-!
# Vertical pasted-comparison factorized routes
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- Top normalization followed by the literal vertical comparison has the
expected lift factorization. -/
theorem verticalBCPastingTopComponentRoute_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    (coreFiberIteratedLift
          (data.pasteNorthwestIso.inv ≫
            (toSemanticBC data.upperPresentation).square.top)
          ((toSemanticBC data.upperPresentation).square.right ≫
            (toSemanticBC data.lowerPresentation).square.right)
          sourcePackage ≫
        ((coreFiberTransportFunctor
          ((toSemanticBC data.upperPresentation).square.right ≫
            (toSemanticBC data.lowerPresentation).square.right)).map
          (coreFiberCompositorApp data.pasteNorthwestIso.inv
            (toSemanticBC data.upperPresentation).square.top
            sourcePackage).hom).1) ≫
      ((verticalBCPastingComponentComparison data).hom.app
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          sourcePackage)).1 =
    coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
      coreFiberIteratedLift
        ((toSemanticBC data.upperPresentation).square.left ≫
          (toSemanticBC data.lowerPresentation).square.left)
        (toSemanticBC data.lowerPresentation).square.bottom
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          sourcePackage) := by
  let nestedPackage :=
    (coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj sourcePackage
  calc
    _ = (coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
          coreFiberIteratedLift
            (toSemanticBC data.upperPresentation).square.top
            ((toSemanticBC data.upperPresentation).square.right ≫
              (toSemanticBC data.lowerPresentation).square.right)
            nestedPackage) ≫
        ((verticalBCPastingComponentComparison data).hom.app
          nestedPackage).1 := congrArg
      (fun q => q ≫
        ((verticalBCPastingComponentComparison data).hom.app
          nestedPackage).1)
      (coreFiberIteratedLift_compositor_whisker_fac
        data.pasteNorthwestIso.inv
        (toSemanticBC data.upperPresentation).square.top
        ((toSemanticBC data.upperPresentation).square.right ≫
          (toSemanticBC data.lowerPresentation).square.right)
        sourcePackage)
    _ = coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
        (coreFiberIteratedLift
            (toSemanticBC data.upperPresentation).square.top
            ((toSemanticBC data.upperPresentation).square.right ≫
              (toSemanticBC data.lowerPresentation).square.right)
            nestedPackage ≫
          ((verticalBCPastingComponentComparison data).hom.app
            nestedPackage).1) := Category.assoc _ _ _
    _ = _ := congrArg
      (fun q => coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫ q)
      (verticalBCPastingComponentComparison_hom_fac data nestedPackage)

/-- The left normalization compositor identifies the literal left-composite
lift with the normalized-left lift. -/
theorem verticalBCPastingLeftRoute_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    (coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
        coreFiberIteratedLift
          ((toSemanticBC data.upperPresentation).square.left ≫
            (toSemanticBC data.lowerPresentation).square.left)
          (toSemanticBC data.lowerPresentation).square.bottom
          ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
            sourcePackage)) ≫
      ((coreFiberTransportFunctor
        (toSemanticBC data.lowerPresentation).square.bottom).map
        (coreFiberCompositorApp data.pasteNorthwestIso.inv
          ((toSemanticBC data.upperPresentation).square.left ≫
            (toSemanticBC data.lowerPresentation).square.left)
          sourcePackage).inv).1 =
    coreFiberIteratedLift
      (normalizedNestedPasteSquare (.vertical data)).left
      (toSemanticBC data.lowerPresentation).square.bottom
      sourcePackage := by
  simpa only [normalizedNestedPasteSquare] using
    coreFiberTripleLift_compositor_inv_whisker_fac
      data.pasteNorthwestIso.inv
      ((toSemanticBC data.upperPresentation).square.left ≫
        (toSemanticBC data.lowerPresentation).square.left)
      (toSemanticBC data.lowerPresentation).square.bottom
      sourcePackage

/-- The top normalization whisker is the mapped compositor component. -/
theorem verticalBCPastingNormalizedTop_hom_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    ((Functor.isoWhiskerRight
      (verticalBCPastingNormalizedTopCompositor data)
      (coreFiberTransportFunctor
        ((toSemanticBC data.upperPresentation).square.right ≫
          (toSemanticBC data.lowerPresentation).square.right))).hom.app
            sourcePackage).1 =
      ((coreFiberTransportFunctor
        ((toSemanticBC data.upperPresentation).square.right ≫
          (toSemanticBC data.lowerPresentation).square.right)).map
        (coreFiberCompositorApp data.pasteNorthwestIso.inv
          (toSemanticBC data.upperPresentation).square.top
          sourcePackage).hom).1 := by
  rfl

/-- The normalized outer top-right lift is the explicit northwest-normalized
component source lift. -/
theorem verticalBCPastingNormalizedSourceLift_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    coreFiberIteratedLift
        (normalizedNestedPasteSquare (.vertical data)).top
        ((toSemanticBC data.upperPresentation).square.right ≫
          (toSemanticBC data.lowerPresentation).square.right)
        sourcePackage =
      coreFiberIteratedLift
        (data.pasteNorthwestIso.inv ≫
          (toSemanticBC data.upperPresentation).square.top)
        ((toSemanticBC data.upperPresentation).square.right ≫
          (toSemanticBC data.lowerPresentation).square.right)
        sourcePackage := rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
