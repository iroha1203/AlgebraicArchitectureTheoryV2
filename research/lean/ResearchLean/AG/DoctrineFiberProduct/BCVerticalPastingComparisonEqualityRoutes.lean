import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComponentFactorization

/-!
# Vertical pasted-comparison factorized routes
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- G-110(E) vertical covariant-square predecessor API: canonical northwest
top normalization followed by the literal generated comparison has the stated
lift factorization.  The northwest isomorphism and component comparison are
generated from `VerticalBCPastingData`. -/
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

/-- G-110(E) vertical covariant-square predecessor API: the generated left
normalization compositor identifies the literal left-composite lift with the
normalized-left lift.  No endpoint equality or compositor is supplied by the
caller. -/
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

/-- G-110(E) vertical covariant-square predecessor API: expose the generated
top-normalization whisker as the mapped G-109 compositor component.  This
definitional API lemma consumes only the canonical northwest normalization. -/
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

/-- G-110(E) vertical covariant-square predecessor API: expose the normalized
outer top-right lift as the explicit northwest-normalized component source
lift.  The equality follows from the generated normalized square definition,
not from a caller certificate. -/
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
