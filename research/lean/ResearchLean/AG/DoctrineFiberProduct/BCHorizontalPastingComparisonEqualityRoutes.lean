import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonFactorization

/-!
# Horizontal pasted-comparison factorized routes

The factorized lift routes are assembled across northwest normalization and
bottom-edge equality transport. Equality with the independently generated
outer semantic comparison is then obtained by strong-cocartesian uniqueness.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The top normalization followed by the literal horizontal comparison has
the expected lift factorization. -/
theorem horizontalBCPastingTopComponentRoute_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    (coreFiberIteratedLift
          (data.pasteNorthwestIso.inv ≫
            ((toSemanticBC data.leftPresentation).square.top ≫
              (toSemanticBC data.rightPresentation).square.top))
          (toSemanticBC data.rightPresentation).square.right sourcePackage ≫
        ((coreFiberTransportFunctor
          (toSemanticBC data.rightPresentation).square.right).map
          (coreFiberCompositorApp data.pasteNorthwestIso.inv
            ((toSemanticBC data.leftPresentation).square.top ≫
              (toSemanticBC data.rightPresentation).square.top)
            sourcePackage).hom).1) ≫
      ((horizontalBCPastingComponentComparison data).hom.app
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          sourcePackage)).1 =
    coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
      coreFiberIteratedLift
        (toSemanticBC data.leftPresentation).square.left
        ((toSemanticBC data.leftPresentation).square.bottom ≫
          (toSemanticBC data.rightPresentation).square.bottom)
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          sourcePackage) := by
  let nestedPackage :=
    (coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj sourcePackage
  calc
    _ = (coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
          coreFiberIteratedLift
            ((toSemanticBC data.leftPresentation).square.top ≫
              (toSemanticBC data.rightPresentation).square.top)
            (toSemanticBC data.rightPresentation).square.right
            nestedPackage) ≫
        ((horizontalBCPastingComponentComparison data).hom.app
          nestedPackage).1 := congrArg
      (fun q => q ≫
        ((horizontalBCPastingComponentComparison data).hom.app
          nestedPackage).1)
      (coreFiberIteratedLift_compositor_whisker_fac
        data.pasteNorthwestIso.inv
        ((toSemanticBC data.leftPresentation).square.top ≫
          (toSemanticBC data.rightPresentation).square.top)
        (toSemanticBC data.rightPresentation).square.right sourcePackage)
    _ = coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
        (coreFiberIteratedLift
            ((toSemanticBC data.leftPresentation).square.top ≫
              (toSemanticBC data.rightPresentation).square.top)
            (toSemanticBC data.rightPresentation).square.right
            nestedPackage ≫
          ((horizontalBCPastingComponentComparison data).hom.app
            nestedPackage).1) := Category.assoc _ _ _
    _ = _ := congrArg
      (fun q => coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫ q)
      (horizontalBCPastingComponentComparison_hom_fac data
        nestedPackage)

/-- The left normalization compositor identifies the literal left-composite
lift with the normalized-left composite lift. -/
theorem horizontalBCPastingLeftRoute_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    (coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
        coreFiberIteratedLift
          (toSemanticBC data.leftPresentation).square.left
          ((toSemanticBC data.leftPresentation).square.bottom ≫
            (toSemanticBC data.rightPresentation).square.bottom)
          ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
            sourcePackage)) ≫
      ((coreFiberTransportFunctor
        ((toSemanticBC data.leftPresentation).square.bottom ≫
          (toSemanticBC data.rightPresentation).square.bottom)).map
        (coreFiberCompositorApp data.pasteNorthwestIso.inv
          (toSemanticBC data.leftPresentation).square.left
          sourcePackage).inv).1 =
    coreFiberIteratedLift
      (normalizedNestedPasteSquare (.horizontal data)).left
      ((toSemanticBC data.leftPresentation).square.bottom ≫
        (toSemanticBC data.rightPresentation).square.bottom)
      sourcePackage := by
  simpa only [normalizedNestedPasteSquare] using
    coreFiberTripleLift_compositor_inv_whisker_fac
      data.pasteNorthwestIso.inv
      (toSemanticBC data.leftPresentation).square.left
      ((toSemanticBC data.leftPresentation).square.bottom ≫
        (toSemanticBC data.rightPresentation).square.bottom)
      sourcePackage


/-- The left normalization and bottom equality transport finish the normalized
outer lift factorization. -/
theorem horizontalBCPastingLeftBottomRoute_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    ((coreFiberLift data.pasteNorthwestIso.inv sourcePackage ≫
        coreFiberIteratedLift
          (toSemanticBC data.leftPresentation).square.left
          ((toSemanticBC data.leftPresentation).square.bottom ≫
            (toSemanticBC data.rightPresentation).square.bottom)
          ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
            sourcePackage)) ≫
      ((coreFiberTransportFunctor
        ((toSemanticBC data.leftPresentation).square.bottom ≫
          (toSemanticBC data.rightPresentation).square.bottom)).map
        (coreFiberCompositorApp data.pasteNorthwestIso.inv
          (toSemanticBC data.leftPresentation).square.left
          sourcePackage).inv).1) ≫
      ((coreFiberTransportEqIso
        (horizontalBCPastingNormalizedBottom_eq data).symm).hom.app
          ((coreFiberTransportFunctor
            (normalizedNestedPasteSquare (.horizontal data)).left).obj
              sourcePackage)).1 =
    coreFiberIteratedLift
      (normalizedNestedPasteSquare (.horizontal data)).left
      (normalizedNestedPasteSquare (.horizontal data)).bottom
      sourcePackage := by
  calc
    _ = coreFiberIteratedLift
          (data.pasteNorthwestIso.inv ≫
            (toSemanticBC data.leftPresentation).square.left)
          ((toSemanticBC data.leftPresentation).square.bottom ≫
            (toSemanticBC data.rightPresentation).square.bottom)
          sourcePackage ≫
        ((coreFiberTransportEqIso
          (horizontalBCPastingNormalizedBottom_eq data).symm).hom.app
            ((coreFiberTransportFunctor
              (normalizedNestedPasteSquare (.horizontal data)).left).obj
                sourcePackage)).1 := congrArg
      (fun q => q ≫
        ((coreFiberTransportEqIso
          (horizontalBCPastingNormalizedBottom_eq data).symm).hom.app
            ((coreFiberTransportFunctor
              (normalizedNestedPasteSquare (.horizontal data)).left).obj
                sourcePackage)).1)
      (coreFiberTripleLift_compositor_inv_whisker_fac
        data.pasteNorthwestIso.inv
        (toSemanticBC data.leftPresentation).square.left
        ((toSemanticBC data.leftPresentation).square.bottom ≫
          (toSemanticBC data.rightPresentation).square.bottom)
        sourcePackage)
    _ = _ := coreFiberIteratedLift_transportEqIso_fac
      (normalizedNestedPasteSquare (.horizontal data)).left
      ((toSemanticBC data.leftPresentation).square.bottom ≫
        (toSemanticBC data.rightPresentation).square.bottom)
      (normalizedNestedPasteSquare (.horizontal data)).bottom
      (horizontalBCPastingNormalizedBottom_eq data).symm sourcePackage

/-- The top normalization whisker is the mapped compositor component. -/
theorem horizontalBCPastingNormalizedTop_hom_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    ((Functor.isoWhiskerRight
      (horizontalBCPastingNormalizedTopCompositor data)
      (coreFiberTransportFunctor
        (toSemanticBC data.rightPresentation).square.right)).hom.app
          sourcePackage).1 =
      ((coreFiberTransportFunctor
        (toSemanticBC data.rightPresentation).square.right).map
        (coreFiberCompositorApp data.pasteNorthwestIso.inv
          ((toSemanticBC data.leftPresentation).square.top ≫
            (toSemanticBC data.rightPresentation).square.top)
          sourcePackage).hom).1 := by
  rfl

/-- The normalized outer top-right lift is the explicit northwest-normalized
component source lift. -/
theorem horizontalBCPastingNormalizedSourceLift_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    coreFiberIteratedLift
        (normalizedNestedPasteSquare (.horizontal data)).top
        (normalizedNestedPasteSquare (.horizontal data)).right sourcePackage =
      coreFiberIteratedLift
        (data.pasteNorthwestIso.inv ≫
          ((toSemanticBC data.leftPresentation).square.top ≫
            (toSemanticBC data.rightPresentation).square.top))
        (toSemanticBC data.rightPresentation).square.right
        sourcePackage := rfl

/-- Left whiskering evaluates an isomorphism component at the transported
source package. -/
theorem coreFiber_isoWhiskerLeft_hom_app_val
    {U : AtomCarrier.{u}} {W X Y : ExtractionInstance U}
    (F : CoreFiber W ⥤ CoreFiber X) {G H : CoreFiber X ⥤ CoreFiber Y}
    (e : G ≅ H) (sourcePackage : CoreFiber W) :
    (((F.isoWhiskerLeft e).hom.app sourcePackage)).1 =
      (e.hom.app (F.obj sourcePackage)).1 := rfl



end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
