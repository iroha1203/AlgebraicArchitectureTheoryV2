import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComparisonNormalization

/-!
# Vertical componentwise comparison factorization
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- G-110(E) vertical covariant-square predecessor API: expanding the generated
G-109 compositor on the second edge produces the corresponding three-stage
lift.  Its arrows and lift are ordinary categorical inputs; no factorization
certificate is assumed. -/
theorem coreFiberIteratedLift_second_compositor_hom_fac
    {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (first : W ⟶ X) (second : X ⟶ Y) (third : Y ⟶ Z)
    (sourcePackage : CoreFiber W) :
    coreFiberIteratedLift first (second ≫ third) sourcePackage ≫
        (coreFiberCompositorApp second third
          ((coreFiberTransportFunctor first).obj sourcePackage)).hom.1 =
      coreFiberLift first sourcePackage ≫
        coreFiberIteratedLift second third
          ((coreFiberTransportFunctor first).obj sourcePackage) := by
  unfold coreFiberIteratedLift
  rw [Category.assoc]
  rw [coreFiberCompositorApp_hom_fac]
  exact (Category.assoc _ _ _).symm

/-- G-110(E) vertical covariant-square predecessor API: the literal generated
component comparison carries the outer top-right lift to the outer left-bottom
lift.  The two square comparisons and both compositors arise from the upper
and lower presentations in `VerticalBCPastingData`; none is caller-authored. -/
theorem verticalBCPastingComponentComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber data.nestedSquare.northwest) :
    coreFiberIteratedLift
          (toSemanticBC data.upperPresentation).square.top
          ((toSemanticBC data.upperPresentation).square.right ≫
            (toSemanticBC data.lowerPresentation).square.right)
          sourcePackage ≫
        ((verticalBCPastingComponentComparison data).hom.app sourcePackage).1 =
      coreFiberIteratedLift
        ((toSemanticBC data.upperPresentation).square.left ≫
          (toSemanticBC data.lowerPresentation).square.left)
        (toSemanticBC data.lowerPresentation).square.bottom
        sourcePackage := by
  unfold verticalBCPastingComponentComparison
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change coreFiberIteratedLift
        (toSemanticBC data.upperPresentation).square.top
        ((toSemanticBC data.upperPresentation).square.right ≫
          (toSemanticBC data.lowerPresentation).square.right)
        sourcePackage ≫
      ((coreFiberCompositorApp
        (toSemanticBC data.upperPresentation).square.right
        (toSemanticBC data.lowerPresentation).square.right
        ((coreFiberTransportFunctor
          (toSemanticBC data.upperPresentation).square.top).obj
            sourcePackage)).hom.1 ≫
      ((coreFiberTransportFunctor
          (toSemanticBC data.lowerPresentation).square.right).map
        ((bcSemanticCoreTransportSquareIso
          (toSemanticBC data.upperPresentation)).hom.app sourcePackage)).1 ≫
      ((bcSemanticCoreTransportSquareIso
        (toSemanticBC data.lowerPresentation)).hom.app
          ((coreFiberTransportFunctor
            (toSemanticBC data.upperPresentation).square.left).obj
              sourcePackage)).1 ≫
      ((coreFiberTransportFunctor
          (toSemanticBC data.lowerPresentation).square.bottom).map
        (coreFiberCompositorApp
          (toSemanticBC data.upperPresentation).square.left
          (toSemanticBC data.lowerPresentation).square.left
          sourcePackage).inv).1) =
    coreFiberIteratedLift
      ((toSemanticBC data.upperPresentation).square.left ≫
        (toSemanticBC data.lowerPresentation).square.left)
      (toSemanticBC data.lowerPresentation).square.bottom
      sourcePackage
  simp only [← Category.assoc]
  rw [coreFiberIteratedLift_second_compositor_hom_fac]
  have hupper :=
    bcSemanticCoreTransportSquareIso_whisker_right_hom_fac
      (toSemanticBC data.upperPresentation)
      (toSemanticBC data.lowerPresentation).square.right sourcePackage
  have hsource :
      coreFiberLift (toSemanticBC data.upperPresentation).square.top
          sourcePackage ≫
        coreFiberIteratedLift
          (toSemanticBC data.upperPresentation).square.right
          (toSemanticBC data.lowerPresentation).square.right
          ((coreFiberTransportFunctor
            (toSemanticBC data.upperPresentation).square.top).obj
              sourcePackage) =
      coreFiberIteratedLift
          (toSemanticBC data.upperPresentation).square.top
          (toSemanticBC data.upperPresentation).square.right sourcePackage ≫
        coreFiberLift (toSemanticBC data.lowerPresentation).square.right
          ((coreFiberTransportFunctor
            (toSemanticBC data.upperPresentation).square.right).obj
              ((coreFiberTransportFunctor
                (toSemanticBC data.upperPresentation).square.top).obj
                  sourcePackage)) := by
    unfold coreFiberIteratedLift
    exact (Category.assoc _ _ _).symm
  rw [hsource]
  rw [hupper]
  have hlower := bcSemanticCoreTransportSquareIso_hom_fac
    (toSemanticBC data.lowerPresentation)
    ((coreFiberTransportFunctor
      (toSemanticBC data.upperPresentation).square.left).obj sourcePackage)
  have hmiddle :
      coreFiberIteratedLift
          (toSemanticBC data.upperPresentation).square.left
          (toSemanticBC data.upperPresentation).square.bottom sourcePackage ≫
        coreFiberLift (toSemanticBC data.lowerPresentation).square.right
          ((coreFiberTransportFunctor
            (toSemanticBC data.upperPresentation).square.bottom).obj
              ((coreFiberTransportFunctor
                (toSemanticBC data.upperPresentation).square.left).obj
                  sourcePackage)) =
      coreFiberLift (toSemanticBC data.upperPresentation).square.left
          sourcePackage ≫
        coreFiberIteratedLift
          (toSemanticBC data.lowerPresentation).square.top
          (toSemanticBC data.lowerPresentation).square.right
          ((coreFiberTransportFunctor
            (toSemanticBC data.upperPresentation).square.left).obj
              sourcePackage) := by
    unfold coreFiberIteratedLift
    exact Category.assoc _ _ _
  rw [hmiddle]
  rw [Category.assoc
    (coreFiberLift (toSemanticBC data.upperPresentation).square.left
      sourcePackage)
    (coreFiberIteratedLift
      (toSemanticBC data.lowerPresentation).square.top
      (toSemanticBC data.lowerPresentation).square.right
      ((coreFiberTransportFunctor
        (toSemanticBC data.upperPresentation).square.left).obj sourcePackage))]
  rw [hlower]
  exact coreFiberTripleLift_compositor_inv_whisker_fac
    (toSemanticBC data.upperPresentation).square.left
    (toSemanticBC data.lowerPresentation).square.left
    (toSemanticBC data.lowerPresentation).square.bottom sourcePackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
