import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingBottomAlignment

/-!
# Beck--Chevalley comparison lift factorization

The generated semantic Beck--Chevalley comparison carries the iterated lift
around a commutative square to the iterated lift along the other two sides.
This factorization is the component-level normalization used to compare the
outer square with the horizontally pasted component route.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The inverse compositor sends the iterated lift back to the generated
lift along the composite. -/
theorem coreFiberIteratedLift_compositor_inv_fac
    {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U}
    (first : X ⟶ Y) (second : Y ⟶ Z) (sourcePackage : CoreFiber X) :
    coreFiberIteratedLift first second sourcePackage ≫
        (coreFiberCompositorApp first second sourcePackage).inv.1 =
      coreFiberLift (first ≫ second) sourcePackage := by
  rw [← coreFiberCompositorApp_hom_fac first second sourcePackage]
  rw [Category.assoc]
  have hcancel :
      (coreFiberCompositorApp first second sourcePackage).hom.1 ≫
          (coreFiberCompositorApp first second sourcePackage).inv.1 =
        (𝟙 _ : (coreFiberTransportFunctor (first ≫ second)).obj sourcePackage ⟶
          (coreFiberTransportFunctor (first ≫ second)).obj sourcePackage).1 :=
    congrArg (fun f => f.1)
      (Iso.hom_inv_id (coreFiberCompositorApp first second sourcePackage))
  rw [hcancel]
  rfl

/-- The semantic square comparison carries the top-right iterated lift to
the left-bottom iterated lift. -/
theorem bcSemanticCoreTransportSquareIso_hom_fac
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    (sourcePackage : CoreFiber input.square.northwest) :
    coreFiberIteratedLift input.square.top input.square.right sourcePackage ≫
        ((bcSemanticCoreTransportSquareIso input).hom.app sourcePackage).1 =
      coreFiberIteratedLift input.square.left input.square.bottom sourcePackage := by
  unfold bcSemanticCoreTransportSquareIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ← Category.assoc]
  change coreFiberIteratedLift input.square.top input.square.right sourcePackage ≫
      ((coreFiberCompositorApp input.square.top input.square.right
          sourcePackage).inv.1 ≫
        ((eqToIso (congrArg coreFiberTransportFunctor
          input.square.commutes.symm)).hom.app sourcePackage).1 ≫
        (coreFiberCompositorApp input.square.left input.square.bottom
          sourcePackage).hom.1) =
    coreFiberIteratedLift input.square.left input.square.bottom sourcePackage
  simp only [← Category.assoc]
  rw [coreFiberIteratedLift_compositor_inv_fac]
  rw [coreFiberLift_eqToIso_fac _ _ input.square.commutes.symm]
  exact coreFiberCompositorApp_hom_fac _ _ sourcePackage

/-- Whiskering a compositor component by a third transport changes the
composite-first iterated lift into the corresponding three-stage lift. -/
theorem coreFiberIteratedLift_compositor_whisker_fac
    {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (first : W ⟶ X) (second : X ⟶ Y) (third : Y ⟶ Z)
    (sourcePackage : CoreFiber W) :
    coreFiberIteratedLift (first ≫ second) third sourcePackage ≫
        ((coreFiberTransportFunctor third).map
          (coreFiberCompositorApp first second sourcePackage).hom).1 =
      coreFiberLift first sourcePackage ≫
        coreFiberIteratedLift second third
          ((coreFiberTransportFunctor first).obj sourcePackage) := by
  calc
    _ = coreFiberLift (first ≫ second) sourcePackage ≫
        (coreFiberLift third
            ((coreFiberTransportFunctor (first ≫ second)).obj sourcePackage) ≫
          ((coreFiberTransportFunctor third).map
            (coreFiberCompositorApp first second sourcePackage).hom).1) := by
      rfl
    _ = coreFiberLift (first ≫ second) sourcePackage ≫
        ((coreFiberCompositorApp first second sourcePackage).hom.1 ≫
          coreFiberLift third
            ((coreFiberTransportFunctor second).obj
              ((coreFiberTransportFunctor first).obj sourcePackage))) := by
      simpa only [coreFiberTransportFunctor] using congrArg
        (fun q => coreFiberLift (first ≫ second) sourcePackage ≫ q)
        (coreFiberTransportMap_fac third
          (coreFiberCompositorApp first second sourcePackage).hom)
    _ = (coreFiberLift (first ≫ second) sourcePackage ≫
          (coreFiberCompositorApp first second sourcePackage).hom.1) ≫
        coreFiberLift third
          ((coreFiberTransportFunctor second).obj
            ((coreFiberTransportFunctor first).obj sourcePackage)) :=
      (Category.assoc _ _ _).symm
    _ = coreFiberIteratedLift first second sourcePackage ≫
        coreFiberLift third
          ((coreFiberTransportFunctor second).obj
            ((coreFiberTransportFunctor first).obj sourcePackage)) := by
      rw [coreFiberCompositorApp_hom_fac]
    _ = _ := rfl

/-- The final inverse compositor contracts the last two stages of a
three-stage lift. -/
theorem coreFiberTripleLift_compositor_inv_fac
    {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (first : W ⟶ X) (second : X ⟶ Y) (third : Y ⟶ Z)
    (sourcePackage : CoreFiber W) :
    (coreFiberIteratedLift first second sourcePackage ≫
        coreFiberLift third
          ((coreFiberTransportFunctor second).obj
            ((coreFiberTransportFunctor first).obj sourcePackage))) ≫
        (coreFiberCompositorApp second third
          ((coreFiberTransportFunctor first).obj sourcePackage)).inv.1 =
      coreFiberIteratedLift first (second ≫ third) sourcePackage := by
  calc
    _ = coreFiberLift first sourcePackage ≫
        (coreFiberIteratedLift second third
            ((coreFiberTransportFunctor first).obj sourcePackage) ≫
          (coreFiberCompositorApp second third
            ((coreFiberTransportFunctor first).obj sourcePackage)).inv.1) := by
      unfold coreFiberIteratedLift
      simp only [Category.assoc]
    _ = coreFiberLift first sourcePackage ≫
        coreFiberLift (second ≫ third)
          ((coreFiberTransportFunctor first).obj sourcePackage) := by
      rw [coreFiberIteratedLift_compositor_inv_fac]
    _ = _ := rfl

/-- A semantic square comparison remains lift-normalized after whiskering on
the right by one further transport. -/
theorem bcSemanticCoreTransportSquareIso_whisker_right_hom_fac
    {U : AtomCarrier.{u}} (input : BCSemanticInput U)
    {target : ExtractionInstance U} (third : input.square.southeast ⟶ target)
    (sourcePackage : CoreFiber input.square.northwest) :
    (coreFiberIteratedLift input.square.top input.square.right sourcePackage ≫
        coreFiberLift third
          ((coreFiberTransportFunctor input.square.right).obj
            ((coreFiberTransportFunctor input.square.top).obj sourcePackage))) ≫
        ((coreFiberTransportFunctor third).map
          ((bcSemanticCoreTransportSquareIso input).hom.app sourcePackage)).1 =
      coreFiberIteratedLift input.square.left input.square.bottom sourcePackage ≫
        coreFiberLift third
          ((coreFiberTransportFunctor input.square.bottom).obj
            ((coreFiberTransportFunctor input.square.left).obj sourcePackage)) := by
  calc
    _ = coreFiberIteratedLift input.square.top input.square.right sourcePackage ≫
        (coreFiberLift third
            ((coreFiberTransportFunctor input.square.right).obj
              ((coreFiberTransportFunctor input.square.top).obj sourcePackage)) ≫
          ((coreFiberTransportFunctor third).map
            ((bcSemanticCoreTransportSquareIso input).hom.app sourcePackage)).1) :=
      Category.assoc _ _ _
    _ = coreFiberIteratedLift input.square.top input.square.right sourcePackage ≫
        (((bcSemanticCoreTransportSquareIso input).hom.app sourcePackage).1 ≫
          coreFiberLift third
            ((coreFiberTransportFunctor input.square.bottom).obj
              ((coreFiberTransportFunctor input.square.left).obj sourcePackage))) := by
      simpa only [coreFiberTransportFunctor] using congrArg
        (fun q => coreFiberIteratedLift input.square.top input.square.right
          sourcePackage ≫ q)
        (coreFiberTransportMap_fac third
          ((bcSemanticCoreTransportSquareIso input).hom.app sourcePackage))
    _ = (coreFiberIteratedLift input.square.top input.square.right sourcePackage ≫
          ((bcSemanticCoreTransportSquareIso input).hom.app sourcePackage).1) ≫
        coreFiberLift third
          ((coreFiberTransportFunctor input.square.bottom).obj
            ((coreFiberTransportFunctor input.square.left).obj sourcePackage)) :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [bcSemanticCoreTransportSquareIso_hom_fac]

/-- The literal horizontal component route carries the outer top-right
iterated lift to the outer left-bottom iterated lift. -/
theorem horizontalBCPastingComponentComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber data.nestedSquare.northwest) :
    coreFiberIteratedLift
          ((toSemanticBC data.leftPresentation).square.top ≫
            (toSemanticBC data.rightPresentation).square.top)
          (toSemanticBC data.rightPresentation).square.right sourcePackage ≫
        ((horizontalBCPastingComponentComparison data).hom.app sourcePackage).1 =
      coreFiberIteratedLift
        (toSemanticBC data.leftPresentation).square.left
        ((toSemanticBC data.leftPresentation).square.bottom ≫
          (toSemanticBC data.rightPresentation).square.bottom)
        sourcePackage := by
  unfold horizontalBCPastingComponentComparison
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change coreFiberIteratedLift
        ((toSemanticBC data.leftPresentation).square.top ≫
          (toSemanticBC data.rightPresentation).square.top)
        (toSemanticBC data.rightPresentation).square.right sourcePackage ≫
      (((coreFiberTransportFunctor
          (toSemanticBC data.rightPresentation).square.right).map
        (coreFiberCompositorApp
          (toSemanticBC data.leftPresentation).square.top
          (toSemanticBC data.rightPresentation).square.top
          sourcePackage).hom).1 ≫
      ((bcSemanticCoreTransportSquareIso
        (toSemanticBC data.rightPresentation)).hom.app
          ((coreFiberTransportFunctor
            (toSemanticBC data.leftPresentation).square.top).obj
              sourcePackage)).1 ≫
      ((coreFiberTransportFunctor
          (toSemanticBC data.rightPresentation).square.bottom).map
        ((bcSemanticCoreTransportSquareIso
          (toSemanticBC data.leftPresentation)).hom.app sourcePackage)).1 ≫
      (coreFiberCompositorApp
        (toSemanticBC data.leftPresentation).square.bottom
        (toSemanticBC data.rightPresentation).square.bottom
        ((coreFiberTransportFunctor
          (toSemanticBC data.leftPresentation).square.left).obj
            sourcePackage)).inv.1) =
    coreFiberIteratedLift
      (toSemanticBC data.leftPresentation).square.left
      ((toSemanticBC data.leftPresentation).square.bottom ≫
        (toSemanticBC data.rightPresentation).square.bottom)
      sourcePackage
  simp only [← Category.assoc]
  rw [coreFiberIteratedLift_compositor_whisker_fac]
  rw [Category.assoc
    (coreFiberLift (toSemanticBC data.leftPresentation).square.top sourcePackage)
    (coreFiberIteratedLift
      (toSemanticBC data.rightPresentation).square.top
      (toSemanticBC data.rightPresentation).square.right
      ((coreFiberTransportFunctor
        (toSemanticBC data.leftPresentation).square.top).obj sourcePackage))]
  rw [bcSemanticCoreTransportSquareIso_hom_fac]
  have hleft :=
    bcSemanticCoreTransportSquareIso_whisker_right_hom_fac
      (toSemanticBC data.leftPresentation)
      (toSemanticBC data.rightPresentation).square.bottom sourcePackage
  have hroute :
      coreFiberLift (toSemanticBC data.leftPresentation).square.top sourcePackage ≫
          coreFiberIteratedLift
            (toSemanticBC data.rightPresentation).square.left
            (toSemanticBC data.rightPresentation).square.bottom
            ((coreFiberTransportFunctor
              (toSemanticBC data.leftPresentation).square.top).obj sourcePackage) =
        coreFiberIteratedLift
            (toSemanticBC data.leftPresentation).square.top
            (toSemanticBC data.leftPresentation).square.right sourcePackage ≫
          coreFiberLift
            (toSemanticBC data.rightPresentation).square.bottom
            ((coreFiberTransportFunctor
                (toSemanticBC data.leftPresentation).square.right).obj
              ((coreFiberTransportFunctor
                (toSemanticBC data.leftPresentation).square.top).obj
                  sourcePackage)) := by
    change coreFiberLift
          (toSemanticBC data.leftPresentation).square.top sourcePackage ≫
        (coreFiberLift
            (toSemanticBC data.leftPresentation).square.right
            ((coreFiberTransportFunctor
              (toSemanticBC data.leftPresentation).square.top).obj sourcePackage) ≫
          coreFiberLift
            (toSemanticBC data.rightPresentation).square.bottom _) =
      (coreFiberLift
          (toSemanticBC data.leftPresentation).square.top sourcePackage ≫
        coreFiberLift
          (toSemanticBC data.leftPresentation).square.right
          ((coreFiberTransportFunctor
            (toSemanticBC data.leftPresentation).square.top).obj sourcePackage)) ≫
        coreFiberLift
          (toSemanticBC data.rightPresentation).square.bottom _
    exact (Category.assoc _ _ _).symm
  rw [hroute]
  rw [hleft]
  exact coreFiberTripleLift_compositor_inv_fac
    (toSemanticBC data.leftPresentation).square.left
    (toSemanticBC data.leftPresentation).square.bottom
    (toSemanticBC data.rightPresentation).square.bottom sourcePackage

/-- Contracting the first two stages by an inverse compositor remains
lift-normalized after whiskering on the right. -/
theorem coreFiberTripleLift_compositor_inv_whisker_fac
    {U : AtomCarrier.{u}}
    {W X Y Z : ExtractionInstance U}
    (first : W ⟶ X) (second : X ⟶ Y) (third : Y ⟶ Z)
    (sourcePackage : CoreFiber W) :
    (coreFiberLift first sourcePackage ≫
        coreFiberIteratedLift second third
          ((coreFiberTransportFunctor first).obj sourcePackage)) ≫
        ((coreFiberTransportFunctor third).map
          (coreFiberCompositorApp first second sourcePackage).inv).1 =
      coreFiberIteratedLift (first ≫ second) third sourcePackage := by
  calc
    _ = (coreFiberIteratedLift first second sourcePackage ≫
          coreFiberLift third
            ((coreFiberTransportFunctor second).obj
              ((coreFiberTransportFunctor first).obj sourcePackage))) ≫
        ((coreFiberTransportFunctor third).map
          (coreFiberCompositorApp first second sourcePackage).inv).1 := by
      rfl
    _ = coreFiberIteratedLift first second sourcePackage ≫
        (coreFiberLift third
            ((coreFiberTransportFunctor second).obj
              ((coreFiberTransportFunctor first).obj sourcePackage)) ≫
          ((coreFiberTransportFunctor third).map
            (coreFiberCompositorApp first second sourcePackage).inv).1) :=
      Category.assoc _ _ _
    _ = coreFiberIteratedLift first second sourcePackage ≫
        ((coreFiberCompositorApp first second sourcePackage).inv.1 ≫
          coreFiberLift third
            ((coreFiberTransportFunctor (first ≫ second)).obj sourcePackage)) := by
      simpa only [coreFiberTransportFunctor] using congrArg
        (fun q => coreFiberIteratedLift first second sourcePackage ≫ q)
        (coreFiberTransportMap_fac third
          (coreFiberCompositorApp first second sourcePackage).inv)
    _ = (coreFiberIteratedLift first second sourcePackage ≫
          (coreFiberCompositorApp first second sourcePackage).inv.1) ≫
        coreFiberLift third
          ((coreFiberTransportFunctor (first ≫ second)).obj sourcePackage) :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      rw [coreFiberIteratedLift_compositor_inv_fac]
      rfl

/-- Equality transport of the second edge carries one iterated lift to the
iterated lift along the equal edge. -/
theorem coreFiberIteratedLift_eqToIso_fac
    {U : AtomCarrier.{u}}
    {W X Y : ExtractionInstance U}
    (first : W ⟶ X) (second third : X ⟶ Y) (edge_eq : second = third)
    (sourcePackage : CoreFiber W) :
    coreFiberIteratedLift first second sourcePackage ≫
        ((eqToIso (congrArg coreFiberTransportFunctor edge_eq)).hom.app
          ((coreFiberTransportFunctor first).obj sourcePackage)).1 =
      coreFiberIteratedLift first third sourcePackage := by
  unfold coreFiberIteratedLift
  rw [Category.assoc]
  rw [coreFiberLift_eqToIso_fac second third edge_eq]

/-- Equality transport exposed through `coreFiberTransportEqIso` has the same
iterated-lift factorization. -/
theorem coreFiberIteratedLift_transportEqIso_fac
    {U : AtomCarrier.{u}}
    {W X Y : ExtractionInstance U}
    (first : W ⟶ X) (second third : X ⟶ Y) (edge_eq : second = third)
    (sourcePackage : CoreFiber W) :
    coreFiberIteratedLift first second sourcePackage ≫
        ((coreFiberTransportEqIso edge_eq).hom.app
          ((coreFiberTransportFunctor first).obj sourcePackage)).1 =
      coreFiberIteratedLift first third sourcePackage := by
  exact coreFiberIteratedLift_eqToIso_fac
    first second third edge_eq sourcePackage

/-- The inverse equality transport has the corresponding reverse-edge lift
factorization. -/
theorem coreFiberIteratedLift_eqToIso_symm_fac
    {U : AtomCarrier.{u}}
    {W X Y : ExtractionInstance U}
    (first : W ⟶ X) (second third : X ⟶ Y) (edge_eq : third = second)
    (sourcePackage : CoreFiber W) :
    coreFiberIteratedLift first second sourcePackage ≫
        (((eqToIso (congrArg coreFiberTransportFunctor edge_eq)).symm).hom.app
          ((coreFiberTransportFunctor first).obj sourcePackage)).1 =
      coreFiberIteratedLift first third sourcePackage := by
  change coreFiberIteratedLift first second sourcePackage ≫
      ((eqToIso (congrArg coreFiberTransportFunctor edge_eq.symm)).hom.app
        ((coreFiberTransportFunctor first).obj sourcePackage)).1 =
    coreFiberIteratedLift first third sourcePackage
  exact coreFiberIteratedLift_eqToIso_fac
    first second third edge_eq.symm sourcePackage

/-- Composition in a core fiber is composition of the underlying package
morphisms. -/
theorem coreFiber_comp_val
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P Q R : CoreFiber X} (first : P ⟶ Q) (second : Q ⟶ R) :
    (first ≫ second).1 = first.1 ≫ second.1 := rfl

/-- The literal horizontal outer top edge is the composite of component tops. -/
theorem horizontalBCPastingNestedTop_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    data.nestedSquare.top =
      (toSemanticBC data.leftPresentation).square.top ≫
        (toSemanticBC data.rightPresentation).square.top := rfl

/-- The literal horizontal outer right edge is the right component edge. -/
theorem horizontalBCPastingNestedRight_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    data.nestedSquare.right =
      (toSemanticBC data.rightPresentation).square.right := rfl

/-- The literal horizontal outer left edge is the left component edge. -/
theorem horizontalBCPastingNestedLeft_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    data.nestedSquare.left =
      (toSemanticBC data.leftPresentation).square.left := rfl


end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
