import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMate
import ResearchLean.AG.DoctrineFiberProduct.CoreTransportReindexCleavageIndependence

/-!
# Cleavage independence of the canonical core Beck--Chevalley mate

For arbitrary cartesian cleavages on the two reindexing legs of a validated
Beck--Chevalley presentation, this module generates the corresponding mate
from the Cycle 36 adjunctions.  It proves that changing either cleavage changes
the mate only through the canonical cartesian-lift comparisons, and identifies
the Cycle 37 selected-cleavage mate as the normalization anchor.

No adjunction, unit, counit, square comparison, mate, or comparison certificate
is supplied by a caller.  This is choice independence up to generated natural
isomorphism; it is not literal functor equality and does not assert that any
mate is an isomorphism.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Arbitrary-cleavage mates -/

/-- The exact realized first projection used by the left arbitrary cleavage. -/
def bcLeftInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) : RealizableHom U :=
  typedRealizableHom (bcLeftPresentation presentation)

/-- The exact realized second cospan leg used by the right arbitrary cleavage. -/
def bcRightInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) : RealizableHom U :=
  typedRealizableHom (bcRightPresentation presentation)

/--
The fixed-orientation Beck--Chevalley mate generated from arbitrary cleavages
on `pi1` and `sigma2`.
-/
noncomputable def coreBeckChevalleyCleavageMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic) :
    leftCleavage.reindexFunctor ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)) ⟶
      coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation)) ⋙
        rightCleavage.reindexFunctor :=
  (mateEquiv
    (coreTransportCleavageAdjunction (bcLeftInput presentation) leftCleavage)
    (coreTransportCleavageAdjunction (bcRightInput presentation) rightCleavage)
    (bcCoreTransportSquareIso presentation).hom).natTrans

/--
The arbitrary-cleavage mate component is its generated right unit, mapped
covariant square, and mapped left counit.
-/
theorem coreBeckChevalleyCleavageMate_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic)
    (sourcePackage : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    (coreBeckChevalleyCleavageMate presentation leftCleavage rightCleavage).app
        sourcePackage =
      (coreTransportCleavageUnit (bcRightInput presentation) rightCleavage).app
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj
            (leftCleavage.reindexFunctor.obj sourcePackage)) ≫
        rightCleavage.reindexFunctor.map
          ((bcCoreTransportSquareIso presentation).hom.app
            (leftCleavage.reindexFunctor.obj sourcePackage)) ≫
        rightCleavage.reindexFunctor.map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((coreTransportCleavageCounit
              (bcLeftInput presentation) leftCleavage).app sourcePackage)) := by
  simp [coreBeckChevalleyCleavageMate, mateEquiv_apply,
    coreTransportCleavageUnit, coreTransportCleavageCounit]

/-- Naturality of every generated arbitrary-cleavage mate. -/
theorem coreBeckChevalleyCleavageMate_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic)
    {sourcePackage targetPackage :
      CoreFiber presentation.1.cospan.firstSource.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    (leftCleavage.reindexFunctor ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation presentation))).map hom ≫
        (coreBeckChevalleyCleavageMate presentation leftCleavage
          rightCleavage).app targetPackage =
      (coreBeckChevalleyCleavageMate presentation leftCleavage
        rightCleavage).app sourcePackage ≫
        (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation)) ⋙
          rightCleavage.reindexFunctor).map hom :=
  (coreBeckChevalleyCleavageMate presentation leftCleavage
    rightCleavage).naturality hom

/--
The mate component is the right arbitrary adjunction's transpose of the
covariant square followed by the left arbitrary counit.
-/
theorem coreBeckChevalleyCleavageMate_homEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic)
    (sourcePackage : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    (coreBeckChevalleyCleavageMate presentation leftCleavage rightCleavage).app
        sourcePackage =
      (coreTransportCleavageAdjunction
        (bcRightInput presentation) rightCleavage).homEquiv
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj
            (leftCleavage.reindexFunctor.obj sourcePackage))
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).obj sourcePackage)
          ((bcCoreTransportSquareIso presentation).hom.app
              (leftCleavage.reindexFunctor.obj sourcePackage) ≫
            (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              ((coreTransportCleavageCounit
                (bcLeftInput presentation) leftCleavage).app
                  sourcePackage)) := by
  rw [coreBeckChevalleyCleavageMate_app]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

/-! ## Canonical comparison under a change of cleavage -/

/--
Changing both cleavages commutes with the generated mate through the canonical
Cycle 33 comparisons.
-/
theorem coreBeckChevalleyCleavageMate_comparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (leftFirst leftSecond : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightFirst rightSecond : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic) :
    Functor.whiskerRight
          (CoreFiberCartesianCleavage.comparison leftFirst leftSecond).hom
          (coreFiberTransportFunctor
            (typedPresentationToSemantic (bcTopPresentation presentation))) ≫
        coreBeckChevalleyCleavageMate presentation leftSecond rightSecond =
      coreBeckChevalleyCleavageMate presentation leftFirst rightFirst ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic (bcBottomPresentation presentation)))
          (CoreFiberCartesianCleavage.comparison
            rightFirst rightSecond).hom := by
  apply NatTrans.ext
  funext sourcePackage
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [coreBeckChevalleyCleavageMate_homEquiv,
    coreBeckChevalleyCleavageMate_homEquiv]
  have leftCounitComparison :
      (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation presentation))).map
          ((CoreFiberCartesianCleavage.comparison
            leftFirst leftSecond).hom.app sourcePackage) ≫
        (coreTransportCleavageCounit
          (bcLeftInput presentation) leftSecond).app sourcePackage =
      (coreTransportCleavageCounit
        (bcLeftInput presentation) leftFirst).app sourcePackage := by
    simpa [bcLeftInput] using
      coreTransportCleavageCounit_comparison
        (bcLeftInput presentation) leftFirst leftSecond sourcePackage
  calc
    (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).map
          ((CoreFiberCartesianCleavage.comparison
            leftFirst leftSecond).hom.app sourcePackage) ≫
        (coreTransportCleavageAdjunction
          (bcRightInput presentation) rightSecond).homEquiv _ _
            ((bcCoreTransportSquareIso presentation).hom.app
                (leftSecond.reindexFunctor.obj sourcePackage) ≫
              (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation))).map
                ((coreTransportCleavageCounit
                  (bcLeftInput presentation) leftSecond).app sourcePackage)) =
      (coreTransportCleavageAdjunction
        (bcRightInput presentation) rightSecond).homEquiv _ _
          ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcRightPresentation presentation))).map
              ((coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcTopPresentation presentation))).map
                ((CoreFiberCartesianCleavage.comparison
                  leftFirst leftSecond).hom.app sourcePackage)) ≫
            ((bcCoreTransportSquareIso presentation).hom.app
                (leftSecond.reindexFunctor.obj sourcePackage) ≫
              (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation))).map
                ((coreTransportCleavageCounit
                  (bcLeftInput presentation) leftSecond).app
                    sourcePackage))) := by
        exact ((coreTransportCleavageAdjunction
          (bcRightInput presentation) rightSecond).homEquiv_naturality_left
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcTopPresentation presentation))).map
              ((CoreFiberCartesianCleavage.comparison
                leftFirst leftSecond).hom.app sourcePackage))
            ((bcCoreTransportSquareIso presentation).hom.app
                (leftSecond.reindexFunctor.obj sourcePackage) ≫
              (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation))).map
                ((coreTransportCleavageCounit
                  (bcLeftInput presentation) leftSecond).app
                    sourcePackage))).symm
    _ = (coreTransportCleavageAdjunction
        (bcRightInput presentation) rightSecond).homEquiv _ _
          ((bcCoreTransportSquareIso presentation).hom.app
              (leftFirst.reindexFunctor.obj sourcePackage) ≫
            (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              ((coreTransportCleavageCounit
                (bcLeftInput presentation) leftFirst).app sourcePackage)) := by
      apply congrArg
      calc
        _ = ((coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcTopPresentation presentation))) ⋙
              coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcRightPresentation presentation))).map
              ((CoreFiberCartesianCleavage.comparison
                leftFirst leftSecond).hom.app sourcePackage) ≫
            ((bcCoreTransportSquareIso presentation).hom.app
                (leftSecond.reindexFunctor.obj sourcePackage) ≫
              (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation))).map
                ((coreTransportCleavageCounit
                  (bcLeftInput presentation) leftSecond).app sourcePackage)) := by
            rfl
        _ = _ := by
          rw [← Category.assoc]
          rw [(bcCoreTransportSquareIso presentation).hom.naturality]
          rw [Functor.comp_map]
          rw [Category.assoc, ← Functor.map_comp]
          rw [leftCounitComparison]
    _ = (coreTransportCleavageAdjunction
          (bcRightInput presentation) rightFirst).homEquiv _ _
            ((bcCoreTransportSquareIso presentation).hom.app
                (leftFirst.reindexFunctor.obj sourcePackage) ≫
              (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation))).map
                ((coreTransportCleavageCounit
                  (bcLeftInput presentation) leftFirst).app sourcePackage)) ≫
        (CoreFiberCartesianCleavage.comparison
          rightFirst rightSecond).hom.app
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).obj
              sourcePackage) := by
      exact (coreTransportCleavageHomEquiv_comparison
        (bcRightInput presentation) rightFirst rightSecond
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).obj
          (leftFirst.reindexFunctor.obj sourcePackage))
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation presentation))).obj sourcePackage)
        ((bcCoreTransportSquareIso presentation).hom.app
            (leftFirst.reindexFunctor.obj sourcePackage) ≫
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((coreTransportCleavageCounit
              (bcLeftInput presentation) leftFirst).app
                sourcePackage))).symm

/-! ## The selected mate as normalization anchor -/

/-- The selected mate is the selected right transpose of its square/counit composite. -/
theorem coreBeckChevalleyMate_homEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (sourcePackage : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    (coreBeckChevalleyMate presentation).app sourcePackage =
      (bcRightAdjunction presentation).homEquiv
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).obj
          ((selectedCoreFiberReindexFunctor
            (bcLeftInput presentation)).obj sourcePackage))
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation presentation))).obj sourcePackage)
        ((bcCoreTransportSquareIso presentation).hom.app
            ((selectedCoreFiberReindexFunctor
              (bcLeftInput presentation)).obj sourcePackage) ≫
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((bcLeftAdjunction presentation).counit.app sourcePackage)) := by
  rw [coreBeckChevalleyMate_app]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

/-- The selected right adjunction's forward correspondence is the Cycle 35 transpose. -/
theorem bcRightAdjunction_homEquiv_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (sourcePackage : CoreFiber (bcRightInput presentation).semantic.source)
    (targetPackage : CoreFiber (bcRightInput presentation).semantic.target)
    (hom : (coreFiberTransportFunctor
      (bcRightInput presentation).semantic.hom).obj sourcePackage ⟶
        targetPackage) :
    (bcRightAdjunction presentation).homEquiv
        sourcePackage targetPackage hom =
      coreTransportToReindexHom (bcRightInput presentation)
        sourcePackage targetPackage hom := by
  change (Adjunction.mkOfHomEquiv
    (coreTransportReindexCoreHomEquiv
      (bcRightInput presentation))).homEquiv
        sourcePackage targetPackage hom = _
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/--
Every arbitrary-cleavage mate compares canonically with the Cycle 37 selected
mate through the two generated arbitrary-to-selected bridges.
-/
theorem coreBeckChevalleyCleavageMate_selectedComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic) :
    Functor.whiskerRight
          (coreFiberCleavageSelectedComparison
            (bcLeftInput presentation) leftCleavage).hom
          (coreFiberTransportFunctor
            (typedPresentationToSemantic (bcTopPresentation presentation))) ≫
        coreBeckChevalleyMate presentation =
      coreBeckChevalleyCleavageMate presentation leftCleavage rightCleavage ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic (bcBottomPresentation presentation)))
          (coreFiberCleavageSelectedComparison
            (bcRightInput presentation) rightCleavage).hom := by
  apply NatTrans.ext
  funext sourcePackage
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [coreBeckChevalleyMate_homEquiv,
    coreBeckChevalleyCleavageMate_homEquiv]
  have leftCounitBridge :
      (coreTransportCleavageCounit
        (bcLeftInput presentation) leftCleavage).app sourcePackage =
        (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation presentation))).map
            ((coreFiberCleavageSelectedComparison
              (bcLeftInput presentation) leftCleavage).hom.app
                sourcePackage) ≫
          (bcLeftAdjunction presentation).counit.app sourcePackage := by
    simpa [bcLeftInput, bcLeftAdjunction,
      coreTransportReindexCounit] using
      coreTransportCleavageCounit_app
        (bcLeftInput presentation) leftCleavage sourcePackage
  calc
    (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).map
          ((coreFiberCleavageSelectedComparison
            (bcLeftInput presentation) leftCleavage).hom.app sourcePackage) ≫
        (bcRightAdjunction presentation).homEquiv _ _
          ((bcCoreTransportSquareIso presentation).hom.app
              ((selectedCoreFiberReindexFunctor
                (bcLeftInput presentation)).obj sourcePackage) ≫
            (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              ((bcLeftAdjunction presentation).counit.app sourcePackage)) =
      (bcRightAdjunction presentation).homEquiv _ _
        ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcRightPresentation presentation))).map
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcTopPresentation presentation))).map
              ((coreFiberCleavageSelectedComparison
                (bcLeftInput presentation) leftCleavage).hom.app
                  sourcePackage)) ≫
          ((bcCoreTransportSquareIso presentation).hom.app
              ((selectedCoreFiberReindexFunctor
                (bcLeftInput presentation)).obj sourcePackage) ≫
            (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              ((bcLeftAdjunction presentation).counit.app
                sourcePackage))) := by
        exact ((bcRightAdjunction presentation).homEquiv_naturality_left
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).map
            ((coreFiberCleavageSelectedComparison
              (bcLeftInput presentation) leftCleavage).hom.app
                sourcePackage))
          ((bcCoreTransportSquareIso presentation).hom.app
              ((selectedCoreFiberReindexFunctor
                (bcLeftInput presentation)).obj sourcePackage) ≫
            (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              ((bcLeftAdjunction presentation).counit.app
                sourcePackage))).symm
    _ = (bcRightAdjunction presentation).homEquiv _ _
        ((bcCoreTransportSquareIso presentation).hom.app
            (leftCleavage.reindexFunctor.obj sourcePackage) ≫
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((coreTransportCleavageCounit
              (bcLeftInput presentation) leftCleavage).app
                sourcePackage)) := by
      apply congrArg
      calc
        _ = ((coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcTopPresentation presentation))) ⋙
              coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcRightPresentation presentation))).map
              ((coreFiberCleavageSelectedComparison
                (bcLeftInput presentation) leftCleavage).hom.app
                  sourcePackage) ≫
            ((bcCoreTransportSquareIso presentation).hom.app
                ((selectedCoreFiberReindexFunctor
                  (bcLeftInput presentation)).obj sourcePackage) ≫
              (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation))).map
                ((bcLeftAdjunction presentation).counit.app
                  sourcePackage)) := by rfl
        _ = _ := by
          rw [← Category.assoc]
          rw [(bcCoreTransportSquareIso presentation).hom.naturality]
          rw [Functor.comp_map]
          rw [Category.assoc, ← Functor.map_comp]
          rw [leftCounitBridge]
    _ = coreTransportToReindexHom
        (bcRightInput presentation)
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).obj
          (leftCleavage.reindexFunctor.obj sourcePackage))
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation presentation))).obj sourcePackage)
        ((bcCoreTransportSquareIso presentation).hom.app
            (leftCleavage.reindexFunctor.obj sourcePackage) ≫
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((coreTransportCleavageCounit
              (bcLeftInput presentation) leftCleavage).app
                sourcePackage)) := by
      exact bcRightAdjunction_homEquiv_apply presentation _ _ _
    _ = (coreTransportCleavageAdjunction
          (bcRightInput presentation) rightCleavage).homEquiv _ _
            ((bcCoreTransportSquareIso presentation).hom.app
                (leftCleavage.reindexFunctor.obj sourcePackage) ≫
              (coreFiberTransportFunctor
                (typedPresentationToSemantic
                  (bcBottomPresentation presentation))).map
                ((coreTransportCleavageCounit
                  (bcLeftInput presentation) leftCleavage).app
                    sourcePackage)) ≫
        (coreFiberCleavageSelectedComparison
          (bcRightInput presentation) rightCleavage).hom.app
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).obj
              sourcePackage) := by
      rw [coreTransportCleavageAdjunction_homEquiv_apply]
      simp [coreFiberCleavageSelectedComparison]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
