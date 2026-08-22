import ResearchLean.AG.DoctrineFiberProduct.CoreTransportReindexAdjunction
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationWitnesses

/-!
# Finite witnesses for the core transport/reindexing adjunction

The generated adjunction is fired on the existing selective-two finite-code
arrow.  Its base leg is noninvertible, and naturality is exercised by the
genuine four-axis swap in the target fiber.  The same witness also fires unit,
counit, both inverse laws, both triangles, and raw-distinct presentation
replacement compatibility.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

local instance finiteCoreAdjunctionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The finite selected transport/reindexing adjunction over a noninvertible leg. -/
noncomputable def finiteCoreTransportReindexAdjunction :
    coreFiberTransportFunctor finiteSelectiveTwoToSupportInput.semantic.hom ⊣
      selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput :=
  coreTransportReindexAdjunction finiteSelectiveTwoToSupportInput

/-- The adjunction witness really uses the established noninvertible base leg. -/
theorem finiteCoreTransportReindexAdjunction_base_not_isIso :
    ¬ IsIso finiteSelectiveTwoToSupportInput.semantic.hom :=
  finiteSelectiveTwoReindexInput_not_isIso

/-- The finite counit is the cocartesian transpose of the identity. -/
theorem finiteCoreTransportReindexCounit_app :
    (coreTransportReindexCounit finiteSelectiveTwoToSupportInput).app
        finiteReindexFourAxisTarget =
      reindexToCoreTransportHom finiteSelectiveTwoToSupportInput
        finiteSelectiveTwoReindexedFourAxisObject
        finiteReindexFourAxisTarget
        (𝟙 finiteSelectiveTwoReindexedFourAxisObject) :=
  coreTransportReindexCounit_app finiteSelectiveTwoToSupportInput
    finiteReindexFourAxisTarget

/-- Forward transposition of the finite counit recovers the identity. -/
theorem finiteCoreTransportReindexCounit_forward_eq_id :
    coreTransportToReindexHom finiteSelectiveTwoToSupportInput
        finiteSelectiveTwoReindexedFourAxisObject
        finiteReindexFourAxisTarget
        ((coreTransportReindexCounit finiteSelectiveTwoToSupportInput).app
          finiteReindexFourAxisTarget) =
      𝟙 finiteSelectiveTwoReindexedFourAxisObject := by
  rw [finiteCoreTransportReindexCounit_app]
  exact coreTransportToReindexHom_toCoreTransport
    finiteSelectiveTwoToSupportInput finiteSelectiveTwoReindexedFourAxisObject
    finiteReindexFourAxisTarget (𝟙 finiteSelectiveTwoReindexedFourAxisObject)

/-- Backward transposition of the finite unit recovers the identity. -/
theorem finiteCoreTransportReindexUnit_backward_eq_id :
    reindexToCoreTransportHom finiteSelectiveTwoToSupportInput
        finiteSelectiveTwoReindexedFourAxisObject
        ((coreFiberTransportFunctor
          finiteSelectiveTwoToSupportInput.semantic.hom).obj
            finiteSelectiveTwoReindexedFourAxisObject)
        ((coreTransportReindexUnit finiteSelectiveTwoToSupportInput).app
          finiteSelectiveTwoReindexedFourAxisObject) =
      𝟙 ((coreFiberTransportFunctor
        finiteSelectiveTwoToSupportInput.semantic.hom).obj
          finiteSelectiveTwoReindexedFourAxisObject) := by
  rw [coreTransportReindexUnit_app]
  exact reindexToCoreTransportHom_toReindex
    finiteSelectiveTwoToSupportInput finiteSelectiveTwoReindexedFourAxisObject
    ((coreFiberTransportFunctor
      finiteSelectiveTwoToSupportInput.semantic.hom).obj
        finiteSelectiveTwoReindexedFourAxisObject)
    (𝟙 ((coreFiberTransportFunctor
      finiteSelectiveTwoToSupportInput.semantic.hom).obj
        finiteSelectiveTwoReindexedFourAxisObject))

/-- The finite unit fires its canonical cocartesian/cartesian factor graph. -/
theorem finiteCoreTransportReindexUnit_fac :
    ((coreTransportReindexUnit finiteSelectiveTwoToSupportInput).app
        finiteSelectiveTwoReindexedFourAxisObject).1 ≫
      (selectedCoreFiberCartesianLift finiteSelectiveTwoToSupportInput
        ((coreFiberTransportFunctor
          finiteSelectiveTwoToSupportInput.semantic.hom).obj
            finiteSelectiveTwoReindexedFourAxisObject)).hom =
      coreFiberLift finiteSelectiveTwoToSupportInput.semantic.hom
        finiteSelectiveTwoReindexedFourAxisObject :=
  coreTransportReindexUnit_app_fac finiteSelectiveTwoToSupportInput
    finiteSelectiveTwoReindexedFourAxisObject

/-- The finite counit fires its canonical cocartesian/cartesian factor graph. -/
theorem finiteCoreTransportReindexCounit_fac :
    coreFiberLift finiteSelectiveTwoToSupportInput.semantic.hom
        finiteSelectiveTwoReindexedFourAxisObject ≫
      ((coreTransportReindexCounit finiteSelectiveTwoToSupportInput).app
        finiteReindexFourAxisTarget).1 =
      (selectedCoreFiberCartesianLift finiteSelectiveTwoToSupportInput
        finiteReindexFourAxisTarget).hom :=
  coreTransportReindexCounit_app_fac finiteSelectiveTwoToSupportInput
    finiteReindexFourAxisTarget

/--
Right naturality is fired with the genuine nonidentity axis swap over the
noninvertible selective base leg.
-/
theorem finiteCoreTransportReindex_axisSwap_naturality :
    coreTransportToReindexHom finiteSelectiveTwoToSupportInput
        finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
        ((coreTransportReindexCounit finiteSelectiveTwoToSupportInput).app
          finiteReindexFourAxisTarget ≫ finiteReindexAxisSwapHom) =
      coreTransportToReindexHom finiteSelectiveTwoToSupportInput
          finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
          ((coreTransportReindexCounit finiteSelectiveTwoToSupportInput).app
            finiteReindexFourAxisTarget) ≫
        finiteSelectiveTwoReindexedAxisSwap :=
  coreTransportToReindexHom_comp_right finiteSelectiveTwoToSupportInput
    finiteSelectiveTwoReindexedFourAxisObject
    ((coreTransportReindexCounit finiteSelectiveTwoToSupportInput).app
      finiteReindexFourAxisTarget)
    finiteReindexAxisSwapHom

/-- The nonidentity vertical morphism used by the finite naturality witness. -/
theorem finiteCoreTransportReindex_axisSwap_ne_id :
    finiteReindexAxisSwapHom ≠ 𝟙 finiteReindexFourAxisTarget :=
  finiteReindexAxisSwapHom_ne_id

/-- The left triangle is fired on the finite noninvertible base adjunction. -/
theorem finiteCoreTransportReindex_left_triangle :
    Functor.whiskerRight
        (coreTransportReindexUnit finiteSelectiveTwoToSupportInput)
        (coreFiberTransportFunctor finiteSelectiveTwoToSupportInput.semantic.hom) ≫
      (Functor.associator
        (coreFiberTransportFunctor finiteSelectiveTwoToSupportInput.semantic.hom)
        (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput)
        (coreFiberTransportFunctor
          finiteSelectiveTwoToSupportInput.semantic.hom)).hom ≫
      Functor.whiskerLeft
        (coreFiberTransportFunctor finiteSelectiveTwoToSupportInput.semantic.hom)
        (coreTransportReindexCounit finiteSelectiveTwoToSupportInput) =
      NatTrans.id
        (𝟭 (CoreFiber finiteSelectiveTwoToSupportInput.semantic.source) ⋙
          coreFiberTransportFunctor
            finiteSelectiveTwoToSupportInput.semantic.hom) :=
  coreTransportReindex_left_triangle finiteSelectiveTwoToSupportInput

/-- The right triangle is fired on the finite noninvertible base adjunction. -/
theorem finiteCoreTransportReindex_right_triangle :
    Functor.whiskerLeft
        (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput)
        (coreTransportReindexUnit finiteSelectiveTwoToSupportInput) ≫
      (Functor.associator
        (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput)
        (coreFiberTransportFunctor finiteSelectiveTwoToSupportInput.semantic.hom)
        (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput)).inv ≫
      Functor.whiskerRight
        (coreTransportReindexCounit finiteSelectiveTwoToSupportInput)
        (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput) =
      NatTrans.id
        (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput ⋙
          𝟭 (CoreFiber finiteSelectiveTwoToSupportInput.semantic.source)) :=
  coreTransportReindex_right_triangle finiteSelectiveTwoToSupportInput

/-- Producer-side comparison for the raw-distinct padded presentation. -/
noncomputable def finiteCoreTransportPaddedPresentationComparisonApp
    (sourcePackage : CoreFiber
      finiteSelectiveTwoInstance.toSemantic) :=
  typedCoreFiberTransportPresentationComparisonApp
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    sourcePackage

/-- Selector-side comparison for the raw-distinct padded presentation. -/
noncomputable def finiteCoreReindexPaddedPresentationComparisonApp
    (targetPackage : CoreFiber
      finitePortfolioSupportInstance.toSemantic) :=
  selectedTypedCoreFiberPresentationComparisonApp
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    targetPackage

/--
The actual hom-set correspondence commutes across the raw-distinct padded
presentation, fired on the finite counit over the noninvertible base leg.
-/
theorem finiteCoreTransportReindexHomEquiv_paddedPresentationCompatibility :
    (coreTransportReindexHomEquiv
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)
      finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget)
        ((coreTransportReindexCounit
          (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
            finiteReindexFourAxisTarget) ≫
      (finiteCoreReindexPaddedPresentationComparisonApp
        finiteReindexFourAxisTarget).hom =
    (coreTransportReindexHomEquiv
      (typedRealizableHom finitePaddedSelectiveTwoToSupportPresentation)
      finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget)
        ((finiteCoreTransportPaddedPresentationComparisonApp
          finiteSelectiveTwoReindexedFourAxisObject).inv ≫
          (coreTransportReindexCounit
            (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
              finiteReindexFourAxisTarget) :=
  coreTransportReindexHomEquiv_typedPresentationCompatibility
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
    ((coreTransportReindexCounit
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
        finiteReindexFourAxisTarget)

/-- The inverse correspondence commutes across the same padded presentation. -/
theorem finiteCoreTransportReindexInverse_paddedPresentationCompatibility :
    (finiteCoreTransportPaddedPresentationComparisonApp
      finiteSelectiveTwoReindexedFourAxisObject).hom ≫
      reindexToCoreTransportHom
        (typedRealizableHom finitePaddedSelectiveTwoToSupportPresentation)
        finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
        ((𝟙 finiteSelectiveTwoReindexedFourAxisObject) ≫
          (finiteCoreReindexPaddedPresentationComparisonApp
            finiteReindexFourAxisTarget).hom) =
    reindexToCoreTransportHom
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)
      finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
      (𝟙 finiteSelectiveTwoReindexedFourAxisObject) :=
  reindexToCoreTransportHom_typedPresentationCompatibility
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
    (𝟙 finiteSelectiveTwoReindexedFourAxisObject)

/-- The generated unit forms the padded-presentation comparison square. -/
theorem finiteCoreTransportReindexUnit_paddedPresentationCompatibility :
    (coreTransportReindexUnit
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
        finiteSelectiveTwoReindexedFourAxisObject ≫
      (finiteCoreReindexPaddedPresentationComparisonApp
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            finiteSelectiveTwoToSupportPresentation)).obj
              finiteSelectiveTwoReindexedFourAxisObject)).hom ≫
      (selectedTypedCoreFiberReindexFunctor
        finitePaddedSelectiveTwoToSupportPresentation).map
        (finiteCoreTransportPaddedPresentationComparisonApp
          finiteSelectiveTwoReindexedFourAxisObject).hom =
    (coreTransportReindexUnit
      (typedRealizableHom finitePaddedSelectiveTwoToSupportPresentation)).app
        finiteSelectiveTwoReindexedFourAxisObject :=
  coreTransportReindexUnit_typedPresentationCompatibility
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    finiteSelectiveTwoReindexedFourAxisObject

/-- The generated counit forms the padded-presentation comparison square. -/
theorem finiteCoreTransportReindexCounit_paddedPresentationCompatibility :
    (coreFiberTransportFunctor
      (typedPresentationToSemantic
        finiteSelectiveTwoToSupportPresentation)).map
        (finiteCoreReindexPaddedPresentationComparisonApp
          finiteReindexFourAxisTarget).hom ≫
      (finiteCoreTransportPaddedPresentationComparisonApp
        ((selectedTypedCoreFiberReindexFunctor
          finitePaddedSelectiveTwoToSupportPresentation).obj
            finiteReindexFourAxisTarget)).hom ≫
      (coreTransportReindexCounit
        (typedRealizableHom
          finitePaddedSelectiveTwoToSupportPresentation)).app
            finiteReindexFourAxisTarget =
    (coreTransportReindexCounit
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
        finiteReindexFourAxisTarget :=
  coreTransportReindexCounit_typedPresentationCompatibility
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    finiteReindexFourAxisTarget

/--
Presentation compatibility also fires after composing the finite counit with
the genuine nonidentity target-axis swap.
-/
theorem finiteCoreTransportReindexAxisSwap_paddedPresentationCompatibility :
    coreTransportToReindexHom
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)
      finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
      ((coreTransportReindexCounit
        (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
          finiteReindexFourAxisTarget ≫ finiteReindexAxisSwapHom) ≫
      (finiteCoreReindexPaddedPresentationComparisonApp
        finiteReindexFourAxisTarget).hom =
    coreTransportToReindexHom
      (typedRealizableHom finitePaddedSelectiveTwoToSupportPresentation)
      finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
      ((finiteCoreTransportPaddedPresentationComparisonApp
        finiteSelectiveTwoReindexedFourAxisObject).inv ≫
        ((coreTransportReindexCounit
          (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
            finiteReindexFourAxisTarget ≫ finiteReindexAxisSwapHom)) :=
  coreTransportToReindexHom_typedPresentationCompatibility
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    finiteSelectiveTwoReindexedFourAxisObject finiteReindexFourAxisTarget
    ((coreTransportReindexCounit
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
        finiteReindexFourAxisTarget ≫ finiteReindexAxisSwapHom)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
