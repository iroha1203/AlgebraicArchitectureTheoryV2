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

/--
The finite unit factor graph is unchanged after replacing the canonical code by
the raw-distinct padded presentation with the same semantic decoder.
-/
theorem finiteCoreTransportReindexUnit_paddedPresentationCompatibility :
    ((coreTransportReindexUnit
      (typedRealizableHom finiteSelectiveTwoToSupportPresentation)).app
        finiteSelectiveTwoReindexedFourAxisObject).1 ≫
      (selectedTypedCoreFiberPresentationComparisonApp
        finiteSelectiveTwoToSupportPresentation
        finitePaddedSelectiveTwoToSupportPresentation
        finiteSelectiveTwoToSupportPresentation_semanticHom_eq
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            finiteSelectiveTwoToSupportPresentation)).obj
              finiteSelectiveTwoReindexedFourAxisObject)).hom.1 ≫
      (selectedTypedCoreFiberCartesianLift
        finitePaddedSelectiveTwoToSupportPresentation
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            finiteSelectiveTwoToSupportPresentation)).obj
              finiteSelectiveTwoReindexedFourAxisObject)).hom =
    coreFiberLift
      (typedPresentationToSemantic finiteSelectiveTwoToSupportPresentation)
      finiteSelectiveTwoReindexedFourAxisObject :=
  coreTransportReindexUnit_typedPresentationCompatibility
    finiteSelectiveTwoToSupportPresentation
    finitePaddedSelectiveTwoToSupportPresentation
    finiteSelectiveTwoToSupportPresentation_semanticHom_eq
    finiteSelectiveTwoReindexedFourAxisObject

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
