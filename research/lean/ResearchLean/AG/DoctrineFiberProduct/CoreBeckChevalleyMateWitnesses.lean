import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMate
import ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingWitnesses

/-!
# Finite witnesses for the canonical core Beck--Chevalley mate

This module fires the generated mate on an asymmetric finite pullback.  The
bottom leg is the typed identity of the portfolio-support instance and the
right leg is the existing noninvertible selective-two-to-support
presentation.  Thus the identity side is a control while the right reindexing
leg is genuinely noninvertible.

The mate is evaluated at the reviewed four-axis support package and its
naturality square is fired on the genuine nonidentity axis-swap map.  No
pullback square, adjunction, unit, counit, or mate component is supplied by the
witness.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory CategoryTheory.Limits
open AtomFoundation CrossStageCoherence

/-- Executable Atom equality for the finite carrier. -/
local instance finiteCanonicalMateAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## A validated asymmetric finite pullback code -/

/-- Identity/support versus selective-two/support cospan. -/
def finiteCanonicalMateCospan :
    CartCospanPresentation FiniteModel.carrier where
  firstSource := finitePortfolioSupportInstance
  secondSource := finiteSelectiveTwoInstance
  base := finitePortfolioSupportInstance
  first := idTypedPresentation finitePortfolioSupportInstance
  second := finiteSelectiveTwoToSupportPresentation

/-- The authored selected-point table for the asymmetric cospan. -/
def finiteCanonicalMatePointCode : CompatiblePointCode where
  sourcePoints := fun index => if index = 0 then 1 else 0
  basePoint := 1
  images := fun _ => 1

/-- The finite selected-point table agrees with both generated cospan legs. -/
theorem finiteCanonicalMatePointCode_wellFormed :
    finiteCanonicalMatePointCode.WellFormed finiteCanonicalMateCospan := by
  simp [CompatiblePointCode.WellFormed, finiteCanonicalMatePointCode,
    finiteCanonicalMateCospan, finitePortfolioSupportInstance,
    finiteModelDoctrineCode,
    finiteSelectiveTwoInstance, finiteSelectiveTwoPoint,
    finiteSelectiveTwoToSupportPresentation,
    finiteSelectiveTwoToOnePresentation,
    finiteSelectiveOneToSupportPresentation, compPresentation,
    idTypedPresentation]

/-- Raw finite input for the canonical-mate witness. -/
def finiteCanonicalMateRawCode : BCRawCode FiniteModel.carrier where
  cospan := finiteCanonicalMateCospan
  compatiblePoints := finiteCanonicalMatePointCode
  diagnostic := finiteBCDiagnosticPresentation

/-- The raw witness passes the exact finite validator. -/
theorem finiteCanonicalMateRawCode_wellFormed :
    finiteCanonicalMateRawCode.WellFormed :=
  finiteCanonicalMatePointCode_wellFormed

/-- Validated finite presentation used to fire the generated mate. -/
def finiteCanonicalMatePresentation : BCPresentation FiniteModel.carrier :=
  ⟨finiteCanonicalMateRawCode, finiteCanonicalMateRawCode_wellFormed⟩

/-- Its exact decoded four-leg square is producer-derived pullback data. -/
theorem finiteCanonicalMate_isPullback :
    IsPullback
      (typedPresentationToSemantic
        (bcLeftPresentation finiteCanonicalMatePresentation))
      (typedPresentationToSemantic
        (bcTopPresentation finiteCanonicalMatePresentation))
      (typedPresentationToSemantic
        (bcBottomPresentation finiteCanonicalMatePresentation))
      (typedPresentationToSemantic
        (bcRightPresentation finiteCanonicalMatePresentation)) :=
  bcPresentation_isPullback_from_producer finiteCanonicalMatePresentation

/-! ## Nondegenerate mate firing -/

/-- The relevant right reindexing leg is the reviewed noninvertible prefix. -/
theorem finiteCanonicalMate_right_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcRightPresentation finiteCanonicalMatePresentation)) := by
  simpa [typedPresentationToSemantic, typedRealizableHom_hom,
    bcRightPresentation, finiteCanonicalMatePresentation,
    finiteCanonicalMateRawCode, finiteCanonicalMateCospan,
    finiteSelectiveTwoToSupportInput] using
      finiteSelectiveTwoToSupportInput_not_isIso

/-- First compatible pullback source, over the selected selective-two cell. -/
def finiteCanonicalMatePullbackSourceFirst :
    (pullbackInstanceCode
      (idTypedPresentation finitePortfolioSupportInstance)
      finiteSelectiveTwoToSupportPresentation).doctrine.Source :=
  (compatibleSourceEquiv
      (idTypedPresentation finitePortfolioSupportInstance)
      finiteSelectiveTwoToSupportPresentation).symm
    ⟨(finitePortfolioSupportInstance.point, finiteSelectiveTwoPoint), rfl⟩

/-- Second compatible pullback source, over the other selective-two cell. -/
def finiteCanonicalMatePullbackSourceOther :
    (pullbackInstanceCode
      (idTypedPresentation finitePortfolioSupportInstance)
      finiteSelectiveTwoToSupportPresentation).doctrine.Source :=
  (compatibleSourceEquiv
      (idTypedPresentation finitePortfolioSupportInstance)
      finiteSelectiveTwoToSupportPresentation).symm
    ⟨(finitePortfolioSupportInstance.point, finiteSelectiveTwoOther), rfl⟩

/-- The two generated pullback sources are distinct. -/
theorem finiteCanonicalMatePullbackSources_ne :
    finiteCanonicalMatePullbackSourceFirst ≠
      finiteCanonicalMatePullbackSourceOther := by
  intro equality
  have pairEquality := congrArg
    (compatibleSourceEquiv
      (idTypedPresentation finitePortfolioSupportInstance)
      finiteSelectiveTwoToSupportPresentation) equality
  have secondEquality := congrArg (fun pair => pair.val.2) pairEquality
  simpa [finiteCanonicalMatePullbackSourceFirst,
    finiteCanonicalMatePullbackSourceOther] using
      finiteSelectiveTwoToSupport_source_points_ne secondEquality

/-- The first projection identifies those two distinct generated sources. -/
theorem finiteCanonicalMate_left_sourceMap_eq :
    (typedPresentationToSemantic
      (bcLeftPresentation finiteCanonicalMatePresentation)).doctrineHom.sourceMap
        finiteCanonicalMatePullbackSourceFirst =
      (typedPresentationToSemantic
        (bcLeftPresentation finiteCanonicalMatePresentation)).doctrineHom.sourceMap
          finiteCanonicalMatePullbackSourceOther := by
  rfl

/-- The generated left projection is also genuinely noninvertible. -/
theorem finiteCanonicalMate_left_not_isIso :
    ¬ IsIso
      (typedPresentationToSemantic
        (bcLeftPresentation finiteCanonicalMatePresentation)) := by
  intro hiso
  letI : IsIso
      (typedPresentationToSemantic
        (bcLeftPresentation finiteCanonicalMatePresentation)) := hiso
  exact finiteCanonicalMatePullbackSources_ne
    (extInstHom_sourceMap_injective_of_isIso
      (typedPresentationToSemantic
        (bcLeftPresentation finiteCanonicalMatePresentation))
      finiteCanonicalMate_left_sourceMap_eq)

/-- The generated canonical mate for the asymmetric finite presentation. -/
noncomputable def finiteCanonicalCoreBeckChevalleyMate :=
  coreBeckChevalleyMate finiteCanonicalMatePresentation

/-- Its concrete component has the generated unit--square--counit expansion. -/
theorem finiteCanonicalCoreBeckChevalleyMate_app :
    (finiteCanonicalCoreBeckChevalleyMate.app finiteReindexFourAxisTarget) =
      (bcRightAdjunction finiteCanonicalMatePresentation).unit.app
          ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcTopPresentation finiteCanonicalMatePresentation))).obj
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation finiteCanonicalMatePresentation))).obj
                finiteReindexFourAxisTarget)) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcRightPresentation finiteCanonicalMatePresentation))).map
          ((bcCoreTransportSquareIso finiteCanonicalMatePresentation).hom.app
            ((selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcLeftPresentation finiteCanonicalMatePresentation))).obj
                  finiteReindexFourAxisTarget)) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcRightPresentation finiteCanonicalMatePresentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation finiteCanonicalMatePresentation))).map
            ((bcLeftAdjunction finiteCanonicalMatePresentation).counit.app
              finiteReindexFourAxisTarget)) :=
  coreBeckChevalleyMate_app finiteCanonicalMatePresentation
    finiteReindexFourAxisTarget

/-- Naturality is exercised on the genuine nonidentity support-fiber map. -/
theorem finiteCanonicalCoreBeckChevalleyMate_axisSwap_naturality :
    (selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation finiteCanonicalMatePresentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation finiteCanonicalMatePresentation))).map
          finiteReindexAxisSwapHom ≫
        finiteCanonicalCoreBeckChevalleyMate.app finiteReindexFourAxisTarget =
      finiteCanonicalCoreBeckChevalleyMate.app finiteReindexFourAxisTarget ≫
        (coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation finiteCanonicalMatePresentation)) ⋙
            selectedCoreFiberReindexFunctor
              (typedRealizableHom
                (bcRightPresentation finiteCanonicalMatePresentation))).map
          finiteReindexAxisSwapHom :=
  coreBeckChevalleyMate_naturality finiteCanonicalMatePresentation
    finiteReindexAxisSwapHom

/-- The map on which mate naturality is fired is not an identity control. -/
theorem finiteCanonicalMate_axisSwap_ne_id :
    finiteReindexAxisSwapHom ≠ 𝟙 finiteReindexFourAxisTarget :=
  finiteReindexAxisSwapHom_ne_id

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
