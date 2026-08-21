import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema
import ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses

/-!
# Finite witnesses for Beck--Chevalley pasting

The examples below exercise both pasting directions with noninvertible finite
arrows.  Each nested diagram contains two genuine generated pullback squares;
the outer presentation again has four compatible source cells.  The final
example instantiates the one-field authored 2-cell table directly from the
reviewed G-106 comparator datum.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open CategoryTheory.Limits
open AtomFoundation
open TransportCoherence

/-- Executable equality for the concrete finite Atom carrier. -/
local instance finiteBCPastingCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Horizontal and vertical noninvertible pastes -/

/--
Horizontal seed: constant `2 → 1`, identity `1 → 1`, and constant
`2 → 1`.  The generated right square shares its first projection with the
generated left square by construction.
-/
def finiteHorizontalBCPastingData :
    HorizontalBCPastingData FiniteModel.carrier where
  southwest := finiteTwoSourceInstance
  middleSouth := finiteOneSourceInstance
  northeast := finiteTwoSourceInstance
  southeast := finiteOneSourceInstance
  bottomLeft := finiteConstantPresentation
  bottomRight := idTypedPresentation finiteOneSourceInstance
  right := finiteConstantPresentation
  diagnostic := finiteBCDiagnosticPresentation

/-- Both component presentations of the horizontal seed share one diagnostic. -/
theorem finiteHorizontalBCPasting_diagnostic_shared :
    finiteHorizontalBCPastingData.leftPresentation.1.diagnostic =
        finiteHorizontalBCPastingData.rightPresentation.1.diagnostic := rfl

/-- The horizontal outer presentation has the expected four-cell source. -/
theorem finiteHorizontalBCPasting_sourceCard :
    readBCProjection (.cart .top .sourceCard)
        finiteHorizontalBCPastingData.pastePresentation = ULift.up 4 := by
  rfl

/-- The literal horizontal nested square is a semantic pullback. -/
theorem finiteHorizontalBCPasting_isPullback :
    IsPullback finiteHorizontalBCPastingData.nestedSquare.left
      finiteHorizontalBCPastingData.nestedSquare.top
      finiteHorizontalBCPastingData.nestedSquare.bottom
      finiteHorizontalBCPastingData.nestedSquare.right :=
  finiteHorizontalBCPastingData.nestedSquare_isPullback

/-- The concrete horizontal components inhabit the pair-level strict domain. -/
theorem finiteHorizontalBCPasting_strictComposable :
    StrictHorizontalComposable
      finiteHorizontalBCPastingData.leftPresentation
      finiteHorizontalBCPastingData.rightPresentation :=
  finiteHorizontalBCPastingData.strictComposable

/-- The horizontal outer decoder equals the canonically transported literal paste. -/
theorem finiteHorizontalBCPasting_realization_eq :
    toSemanticBC finiteHorizontalBCPastingData.pastePresentation =
      normalizedNestedPasteSemanticInput
        (.horizontal finiteHorizontalBCPastingData) :=
  toSemanticBC_pastePresentation_eq
    (.horizontal finiteHorizontalBCPastingData)

/--
Vertical seed: constant `2 → 1` on the upper right and lower bottom,
with identity `1 → 1` on the lower right.
-/
def finiteVerticalBCPastingData :
    VerticalBCPastingData FiniteModel.carrier where
  northeast := finiteTwoSourceInstance
  middleEast := finiteOneSourceInstance
  southwest := finiteTwoSourceInstance
  southeast := finiteOneSourceInstance
  rightTop := finiteConstantPresentation
  bottom := finiteConstantPresentation
  rightBottom := idTypedPresentation finiteOneSourceInstance
  diagnostic := finiteBCDiagnosticPresentation

/-- Both component presentations of the vertical seed share one diagnostic. -/
theorem finiteVerticalBCPasting_diagnostic_shared :
    finiteVerticalBCPastingData.upperPresentation.1.diagnostic =
        finiteVerticalBCPastingData.lowerPresentation.1.diagnostic := rfl

/-- The vertical outer presentation has the expected four-cell source. -/
theorem finiteVerticalBCPasting_sourceCard :
    readBCProjection (.cart .top .sourceCard)
        finiteVerticalBCPastingData.pastePresentation = ULift.up 4 := by
  rfl

/-- The literal vertical nested square is a semantic pullback. -/
theorem finiteVerticalBCPasting_isPullback :
    IsPullback finiteVerticalBCPastingData.nestedSquare.left
      finiteVerticalBCPastingData.nestedSquare.top
      finiteVerticalBCPastingData.nestedSquare.bottom
      finiteVerticalBCPastingData.nestedSquare.right :=
  finiteVerticalBCPastingData.nestedSquare_isPullback

/-- The concrete vertical components inhabit the pair-level strict domain. -/
theorem finiteVerticalBCPasting_strictComposable :
    StrictVerticalComposable
      finiteVerticalBCPastingData.upperPresentation
      finiteVerticalBCPastingData.lowerPresentation :=
  finiteVerticalBCPastingData.strictComposable

/-- The vertical outer decoder equals the canonically transported literal paste. -/
theorem finiteVerticalBCPasting_realization_eq :
    toSemanticBC finiteVerticalBCPastingData.pastePresentation =
      normalizedNestedPasteSemanticInput
        (.vertical finiteVerticalBCPastingData) :=
  toSemanticBC_pastePresentation_eq
    (.vertical finiteVerticalBCPastingData)

/-! ## Strict-composability boundary instances -/

/-- The constant BC presentation is not horizontally composable with itself. -/
theorem finiteConstantBC_not_strictHorizontal_self :
    ¬ StrictHorizontalComposable finiteConstantBCPresentation
      finiteConstantBCPresentation := by
  intro composable
  have hnorth := composable.north_eq
  have hcard := congrArg
    (fun code : FiniteInstanceCode FiniteModel.carrier =>
      code.doctrine.sourceCard) hnorth
  have hpullbackCard :
      (pullbackInstanceCode
          (finiteConstantBCPresentation.1.cospan.first)
          (finiteConstantBCPresentation.1.cospan.second)).doctrine.sourceCard =
        4 := by
    simpa [finiteConstantBCPresentation, finiteConstantBCRawCode,
      finiteConstantBCCospan, pullbackInstanceCode] using
        finiteConstantPullback_sourceCard
  change
    finiteConstantBCPresentation.1.cospan.secondSource.doctrine.sourceCard =
      (pullbackInstanceCode
        finiteConstantBCPresentation.1.cospan.first
        finiteConstantBCPresentation.1.cospan.second).doctrine.sourceCard
    at hcard
  rw [hpullbackCard] at hcard
  norm_num [finiteConstantBCPresentation, finiteConstantBCRawCode,
    finiteConstantBCCospan, finiteTwoSourceInstance,
    finiteAllDoctrineCode] at hcard

/-- The constant BC presentation is not vertically composable with itself. -/
theorem finiteConstantBC_not_strictVertical_self :
    ¬ StrictVerticalComposable finiteConstantBCPresentation
      finiteConstantBCPresentation := by
  intro composable
  have heast := composable.east_eq
  have hcard := congrArg
    (fun code : FiniteInstanceCode FiniteModel.carrier =>
      code.doctrine.sourceCard) heast
  norm_num [finiteConstantBCPresentation, finiteConstantBCRawCode,
    finiteConstantBCCospan, finiteOneSourceInstance, finiteTwoSourceInstance,
    finiteAllDoctrineCode] at hcard

/-! ## One-field authored 2-cell table -/

/-- The concrete G-106 authored comparator inhabits the F0b2 raw schema. -/
noncomputable def finiteAuthoredBC2CellPresentation :=
  AuthoredBC2CellPresentation.ofTransportData
    finiteBCDiagnosticTransportData

/-- The concrete authored table contains the identity fiber automorphism. -/
theorem finiteAuthoredBC2CellPresentation_comparator :
    finiteAuthoredBC2CellPresentation.comparator
        FiniteBCDiagnosticCell.cell = 1 := rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
