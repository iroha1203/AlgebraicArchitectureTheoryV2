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
