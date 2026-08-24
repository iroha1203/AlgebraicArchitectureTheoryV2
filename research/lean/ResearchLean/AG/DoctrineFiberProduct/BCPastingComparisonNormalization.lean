import ResearchLean.AG.DoctrineFiberProduct.BCPastingComparisonRealization

/-!
# Beck--Chevalley pasted-comparison northwest normalization

The literal horizontal and vertical pastes start at an iterated pullback,
whereas the canonical outer presentation starts at the independently generated
outer pullback.  The pasting schema supplies their canonical northwest
isomorphism.  This module exposes that isomorphism uniformly in the pasting
direction and factors both incident covariant transport functors through its
inverse by the generated G-109 compositor.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The direction-independent canonical isomorphism from the literal pasted
northwest object to the northwest object used by the normalized outer square. -/
noncomputable def bcPastingNorthwestIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCPastingInput U) :
    (nestedPasteSquare input).northwest ≅
      (normalizedNestedPasteSquare input).northwest := by
  cases input with
  | horizontal data => exact data.pasteNorthwestIso
  | vertical data => exact data.pasteNorthwestIso

/-- Horizontal normalized top-edge transport factors through the inverse
northwest comparison and the literal pasted top edge. -/
noncomputable def horizontalBCPastingNormalizedTopCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.horizontal data)).top ≅
      coreFiberTransportFunctor (bcPastingNorthwestIso (.horizontal data)).inv ⋙
        coreFiberTransportFunctor data.nestedSquare.top :=
  coreFiberCompositor _ _

/-- Horizontal normalized left-edge transport factors through the inverse
northwest comparison and the literal pasted left edge. -/
noncomputable def horizontalBCPastingNormalizedLeftCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.horizontal data)).left ≅
      coreFiberTransportFunctor (bcPastingNorthwestIso (.horizontal data)).inv ⋙
        coreFiberTransportFunctor data.nestedSquare.left :=
  coreFiberCompositor _ _

/-- Vertical normalized top-edge transport factors through the inverse
northwest comparison and the literal pasted top edge. -/
noncomputable def verticalBCPastingNormalizedTopCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.vertical data)).top ≅
      coreFiberTransportFunctor (bcPastingNorthwestIso (.vertical data)).inv ⋙
        coreFiberTransportFunctor data.nestedSquare.top :=
  coreFiberCompositor _ _

/-- Vertical normalized left-edge transport factors through the inverse
northwest comparison and the literal pasted left edge. -/
noncomputable def verticalBCPastingNormalizedLeftCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.vertical data)).left ≅
      coreFiberTransportFunctor (bcPastingNorthwestIso (.vertical data)).inv ⋙
        coreFiberTransportFunctor data.nestedSquare.left :=
  coreFiberCompositor _ _

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
