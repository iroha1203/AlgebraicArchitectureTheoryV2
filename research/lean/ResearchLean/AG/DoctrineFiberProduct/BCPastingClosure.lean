import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema

/-!
# Beck--Chevalley pullback-pasting closure

This module packages the first K4/E obligation of G-110.  For either generated
horizontal or vertical paste, one theorem returns the pullback certificate for
the literal nested square, the pullback certificate for the generated outer
`BCPresentation`, and the canonical normalized realization equality relating
them.  All three fields are theorem outputs; the direction-indexed input
contains only the finite-code seed data.

Comparison, diagnostic, and compositor compatibility are deliberately not
claimed here.  They remain later K4 obligations over this closure package.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open CategoryTheory.Limits
open AtomFoundation

/--
The pullback and realization outputs shared by horizontal and vertical
finite-code Beck--Chevalley pasting.
-/
structure BCPastingClosure
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCPastingInput U) : Prop where
  /-- The literal nested horizontal or vertical paste is a pullback square. -/
  nested_isPullback :
    IsPullback (nestedPasteSquare input).left
      (nestedPasteSquare input).top
      (nestedPasteSquare input).bottom
      (nestedPasteSquare input).right
  /-- The finite-code constructor generates a validated outer pullback square. -/
  outer_isPullback :
    IsPullback (toSemanticBC (pastePresentation input)).square.left
      (toSemanticBC (pastePresentation input)).square.top
      (toSemanticBC (pastePresentation input)).square.bottom
      (toSemanticBC (pastePresentation input)).square.right
  /-- The generated outer presentation realizes the canonically normalized paste. -/
  realization_eq :
    toSemanticBC (pastePresentation input) =
      normalizedNestedPasteSemanticInput input

/--
Both directions of the finite-code pasting constructor satisfy the complete
pullback-and-realization closure package.
-/
theorem bcPastingClosure
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCPastingInput U) : BCPastingClosure input where
  nested_isPullback := nestedPasteSquare_isPullback input
  outer_isPullback := (toSemanticBC_sound (pastePresentation input)).1
  realization_eq := toSemanticBC_pastePresentation_eq input

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
