import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyCleavage
import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyFactorization

/-! Pasting of semantic Beck--Chevalley squares. -/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence
open CategoryTheory.TwoSquare

set_option maxHeartbeats 3000000

/-- Two horizontally composable exact pointed squares. -/
structure SemanticHorizontalPasting (U : AtomCarrier.{u}) where
  northwest : ExtractionInstance U
  northmiddle : ExtractionInstance U
  northeast : ExtractionInstance U
  southwest : ExtractionInstance U
  southmiddle : ExtractionInstance U
  southeast : ExtractionInstance U
  topLeft : northwest ⟶ northmiddle
  topRight : northmiddle ⟶ northeast
  bottomLeft : southwest ⟶ southmiddle
  bottomRight : southmiddle ⟶ southeast
  left : northwest ⟶ southwest
  middle : northmiddle ⟶ southmiddle
  right : northeast ⟶ southeast
  leftCommutes : topLeft ≫ middle = left ≫ bottomLeft
  rightCommutes : topRight ≫ right = middle ≫ bottomRight

namespace SemanticHorizontalPasting

def first {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    ExtInstSquare U where
  northwest := data.northwest
  northeast := data.northmiddle
  southwest := data.southwest
  southeast := data.southmiddle
  top := data.topLeft
  left := data.left
  right := data.middle
  bottom := data.bottomLeft
  commutes := data.leftCommutes.symm

def second {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    ExtInstSquare U where
  northwest := data.northmiddle
  northeast := data.northeast
  southwest := data.southmiddle
  southeast := data.southeast
  top := data.topRight
  left := data.middle
  right := data.right
  bottom := data.bottomRight
  commutes := data.rightCommutes.symm

def outer {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    ExtInstSquare U where
  northwest := data.northwest
  northeast := data.northeast
  southwest := data.southwest
  southeast := data.southeast
  top := data.topLeft ≫ data.topRight
  left := data.left
  right := data.right
  bottom := data.bottomLeft ≫ data.bottomRight
  commutes := by
    symm
    calc
      (data.topLeft ≫ data.topRight) ≫ data.right =
          data.topLeft ≫ (data.topRight ≫ data.right) := Category.assoc _ _ _
      _ = data.topLeft ≫ (data.middle ≫ data.bottomRight) :=
        congrArg (data.topLeft ≫ ·) data.rightCommutes
      _ = (data.topLeft ≫ data.middle) ≫ data.bottomRight :=
        (Category.assoc _ _ _).symm
      _ = (data.left ≫ data.bottomLeft) ≫ data.bottomRight :=
        congrArg (· ≫ data.bottomRight) data.leftCommutes
      _ = data.left ≫ (data.bottomLeft ≫ data.bottomRight) :=
        Category.assoc _ _ _

/-- Generic covariant horizontal pasting, aligned with the independently
generated outer square. -/
theorem transport_square_pasting
    {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    indexedHorizontalComponentRoute
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.leftCommutes.symm : IndexedBaseSquareTerm U
            data.topLeft data.left data.middle data.bottomLeft))
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.rightCommutes.symm : IndexedBaseSquareTerm U
            data.topRight data.middle data.right data.bottomRight)) =
      semanticCoreTransportSquareIso data.outer := by
  let first : ValidatedIndexedBaseSquare U
      data.topLeft data.left data.middle data.bottomLeft :=
    .ofTerm (.leaf data.leftCommutes.symm)
  let second : ValidatedIndexedBaseSquare U
      data.topRight data.middle data.right data.bottomRight :=
    .ofTerm (.leaf data.rightCommutes.symm)
  have h := indexedHorizontalPastingCoherence first second
  change indexedHorizontalComponentRoute first second =
    semanticCoreTransportSquareIso data.outer at h
  exact h

/-- The normalized mate of the pasted squares is the canonical mate of the
outer semantic square. -/
theorem mate_normalized_outer
    {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    (mateEquiv
      (semanticCoreTransportReindexAdjunction
        ⟨data.northwest, data.southwest, data.left⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northeast, data.southeast, data.right⟩)
      (indexedHorizontalComponentRoute
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.leftCommutes.symm : IndexedBaseSquareTerm U
            data.topLeft data.left data.middle data.bottomLeft))
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.rightCommutes.symm : IndexedBaseSquareTerm U
            data.topRight data.middle data.right data.bottomRight))).hom).natTrans =
      semanticCoreBeckChevalleyMate data.outer := by
  rw [transport_square_pasting]
  rfl

/-- The mate of the horizontal composite of covariant semantic squares is
the vertical composite of their generated mates. -/
theorem mate_pasting
    {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    (mateEquiv
      (semanticCoreTransportReindexAdjunction
        ⟨data.northwest, data.southwest, data.left⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northeast, data.southeast, data.right⟩)
      ((semanticCoreTransportSquareIso data.first).hom ≫ₕ
        (semanticCoreTransportSquareIso data.second).hom)) =
      (TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.first)) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.second)) := by
  simpa only [semanticCoreBeckChevalleyMate] using
    mateEquiv_vcomp
      (semanticCoreTransportReindexAdjunction
        ⟨data.northwest, data.southwest, data.left⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northmiddle, data.southmiddle, data.middle⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northeast, data.southeast, data.right⟩)
      (semanticCoreTransportSquareIso data.first).hom
      (semanticCoreTransportSquareIso data.second).hom


end SemanticHorizontalPasting

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
