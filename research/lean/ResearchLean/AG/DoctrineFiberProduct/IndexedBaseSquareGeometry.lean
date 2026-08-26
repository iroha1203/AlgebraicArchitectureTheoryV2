import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Diagnostic-free indexed base-square geometry

This module isolates the square boundary and pasting operations used by G-111.
Its data consists only of extraction instances, base arrows, commutativity, and
construction provenance.  Package, comparison, defect, and diagnostic data do
not occur in this surface.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- Construction provenance retained by an indexed base square. -/
inductive IndexedSquareRoute where
  /-- One authored square leaf. -/
  | leaf
  /-- An identity square. -/
  | identity
  /-- Sequential square composition. -/
  | comp (first second : IndexedSquareRoute)
  /-- Horizontal square pasting. -/
  | pasteHorizontal (first second : IndexedSquareRoute)
  /-- Vertical square pasting. -/
  | pasteVertical (first second : IndexedSquareRoute)
  deriving DecidableEq

/-- A commutative base square with un-erased construction provenance. -/
structure IndexedBaseSquare (U : AtomCarrier.{u})
    (northwest northeast southwest southeast : ExtractionInstance U) where
  top : northwest ⟶ northeast
  left : northwest ⟶ southwest
  right : northeast ⟶ southeast
  bottom : southwest ⟶ southeast
  commutes : left ≫ bottom = top ≫ right
  route : IndexedSquareRoute

namespace IndexedBaseSquare

/-- The horizontal identity square on one base arrow. -/
def identity {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) : IndexedBaseSquare U source target source target where
  top := hom
  left := 𝟙 source
  right := 𝟙 target
  bottom := hom
  commutes := by simp
  route := .identity

/-- Sequentially compose two vertically adjacent base squares. -/
def verticalComp {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    (first : IndexedBaseSquare U northwest northeast middleLeft middleRight)
    (second : IndexedBaseSquare U middleLeft middleRight southwest southeast)
    (boundary : first.bottom = second.top) :
    IndexedBaseSquare U northwest northeast southwest southeast where
  top := first.top
  left := first.left ≫ second.left
  right := first.right ≫ second.right
  bottom := second.bottom
  commutes := by
    rw [Category.assoc, second.commutes]
    rw [← Category.assoc, ← boundary, first.commutes, Category.assoc]
  route := .comp first.route second.route

/-- Vertically paste two adjacent base squares while retaining paste provenance. -/
def verticalPaste {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    (first : IndexedBaseSquare U northwest northeast middleLeft middleRight)
    (second : IndexedBaseSquare U middleLeft middleRight southwest southeast)
    (boundary : first.bottom = second.top) :
    IndexedBaseSquare U northwest northeast southwest southeast where
  top := first.top
  left := first.left ≫ second.left
  right := first.right ≫ second.right
  bottom := second.bottom
  commutes := by
    rw [Category.assoc, second.commutes]
    rw [← Category.assoc, ← boundary, first.commutes, Category.assoc]
  route := .pasteVertical first.route second.route

/-- Horizontally paste two adjacent base squares. -/
def horizontalComp {U : AtomCarrier.{u}}
    {northwest northMiddle northeast southwest southMiddle southeast :
      ExtractionInstance U}
    (first : IndexedBaseSquare U northwest northMiddle southwest southMiddle)
    (second : IndexedBaseSquare U northMiddle northeast southMiddle southeast)
    (boundary : first.right = second.left) :
    IndexedBaseSquare U northwest northeast southwest southeast where
  top := first.top ≫ second.top
  left := first.left
  right := second.right
  bottom := first.bottom ≫ second.bottom
  commutes := by
    rw [← Category.assoc, first.commutes, Category.assoc]
    rw [boundary, second.commutes, ← Category.assoc]
  route := .pasteHorizontal first.route second.route

end IndexedBaseSquare

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
