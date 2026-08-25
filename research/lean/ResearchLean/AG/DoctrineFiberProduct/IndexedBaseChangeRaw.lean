import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Raw morphism-indexed base-change syntax

This module fixes the G-111 F0 type surface. Authored terms contain only
pointed extraction-instance arrows and commutative squares. The generated
fiber action, total lift, and square comparison are the canonical constructions
from `CorePseudofunctor`; none is an authored field.

## Implementation notes

The syntax is intrinsically typed because deciding equality of arbitrary
`ExtractionInstance` objects is not part of the authored input. Malformed
source/target or square-boundary data is therefore unrepresentable, while every
actual arrow and commutative square remains a leaf. The rejected alternative
was an endofunctor/relabel language: it did not quantify over the revised
morphism-indexed domain.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Finite arrow syntax -/

/-- Finite syntax for arrows in `ExtInstCategory U`. -/
inductive IndexedBaseHom (U : AtomCarrier.{u}) :
    (source target : ExtractionInstance U) → Type (u + 1) where
  /-- One authored base arrow. -/
  | leaf {source target : ExtractionInstance U} (hom : source ⟶ target) :
      IndexedBaseHom U source target
  /-- Identity syntax. -/
  | identity (object : ExtractionInstance U) : IndexedBaseHom U object object
  /-- Sequential composition syntax. -/
  | comp {source middle target : ExtractionInstance U}
      (first : IndexedBaseHom U source middle)
      (second : IndexedBaseHom U middle target) :
      IndexedBaseHom U source target

namespace IndexedBaseHom

/-- Decode finite arrow syntax to the represented pointed base arrow. -/
def decode {U : AtomCarrier.{u}} :
    {source target : ExtractionInstance U} →
      IndexedBaseHom U source target → (source ⟶ target)
  | _, _, .leaf hom => hom
  | _, _, .identity object => 𝟙 object
  | _, _, .comp first second => first.decode ≫ second.decode

@[simp]
theorem decode_leaf {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (hom : source ⟶ target) :
    (leaf hom : IndexedBaseHom U source target).decode = hom := rfl

@[simp]
theorem decode_identity {U : AtomCarrier.{u}}
    (object : ExtractionInstance U) :
    (identity object : IndexedBaseHom U object object).decode = 𝟙 object := rfl

@[simp]
theorem decode_comp {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : IndexedBaseHom U source middle)
    (second : IndexedBaseHom U middle target) :
    (comp first second).decode = first.decode ≫ second.decode := rfl

/--
Intrinsic arrow typing is the decidable F0 well-formedness condition. A negative
instance cannot be constructed because malformed source/target data has no term.
-/
def WellFormed {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (_term : IndexedBaseHom U source target) : Prop := True

instance wellFormedDecidable {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) : Decidable term.WellFormed :=
  inferInstanceAs (Decidable True)

@[simp]
theorem wellFormed {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) : term.WellFormed := trivial

end IndexedBaseHom

/-! ## Finite square syntax -/

/-- A decoded commutative square of pointed extraction-instance arrows. -/
structure IndexedBaseSquare (U : AtomCarrier.{u})
    (northwest northeast southwest southeast : ExtractionInstance U) where
  top : northwest ⟶ northeast
  left : northwest ⟶ southwest
  right : northeast ⟶ southeast
  bottom : southwest ⟶ southeast
  commutes : left ≫ bottom = top ≫ right

/--
Finite syntax for commutative squares. `comp` is sequential square composition;
the horizontal and vertical paste constructors remain syntactically distinct.
-/
inductive IndexedBaseSquareTerm (U : AtomCarrier.{u}) :
    {northwest northeast southwest southeast : ExtractionInstance U} →
    (top : northwest ⟶ northeast) →
    (left : northwest ⟶ southwest) →
    (right : northeast ⟶ southeast) →
    (bottom : southwest ⟶ southeast) → Type (u + 1) where
  /-- One authored commutative square. -/
  | leaf
      {northwest northeast southwest southeast : ExtractionInstance U}
      {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
      {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
      (commutes : left ≫ bottom = top ≫ right) :
      IndexedBaseSquareTerm U top left right bottom
  /-- The horizontal identity square on one finite arrow term. -/
  | identity {source target : ExtractionInstance U}
      (hom : source ⟶ target) :
      IndexedBaseSquareTerm U hom (𝟙 source) (𝟙 target) hom
  /-- Sequential composition of vertically adjacent square terms. -/
  | comp
      {northwest northeast middleLeft middleRight southwest southeast :
        ExtractionInstance U}
      {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
      {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
      {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
      {bottom : southwest ⟶ southeast}
      (first : IndexedBaseSquareTerm U top left₁ right₁ middle)
      (second : IndexedBaseSquareTerm U middle left₂ right₂ bottom) :
      IndexedBaseSquareTerm U top (left₁ ≫ left₂) (right₁ ≫ right₂) bottom
  /-- Horizontal pasting of adjacent square terms. -/
  | pasteHorizontal
      {northwest northMiddle northeast southwest southMiddle southeast :
        ExtractionInstance U}
      {top₁ : northwest ⟶ northMiddle} {left : northwest ⟶ southwest}
      {middle : northMiddle ⟶ southMiddle} {bottom₁ : southwest ⟶ southMiddle}
      {top₂ : northMiddle ⟶ northeast} {right : northeast ⟶ southeast}
      {bottom₂ : southMiddle ⟶ southeast}
      (first : IndexedBaseSquareTerm U top₁ left middle bottom₁)
      (second : IndexedBaseSquareTerm U top₂ middle right bottom₂) :
      IndexedBaseSquareTerm U (top₁ ≫ top₂) left right (bottom₁ ≫ bottom₂)
  /-- Vertical pasting, retained separately from sequential composition. -/
  | pasteVertical
      {northwest northeast middleLeft middleRight southwest southeast :
        ExtractionInstance U}
      {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
      {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
      {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
      {bottom : southwest ⟶ southeast}
      (first : IndexedBaseSquareTerm U top left₁ right₁ middle)
      (second : IndexedBaseSquareTerm U middle left₂ right₂ bottom) :
      IndexedBaseSquareTerm U top (left₁ ≫ left₂) (right₁ ≫ right₂) bottom

namespace IndexedBaseSquare

/-- Horizontal identity square on one decoded base arrow. -/
def identity {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) : IndexedBaseSquare U source target source target where
  top := hom
  left := 𝟙 source
  right := 𝟙 target
  bottom := hom
  commutes := by simp

/-- Vertical composite of two decoded squares. -/
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

/-- Horizontal composite of two decoded squares. -/
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

end IndexedBaseSquare

namespace IndexedBaseSquareTerm

/--
Intrinsic square typing is the decidable well-formedness condition. A negative
instance cannot be constructed because malformed boundary data has no term.
-/
def WellFormed {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (_term : IndexedBaseSquareTerm U top left right bottom) : Prop := True

instance wellFormedDecidable {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    Decidable term.WellFormed := inferInstanceAs (Decidable True)

@[simp]
theorem wellFormed {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) : term.WellFormed :=
  trivial

/-- Every finite square term decodes to a commutative boundary. -/
theorem commutes {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast} :
    IndexedBaseSquareTerm U top left right bottom →
      left ≫ bottom = top ≫ right
  | .leaf equality => equality
  | .identity _ => by simp
  | .comp first second => by
      rw [Category.assoc, commutes second]
      rw [← Category.assoc, commutes first, Category.assoc]
  | .pasteHorizontal first second => by
      rw [← Category.assoc, commutes first, Category.assoc]
      rw [commutes second, ← Category.assoc]
  | .pasteVertical first second => by
      rw [Category.assoc, commutes second]
      rw [← Category.assoc, commutes first, Category.assoc]

/-- Decode finite square syntax to an actual commutative square. -/
def decode {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    IndexedBaseSquare U northwest northeast southwest southeast where
  top := top
  left := left
  right := right
  bottom := bottom
  commutes := term.commutes

end IndexedBaseSquareTerm

/-! ## Canonically generated action spine -/

/-- Canonical fiber action generated by one decoded base-arrow term. -/
noncomputable def indexedFiberAction {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) : CoreFiber source ⥤ CoreFiber target :=
  coreFiberTransportFunctor term.decode

/-- Canonical total lift generated over one decoded base-arrow term. -/
noncomputable def indexedTotalLift {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) (package : CoreFiber source) :
    package.1 ⟶ ((indexedFiberAction term).obj package).1 :=
  coreFiberLift term.decode package

/-- The generated total lift lies over the decoded base arrow. -/
theorem indexedTotalLift_projection {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) (package : CoreFiber source) :
    (packageProjection U).map (indexedTotalLift term package) ≫
        eqToHom ((indexedFiberAction term).obj package).2 =
      eqToHom package.2 ≫ term.decode :=
  coreFiberLift_projection term.decode package

/-- The generated total lift is the reviewed canonical strong lift. -/
theorem indexedTotalLift_isStronglyCocartesian {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) (package : CoreFiber source) :
    (packageProjection U).IsStronglyCocartesian term.decode
      (indexedTotalLift term package) :=
  coreFiberLift_isStronglyCocartesian term.decode package

/-- Identity-action comparison generated by the canonical unitor. -/
noncomputable def indexedFiberIdentityComparison {U : AtomCarrier.{u}}
    (object : ExtractionInstance U) :
    indexedFiberAction (IndexedBaseHom.identity object) ≅ 𝟭 (CoreFiber object) :=
  coreFiberUnitor object

/-- Composition-action comparison generated by the canonical compositor. -/
noncomputable def indexedFiberCompositionComparison {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : IndexedBaseHom U source middle)
    (second : IndexedBaseHom U middle target) :
    indexedFiberAction (IndexedBaseHom.comp first second) ≅
      indexedFiberAction first ⋙ indexedFiberAction second :=
  coreFiberCompositor first.decode second.decode

/--
The output type of square transport: the two decoded boundary routes are
compared at the fiber-action level.
-/
abbrev IndexedSquareActionType {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    (square : IndexedBaseSquare U northwest northeast southwest southeast) :=
  (coreFiberTransportFunctor square.top ⋙
      coreFiberTransportFunctor square.right) ≅
    (coreFiberTransportFunctor square.left ⋙
      coreFiberTransportFunctor square.bottom)

/-- Canonical comparison generated from compositor coherence and square commutativity. -/
noncomputable def indexedSquareAction {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    (square : IndexedBaseSquare U northwest northeast southwest southeast) :
    IndexedSquareActionType square :=
  (coreFiberCompositor square.top square.right).symm ≪≫
    eqToIso (congrArg coreFiberTransportFunctor square.commutes.symm) ≪≫
      coreFiberCompositor square.left square.bottom

/-- Decode a square term and generate its canonical comparison. -/
noncomputable def indexedSquareTermAction {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    IndexedSquareActionType term.decode :=
  indexedSquareAction term.decode

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
