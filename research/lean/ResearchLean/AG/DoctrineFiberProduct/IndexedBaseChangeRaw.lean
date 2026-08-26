import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor

/-!
# Raw morphism-indexed base-change syntax

This module fixes the G-111 F0 type surface. Authored terms contain only
pointed extraction-instance arrows and commutative squares. The generated
fiber action, total lift, and square comparison are the canonical constructions
from `CorePseudofunctor`; none is an authored field.

## Implementation notes

The syntax is intrinsically boundary-typed because deciding equality of
arbitrary `ExtractionInstance` objects is not part of the authored input. Raw
trees may nevertheless have missing arrow leaves or missing commutativity
witnesses. Their partial recursive decoders therefore give a genuine decidable
well-formedness condition with positive and negative trees. Public action
producers consume the validated form. Every actual arrow and commutative square
remains a leaf. The rejected alternatives were an endofunctor/relabel language
and an inert route tag whose generated comparison ignored paste structure.
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

/-- Decoding an arrow leaf returns its authored arrow. -/
@[simp]
theorem decode_leaf {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (hom : source ⟶ target) :
    (leaf hom : IndexedBaseHom U source target).decode = hom := rfl

/-- Decoding identity syntax returns the categorical identity. -/
@[simp]
theorem decode_identity {U : AtomCarrier.{u}}
    (object : ExtractionInstance U) :
    (identity object : IndexedBaseHom U object object).decode = 𝟙 object := rfl

/-- Decoding arrow composition returns categorical composition. -/
@[simp]
theorem decode_comp {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : IndexedBaseHom U source middle)
    (second : IndexedBaseHom U middle target) :
    (comp first second).decode = first.decode ≫ second.decode := rfl

end IndexedBaseHom

/-- Raw finite arrow syntax whose authored leaves may be absent. -/
inductive IndexedBaseHomInput (U : AtomCarrier.{u}) :
    (source target : ExtractionInstance U) → Type (u + 1) where
  /-- A possibly missing authored base arrow. -/
  | leaf {source target : ExtractionInstance U}
      (candidate : Option (source ⟶ target)) :
      IndexedBaseHomInput U source target
  /-- Raw identity syntax. -/
  | identity (object : ExtractionInstance U) :
      IndexedBaseHomInput U object object
  /-- Raw sequential composition. -/
  | comp {source middle target : ExtractionInstance U}
      (first : IndexedBaseHomInput U source middle)
      (second : IndexedBaseHomInput U middle target) :
      IndexedBaseHomInput U source target

namespace IndexedBaseHomInput

/-- Partially decode a raw arrow tree, failing exactly at a missing leaf. -/
def decodeCandidate {U : AtomCarrier.{u}} :
    {source target : ExtractionInstance U} →
      IndexedBaseHomInput U source target →
        Option (IndexedBaseHom U source target)
  | _, _, .leaf candidate => candidate.map .leaf
  | _, _, .identity object => some (.identity object)
  | _, _, .comp first second => do
      let first' ← decodeCandidate first
      let second' ← decodeCandidate second
      pure (.comp first' second')

/-- Decoder compatibility: every authored arrow leaf is present. -/
def WellFormed {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (input : IndexedBaseHomInput U source target) : Prop :=
  input.decodeCandidate.isSome = true

/-- Arrow decoder compatibility is decidable. -/
instance wellFormedDecidable {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (input : IndexedBaseHomInput U source target) : Decidable input.WellFormed :=
  inferInstanceAs (Decidable (input.decodeCandidate.isSome = true))

/-- Embed any typed arrow term as a positive raw decoder input. -/
def ofTerm {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) : IndexedBaseHomInput U source target :=
  match term with
  | .leaf hom => .leaf (some hom)
  | .identity object => .identity object
  | .comp first second => .comp (ofTerm first) (ofTerm second)

/-- A concrete malformed decoder input. -/
def missing {U : AtomCarrier.{u}} (source target : ExtractionInstance U) :
    IndexedBaseHomInput U source target := .leaf none

/-- Positive decoder-compatibility instance. -/
@[simp]
theorem decodeCandidate_ofTerm {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) :
    (ofTerm term).decodeCandidate = some term := by
  induction term <;> simp [ofTerm, decodeCandidate, *]

/-- Positive decoder-compatibility instance. -/
@[simp]
theorem ofTerm_wellFormed {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) : (ofTerm term).WellFormed := by
  simp [WellFormed]

/-- Negative decoder-compatibility instance. -/
@[simp]
theorem missing_not_wellFormed {U : AtomCarrier.{u}}
    (source target : ExtractionInstance U) :
    ¬(missing source target).WellFormed := by
  simp [WellFormed, missing, decodeCandidate]

/-- Extract the typed syntax certified by a well-formed raw input. -/
def term {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (input : IndexedBaseHomInput U source target) (valid : input.WellFormed) :
    IndexedBaseHom U source target :=
  input.decodeCandidate.get (by simpa [WellFormed] using valid)

end IndexedBaseHomInput

/-- A raw arrow input paired with its decoder-compatibility certificate. -/
structure ValidatedIndexedBaseHom (U : AtomCarrier.{u})
    (source target : ExtractionInstance U) where
  input : IndexedBaseHomInput U source target
  term : IndexedBaseHom U source target
  decodes : input.decodeCandidate = some term

namespace ValidatedIndexedBaseHom

/-- Canonically validate an intrinsically typed arrow term. -/
def ofTerm {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (term : IndexedBaseHom U source target) :
    ValidatedIndexedBaseHom U source target :=
  ⟨.ofTerm term, term, IndexedBaseHomInput.decodeCandidate_ofTerm term⟩

/-- A validated arrow input satisfies recursive decoder compatibility. -/
theorem valid {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (input : ValidatedIndexedBaseHom U source target) : input.input.WellFormed := by
  simp [IndexedBaseHomInput.WellFormed, input.decodes]

/-- Decode a validated arrow input to its base arrow. -/
def decode {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (input : ValidatedIndexedBaseHom U source target) : source ⟶ target :=
  input.term.decode

end ValidatedIndexedBaseHom

/-! ## Finite square syntax -/

/-- Construction provenance retained by decoded square syntax. -/
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

/-- A decoded commutative square, including its un-erased construction route. -/
structure IndexedBaseSquare (U : AtomCarrier.{u})
    (northwest northeast southwest southeast : ExtractionInstance U) where
  top : northwest ⟶ northeast
  left : northwest ⟶ southwest
  right : northeast ⟶ southeast
  bottom : southwest ⟶ southeast
  commutes : left ≫ bottom = top ≫ right
  route : IndexedSquareRoute

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
  route := .identity

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
    route := .comp first.route second.route

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
    route := .pasteHorizontal first.route second.route

end IndexedBaseSquare

namespace IndexedBaseSquareTerm

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
  route := match term with
    | .leaf _ => .leaf
    | .identity _ => .identity
    | .comp first second => .comp first.decode.route second.decode.route
    | .pasteHorizontal first second =>
        .pasteHorizontal first.decode.route second.decode.route
    | .pasteVertical first second =>
        .pasteVertical first.decode.route second.decode.route

/-- Sequential composition and vertical pasting remain distinct after decode. -/
theorem decode_comp_route_ne_pasteVertical {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
    {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
    {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
    {bottom : southwest ⟶ southeast}
    (first : IndexedBaseSquareTerm U top left₁ right₁ middle)
    (second : IndexedBaseSquareTerm U middle left₂ right₂ bottom) :
    (decode (.comp first second)).route ≠
      (decode (.pasteVertical first second)).route := by
  simp [decode]

end IndexedBaseSquareTerm

/-- Raw finite square syntax whose authored commutativity leaves may be absent. -/
inductive IndexedBaseSquareInput (U : AtomCarrier.{u}) :
    {northwest northeast southwest southeast : ExtractionInstance U} →
    (top : northwest ⟶ northeast) → (left : northwest ⟶ southwest) →
    (right : northeast ⟶ southeast) → (bottom : southwest ⟶ southeast) →
    Type (u + 1) where
  /-- A square leaf with a possibly missing authored commutativity witness. -/
  | leaf
      {northwest northeast southwest southeast : ExtractionInstance U}
      {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
      {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
      (candidate : Option (PLift (left ≫ bottom = top ≫ right))) :
      IndexedBaseSquareInput U top left right bottom
  /-- Raw horizontal identity square. -/
  | identity {source target : ExtractionInstance U} (hom : source ⟶ target) :
      IndexedBaseSquareInput U hom (𝟙 source) (𝟙 target) hom
  /-- Raw sequential composition of vertically adjacent squares. -/
  | comp
      {northwest northeast middleLeft middleRight southwest southeast :
        ExtractionInstance U}
      {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
      {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
      {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
      {bottom : southwest ⟶ southeast}
      (first : IndexedBaseSquareInput U top left₁ right₁ middle)
      (second : IndexedBaseSquareInput U middle left₂ right₂ bottom) :
      IndexedBaseSquareInput U top (left₁ ≫ left₂) (right₁ ≫ right₂) bottom
  /-- Raw horizontal pasting of adjacent squares. -/
  | pasteHorizontal
      {northwest northMiddle northeast southwest southMiddle southeast :
        ExtractionInstance U}
      {top₁ : northwest ⟶ northMiddle} {left : northwest ⟶ southwest}
      {middle : northMiddle ⟶ southMiddle} {bottom₁ : southwest ⟶ southMiddle}
      {top₂ : northMiddle ⟶ northeast} {right : northeast ⟶ southeast}
      {bottom₂ : southMiddle ⟶ southeast}
      (first : IndexedBaseSquareInput U top₁ left middle bottom₁)
      (second : IndexedBaseSquareInput U top₂ middle right bottom₂) :
      IndexedBaseSquareInput U (top₁ ≫ top₂) left right (bottom₁ ≫ bottom₂)
  /-- Raw vertical pasting, distinct from sequential composition. -/
  | pasteVertical
      {northwest northeast middleLeft middleRight southwest southeast :
        ExtractionInstance U}
      {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
      {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
      {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
      {bottom : southwest ⟶ southeast}
      (first : IndexedBaseSquareInput U top left₁ right₁ middle)
      (second : IndexedBaseSquareInput U middle left₂ right₂ bottom) :
      IndexedBaseSquareInput U top (left₁ ≫ left₂) (right₁ ≫ right₂) bottom

namespace IndexedBaseSquareInput

/-- Partially decode a raw square tree, failing at any missing leaf witness. -/
def decodeCandidate {U : AtomCarrier.{u}} :
    {northwest northeast southwest southeast : ExtractionInstance U} →
    {top : northwest ⟶ northeast} → {left : northwest ⟶ southwest} →
    {right : northeast ⟶ southeast} → {bottom : southwest ⟶ southeast} →
    IndexedBaseSquareInput U top left right bottom →
      Option (IndexedBaseSquareTerm U top left right bottom)
  | _, _, _, _, _, _, _, _, .leaf candidate =>
      candidate.map fun equality => .leaf equality.down
  | _, _, _, _, _, _, _, _, .identity hom => some (.identity hom)
  | _, _, _, _, _, _, _, _, .comp first second => do
      let first' ← decodeCandidate first
      let second' ← decodeCandidate second
      pure (.comp first' second')
  | _, _, _, _, _, _, _, _, .pasteHorizontal first second => do
      let first' ← decodeCandidate first
      let second' ← decodeCandidate second
      pure (.pasteHorizontal first' second')
  | _, _, _, _, _, _, _, _, .pasteVertical first second => do
      let first' ← decodeCandidate first
      let second' ← decodeCandidate second
      pure (.pasteVertical first' second')

/-- Decoder compatibility: every authored square leaf has its witness. -/
def WellFormed {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (input : IndexedBaseSquareInput U top left right bottom) : Prop :=
  input.decodeCandidate.isSome = true

/-- Square decoder compatibility is decidable. -/
instance wellFormedDecidable {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (input : IndexedBaseSquareInput U top left right bottom) :
    Decidable input.WellFormed :=
  inferInstanceAs (Decidable (input.decodeCandidate.isSome = true))

/-- Embed any typed square term as a positive raw decoder input. -/
def ofTerm {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    IndexedBaseSquareInput U top left right bottom :=
  match term with
  | .leaf equality => .leaf (some ⟨equality⟩)
  | .identity hom => .identity hom
  | .comp first second => .comp (ofTerm first) (ofTerm second)
  | .pasteHorizontal first second =>
      .pasteHorizontal (ofTerm first) (ofTerm second)
  | .pasteVertical first second => .pasteVertical (ofTerm first) (ofTerm second)

/-- A concrete malformed square decoder input. -/
def missing {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    (top : northwest ⟶ northeast) (left : northwest ⟶ southwest)
    (right : northeast ⟶ southeast) (bottom : southwest ⟶ southeast) :
    IndexedBaseSquareInput U top left right bottom := .leaf none

/-- Embedding a typed square term is a successful recursive decode. -/
@[simp]
theorem decodeCandidate_ofTerm {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    (ofTerm term).decodeCandidate = some term := by
  induction term <;> simp [ofTerm, decodeCandidate, *]

/-- Positive square decoder-compatibility instance. -/
@[simp]
theorem ofTerm_wellFormed {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    (ofTerm term).WellFormed := by
  simp [WellFormed]

/-- Negative square decoder-compatibility instance. -/
@[simp]
theorem missing_not_wellFormed {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    (top : northwest ⟶ northeast) (left : northwest ⟶ southwest)
    (right : northeast ⟶ southeast) (bottom : southwest ⟶ southeast) :
    ¬(missing top left right bottom).WellFormed := by
  simp [WellFormed, missing, decodeCandidate]

/-- Extract the typed square syntax certified by a well-formed raw input. -/
def term {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (input : IndexedBaseSquareInput U top left right bottom)
    (valid : input.WellFormed) :
    IndexedBaseSquareTerm U top left right bottom :=
  input.decodeCandidate.get (by simpa [WellFormed] using valid)

end IndexedBaseSquareInput

/-- A raw square input paired with its decoder-compatibility certificate. -/
structure ValidatedIndexedBaseSquare (U : AtomCarrier.{u})
    {northwest northeast southwest southeast : ExtractionInstance U}
    (top : northwest ⟶ northeast) (left : northwest ⟶ southwest)
    (right : northeast ⟶ southeast) (bottom : southwest ⟶ southeast) where
  input : IndexedBaseSquareInput U top left right bottom
  term : IndexedBaseSquareTerm U top left right bottom
  decodes : input.decodeCandidate = some term

namespace ValidatedIndexedBaseSquare

/-- Canonically validate an intrinsically typed square term. -/
def ofTerm {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    ValidatedIndexedBaseSquare U top left right bottom :=
  ⟨.ofTerm term, term, IndexedBaseSquareInput.decodeCandidate_ofTerm term⟩

/-- A validated square input satisfies recursive decoder compatibility. -/
theorem valid {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (input : ValidatedIndexedBaseSquare U top left right bottom) :
    input.input.WellFormed := by
  simp [IndexedBaseSquareInput.WellFormed, input.decodes]

end ValidatedIndexedBaseSquare

/-! ## Canonically generated action spine -/

/-- Canonical fiber action generated by one decoded base-arrow term. -/
noncomputable def indexedFiberAction {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U source target) :
    CoreFiber source ⥤ CoreFiber target :=
  coreFiberTransportFunctor term.decode

/-- Canonical total lift generated over one decoded base-arrow term. -/
noncomputable def indexedTotalLift {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U source target) (package : CoreFiber source) :
    package.1 ⟶ ((indexedFiberAction term).obj package).1 :=
  coreFiberLift term.decode package

/--
The universal edge law type for a generated lift: every package-total morphism
in the source fiber commutes with the canonical lift and transported map.
-/
def IndexedUniversalEdgeLaw {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U source target) : Prop :=
  ∀ {P Q : CoreFiber source} (f : P ⟶ Q),
    indexedTotalLift term P ≫ ((indexedFiberAction term).map f).1 =
      f.1 ≫ indexedTotalLift term Q

/-- The canonical lift satisfies the fixed universal edge law. -/
theorem indexedUniversalEdgeLaw {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U source target) :
    IndexedUniversalEdgeLaw term :=
  fun f => coreFiberTransportMap_fac term.decode f

/--
Transport an arbitrary package-total morphism over the left edge of a raw
square to the right edge by the canonical strong cocartesian lift.
-/
noncomputable def indexedSquareTotalMap {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom)
    (P : CoreFiber northwest) (Q : CoreFiber southwest)
    (f : P.1 ⟶ Q.1) (hf : (packageProjection U).IsHomLift left f) :
    (coreFiberTransportObj top P).1 ⟶ (coreFiberTransportObj bottom Q).1 := by
  letI : (packageProjection U).IsStronglyCocartesian top
      (coreFiberLift top P) := coreFiberLift_isStronglyCocartesian top P
  letI : (packageProjection U).IsHomLift left f := hf
  letI : (packageProjection U).IsHomLift bottom (coreFiberLift bottom Q) :=
    coreFiberLift_isHomLift bottom Q
  letI : (packageProjection U).IsHomLift (left ≫ bottom)
      (f ≫ coreFiberLift bottom Q) := inferInstance
  exact CategoryTheory.Functor.IsStronglyCocartesian.map
    (packageProjection U) top (coreFiberLift top P)
    (g := right) (f' := left ≫ bottom) term.term.commutes
    (f ≫ coreFiberLift bottom Q)

/-- The generated square-total morphism lies over the square's right edge. -/
theorem indexedSquareTotalMap_isHomLift {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom)
    (P : CoreFiber northwest) (Q : CoreFiber southwest)
    (f : P.1 ⟶ Q.1) (hf : (packageProjection U).IsHomLift left f) :
    (packageProjection U).IsHomLift right
      (indexedSquareTotalMap term P Q f hf) := by
  unfold indexedSquareTotalMap
  infer_instance

/--
Universal square-edge law over every commutative raw square and every
package-total morphism lying over its left edge.
-/
def IndexedUniversalSquareEdgeLaw {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom) : Prop :=
  ∀ (P : CoreFiber northwest) (Q : CoreFiber southwest)
      (f : P.1 ⟶ Q.1) (hf : (packageProjection U).IsHomLift left f),
    coreFiberLift top P ≫ indexedSquareTotalMap term P Q f hf =
      f ≫ coreFiberLift bottom Q

/-- The generated square-total map satisfies the universal square-edge law. -/
theorem indexedUniversalSquareEdgeLaw {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom) :
    IndexedUniversalSquareEdgeLaw term := by
  intro P Q f hf
  letI : (packageProjection U).IsStronglyCocartesian top
      (coreFiberLift top P) := coreFiberLift_isStronglyCocartesian top P
  letI : (packageProjection U).IsHomLift left f := hf
  letI : (packageProjection U).IsHomLift bottom (coreFiberLift bottom Q) :=
    coreFiberLift_isHomLift bottom Q
  letI : (packageProjection U).IsHomLift (left ≫ bottom)
      (f ≫ coreFiberLift bottom Q) := inferInstance
  exact CategoryTheory.Functor.IsStronglyCocartesian.fac
    (packageProjection U) top (coreFiberLift top P) term.term.commutes
    (f ≫ coreFiberLift bottom Q)

/-- The generated total lift lies over the decoded base arrow. -/
theorem indexedTotalLift_projection {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U source target) (package : CoreFiber source) :
    (packageProjection U).map (indexedTotalLift term package) ≫
        eqToHom ((indexedFiberAction term).obj package).2 =
      eqToHom package.2 ≫ term.decode :=
  coreFiberLift_projection term.decode package

/-- The generated total lift is the reviewed canonical strong lift. -/
theorem indexedTotalLift_isStronglyCocartesian {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U source target) (package : CoreFiber source) :
    (packageProjection U).IsStronglyCocartesian term.decode
      (indexedTotalLift term package) :=
  coreFiberLift_isStronglyCocartesian term.decode package

/-- Identity-action comparison generated by the canonical unitor. -/
noncomputable def indexedFiberIdentityComparison {U : AtomCarrier.{u}}
    (object : ExtractionInstance U) :
    indexedFiberAction (.ofTerm (.identity object)) ≅ 𝟭 (CoreFiber object) :=
  coreFiberUnitor object

/-- Composition-action comparison generated by the canonical compositor. -/
noncomputable def indexedFiberCompositionComparison {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : ValidatedIndexedBaseHom U source middle)
    (second : ValidatedIndexedBaseHom U middle target) :
    indexedFiberAction (.ofTerm (.comp first.term second.term)) ≅
      indexedFiberAction first ⋙ indexedFiberAction second :=
  coreFiberCompositor first.decode second.decode

/-- The generated identity comparison contracts the generated identity lift. -/
theorem indexedFiberIdentityComparison_hom_fac {U : AtomCarrier.{u}}
    (object : ExtractionInstance U) (P : CoreFiber object) :
    indexedTotalLift (.ofTerm (.identity object)) P ≫
        ((indexedFiberIdentityComparison object).hom.app P).1 = 𝟙 P.1 := by
  simpa [indexedTotalLift, indexedFiberIdentityComparison] using
    coreFiberUnitorApp_hom_fac object P

/-- The generated composition comparison identifies composite and iterated lifts. -/
theorem indexedFiberCompositionComparison_hom_fac {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : ValidatedIndexedBaseHom U source middle)
    (second : ValidatedIndexedBaseHom U middle target)
    (P : CoreFiber source) :
    indexedTotalLift (.ofTerm (.comp first.term second.term)) P ≫
        ((indexedFiberCompositionComparison first second).hom.app P).1 =
      coreFiberIteratedLift first.decode second.decode P := by
  simpa [indexedTotalLift, indexedFiberCompositionComparison] using
    coreFiberCompositorApp_hom_fac first.decode second.decode P

/-- The outer-boundary comparison associated with any square term. -/
private noncomputable def indexedSquareOuterComparisonAux {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    (coreFiberTransportFunctor top ⋙ coreFiberTransportFunctor right) ≅
      (coreFiberTransportFunctor left ⋙ coreFiberTransportFunctor bottom) :=
  (coreFiberCompositor top right).symm ≪≫
    eqToIso (congrArg coreFiberTransportFunctor term.commutes.symm) ≪≫
      coreFiberCompositor left bottom

/--
Term-indexed generated square action. Sequential `comp` selects the canonical
outer route, while horizontal and vertical paste recursively select the
componentwise route. Their equality is a later soundness theorem, not a tag.
-/
private noncomputable def indexedSquareTermActionAux {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom) :
    (coreFiberTransportFunctor top ⋙ coreFiberTransportFunctor right) ≅
      (coreFiberTransportFunctor left ⋙ coreFiberTransportFunctor bottom) :=
  match term with
  | .leaf equality => indexedSquareOuterComparisonAux (.leaf equality)
  | .identity hom => indexedSquareOuterComparisonAux (.identity hom)
  | .comp first second => indexedSquareOuterComparisonAux (.comp first second)
  | .pasteHorizontal first second =>
      Functor.isoWhiskerRight
          (coreFiberCompositor _ _)
          (coreFiberTransportFunctor _) ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (indexedSquareTermActionAux second) ≪≫
            (Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (indexedSquareTermActionAux first) _ ≪≫
                Functor.associator _ _ _ ≪≫
                  Functor.isoWhiskerLeft _ (coreFiberCompositor _ _).symm
  | .pasteVertical first second =>
      Functor.isoWhiskerLeft
          (coreFiberTransportFunctor _)
          (coreFiberCompositor _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (indexedSquareTermActionAux first) _ ≪≫
            Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerLeft _ (indexedSquareTermActionAux second) ≪≫
                (Functor.associator _ _ _).symm ≪≫
                  Functor.isoWhiskerRight (coreFiberCompositor _ _).symm _

/--
Canonical square action generated from a validated raw input. The comparison
is a definition, not a caller-supplied structure field.
-/
noncomputable def indexedSquareTermAction {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom) :
    (coreFiberTransportFunctor top ⋙ coreFiberTransportFunctor right) ≅
      (coreFiberTransportFunctor left ⋙ coreFiberTransportFunctor bottom) :=
  indexedSquareTermActionAux term.term

/-- Canonical outer-boundary comparison generated from a validated raw square. -/
noncomputable def indexedSquareOuterComparison {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom) :
    (coreFiberTransportFunctor top ⋙ coreFiberTransportFunctor right) ≅
      (coreFiberTransportFunctor left ⋙ coreFiberTransportFunctor bottom) :=
  indexedSquareOuterComparisonAux term.term

/-- The outer square comparison identifies the two canonical iterated lifts. -/
theorem indexedSquareOuterComparison_hom_fac {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom)
    (P : CoreFiber northwest) :
    coreFiberIteratedLift top right P ≫
      ((indexedSquareOuterComparison term).hom.app P).1 =
      coreFiberIteratedLift left bottom P := by
  dsimp [indexedSquareOuterComparison, indexedSquareOuterComparisonAux,
    coreFiberCompositor, coreFiberTransportEqCast]
  have fiber_comp {A B C : CoreFiber southeast} (f : A ⟶ B) (g : B ⟶ C) :
      (f ≫ g).1 = f.1 ≫ g.1 := rfl
  simp only [fiber_comp]
  have cast_fac :
      coreFiberLift (top ≫ right) P ≫
          ((eqToHom (congrArg coreFiberTransportFunctor
            term.term.commutes.symm)).app P).1 =
        coreFiberLift (left ≫ bottom) P := by
    have eq_cast {source target : northwest ⟶ southeast}
        (h : source = target) :
        ((eqToHom (congrArg coreFiberTransportFunctor h)).app P).1 =
          (coreFiberTransportEqCast h P).1 := by
      cases h
      rfl
    rw [eq_cast]
    exact coreFiberLift_eqCast_fac term.term.commutes.symm P
  have compositor_cancel_assoc
      {Z : AATCorePackage U}
      (tail : (coreFiberTransportObj (top ≫ right) P).1 ⟶ Z) :
      (coreFiberCompositorApp top right P).hom.1 ≫
          ((coreFiberCompositorApp top right P).inv.1 ≫ tail) = tail := by
    exact ((Functor.Fiber.fiberInclusion).mapIso
      (coreFiberCompositorApp top right P)).hom_inv_id_assoc tail
  change coreFiberIteratedLift top right P ≫
      (coreFiberCompositorApp top right P).inv.1 ≫
        ((eqToHom (congrArg coreFiberTransportFunctor
          term.term.commutes.symm)).app P).1 ≫
          (coreFiberCompositorApp left bottom P).hom.1 =
    coreFiberIteratedLift left bottom P
  calc
    _ = (coreFiberLift (top ≫ right) P ≫
          (coreFiberCompositorApp top right P).hom.1) ≫
          (coreFiberCompositorApp top right P).inv.1 ≫
          ((eqToHom (congrArg coreFiberTransportFunctor
            term.term.commutes.symm)).app P).1 ≫
            (coreFiberCompositorApp left bottom P).hom.1 := by
      rw [coreFiberCompositorApp_hom_fac]
    _ = coreFiberLift (top ≫ right) P ≫
          ((eqToHom (congrArg coreFiberTransportFunctor
            term.term.commutes.symm)).app P).1 ≫
            (coreFiberCompositorApp left bottom P).hom.1 := by
      simp only [Category.assoc, compositor_cancel_assoc]
    _ = coreFiberLift (left ≫ bottom) P ≫
          (coreFiberCompositorApp left bottom P).hom.1 := by
      rw [← Category.assoc, cast_fac]
    _ = _ := coreFiberCompositorApp_hom_fac left bottom P

/-- The inverse compositor contracts an iterated lift to the composite lift. -/
private theorem coreFiberCompositorApp_inv_fac {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (P : CoreFiber source) :
    coreFiberIteratedLift first second P ≫
        (coreFiberCompositorApp first second P).inv.1 =
      coreFiberLift (first ≫ second) P := by
  calc
    _ = (coreFiberLift (first ≫ second) P ≫
          (coreFiberCompositorApp first second P).hom.1) ≫
        (coreFiberCompositorApp first second P).inv.1 := by
      rw [coreFiberCompositorApp_hom_fac]
    _ = _ := by
      rw [Category.assoc]
      have cancel :
          (coreFiberCompositorApp first second P).hom.1 ≫
              (coreFiberCompositorApp first second P).inv.1 = 𝟙 _ := by
        exact congrArg Subtype.val
          (Iso.hom_inv_id (coreFiberCompositorApp first second P))
      rw [cancel]
      exact Category.comp_id (coreFiberLift (first ≫ second) P)

/-- Naturality of canonical lifts, in the public functor-map notation. -/
@[reassoc]
private theorem coreFiberTransportFunctor_map_fac {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (base : source ⟶ target)
    {P Q : CoreFiber source} (f : P ⟶ Q) :
    coreFiberLift base P ≫ ((coreFiberTransportFunctor base).map f).1 =
      f.1 ≫ coreFiberLift base Q := by
  exact coreFiberTransportMap_fac base f

/-- Compositor factorization, in the public natural-isomorphism notation. -/
@[reassoc]
private theorem coreFiberCompositor_hom_fac {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (P : CoreFiber source) :
    coreFiberLift (first ≫ second) P ≫
        ((coreFiberCompositor first second).hom.app P).1 =
      coreFiberIteratedLift first second P :=
  coreFiberCompositorApp_hom_fac first second P

/-- Inverse compositor factorization, in natural-isomorphism notation. -/
@[reassoc]
private theorem coreFiberCompositor_inv_fac {U : AtomCarrier.{u}}
    {source middle target : ExtractionInstance U}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (P : CoreFiber source) :
    coreFiberIteratedLift first second P ≫
        ((coreFiberCompositor first second).inv.app P).1 =
      coreFiberLift (first ≫ second) P :=
  coreFiberCompositorApp_inv_fac first second P

/-- Forgetting a composite fiber morphism gives the composite total morphism. -/
private theorem coreFiber_hom_comp_val {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} {A B C : CoreFiber X}
    (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- Every recursively generated square comparison identifies its iterated lifts. -/
private theorem indexedSquareTermActionAux_hom_fac {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : IndexedBaseSquareTerm U top left right bottom)
    (P : CoreFiber northwest) :
    coreFiberIteratedLift top right P ≫
      ((indexedSquareTermActionAux term).hom.app P).1 =
      coreFiberIteratedLift left bottom P := by
  induction term with
  | leaf equality =>
      simpa [indexedSquareTermAction, indexedSquareTermActionAux] using
        indexedSquareOuterComparison_hom_fac
          (ValidatedIndexedBaseSquare.ofTerm (.leaf equality)) P
  | identity hom =>
      simpa [indexedSquareTermAction, indexedSquareTermActionAux] using
        indexedSquareOuterComparison_hom_fac
          (ValidatedIndexedBaseSquare.ofTerm (.identity hom)) P
  | comp first second first_ih second_ih =>
      simpa [indexedSquareTermAction, indexedSquareTermActionAux] using
        indexedSquareOuterComparison_hom_fac
          (ValidatedIndexedBaseSquare.ofTerm (.comp first second)) P
  | pasteHorizontal first second first_ih second_ih =>
      rename_i nw nm ne sw sm se t₁ l m b₁ t₂ r b₂
      dsimp [coreFiberIteratedLift] at first_ih second_ih
      simp [indexedSquareTermActionAux, coreFiberIteratedLift,
        coreFiber_hom_comp_val]
      rw [coreFiberTransportFunctor_map_fac_assoc]
      rw [coreFiberCompositor_hom_fac_assoc]
      dsimp [coreFiberIteratedLift]
      simp only [Category.assoc]
      rw [reassoc_of% (second_ih _)]
      rw [coreFiberTransportFunctor_map_fac_assoc]
      rw [reassoc_of% (first_ih P)]
      calc
        _ = coreFiberLift l P ≫
              (coreFiberIteratedLift b₁ b₂
                ((coreFiberTransportFunctor l).obj P) ≫
                ((coreFiberCompositor b₁ b₂).inv.app
                  ((coreFiberTransportFunctor l).obj P)).1) := by
              simp only [coreFiberIteratedLift, Category.assoc]
        _ = _ := by rw [coreFiberCompositor_inv_fac]

  | pasteVertical first second first_ih second_ih =>
      rename_i nw ne ml mr sw se t l₁ r₁ m l₂ r₂ b
      dsimp [coreFiberIteratedLift] at first_ih second_ih
      simp [indexedSquareTermActionAux, coreFiberIteratedLift,
        coreFiber_hom_comp_val]
      rw [coreFiberCompositor_hom_fac_assoc]
      dsimp [coreFiberIteratedLift]
      simp only [Category.assoc]
      rw [coreFiberTransportFunctor_map_fac_assoc]
      rw [reassoc_of% (first_ih P)]
      rw [reassoc_of% (second_ih _)]
      rw [coreFiberTransportFunctor_map_fac]
      calc
        _ = (coreFiberIteratedLift l₁ l₂ P ≫
              ((coreFiberCompositor l₁ l₂).inv.app P).1) ≫
              coreFiberLift b
                ((coreFiberTransportFunctor (l₁ ≫ l₂)).obj P) := by
              simp only [coreFiberIteratedLift, Category.assoc]
        _ = _ := by rw [coreFiberCompositor_inv_fac]

/-- Every validated recursive square action identifies its canonical iterated lifts. -/
theorem indexedSquareTermAction_hom_fac {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (term : ValidatedIndexedBaseSquare U top left right bottom)
    (P : CoreFiber northwest) :
    coreFiberIteratedLift top right P ≫
      ((indexedSquareTermAction term).hom.app P).1 =
      coreFiberIteratedLift left bottom P :=
  indexedSquareTermActionAux_hom_fac term.term P

/-- Two generated square comparisons with the same lift factorization coincide. -/
private theorem indexedSquareComparison_ext {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    {top : northwest ⟶ northeast} {left : northwest ⟶ southwest}
    {right : northeast ⟶ southeast} {bottom : southwest ⟶ southeast}
    (first second :
      (coreFiberTransportFunctor top ⋙ coreFiberTransportFunctor right) ≅
        (coreFiberTransportFunctor left ⋙ coreFiberTransportFunctor bottom))
    (first_fac : ∀ P : CoreFiber northwest,
      coreFiberIteratedLift top right P ≫ (first.hom.app P).1 =
        coreFiberIteratedLift left bottom P)
    (second_fac : ∀ P : CoreFiber northwest,
      coreFiberIteratedLift top right P ≫ (second.hom.app P).1 =
        coreFiberIteratedLift left bottom P) :
    first = second := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian (top ≫ right)
      (coreFiberIteratedLift top right P) :=
    coreFiberIteratedLift_isStronglyCocartesian top right P
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (top ≫ right)
    (coreFiberIteratedLift top right P) (𝟙 southeast)
  change coreFiberIteratedLift top right P ≫ (first.hom.app P).1 =
    coreFiberIteratedLift top right P ≫ (second.hom.app P).1
  rw [first_fac, second_fac]

/-- Exact output type for the componentwise horizontal-pasting route. -/
abbrev IndexedHorizontalComponentRouteType {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    (top : northwest ⟶ northeast) (left : northwest ⟶ southwest)
    (right : northeast ⟶ southeast) (bottom : southwest ⟶ southeast) :=
  (coreFiberTransportFunctor top ⋙ coreFiberTransportFunctor right) ≅
    (coreFiberTransportFunctor left ⋙
      coreFiberTransportFunctor bottom)

/--
The componentwise horizontal route generated from the two square comparisons,
the pseudofunctor compositors, and functor associators.
-/
noncomputable def indexedHorizontalComponentRoute {U : AtomCarrier.{u}}
    {northwest northMiddle northeast southwest southMiddle southeast :
      ExtractionInstance U}
    {top₁ : northwest ⟶ northMiddle} {left : northwest ⟶ southwest}
    {middle : northMiddle ⟶ southMiddle} {bottom₁ : southwest ⟶ southMiddle}
    {top₂ : northMiddle ⟶ northeast} {right : northeast ⟶ southeast}
    {bottom₂ : southMiddle ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top₁ left middle bottom₁)
    (second : ValidatedIndexedBaseSquare U top₂ middle right bottom₂) :
    IndexedHorizontalComponentRouteType (top₁ ≫ top₂) left right
      (bottom₁ ≫ bottom₂) :=
  Functor.isoWhiskerRight
      (coreFiberCompositor top₁ top₂)
      (coreFiberTransportFunctor right) ≪≫
    Functor.associator
        (coreFiberTransportFunctor top₁)
        (coreFiberTransportFunctor top₂)
        (coreFiberTransportFunctor right) ≪≫
      Functor.isoWhiskerLeft
          (coreFiberTransportFunctor top₁)
          (indexedSquareTermAction second) ≪≫
        (Functor.associator
            (coreFiberTransportFunctor top₁)
            (coreFiberTransportFunctor middle)
            (coreFiberTransportFunctor bottom₂)).symm ≪≫
          Functor.isoWhiskerRight
              (indexedSquareTermAction first)
              (coreFiberTransportFunctor bottom₂) ≪≫
            Functor.associator
                (coreFiberTransportFunctor left)
                (coreFiberTransportFunctor bottom₁)
                (coreFiberTransportFunctor bottom₂) ≪≫
              Functor.isoWhiskerLeft
                (coreFiberTransportFunctor left)
                (coreFiberCompositor bottom₁ bottom₂).symm

/-- Horizontal paste is definitionally sent to its componentwise route. -/
theorem indexedSquareTermAction_pasteHorizontal {U : AtomCarrier.{u}}
    {northwest northMiddle northeast southwest southMiddle southeast :
      ExtractionInstance U}
    {top₁ : northwest ⟶ northMiddle} {left : northwest ⟶ southwest}
    {middle : northMiddle ⟶ southMiddle} {bottom₁ : southwest ⟶ southMiddle}
    {top₂ : northMiddle ⟶ northeast} {right : northeast ⟶ southeast}
    {bottom₂ : southMiddle ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top₁ left middle bottom₁)
    (second : ValidatedIndexedBaseSquare U top₂ middle right bottom₂) :
    indexedSquareTermAction (.ofTerm (.pasteHorizontal first.term second.term)) =
      indexedHorizontalComponentRoute first second := rfl

/-- Horizontal-pasting coherence is a theorem equality, not an authored field. -/
abbrev IndexedHorizontalPastingCoherenceType {U : AtomCarrier.{u}}
    {northwest northMiddle northeast southwest southMiddle southeast :
      ExtractionInstance U}
    {top₁ : northwest ⟶ northMiddle} {left : northwest ⟶ southwest}
    {middle : northMiddle ⟶ southMiddle} {bottom₁ : southwest ⟶ southMiddle}
    {top₂ : northMiddle ⟶ northeast} {right : northeast ⟶ southeast}
    {bottom₂ : southMiddle ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top₁ left middle bottom₁)
    (second : ValidatedIndexedBaseSquare U top₂ middle right bottom₂)
    : Prop :=
  indexedHorizontalComponentRoute first second =
    indexedSquareOuterComparison
      (.ofTerm (.pasteHorizontal first.term second.term))

/-- Horizontal pasting agrees with the generated outer-boundary comparison. -/
theorem indexedHorizontalPastingCoherence {U : AtomCarrier.{u}}
    {northwest northMiddle northeast southwest southMiddle southeast :
      ExtractionInstance U}
    {top₁ : northwest ⟶ northMiddle} {left : northwest ⟶ southwest}
    {middle : northMiddle ⟶ southMiddle} {bottom₁ : southwest ⟶ southMiddle}
    {top₂ : northMiddle ⟶ northeast} {right : northeast ⟶ southeast}
    {bottom₂ : southMiddle ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top₁ left middle bottom₁)
    (second : ValidatedIndexedBaseSquare U top₂ middle right bottom₂) :
    IndexedHorizontalPastingCoherenceType first second := by
  apply indexedSquareComparison_ext
  · intro P
    rw [← indexedSquareTermAction_pasteHorizontal first second]
    exact indexedSquareTermAction_hom_fac
      (.ofTerm (.pasteHorizontal first.term second.term)) P
  · exact indexedSquareOuterComparison_hom_fac
      (.ofTerm (.pasteHorizontal first.term second.term))

/-- Exact output type for the componentwise vertical-pasting route. -/
abbrev IndexedVerticalComponentRouteType {U : AtomCarrier.{u}}
    {northwest northeast southwest southeast : ExtractionInstance U}
    (top : northwest ⟶ northeast) (left : northwest ⟶ southwest)
    (right : northeast ⟶ southeast) (bottom : southwest ⟶ southeast) :=
  (coreFiberTransportFunctor top ⋙ coreFiberTransportFunctor right) ≅
    (coreFiberTransportFunctor left ⋙ coreFiberTransportFunctor bottom)

/--
The componentwise vertical route generated from the two square comparisons,
the pseudofunctor compositors, and functor associators.
-/
noncomputable def indexedVerticalComponentRoute {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
    {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
    {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
    {bottom : southwest ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top left₁ right₁ middle)
    (second : ValidatedIndexedBaseSquare U middle left₂ right₂ bottom) :
    IndexedVerticalComponentRouteType top (left₁ ≫ left₂)
      (right₁ ≫ right₂) bottom :=
  Functor.isoWhiskerLeft
      (coreFiberTransportFunctor top)
      (coreFiberCompositor right₁ right₂) ≪≫
    (Functor.associator
        (coreFiberTransportFunctor top)
        (coreFiberTransportFunctor right₁)
        (coreFiberTransportFunctor right₂)).symm ≪≫
      Functor.isoWhiskerRight
          (indexedSquareTermAction first)
          (coreFiberTransportFunctor right₂) ≪≫
        Functor.associator
            (coreFiberTransportFunctor left₁)
            (coreFiberTransportFunctor middle)
            (coreFiberTransportFunctor right₂) ≪≫
          Functor.isoWhiskerLeft
              (coreFiberTransportFunctor left₁)
              (indexedSquareTermAction second) ≪≫
            (Functor.associator
                (coreFiberTransportFunctor left₁)
                (coreFiberTransportFunctor left₂)
                (coreFiberTransportFunctor bottom)).symm ≪≫
              Functor.isoWhiskerRight
                (coreFiberCompositor left₁ left₂).symm
                (coreFiberTransportFunctor bottom)

/-- Vertical paste is definitionally sent to its componentwise route. -/
theorem indexedSquareTermAction_pasteVertical {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
    {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
    {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
    {bottom : southwest ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top left₁ right₁ middle)
    (second : ValidatedIndexedBaseSquare U middle left₂ right₂ bottom) :
    indexedSquareTermAction (.ofTerm (.pasteVertical first.term second.term)) =
      indexedVerticalComponentRoute first second := rfl

/-- Vertical-pasting coherence is a theorem equality, distinct from `comp`. -/
abbrev IndexedVerticalPastingCoherenceType {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
    {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
    {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
    {bottom : southwest ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top left₁ right₁ middle)
    (second : ValidatedIndexedBaseSquare U middle left₂ right₂ bottom)
    : Prop :=
  indexedVerticalComponentRoute first second =
    indexedSquareOuterComparison
      (.ofTerm (.pasteVertical first.term second.term))

/-- Vertical pasting agrees with the generated outer-boundary comparison. -/
theorem indexedVerticalPastingCoherence {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
    {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
    {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
    {bottom : southwest ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top left₁ right₁ middle)
    (second : ValidatedIndexedBaseSquare U middle left₂ right₂ bottom) :
    IndexedVerticalPastingCoherenceType first second := by
  apply indexedSquareComparison_ext
  · intro P
    rw [← indexedSquareTermAction_pasteVertical first second]
    exact indexedSquareTermAction_hom_fac
      (.ofTerm (.pasteVertical first.term second.term)) P
  · exact indexedSquareOuterComparison_hom_fac
      (.ofTerm (.pasteVertical first.term second.term))

/--
The F0 choice for 3-cell coherence is theorem-level equality between two
already generated comparison routes; it is never supplied as raw syntax.
-/
abbrev IndexedThreeCellCoherenceType {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
    {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
    {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
    {bottom : southwest ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top left₁ right₁ middle)
    (second : ValidatedIndexedBaseSquare U middle left₂ right₂ bottom) : Prop :=
  indexedSquareTermAction (.ofTerm (.comp first.term second.term)) =
    indexedSquareTermAction (.ofTerm (.pasteVertical first.term second.term))

/-- Sequential composition and vertical pasting generate the same 3-cell route. -/
theorem indexedThreeCellCoherence {U : AtomCarrier.{u}}
    {northwest northeast middleLeft middleRight southwest southeast :
      ExtractionInstance U}
    {top : northwest ⟶ northeast} {left₁ : northwest ⟶ middleLeft}
    {right₁ : northeast ⟶ middleRight} {middle : middleLeft ⟶ middleRight}
    {left₂ : middleLeft ⟶ southwest} {right₂ : middleRight ⟶ southeast}
    {bottom : southwest ⟶ southeast}
    (first : ValidatedIndexedBaseSquare U top left₁ right₁ middle)
    (second : ValidatedIndexedBaseSquare U middle left₂ right₂ bottom) :
    IndexedThreeCellCoherenceType first second := by
  apply indexedSquareComparison_ext
  · exact indexedSquareTermAction_hom_fac
      (.ofTerm (.comp first.term second.term))
  · exact indexedSquareTermAction_hom_fac
      (.ofTerm (.pasteVertical first.term second.term))

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
