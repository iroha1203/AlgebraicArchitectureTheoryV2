import Formal.SHIGURE.Part1.Derivations

/-! # Declaration data selected by a reading

Definition 1.11 refers to the declaration contexts and covers of
Definitions 3.1 and 3.3. This module defines the data that a reading must
select, including the declaration dependencies of a derived Law.

## Implementation notes

Declaration names exclude the occurrences inside a Law. Those occurrences
contribute to the Law's dependencies. We record direct dependencies as a
set and ask each context to be closed under them. Encoding the full
transitive closure in each Law would duplicate the closure condition.
-/

universe u

namespace SHIGURE

/-- The declaration names of one primitive presentation. -/
inductive Declaration (P : PrimitivePresentation.{u}) : Type u
  | sort : P.signature.SortType → Declaration P
  | total : P.signature.Total → Declaration P
  | relation : P.signature.Rel → Declaration P
  | partialOp : P.signature.Partial → Declaration P
  | quantity : P.signature.Quantity → Declaration P
  | law : P.laws.LawName → Declaration P

namespace Declaration

variable {P : PrimitivePresentation.{u}}

/-- The sort declarations of a context, including its unused positions. -/
def sorts (Γ : List P.signature.SortType) : Set (Declaration P) :=
  Declaration.sort '' {s | s ∈ Γ}

/-- The name referred to by a graph symbol. -/
def ofOperation : Operation P.signature → Declaration P
  | .total f => .total f
  | .partialOp p => .partialOp p
  | .quantity q => .quantity q

/-- A primitive formula refers to its typed relation, domain, or graph declaration. -/
def atomic {Γ : List P.signature.SortType} : Atomic P.signature Γ → Set (Declaration P)
  | .eq _ _ => ∅
  | .rel r _ => {.relation r}
  | .domain p _ => {.partialOp p}
  | .graph op _ _ => {ofOperation op}

/-- The primitive declarations mentioned by a positive formula and its bound sorts. -/
def formula : {Γ : List P.signature.SortType} → Formula P.signature Γ → Set (Declaration P)
  | _, .atom a => atomic a
  | _, .truth => ∅
  | _, .falsehood => ∅
  | _, .conj p q => formula p ∪ formula q
  | _, .disj p q => formula p ∪ formula q
  | _, @Formula.ex _ _ s p => {Declaration.sort s} ∪ formula p

/-- Every position and primitive mentioned by a written Law. -/
def lawBody (law : Law P.signature) : Set (Declaration P) :=
  sorts law.context ∪ formula law.input ∪ formula law.conclusion

/-- The Law declarations, sorts, and symbols used anywhere in the proof tree. -/
def derivation :
    {Γ : List P.signature.SortType} → {p q : Formula P.signature Γ} →
    Derivation P.theory p q → Set (Declaration P)
  | Γ, p, q, proof => sorts Γ ∪ formula p ∪ formula q ∪ match proof with
    | .required name => {Declaration.law name.val}
    | .cut d e | .andIntro d e | .orElim d e => derivation d ∪ derivation e
    | .rename _ d | .existsElim d => derivation d
    | .refl _ | .graph _ | .truth _ | .falsehood _ | .andLeft _ _ | .andRight _ _ |
        .orLeft _ _ | .orRight _ _ | .existsIntro _ _ | .eqRefl _ | .eqSubst _ _ _ => ∅

/-- The immediate references of a declaration in Definition 3.1. -/
def dependsOn (P : PrimitivePresentation.{u}) : Declaration P → Set (Declaration P)
  | .sort _ => ∅
  | .total f => sorts ((P.signature.totalArity f).output :: (P.signature.totalArity f).inputs)
  | .relation r => sorts (P.signature.relInputs r)
  | .quantity q => sorts ((P.signature.quantityArity q).output :: (P.signature.quantityArity q).inputs)
  | .partialOp p =>
    sorts ((P.signature.partialArity p).output :: (P.signature.partialArity p).inputs) ∪
      match P.domainInclusions p with
      | none => ∅
      | some data => {Declaration.sort data.domainSort} ∪
        {a | ∃ (s : P.signature.SortType) (i : Var (P.signature.partialArity p).inputs s),
          a = ofOperation (data.symbol i).operation}
  | .law name =>
    lawBody (P.laws.statement name) ∪
      match role : P.laws.role name with
      | .derived => derivation (P.derived name role)
      | .required | .additional => ∅

end Declaration

/-- The dependency-closed declaration sets used in readings. -/
structure DeclarationContext (P : PrimitivePresentation.{u}) where
  /-- The retained declaration names. -/
  declarations : Set (Declaration P)
  /-- Each retained declaration retains every reference. -/
  closed {a : Declaration P} : a ∈ declarations → Declaration.dependsOn P a ⊆ declarations

/-- A family of subcontexts whose union is the selected context. -/
structure DeclarationCover {P : PrimitivePresentation.{u}} (U : DeclarationContext P) where
  /-- The index type of the cover. -/
  Index : Type u
  /-- A closed declaration context for each index. -/
  piece : Index → DeclarationContext P
  /-- Every piece lies in the context it covers. -/
  subset (i : Index) : (piece i).declarations ⊆ U.declarations
  /-- Every retained name is contained in some local piece. -/
  covers {a : Declaration P} : a ∈ U.declarations → ∃ i, a ∈ (piece i).declarations

end SHIGURE
