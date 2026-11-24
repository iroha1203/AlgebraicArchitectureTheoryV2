import Formal.SHIGURE.Part1.MarkedVocabulary

/-! # The two declaration contexts of Example 3.7

The two pieces independently retain p,q and q,r. Each piece carries its
own two unary symbols and their two unconditional round-trip Laws.
-/

namespace SHIGURE.Marked.RationalExample

open Vocabulary DeclarationContext

/-- The three module sorts of Example 3.7. -/
inductive SortName
  | p | q | r
  deriving DecidableEq

/-- The four unary operations named by the example. -/
inductive Op
  | f | g | u | v
  deriving DecidableEq

/-- The input module of each of the four operations. -/
def Op.source : Op → SortName
  | .f => .p
  | .g => .q
  | .u => .q
  | .v => .r

/-- The output module of each of the four operations. -/
def Op.target : Op → SortName
  | .f => .q
  | .g => .p
  | .u => .r
  | .v => .q

/-- Exactly the right piece has u and v and their round-trip Laws. -/
def Op.right : Op → Bool
  | .f | .g => false
  | .u | .v => true

/-- Two coordinate generators at q and one at p and r. -/
def generatorCount : SortName → ℕ
  | .q => 2
  | .p | .r => 1

/-- The concrete signature has four unary symbols and a prescribed rank of one at each module. -/
def vocabulary : Vocabulary where
  SortName := SortName
  generators := generatorCount
  rank _ := 1
  Multilinear := Op
  inputs name := [name.source]
  output := Op.target

/-- The example has no partial operations, so the equational Law uses total term evaluation. -/
instance signature_noPartial : IsEmpty vocabulary.signature.Partial :=
  inferInstanceAs (IsEmpty PEmpty)

variable {Γ : List (Option SortName)}

/-- Apply a named unary symbol to its actual typed module argument. -/
def unary (name : Op) (x : Term vocabulary.signature Γ (some name.source)) :
    Term vocabulary.signature Γ (some name.target) :=
  Term.app (sig := vocabulary.signature) (.total (Symbol.multilinear name)) (x.argsCons Term.argsNil)

/-- Each Law states that one of the named round trips is the identity. -/
def roundTrip : Op → Law vocabulary.signature
  | .f => Law.equality (Γ := [some .q]) (unary .f (unary .g (.var .here))) (.var .here)
  | .g => Law.equality (Γ := [some .p]) (unary .g (unary .f (.var .here))) (.var .here)
  | .u => Law.equality (Γ := [some .r]) (unary .u (unary .v (.var .here))) (.var .here)
  | .v => Law.equality (Γ := [some .q]) (unary .v (unary .u (.var .here))) (.var .here)

/-- The four literal, required round-trip Laws of Example 3.7. -/
def laws : vocabulary.Laws where
  declarations := ⟨Op, roundTrip, fun _ => .required⟩
  derived _ role := by cases role

/-- The ordinary SHIGURE presentation of the rational example. -/
abbrev presentation := vocabulary.presentation laws

/-- p and r belong to separate pieces, and q is shared. -/
def keepsModule (right : Bool) : SortName → Prop
  | .p => right = false
  | .q => True
  | .r => right = true

/-- The actual declaration sets of the two local pieces. -/
def keeps (right : Bool) : Declaration presentation → Prop
  | .sort none => True
  | .sort (some s) => keepsModule right s
  | .total (.coefficient _) => True
  | .total (.moduleOp s _) => keepsModule right s
  | .total (.multilinear name) => name.right = right
  | .law name => name.right = right
  | .relation p | .partialOp p | .quantity p => nomatch p

private theorem kept_total_support (right : Bool) (name : vocabulary.Symbol)
    (kept : keeps right (.total name)) : Declaration.dependsOn presentation (.total name) ⊆ {d | keeps right d} := by
  rintro _ ⟨s, occurs, rfl⟩
  cases name with
  | coefficient op =>
    cases op <;> simp_all [Vocabulary.presentation, vocabulary, Vocabulary.signature, Vocabulary.arity, keeps]
  | moduleOp s op =>
    cases op <;> simp_all [Vocabulary.presentation, vocabulary, Vocabulary.signature, Vocabulary.arity, keeps]
    aesop
  | multilinear name =>
    cases name <;> cases right <;> simp_all [Vocabulary.presentation, vocabulary, Vocabulary.signature, Vocabulary.arity, keeps,
      Op.source, Op.target, Op.right, keepsModule] <;> aesop

private theorem kept_law_support (right : Bool) (name : Op) (kept : keeps right (.law name)) :
    Declaration.dependsOn presentation (.law name) ⊆ {d | keeps right d} := by
  rw [Declaration.nonderived_dependencies (P := presentation) name (by intro h; cases h)]
  intro d used
  cases name <;> cases right <;>
    simp_all [Vocabulary.presentation, laws, vocabulary, Vocabulary.signature, Vocabulary.arity, Operation.arity,
      roundTrip, unary, keeps, keepsModule, Op.right, Op.source, Op.target, Law.equality,
      Formula.termEq, Term.graph, Term.graphAt, Formula.existsMany, Formula.conjoin, Term.argsCons,
      Declaration.lawBody, Declaration.formula,
      Declaration.atomic, Declaration.ofOperation, Declaration.sorts] <;> aesop

/-- The left and right contexts with all supports of their actual declarations. -/
def piece (right : Bool) : DeclarationContext presentation where
  declarations := {d | keeps right d}
  closed {a} kept := by
    cases a with
    | sort s => exact Set.empty_subset _
    | total name => exact kept_total_support right name kept
    | law n => exact kept_law_support right n kept
    | relation p => exact nomatch p
    | partialOp p => exact nomatch p
    | quantity p => exact nomatch p

/-- The two pieces both preserve the complete module blocks they contain. -/
theorem piece_blockClosed (right : Bool) : BlockClosed (piece right) where
  coefficients _ _ := ⟨True.intro, fun _ => True.intro⟩
  moduleOp _ keep _ := keep

/-- The two pieces together cover every declared sort, operation and Law. -/
def cover : DeclarationCover (DeclarationContext.full presentation) where
  Index := Bool
  piece := piece
  subset _ := Set.subset_univ _
  covers {a} _ := by
    cases a with
    | sort s =>
      cases s with
      | none => exact ⟨false, True.intro⟩
      | some s =>
        cases s
        · exact ⟨false, rfl⟩
        · exact ⟨false, True.intro⟩
        · exact ⟨true, rfl⟩
    | total name =>
      cases name with
      | coefficient op => exact ⟨false, True.intro⟩
      | moduleOp s op =>
        cases s
        · exact ⟨false, rfl⟩
        · exact ⟨false, True.intro⟩
        · exact ⟨true, rfl⟩
      | multilinear name => exact ⟨name.right, rfl⟩
    | law name => exact ⟨name.right, rfl⟩
    | relation p => exact nomatch p
    | partialOp p => exact nomatch p
    | quantity p => exact nomatch p

/-- Neither piece contains the other's extra operations, so the cover is proper. -/
theorem proper_pieces :
    vocabulary.multilinearDecl laws .u ∉ (piece false).declarations ∧
      vocabulary.multilinearDecl laws .f ∉ (piece true).declarations :=
  ⟨Bool.noConfusion, Bool.noConfusion⟩

end SHIGURE.Marked.RationalExample
