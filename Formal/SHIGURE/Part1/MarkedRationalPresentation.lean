import Formal.SHIGURE.Part1.MarkedLawSupport

/-! # The two declaration contexts of Example 3.7

The two pieces independently retain p,q and q,r. Each piece carries its
own two unary symbols and their two unconditional round-trip Laws.

## Implementation notes

Use the outer operation as the name of its round-trip Law. Its side then
controls both its own declaration and that Law, without a duplicate side
table. The Boolean index represents the two pieces of Example 3.7. The
generated equations on each piece use the side of their own operation.
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
  inputs name := [some name.source]
  output name := some name.target

/-- The one written argument position of a rational operation. -/
def argument (name : Op) : vocabulary.Position name :=
  ⟨some name.source, .here⟩

/-- Every argument position in a unary profile is its one written position. -/
theorem argument_eq (name : Op) (i : vocabulary.Position name) : i = argument name := by
  obtain ⟨s, var⟩ := i
  change Var [some name.source] s at var
  cases var with
  | here => rfl
  | there i => cases i

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

/-- The left round trip starting on q is the equation fg = id. -/
theorem roundTrip_f : roundTrip .f =
    Law.equality (Γ := [some .q]) (unary .f (unary .g (.var .here))) (.var .here) := rfl

/-- The left round trip starting on p is the equation gf = id. -/
theorem roundTrip_g : roundTrip .g =
    Law.equality (Γ := [some .p]) (unary .g (unary .f (.var .here))) (.var .here) := rfl

/-- The right round trip starting on r is the equation uv = id. -/
theorem roundTrip_u : roundTrip .u =
    Law.equality (Γ := [some .r]) (unary .u (unary .v (.var .here))) (.var .here) := rfl

/-- The right round trip starting on q is the equation vu = id. -/
theorem roundTrip_v : roundTrip .v =
    Law.equality (Γ := [some .q]) (unary .v (unary .u (.var .here))) (.var .here) := rfl

/-- The four literal, required round-trip Laws of Example 3.7. -/
def laws : vocabulary.Laws where
  declarations := ⟨Op, roundTrip, fun _ => .required⟩
  derived _ role := by cases role

/-- The ordinary SHIGURE presentation of the rational example. -/
noncomputable abbrev presentation := vocabulary.presentation laws

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
  | .law (.inl name) => name.right = right
  | .law (.inr name) => (LinearityLaw.symbol vocabulary name).right = right
  | .relation p | .partialOp p | .quantity p => nomatch p

/-- Retention of a total operation in a rational piece entails retention of all its arity sorts. -/
private theorem kept_total_support (right : Bool) (name : vocabulary.Symbol)
    (kept : keeps right (.total name)) : Declaration.dependsOn presentation (.total name) ⊆ {d | keeps right d} := by
  cases name with
  | coefficient op =>
    rw [vocabulary.coefficient_dependency]
    exact Set.singleton_subset_iff.mpr True.intro
  | moduleOp s op =>
    refine (vocabulary.module_dependencies laws s op).trans ?_
    rintro d (rfl | same)
    · exact kept
    · rw [Set.mem_singleton_iff.mp same]
      exact True.intro
  | multilinear name =>
    rw [vocabulary.multilinear_dependencies, Declaration.sorts_eq_image]
    rintro _ ⟨s, occurs, rfl⟩
    cases name <;> cases right <;>
      simp_all [vocabulary, keeps, Op.source, Op.target, Op.right, keepsModule] <;> aesop

/-- A retained operation's input sorts lie in the same rational piece. -/
private theorem kept_input_sorts (right : Bool) (op : Operation vocabulary.signature)
    (kept : keeps right (Declaration.ofOperation (P := presentation) op)) :
    Declaration.sorts (P := presentation) op.arity.inputs ⊆ {d | keeps right d} := by
  cases op with
  | total name =>
    rw [Declaration.ofOperation_total] at kept
    rw [Declaration.sorts_eq_image]
    rintro _ ⟨s, occurs, rfl⟩
    have support := kept_total_support right name kept
    rw [Declaration.total_dependencies, Declaration.sorts_eq_image] at support
    exact support ⟨s, List.mem_cons_of_mem _ occurs, rfl⟩
  | partialOp p => exact nomatch p
  | quantity q => exact nomatch q

/-- Turn retention of each sort occurring in a context into retention of that context's declaration support. -/
private theorem kept_sorts (right : Bool) {Γ : List (Option SortName)}
    (all : ∀ s ∈ Γ, keeps right (.sort s)) :
    Declaration.sorts (P := presentation) Γ ⊆ {d | keeps right d} := by
  rw [Declaration.sorts_eq_image]
  rintro _ ⟨s, occurs, rfl⟩
  exact all s occurs

/-- A retained unary operation and supported argument contribute only references in that piece. -/
private theorem unary_refs (right : Bool) {Γ : List (Option SortName)} (name : Op)
    (x : Term vocabulary.signature Γ (some name.source))
    (kept : keeps right (vocabulary.multilinearDecl laws name))
    (refs : Selected.termReferences (P := presentation) x ⊆ {d | keeps right d}) :
    Selected.termReferences (P := presentation) (unary name x) ⊆ {d | keeps right d} := by
  unfold unary
  apply app_refs (P := presentation) (.total (Symbol.multilinear name)) _ (by
    rw [Declaration.ofOperation_total]
    exact kept)
  intro t position
  cases position with
  | here => simpa only [Term.argsCons_here] using refs
  | there empty => cases empty

/-- The term obtained by updating the only argument is the ordinary unary application. -/
private theorem unary_updated {Γ : List (Option SortName)} (name : Op)
    (names : Renaming (vocabulary.inputs name) Γ)
    (x : Term vocabulary.signature Γ (some name.source)) :
    vocabulary.updatedTerm names (argument name) x = unary name x := by
  rw [Vocabulary.updatedTerm_eq]
  apply congrArg (fun (args : ∀ {s}, Var [some name.source] s → Term vocabulary.signature Γ s) =>
    Term.app (sig := vocabulary.signature) (.total (Symbol.multilinear name)) args)
  funext s position
  cases position with
  | here => simpa only [Term.argsCons_here] using vocabulary.updatedTerms_same names (argument name) x
  | there empty => cases empty

/-- Each rational piece retains the syntax of its own required round-trip Law. -/
private theorem roundTrip_supported (right : Bool) (name : Op) (side : name.right = right) :
    Declaration.lawBody (P := presentation) (roundTrip name) ⊆ {d | keeps right d} := by
  cases name <;> cases right <;> simp [Op.right] at side
  all_goals
    first | rw [roundTrip_f] | rw [roundTrip_g] | rw [roundTrip_u] | rw [roundTrip_v]
    refine equality_law_support _ _ (kept_input_sorts _) ?_ (by first | exact rfl | exact True.intro) ?_ ?_
    · apply kept_sorts
      intro s occurs
      simp_all [keeps, keepsModule]
    all_goals
      repeat first
        | exact variable_refs (P := presentation) _
        | refine unary_refs _ _ _ (by rfl) ?_

/-- The actual equality expressing linearity uses only the declarations in its operation's piece. -/
private theorem linearity_supported (right : Bool) (linearity : vocabulary.LinearityLaw)
    (side : (LinearityLaw.symbol vocabulary linearity).right = right) :
    Declaration.lawBody (P := presentation) (LinearityLaw.statement vocabulary linearity) ⊆ {d | keeps right d} := by
  cases linearity with
  | add name i | smul name i =>
    obtain rfl := argument_eq name i
    cases name <;> cases right <;> simp [LinearityLaw.symbol_add, LinearityLaw.symbol_smul, Op.right] at side
    all_goals
      simp only [LinearityLaw.statement_add, LinearityLaw.statement_smul, addLinearityLaw_eq,
        smulLinearityLaw_eq, unary_updated]
      refine equality_law_support _ _ (kept_input_sorts _) ?_ (by first | exact rfl | exact True.intro) ?_ ?_
      · apply kept_sorts
        intro s occurs
        simp_all [keeps, keepsModule, Op.source, argument, vocabulary] <;> aesop
      all_goals
        repeat first
          | exact variable_refs (P := presentation) _
          | refine unary_refs _ _ _ (by rfl) ?_
          | refine addTerm_refs (V := vocabulary) (L := laws) _ _ _ (by first | exact rfl | exact True.intro) ?_ ?_
          | refine smulTerm_refs (V := vocabulary) (L := laws) _ _ _ (by first | exact rfl | exact True.intro) ?_ ?_

/-- Every retained rational Law has its required dependencies in the corresponding piece. -/
private theorem kept_law_support (right : Bool) (name : presentation.laws.LawName) (kept : keeps right (.law name)) :
    Declaration.dependsOn presentation (.law name) ⊆ {d | keeps right d} := by
  rw [Declaration.nonderived_dependencies (P := presentation) name (by cases name <;> intro h <;> cases h)]
  cases name with
  | inl name => exact roundTrip_supported right name kept
  | inr name =>
    rw [vocabulary.linearity_statement]
    exact linearity_supported right name kept

/-- The left and right contexts with all supports of their actual declarations. -/
def piece (right : Bool) : DeclarationContext presentation where
  declarations := {d | keeps right d}
  closed {a} kept := by
    cases a with
    | sort s => rw [Declaration.sort_dependencies]; exact Set.empty_subset _
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
    | law name =>
      cases name with
      | inl name => exact ⟨name.right, rfl⟩
      | inr name => exact ⟨(LinearityLaw.symbol vocabulary name).right, rfl⟩
    | relation p => exact nomatch p
    | partialOp p => exact nomatch p
    | quantity p => exact nomatch p

/-- Neither piece contains the other's extra operations, so the cover is proper. -/
theorem proper_pieces :
    vocabulary.multilinearDecl laws .u ∉ (piece false).declarations ∧
      vocabulary.multilinearDecl laws .f ∉ (piece true).declarations :=
  ⟨Bool.noConfusion, Bool.noConfusion⟩

end SHIGURE.Marked.RationalExample
