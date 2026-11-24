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

/-- The extended context retains its new sort and every previous sort. -/
theorem sorts_cons_subset {Γ : List P.signature.SortType} {s : P.signature.SortType}
    {V : Set (Declaration P)} (head : Declaration.sort s ∈ V) (tail : sorts Γ ⊆ V) :
    sorts (s :: Γ) ⊆ V := by
  rintro _ ⟨t, ht, rfl⟩
  rcases List.mem_cons.mp ht with rfl | ht
  · exact head
  · exact tail ⟨t, ht, rfl⟩

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

/-- An atom's support includes all its free context, even positions unused by the atom. -/
def atomicSupport {Γ : List P.signature.SortType} (a : Atomic P.signature Γ) :
    Set (Declaration P) :=
  sorts Γ ∪ atomic a

/-- A formula's direct support. Dependency-closed contexts also contain its indirect support. -/
def formulaSupport {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    Set (Declaration P) :=
  sorts Γ ∪ formula p

/-- Every position and primitive mentioned by a written Law. -/
def lawBody (law : Law P.signature) : Set (Declaration P) :=
  sorts law.context ∪ formula law.input ∪ formula law.conclusion

/-- Read the contexts and formulas of a sequent in the presentation with the same signature. -/
private def sequentSupport {sig : Signature.{u}} (same : sig = P.signature)
    {Γ : List sig.SortType} (p q : Formula sig Γ) : Set (Declaration P) := by
  subst sig
  exact sorts Γ ∪ formula p ∪ formula q

/-- The Law declarations, sorts, and symbols used anywhere in the proof tree. -/
def derivationOf {T : Theory.{u}} (same : T.signature = P.signature)
    (lawName : T.LawName → P.laws.LawName) :
    {Γ : List T.signature.SortType} → {p q : Formula T.signature Γ} →
    Derivation T p q → Set (Declaration P)
  | _, p, q, proof => sequentSupport same p q ∪ match proof with
    | .required name => {Declaration.law (lawName name)}
    | .cut d e | .andIntro d e | .orElim d e => derivationOf same lawName d ∪ derivationOf same lawName e
    | .rename _ d | .existsElim d => derivationOf same lawName d
    | .refl _ | .graph _ | .truth _ | .falsehood _ | .andLeft _ _ | .andRight _ _ |
        .orLeft _ _ | .orRight _ _ | .existsIntro _ _ | .eqRefl _ | .eqSubst _ _ _ => ∅

/-- The support of a derivation in the theory presented here. -/
abbrev derivation {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (proof : Derivation P.theory p q) : Set (Declaration P) :=
  derivationOf rfl Subtype.val proof

/-- The declarations needed to read an ordered ring residual. -/
def ringEquationSupport (name : P.laws.LawName) : Set (Declaration P) :=
  match P.ringEquation name with
  | none => ∅
  | some equation =>
    let ring := equation.written.equation.ring
    formula equation.written.equation.left.graph ∪
      formula equation.written.equation.right.graph ∪
      ((Declaration.law '' equation.axiomNames ∪
        {ofOperation ring.zero.symbol.operation, ofOperation ring.one.symbol.operation,
          ofOperation ring.add.symbol.operation, ofOperation ring.neg.symbol.operation,
          ofOperation ring.mul.symbol.operation}) ∪
        {a | ∃ i, a ∈ derivationOf rfl Subtype.val (equation.axioms_derive i)})

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

/-- A retained derived Law keeps the actual references of its registered derivation. -/
theorem derivation_subset_dependsOn (name : P.laws.LawName) (role : P.laws.role name = .derived) :
    derivation (P.derived name role) ⊆ dependsOn P (.law name) := by
  intro d used
  rw [dependsOn]
  refine Or.inr ?_
  split
  · exact used
  · rename_i otherRole
    cases role.symm.trans otherRole
  · rename_i otherRole
    cases role.symm.trans otherRole

/-- Required and additional Laws refer to their written support. -/
theorem nonderived_dependencies (name : P.laws.LawName) (role : P.laws.role name ≠ .derived) :
    dependsOn P (.law name) = lawBody (P.laws.statement name) := by
  rw [dependsOn]
  split
  · rename_i h
    exact (role h).elim
  · exact Set.union_empty _
  · exact Set.union_empty _

/-- A required Law used by a derivation is among that derivation's declarations. -/
theorem required_mem_derivation (name : P.theory.LawName) :
    Declaration.law name.val ∈ derivation (Derivation.required name) :=
  Or.inr (Set.mem_singleton _)

/-- The named ring Laws support the attached residual presentation. -/
theorem ringLaw_mem_ringEquationSupport {name : P.laws.LawName} {equation : NamedRingEquation P.laws name}
    (attached : P.ringEquation name = some equation) {axiomName : P.laws.LawName}
    (selected : axiomName ∈ equation.axiomNames) :
    Declaration.law axiomName ∈ ringEquationSupport (P := P) name := by
  simp only [ringEquationSupport, attached]
  exact Or.inr (Or.inl (Or.inl ⟨axiomName, selected, rfl⟩))

/-- Every declaration used in an attached ring proof supports that residual presentation. -/
theorem ringProof_mem_ringEquationSupport {name : P.laws.LawName} {equation : NamedRingEquation P.laws name}
    (attached : P.ringEquation name = some equation) {i : RingVocabulary.LawName} {d : Declaration P}
    (used : d ∈ derivationOf rfl Subtype.val (equation.axioms_derive i)) :
    d ∈ ringEquationSupport (P := P) name := by
  simp only [ringEquationSupport, attached]
  exact Or.inr (Or.inr ⟨i, used⟩)

end Declaration

/-- The dependency-closed declaration sets used in readings. -/
structure DeclarationContext (P : PrimitivePresentation.{u}) where
  /-- The retained declaration names. -/
  declarations : Set (Declaration P)
  /-- Each retained declaration retains every reference. -/
  closed {a : Declaration P} : a ∈ declarations → Declaration.dependsOn P a ⊆ declarations

/-- A reading of a particular attached residual retains the names needed by that presentation. -/
def DeclarationContext.RetainsRingSupport {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    (name : P.laws.LawName) : Prop :=
  Declaration.ringEquationSupport (P := P) name ⊆ U.declarations

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
