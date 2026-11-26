import Formal.SHIGURE.Part1.DeclarationContexts
import Mathlib.CategoryTheory.Category.Preorder

/-! # Declaration contexts and their covers

Definition 3.1 gives a preorder of dependency-closed contexts. Definition 3.3
uses intersections and set-indexed unions in this preorder to define covers.

## Implementation notes

A context keeps original declaration names. Its order is inclusion, so the
category is the mathlib category of a preorder. A support is a least closed
context. For terms the raw generators are read from the positive evaluation
graph, which includes the free context, result sort, operation nodes,
and the intermediate sorts of applications and strict bindings.
-/

universe u v

namespace SHIGURE
namespace DeclarationContext

variable {P : PrimitivePresentation.{u}}

/-- A declaration context is determined by its retained names. -/
@[ext] theorem ext {U V : DeclarationContext P} (same : U.declarations = V.declarations) : U = V := by
  cases U
  cases V
  cases same
  rfl

/-- Contexts are ordered by inclusion of declarations. -/
instance partialOrder : PartialOrder (DeclarationContext P) where
  le U V := U.declarations ⊆ V.declarations
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h k := ext (Set.Subset.antisymm h k)

/-- Inclusion in the context category is inclusion of the retained names. -/
theorem le_iff {U V : DeclarationContext P} : U ≤ V ↔ U.declarations ⊆ V.declarations :=
  Iff.rfl

/-- The context retaining no declaration. -/
def empty (P : PrimitivePresentation.{u}) : DeclarationContext P :=
  ⟨∅, fun kept => (Set.notMem_empty _ kept).elim⟩

/-- Every declaration is retained in the full context. -/
def full (P : PrimitivePresentation.{u}) : DeclarationContext P :=
  ⟨Set.univ, fun _ => Set.subset_univ _⟩

/-- Intersections retain all dependencies of their common declarations. -/
def inter (U V : DeclarationContext P) : DeclarationContext P where
  declarations := U.declarations ∩ V.declarations
  closed kept _ used := ⟨U.closed kept.1 used, V.closed kept.2 used⟩

/-- The retained names of an intersection are exactly its common names. -/
@[simp] theorem mem_inter {U V : DeclarationContext P} {d : Declaration P} :
    d ∈ (inter U V).declarations ↔ d ∈ U.declarations ∧ d ∈ V.declarations :=
  Iff.rfl

/-- The intersection is a subcontext of its left factor. -/
theorem inter_le_left (U V : DeclarationContext P) : inter U V ≤ U :=
  fun _ kept => kept.1

/-- The intersection is a subcontext of its right factor. -/
theorem inter_le_right (U V : DeclarationContext P) : inter U V ≤ V :=
  fun _ kept => kept.2

/-- A common subcontext is contained in the intersection. -/
theorem le_inter {U V W : DeclarationContext P} (left : W ≤ U) (right : W ≤ V) : W ≤ inter U V :=
  fun _ kept => ⟨left kept, right kept⟩

/-- Arbitrary intersections of declaration contexts are closed. -/
def intersection {I : Type v} (piece : I → DeclarationContext P) : DeclarationContext P where
  declarations := {d | ∀ i, d ∈ (piece i).declarations}
  closed kept _ used i := (piece i).closed (kept i) used

/-- An indexed intersection retains every name present at all indices. -/
@[simp] theorem mem_intersection {I : Type v} {piece : I → DeclarationContext P} {d : Declaration P} :
    d ∈ (intersection piece).declarations ↔ ∀ i, d ∈ (piece i).declarations :=
  Iff.rfl

/-- Arbitrary unions of declaration contexts are closed. -/
def union {I : Type v} (piece : I → DeclarationContext P) : DeclarationContext P where
  declarations := {d | ∃ i, d ∈ (piece i).declarations}
  closed kept _ used := by
    obtain ⟨i, kept⟩ := kept
    exact ⟨i, (piece i).closed kept used⟩

/-- An indexed union retains exactly those names occurring in some piece. -/
@[simp] theorem mem_union {I : Type v} {piece : I → DeclarationContext P} {d : Declaration P} :
    d ∈ (union piece).declarations ↔ ∃ i, d ∈ (piece i).declarations :=
  Iff.rfl

/-- Every piece is contained in its union. -/
theorem le_union {I : Type v} (piece : I → DeclarationContext P) (i : I) : piece i ≤ union piece :=
  fun _ kept => ⟨i, kept⟩

/-- The union is contained in every common upper bound. -/
theorem union_le {I : Type v} {piece : I → DeclarationContext P} {U : DeclarationContext P}
    (below : ∀ i, piece i ≤ U) : union piece ≤ U := by
  rintro d ⟨i, kept⟩
  exact below i kept

/-- Dependency closure is the least context containing the named generators. -/
def closure (generators : Set (Declaration P)) : DeclarationContext P :=
  intersection fun U : {U : DeclarationContext P // generators ⊆ U.declarations} => U.val

/-- Closing a set of generators retains each generator. -/
theorem subset_closure (generators : Set (Declaration P)) :
    generators ⊆ (closure generators).declarations :=
  fun _ kept U => U.property kept

/-- A closed context retains the closure exactly when it retains the generators. -/
theorem closure_le_iff {generators : Set (Declaration P)} {U : DeclarationContext P} :
    closure generators ≤ U ↔ generators ⊆ U.declarations := by
  constructor
  · intro below d kept
    exact below (subset_closure generators kept)
  · intro keeps d inClosure
    exact inClosure ⟨U, keeps⟩

end DeclarationContext

namespace Declaration

variable {P : PrimitivePresentation.{u}} {Γ : List P.signature.SortType} {s : P.signature.SortType}

/-- A written formula contains no named Law declaration. -/
theorem law_notMem_formula (name : P.laws.LawName) (p : Formula P.signature Γ) :
    Declaration.law name ∉ formula p := by
  induction p with
  | atom a =>
    cases a with
    | eq | rel | domain => simp [formula_atom, atomic_eq, atomic_rel, atomic_domain]
    | graph op => cases op <;> simp
        [formula_atom, atomic_graph, ofOperation_total, ofOperation_partialOp, ofOperation_quantity]
  | truth => simp [formula_truth]
  | falsehood => simp [formula_falsehood]
  | conj p q hp hq => simpa only [formula_conj, Set.mem_union, not_or] using And.intro hp hq
  | disj p q hp hq => simpa only [formula_disj, Set.mem_union, not_or] using And.intro hp hq
  | ex p ih => simpa [formula_ex] using ih

/-- The written support of a Law has only sort and primitive declarations. -/
theorem law_notMem_lawBody (name : P.laws.LawName) (law : Law P.signature) :
    Declaration.law name ∉ lawBody law := by
  have notSort : Declaration.law name ∉ sorts (P := P) law.context := by
    rw [sorts_eq_image]
    rintro ⟨s, _, h⟩
    cases h
  simp only [lawBody_eq, Set.mem_union, not_or, notSort, law_notMem_formula, and_self, not_false_eq_true]

/-- The dependency-closed support of a positive formula, including the free context. -/
def formulaContext (p : Formula P.signature Γ) : DeclarationContext P :=
  DeclarationContext.closure (formulaSupport p)

/-- The dependency-closed support of an ambient term and all its typed values. -/
def termContext (t : Term P.signature Γ s) : DeclarationContext P :=
  formulaContext t.graph

/-- The dependency closure of a Law's written context, input and conclusion. -/
def lawContext (law : Law P.signature) : DeclarationContext P :=
  DeclarationContext.closure (lawBody law)

/-- The support of a retained Law declaration also includes any registered derivation's references. -/
def namedLawContext (name : P.laws.LawName) : DeclarationContext P :=
  DeclarationContext.closure {Declaration.law name}

/-- A context contains formula support precisely by containing its raw generators. -/
theorem formulaContext_le_iff {U : DeclarationContext P} (p : Formula P.signature Γ) :
    formulaContext p ≤ U ↔ formulaSupport p ⊆ U.declarations :=
  DeclarationContext.closure_le_iff

/-- A context contains term support precisely by containing the term graph's raw generators. -/
theorem termContext_le_iff {U : DeclarationContext P} (t : Term P.signature Γ s) :
    termContext t ≤ U ↔ formulaSupport t.graph ⊆ U.declarations :=
  formulaContext_le_iff t.graph

/-- A context contains Law support precisely by containing its input and conclusion generators. -/
theorem lawContext_le_iff {U : DeclarationContext P} (law : Law P.signature) :
    lawContext law ≤ U ↔ lawBody law ⊆ U.declarations :=
  DeclarationContext.closure_le_iff

/-- A retained declaration keeps both forms of its original written support. -/
theorem declaredLawSupport_subset_of_mem {U : DeclarationContext P} {name : P.laws.LawName}
    (kept : Declaration.law name ∈ U.declarations) :
    declaredLawSupport name ⊆ U.declarations := by
  refine Set.Subset.trans ?_ (U.closed kept)
  by_cases role : P.laws.role name = .derived
  · rw [derived_dependencies name role]
    exact Set.subset_union_left
  · rw [nonderived_dependencies name role]

/-- A declared Law in a context has its entire native written support in that context. -/
theorem lawBody_subset_of_mem {U : DeclarationContext P} {name : P.laws.LawName}
    (kept : Declaration.law name ∈ U.declarations) :
    lawBody (P.laws.statement name) ⊆ U.declarations :=
  Set.subset_union_left.trans (declaredLawSupport_subset_of_mem kept)

/-- A retained Law keeps the references of its registered coefficient equation. -/
theorem coefficientWritingSupport_subset_of_mem {U : DeclarationContext P} {name : P.laws.LawName}
    (kept : Declaration.law name ∈ U.declarations)
    {e : Quantities.RegisteredCoefficientEquation P.signature (P.laws.statement name).context}
    (registered : P.coefficientWriting name = some e) : coefficientWritingSupport (P := P) e ⊆ U.declarations := by
  have support : coefficientEquationSupport (P := P) name ⊆ U.declarations :=
    Set.subset_union_right.trans (declaredLawSupport_subset_of_mem kept)
  simpa [coefficientEquationSupport, registered] using support

end Declaration

namespace DeclarationCover

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

/-- A cover's union is exactly the covered context. -/
theorem union_piece (cover : DeclarationCover U) : union cover.piece = U := by
  apply le_antisymm
  · exact union_le cover.subset
  · exact fun _ kept => cover.covers kept

/-- The identity inclusion is a singleton cover. -/
def identity (U : DeclarationContext P) : DeclarationCover U where
  Index := PUnit
  piece _ := U
  subset _ := Set.Subset.rfl
  covers kept := ⟨PUnit.unit, kept⟩

/-- Pull a cover back by intersecting each piece with the smaller context. -/
def pullback (cover : DeclarationCover U) (inside : V ≤ U) : DeclarationCover V where
  Index := cover.Index
  piece i := inter (cover.piece i) V
  subset i := inter_le_right (cover.piece i) V
  covers kept := by
    obtain ⟨i, localKept⟩ := cover.covers (inside kept)
    exact ⟨i, ⟨localKept, kept⟩⟩

/-- Covering each piece and flattening the resulting family gives a cover of the original context. -/
def comp (cover : DeclarationCover U) (refine : ∀ i, DeclarationCover (cover.piece i)) :
    DeclarationCover U where
  Index := Σ i, (refine i).Index
  piece i := (refine i.1).piece i.2
  subset i := (refine i.1).subset i.2 |>.trans (cover.subset i.1)
  covers kept := by
    obtain ⟨i, localKept⟩ := cover.covers kept
    obtain ⟨j, refinedKept⟩ := (refine i).covers localKept
    exact ⟨⟨i, j⟩, refinedKept⟩

/-- A chosen local index for a retained declaration, available from the cover alone. -/
noncomputable def index (cover : DeclarationCover U) {d : Declaration P} (kept : d ∈ U.declarations) :
    cover.Index :=
  Classical.choose (cover.covers kept)

/-- A chosen local piece retains the declaration for which it was selected. -/
theorem mem_index (cover : DeclarationCover U) {d : Declaration P} (kept : d ∈ U.declarations) :
    d ∈ (cover.piece (cover.index kept)).declarations :=
  Classical.choose_spec (cover.covers kept)

end DeclarationCover
end SHIGURE
