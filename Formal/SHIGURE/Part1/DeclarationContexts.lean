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

/-- A context support in Definition 3.1 contains the declared sort of each position. -/
theorem sorts_eq_image (Γ : List P.signature.SortType) :
    sorts (P := P) Γ = Declaration.sort '' {s | s ∈ Γ} :=
  rfl

/-- A sort occurring at any position is in the support of the variable context. -/
theorem sort_mem_sorts {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (mem : s ∈ Γ) : Declaration.sort s ∈ sorts (P := P) Γ :=
  ⟨s, mem, rfl⟩

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

/-- The declaration support of a total graph uses the total-symbol tag. -/
theorem ofOperation_total (f : P.signature.Total) :
    ofOperation (P := P) (.total f) = .total f :=
  rfl

/-- The declaration support of a partial graph uses the partial-symbol tag. -/
theorem ofOperation_partialOp (p : P.signature.Partial) :
    ofOperation (P := P) (.partialOp p) = .partialOp p :=
  rfl

/-- The declaration support of a quantity graph uses the quantity-symbol tag. -/
theorem ofOperation_quantity (q : P.signature.Quantity) :
    ofOperation (P := P) (.quantity q) = .quantity q :=
  rfl

/-- A primitive formula refers to its typed relation, domain, or graph declaration. -/
def atomic {Γ : List P.signature.SortType} : Atomic P.signature Γ → Set (Declaration P)
  | .eq _ _ => ∅
  | .rel r _ => {.relation r}
  | .domain p _ => {.partialOp p}
  | .graph op _ _ => {ofOperation op}

/-- Equality adds no primitive declaration to the support of its variables. -/
theorem atomic_eq {Γ : List P.signature.SortType} {s : P.signature.SortType} (x y : Var Γ s) :
    atomic (P := P) (.eq x y) = ∅ :=
  rfl

/-- A relation atom refers to its declared relation. -/
theorem atomic_rel {Γ : List P.signature.SortType} (r : P.signature.Rel)
    (vars : Renaming (P.signature.relInputs r) Γ) :
    atomic (P := P) (.rel r vars) = {.relation r} :=
  rfl

/-- A domain atom refers to its declared partial operation. -/
theorem atomic_domain {Γ : List P.signature.SortType} (p : P.signature.Partial)
    (vars : Renaming (P.signature.partialArity p).inputs Γ) :
    atomic (P := P) (.domain p vars) = {.partialOp p} :=
  rfl

/-- A graph atom refers to the declaration determined by its operation tag. -/
theorem atomic_graph {Γ : List P.signature.SortType} (op : Operation P.signature)
    (vars : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    atomic (P := P) (.graph op vars y) = {ofOperation op} :=
  rfl

/-- The primitive declarations mentioned by a positive formula and its bound sorts. -/
def formula : {Γ : List P.signature.SortType} → Formula P.signature Γ → Set (Declaration P)
  | _, .atom a => atomic a
  | _, .truth => ∅
  | _, .falsehood => ∅
  | _, .conj p q => formula p ∪ formula q
  | _, .disj p q => formula p ∪ formula q
  | _, @Formula.ex _ _ s p => {Declaration.sort s} ∪ formula p

/-- An atomic formula inherits its primitive declaration support. -/
theorem formula_atom {Γ : List P.signature.SortType} (a : Atomic P.signature Γ) :
    formula (P := P) (.atom a) = atomic a :=
  rfl

/-- Truth adds no primitive support. -/
theorem formula_truth {Γ : List P.signature.SortType} :
    formula (P := P) (Γ := Γ) .truth = ∅ :=
  rfl

/-- Falsehood adds no primitive support. -/
theorem formula_falsehood {Γ : List P.signature.SortType} :
    formula (P := P) (Γ := Γ) .falsehood = ∅ :=
  rfl

/-- A conjunction uses the primitive declarations of both of its formulas. -/
theorem formula_conj {Γ : List P.signature.SortType} (p q : Formula P.signature Γ) :
    formula (P := P) (p.conj q) = formula p ∪ formula q :=
  rfl

/-- A disjunction uses the primitive declarations of both of its formulas. -/
theorem formula_disj {Γ : List P.signature.SortType} (p q : Formula P.signature Γ) :
    formula (P := P) (p.disj q) = formula p ∪ formula q :=
  rfl

/-- The support of an existential includes its bound sort and the body's primitive references. -/
theorem formula_ex {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) :
    formula (P := P) p.ex = {Declaration.sort s} ∪ formula p :=
  rfl

/-- An atom's support includes all its free context, even positions unused by the atom. -/
def atomicSupport {Γ : List P.signature.SortType} (a : Atomic P.signature Γ) :
    Set (Declaration P) :=
  sorts Γ ∪ atomic a

/-- Atomic support in Definition 3.1 contains both the free context and the
primitive names of the atom. -/
theorem atomicSupport_eq {Γ : List P.signature.SortType} (a : Atomic P.signature Γ) :
    atomicSupport (P := P) a = sorts Γ ∪ atomic a :=
  rfl

/-- The support of a relation atom includes its relation declaration. -/
theorem relation_mem_atomicSupport {Γ : List P.signature.SortType} (r : P.signature.Rel)
    (vars : Renaming (P.signature.relInputs r) Γ) :
    Declaration.relation r ∈ atomicSupport (.rel r vars) := by
  rw [atomicSupport_eq, atomic_rel]
  exact Or.inr (Set.mem_singleton _)

/-- The support of a domain atom includes its partial-operation declaration. -/
theorem domain_mem_atomicSupport {Γ : List P.signature.SortType} (p : P.signature.Partial)
    (vars : Renaming (P.signature.partialArity p).inputs Γ) :
    Declaration.partialOp p ∈ atomicSupport (.domain p vars) := by
  rw [atomicSupport_eq, atomic_domain]
  exact Or.inr (Set.mem_singleton _)

/-- The support of a graph atom includes its tagged operation declaration. -/
theorem graph_mem_atomicSupport {Γ : List P.signature.SortType} (op : Operation P.signature)
    (vars : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    ofOperation op ∈ atomicSupport (.graph op vars y) := by
  rw [atomicSupport_eq, atomic_graph]
  exact Or.inr (Set.mem_singleton _)

/-- A formula's direct support. Dependency-closed contexts also contain its indirect support. -/
def formulaSupport {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    Set (Declaration P) :=
  sorts Γ ∪ formula p

/-- Formula support in Definition 3.1 joins the free context and direct references. -/
theorem formulaSupport_eq {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    formulaSupport (P := P) p = sorts Γ ∪ formula p :=
  rfl

/-- All free sorts of an atom occur in its support. -/
theorem sorts_subset_atomicSupport {Γ : List P.signature.SortType} (a : Atomic P.signature Γ) :
    sorts Γ ⊆ atomicSupport (P := P) a :=
  Set.subset_union_left

/-- All free sorts of a formula occur in its support. -/
theorem sorts_subset_formulaSupport {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    sorts Γ ⊆ formulaSupport (P := P) p :=
  Set.subset_union_left

/-- The atom and the formula it generates have identical support. -/
theorem formulaSupport_atom {Γ : List P.signature.SortType} (a : Atomic P.signature Γ) :
    formulaSupport (P := P) (.atom a) = atomicSupport a :=
  rfl

/-- The support of either binary connective contains the support of its left operand. -/
theorem binarySupport_left {Γ : List P.signature.SortType} {p q r : Formula P.signature Γ}
    (body : formula (P := P) r = formula p ∪ formula q) :
    formulaSupport p ⊆ formulaSupport r := by
  rw [formulaSupport_eq, formulaSupport_eq, body]
  exact Set.union_subset (Set.subset_union_left) (Set.subset_union_left.trans Set.subset_union_right)

/-- The support of either binary connective contains the support of its right operand. -/
theorem binarySupport_right {Γ : List P.signature.SortType} {p q r : Formula P.signature Γ}
    (body : formula (P := P) r = formula p ∪ formula q) :
    formulaSupport q ⊆ formulaSupport r := by
  rw [formulaSupport_eq, formulaSupport_eq, body]
  exact Set.union_subset (Set.subset_union_left) (Set.subset_union_right.trans Set.subset_union_right)

/-- The bound sort of an existential belongs to its formula support. -/
theorem boundSort_mem_formulaSupport {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) :
    Declaration.sort s ∈ formulaSupport p.ex := by
  rw [formulaSupport_eq, formula_ex]
  exact Or.inr (Or.inl (Set.mem_singleton _))

/-- The support of an existential contains the support of its body in the extended context. -/
theorem formulaSupport_ex_body {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (p : Formula P.signature (s :: Γ)) : formulaSupport (P := P) p ⊆ formulaSupport p.ex := by
  apply Set.union_subset
  · exact sorts_cons_subset (boundSort_mem_formulaSupport p) (sorts_subset_formulaSupport p.ex)
  · rw [formulaSupport_eq, formula_ex]
    exact Set.subset_union_right.trans Set.subset_union_right

/-- Every position and primitive mentioned by a written Law. -/
def lawBody (law : Law P.signature) : Set (Declaration P) :=
  sorts law.context ∪ formula law.input ∪ formula law.conclusion

/-- The written part of a Law keeps the context sorts and both formula supports. -/
theorem lawBody_eq (law : Law P.signature) :
    lawBody (P := P) law = sorts law.context ∪ formula law.input ∪ formula law.conclusion :=
  rfl

/-- The free sorts of a Law belong to its written support. -/
theorem sorts_subset_lawBody (law : Law P.signature) : sorts law.context ⊆ lawBody (P := P) law :=
  Set.subset_union_left.trans Set.subset_union_left

/-- Its antecedent uses only the written support of the Law. -/
theorem formulaSupport_input_subset_lawBody (law : Law P.signature) :
    formulaSupport (P := P) law.input ⊆ lawBody law :=
  Set.subset_union_left

/-- Its conclusion uses only the written support of the Law. -/
theorem formulaSupport_conclusion_subset_lawBody (law : Law P.signature) :
    formulaSupport (P := P) law.conclusion ⊆ lawBody law :=
  Set.union_subset (sorts_subset_lawBody law) Set.subset_union_right

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

/-- The support of each rule combines its written sequent and the references of its premises. -/
theorem derivationOf_support_eq {I : Type u} {statement : I → Law P.signature}
    (name : I → P.laws.LawName) :
    {Γ : List P.signature.SortType} → {p q : Formula P.signature Γ} →
    (d : Derivation (⟨P.signature, I, statement⟩ : Theory) p q) →
    derivationOf rfl name d = match Γ, p, q, d with
    | Γ, p, q, proof => lawBody (P := P) ⟨Γ, p, q⟩ ∪ match proof with
      | .required i => {Declaration.law (name i)}
      | .cut l r | .andIntro l r | .orElim l r => derivationOf rfl name l ∪ derivationOf rfl name r
      | .rename _ child | .existsElim child => derivationOf rfl name child
      | .refl _ | .graph _ | .truth _ | .falsehood _ | .andLeft _ _ | .andRight _ _ |
          .orLeft _ _ | .orRight _ _ | .existsIntro _ _ | .eqRefl _ | .eqSubst _ _ _ => ∅
  | _, _, _, .required _ | _, _, _, .cut _ _ | _, _, _, .andIntro _ _ | _, _, _, .orElim _ _ |
    _, _, _, .rename _ _ | _, _, _, .existsElim _ | _, _, _, .refl _ | _, _, _, .graph _ |
    _, _, _, .truth _ | _, _, _, .falsehood _ | _, _, _, .andLeft _ _ | _, _, _, .andRight _ _ |
    _, _, _, .orLeft _ _ | _, _, _, .orRight _ _ | _, _, _, .existsIntro _ _ |
    _, _, _, .eqRefl _ | _, _, _, .eqSubst _ _ _ => rfl

/-- A derivation records the written support of its root sequent. -/
theorem lawBody_subset_derivationOf {I : Type u} {statement : I → Law P.signature}
    {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (name : I → P.laws.LawName) (d : Derivation (⟨P.signature, I, statement⟩ : Theory) p q) :
    lawBody (P := P) ⟨Γ, p, q⟩ ⊆ derivationOf rfl name d := by
  rw [derivationOf_support_eq]
  exact Set.subset_union_left

/-- A required leaf retains the declaration name of its premise. -/
theorem law_mem_derivationOf_required {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName) (i : T.LawName) :
    Declaration.law (name i) ∈ derivationOf same name (Derivation.required (T := T) i) :=
  Or.inr (Set.mem_singleton _)

/-- Cut retains all references from its left premise. -/
theorem derivationOf_cut_left {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ : List T.signature.SortType} {p q r : Formula T.signature Γ}
    (left : Derivation T p q) (right : Derivation T q r) :
    derivationOf same name left ⊆ derivationOf same name (Derivation.cut left right) :=
  fun _ member => Or.inr (Or.inl member)

/-- Cut retains all references from its right premise. -/
theorem derivationOf_cut_right {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ : List T.signature.SortType} {p q r : Formula T.signature Γ}
    (left : Derivation T p q) (right : Derivation T q r) :
    derivationOf same name right ⊆ derivationOf same name (Derivation.cut left right) :=
  fun _ member => Or.inr (Or.inr member)

/-- Conjunction introduction retains all references from its left premise. -/
theorem derivationOf_andIntro_left {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ : List T.signature.SortType} {p q r : Formula T.signature Γ}
    (left : Derivation T p q) (right : Derivation T p r) :
    derivationOf same name left ⊆ derivationOf same name (Derivation.andIntro left right) :=
  fun _ member => Or.inr (Or.inl member)

/-- Conjunction introduction retains all references from its right premise. -/
theorem derivationOf_andIntro_right {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ : List T.signature.SortType} {p q r : Formula T.signature Γ}
    (left : Derivation T p q) (right : Derivation T p r) :
    derivationOf same name right ⊆ derivationOf same name (Derivation.andIntro left right) :=
  fun _ member => Or.inr (Or.inr member)

/-- Disjunction elimination retains all references from its left premise. -/
theorem derivationOf_orElim_left {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ : List T.signature.SortType} {p q r q' : Formula T.signature Γ}
    (left : Derivation T (p.conj q) r) (right : Derivation T (p.conj q') r) :
    derivationOf same name left ⊆ derivationOf same name (Derivation.orElim left right) :=
  fun _ member => Or.inr (Or.inl member)

/-- Disjunction elimination retains all references from its right premise. -/
theorem derivationOf_orElim_right {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ : List T.signature.SortType} {p q r q' : Formula T.signature Γ}
    (left : Derivation T (p.conj q) r) (right : Derivation T (p.conj q') r) :
    derivationOf same name right ⊆ derivationOf same name (Derivation.orElim left right) :=
  fun _ member => Or.inr (Or.inr member)

/-- A renaming retains all references from its premise. -/
theorem derivationOf_rename {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ Δ : List T.signature.SortType} {p q : Formula T.signature Γ}
    (ρ : Renaming Γ Δ) (child : Derivation T p q) :
    derivationOf same name child ⊆ derivationOf same name (Derivation.rename ρ child) :=
  Set.subset_union_right

/-- Existential elimination retains all references from its premise. -/
theorem derivationOf_existsElim {T : Theory.{u}} (same : T.signature = P.signature)
    (name : T.LawName → P.laws.LawName)
    {Γ : List T.signature.SortType} {s : T.signature.SortType} {p : Formula T.signature (s :: Γ)}
    {c q : Formula T.signature Γ}
    (child : Derivation T ((c.rename (fun i => Var.there i)).conj p)
      (q.rename (fun i => Var.there i))) :
    derivationOf same name child ⊆ derivationOf same name
      (Derivation.existsElim (p := p) (c := c) (q := q) child) :=
  Set.subset_union_right

/-- The support of a derivation in the theory presented here. -/
abbrev derivation {Γ : List P.signature.SortType} {p q : Formula P.signature Γ}
    (proof : Derivation P.theory p q) : Set (Declaration P) :=
  derivationOf rfl Subtype.val proof

/-- Induct on derivation support through sequents, required Law leaves, and unions. -/
theorem derivation_support_induction {M : Set (Declaration P) → Prop}
    (empty : M ∅) (ofSorts : ∀ Γ, M (sorts Γ))
    (ofFormula : ∀ {Γ : List P.theory.signature.SortType} (p : Formula P.theory.signature Γ),
      M (formula p))
    (ofRequired : ∀ name : P.theory.LawName, M {Declaration.law name.val})
    (join : ∀ {A B}, M A → M B → M (A ∪ B))
    {Γ : List P.theory.signature.SortType} {p q : Formula P.theory.signature Γ}
    (proof : Derivation P.theory p q) : M (derivation proof) := by
  unfold derivation
  induction proof <;> rw [derivationOf]
  all_goals
    refine join (join (join (ofSorts _) (ofFormula _)) (ofFormula _)) ?_
    first
    | exact empty
    | exact ofRequired _
    | exact join (by assumption) (by assumption)
    | assumption

/-- The five named operations of a declared value ring. -/
def ringVocabularySupport {s : P.signature.SortType} (ring : RingVocabulary P.signature s) :
    Set (Declaration P) :=
  {ofOperation ring.zero.symbol.operation, ofOperation ring.one.symbol.operation,
    ofOperation ring.add.symbol.operation, ofOperation ring.neg.symbol.operation,
    ofOperation ring.mul.symbol.operation}

/-- A written ring contributes the declarations of its zero, unit, addition,
negation and multiplication symbols to the context support. -/
theorem ringVocabularySupport_eq {s : P.signature.SortType} (ring : RingVocabulary P.signature s) :
    ringVocabularySupport (P := P) ring =
      {ofOperation ring.zero.symbol.operation, ofOperation ring.one.symbol.operation,
        ofOperation ring.add.symbol.operation, ofOperation ring.neg.symbol.operation,
        ofOperation ring.mul.symbol.operation} :=
  rfl

/-- The declarations needed to read an ordered ring residual. -/
def ringEquationSupport (name : P.laws.LawName) : Set (Declaration P) :=
  match P.ringEquation name with
  | none => ∅
  | some equation =>
    let ring := equation.written.equation.ring
    formula equation.written.equation.left.graph ∪
      formula equation.written.equation.right.graph ∪
      ((Declaration.law '' equation.axiomNames ∪ ringVocabularySupport ring) ∪
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

/-- A sort declaration has no immediate dependencies. -/
theorem sort_dependencies (s : P.signature.SortType) : dependsOn P (.sort s) = ∅ :=
  rfl

/-- A quantity depends on its input and output sorts. -/
theorem quantity_dependencies (q : P.signature.Quantity) :
    dependsOn P (.quantity q) =
      sorts ((P.signature.quantityArity q).output :: (P.signature.quantityArity q).inputs) :=
  rfl

/-- A total operation in Definition 3.1 depends on its input and output sorts. -/
theorem total_dependencies (f : P.signature.Total) :
    dependsOn P (.total f) =
      sorts ((P.signature.totalArity f).output :: (P.signature.totalArity f).inputs) :=
  rfl

/-- A partial operation retains its arity and the data of any declared domain inclusion. -/
theorem partial_dependencies (p : P.signature.Partial) :
    dependsOn P (.partialOp p) =
      sorts ((P.signature.partialArity p).output :: (P.signature.partialArity p).inputs) ∪
        match P.domainInclusions p with
        | none => ∅
        | some data => {Declaration.sort data.domainSort} ∪
          {a | ∃ (s : P.signature.SortType) (i : Var (P.signature.partialArity p).inputs s),
            a = ofOperation (data.symbol i).operation} :=
  rfl

/-- The input and output sorts of a graph operation belong to its dependencies. -/
theorem operationSorts_subset_dependsOn (op : Operation P.signature) :
    sorts (op.arity.output :: op.arity.inputs) ⊆ dependsOn P (ofOperation op) := by
  cases op with
  | total => exact Set.Subset.rfl
  | partialOp => exact fun _ member => Or.inl member
  | quantity => exact Set.Subset.rfl

/-- A relation depends on the sorts of its input context. -/
theorem relation_dependencies (r : P.signature.Rel) :
    dependsOn P (.relation r) = sorts (P.signature.relInputs r) :=
  rfl

/-- A declared domain inclusion adds its stated sort to the operation's dependencies. -/
theorem partial_domainSort_mem_dependsOn {p : P.signature.Partial} (data : DomainInclusions p)
    (attached : P.domainInclusions p = some data) :
    Declaration.sort data.domainSort ∈ dependsOn P (.partialOp p) := by
  rw [partial_dependencies, attached]
  exact Or.inr (Or.inl (Set.mem_singleton _))

/-- A declared domain inclusion adds every named coordinate to the operation's dependencies. -/
theorem partial_domainSymbol_mem_dependsOn {p : P.signature.Partial} (data : DomainInclusions p)
    (attached : P.domainInclusions p = some data) {s : P.signature.SortType}
    (i : Var (P.signature.partialArity p).inputs s) :
    ofOperation (data.symbol i).operation ∈ dependsOn P (.partialOp p) := by
  rw [partial_dependencies, attached]
  exact Or.inr (Or.inr ⟨s, i, rfl⟩)

/-- A derived Law retains its written support and the references from its proof tree. -/
theorem derived_dependencies (name : P.laws.LawName) (role : P.laws.role name = .derived) :
    dependsOn P (.law name) = lawBody (P.laws.statement name) ∪ derivation (P.derived name role) := by
  rw [dependsOn]
  split
  · rfl
  · rename_i otherRole
    cases role.symm.trans otherRole
  · rename_i otherRole
    cases role.symm.trans otherRole

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

/-- The declared operations of an attached residual ring are part of its support. -/
theorem ringVocabulary_subset_ringEquationSupport {name : P.laws.LawName}
    {equation : NamedRingEquation P.laws name} (attached : P.ringEquation name = some equation) :
    ringVocabularySupport (P := P) equation.written.equation.ring ⊆ ringEquationSupport (P := P) name := by
  intro d keeps
  simp only [ringEquationSupport, attached]
  exact Or.inr (Or.inl (Or.inr keeps))

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
