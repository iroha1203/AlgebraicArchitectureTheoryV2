import Formal.SHIGURE.Part1.DeclarationContexts
import Formal.SHIGURE.Part1.Interpretation

/-! # Names and syntax of a selected presentation

A selection preserves the arities, literal Law syntax and declaration roles.
Its structures can be given directly or obtained from ambient structures.

## Implementation notes

Typed names preserve the presentation independently of the concrete choice
of subtype indices. A selection certifies a given presentation here. A
canonical subtype presentation can supply the same certificate when built.
Each selected Law is compared with its renamed ambient Law and recorded
attachments. The proof record retains each sequent, rule, and ordered
premises, including the variable map of a renaming rule. A set of referenced
names alone cannot distinguish proofs or ordered equations with the same support.
-/

universe u v

namespace SHIGURE

/-- A change of names that preserves every input position and result sort. -/
structure SignatureNames (S T : Signature.{u}) where
  /-- The ambient name of a sort. -/
  onSort : S.SortType → T.SortType
  /-- The ambient name of a total operation. -/
  onTotal : S.Total → T.Total
  /-- The ambient name of a relation. -/
  onRel : S.Rel → T.Rel
  /-- The ambient name of a partial operation. -/
  onPartial : S.Partial → T.Partial
  /-- The ambient name of a quantity. -/
  onQuantity : S.Quantity → T.Quantity
  /-- Total operation argument and result sorts are retained. -/
  totalArity (f : S.Total) :
    ⟨(S.totalArity f).inputs.map onSort, onSort (S.totalArity f).output⟩ = T.totalArity (onTotal f)
  /-- Relation argument sorts are retained in order. -/
  relInputs (r : S.Rel) : (S.relInputs r).map onSort = T.relInputs (onRel r)
  /-- Partial operation argument and result sorts are retained. -/
  partialArity (p : S.Partial) :
    ⟨(S.partialArity p).inputs.map onSort, onSort (S.partialArity p).output⟩ = T.partialArity (onPartial p)
  /-- Quantity argument and result sorts are retained. -/
  quantityArity (q : S.Quantity) :
    ⟨(S.quantityArity q).inputs.map onSort, onSort (S.quantityArity q).output⟩ = T.quantityArity (onQuantity q)

namespace SignatureNames

variable {S T : Signature.{u}}

/-- Keep every sort and symbol name. -/
def identity (S : Signature.{u}) : SignatureNames S S where
  onSort := id
  onTotal := id
  onRel := id
  onPartial := id
  onQuantity := id
  totalArity f := by
    change ⟨(S.totalArity f).inputs.map id, (S.totalArity f).output⟩ = S.totalArity f
    rw [List.map_id]
  relInputs r := List.map_id _
  partialArity p := by
    change ⟨(S.partialArity p).inputs.map id, (S.partialArity p).output⟩ = S.partialArity p
    rw [List.map_id]
  quantityArity q := by
    change ⟨(S.quantityArity q).inputs.map id, (S.quantityArity q).output⟩ = S.quantityArity q
    rw [List.map_id]

/-- Map a tagged operation to the same kind of operation in the other signature. -/
def operation (names : SignatureNames S T) : Operation S → Operation T
  | .total f => .total (names.onTotal f)
  | .partialOp p => .partialOp (names.onPartial p)
  | .quantity q => .quantity (names.onQuantity q)

/-- Renaming preserves the input and output sorts of each tagged operation. -/
private theorem operationArity (names : SignatureNames S T) (op : Operation S) :
    ⟨op.arity.inputs.map names.onSort, names.onSort op.arity.output⟩ = (names.operation op).arity := by
  cases op with
  | total f => exact names.totalArity f
  | partialOp p => exact names.partialArity p
  | quantity q => exact names.quantityArity q

/-- Rename the variables and symbols of one typed atom. -/
private def atomic (names : SignatureNames S T) {Γ : List S.SortType} :
    Atomic S Γ → Atomic T (Γ.map names.onSort)
  | .eq x y => .eq (x.mapSorts names.onSort) (y.mapSorts names.onSort)
  | .rel r args => .rel (names.onRel r) (names.relInputs r ▸ args.mapSorts names.onSort)
  | .domain p args =>
    .domain (names.onPartial p) (congrArg Arity.inputs (names.partialArity p) ▸ args.mapSorts names.onSort)
  | .graph op args y => .graph (names.operation op)
      (congrArg Arity.inputs (names.operationArity op) ▸ args.mapSorts names.onSort)
      (congrArg Arity.output (names.operationArity op) ▸ y.mapSorts names.onSort)

/-- Renaming an equality atom sends both variable positions along the sort map. -/
private theorem atomic_eq (names : SignatureNames S T) {Γ : List S.SortType}
    {s : S.SortType} (x y : Var Γ s) :
    names.atomic (.eq x y) = .eq (x.mapSorts names.onSort) (y.mapSorts names.onSort) :=
  rfl

/-- Renaming a relation atom transports its selected input positions along the declared arity. -/
private theorem atomic_rel (names : SignatureNames S T) {Γ : List S.SortType}
    (r : S.Rel) (args : Renaming (S.relInputs r) Γ) :
    names.atomic (.rel r args) = .rel (names.onRel r) (names.relInputs r ▸ args.mapSorts names.onSort) :=
  rfl

/-- Renaming a domain atom transports its selected input positions along the declared arity. -/
private theorem atomic_domain (names : SignatureNames S T) {Γ : List S.SortType}
    (p : S.Partial) (args : Renaming (S.partialArity p).inputs Γ) :
    names.atomic (.domain p args) =
      .domain (names.onPartial p) (congrArg Arity.inputs (names.partialArity p) ▸ args.mapSorts names.onSort) :=
  rfl

/-- Renaming a graph atom transports both the selected inputs and the output position. -/
private theorem atomic_graph (names : SignatureNames S T) {Γ : List S.SortType}
    (op : Operation S) (args : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    names.atomic (.graph op args y) =
      .graph (names.operation op)
        (congrArg Arity.inputs (names.operationArity op) ▸ args.mapSorts names.onSort)
        (congrArg Arity.output (names.operationArity op) ▸ y.mapSorts names.onSort) :=
  rfl

/-- Rename the literal positive syntax. Each atom retains its kind. -/
def formula (names : SignatureNames S T) :
    {Γ : List S.SortType} → Formula S Γ → Formula T (Γ.map names.onSort)
  | _, .atom a => .atom (names.atomic a)
  | _, .truth => .truth
  | _, .falsehood => .falsehood
  | _, .conj p q => .conj (names.formula p) (names.formula q)
  | _, .disj p q => .disj (names.formula p) (names.formula q)
  | _, .ex p => .ex (names.formula p)

/-- Rename the context, antecedent and conclusion of a written Law. -/
def law (names : SignatureNames S T) (ℓ : Law S) : Law T :=
  ⟨ℓ.context.map names.onSort, names.formula ℓ.input, names.formula ℓ.conclusion⟩

/-- Rename a term through its exact typed primitive operations. -/
def term (names : SignatureNames S T) :
    {Γ : List S.SortType} → {s : S.SortType} → Term S Γ s → Term T (Γ.map names.onSort) (names.onSort s)
  | _, _, .var i => .var (i.mapSorts names.onSort)
  | Γ, _, .app op args =>
    let renameArgs : ∀ {s}, Var (op.arity.inputs.map names.onSort) s → Term T (Γ.map names.onSort) s :=
      Var.reindex names.onSort (fun i => names.term (args i))
    let sorts := congrArg Arity.inputs (names.operationArity op)
    cast (congrArg (Term T (Γ.map names.onSort)) (congrArg Arity.output (names.operationArity op)).symm)
      (.app (names.operation op) (fun {s} i => renameArgs (cast (congrArg (fun ctx => Var ctx s) sorts.symm) i)))
  | _, _, .letBind x y => .letBind (names.term x) (names.term y)

/-- Rename both members of an ordered equation and its input condition. -/
def equation (names : SignatureNames S T) (eqn : OrderedEquation S) : OrderedEquation T where
  context := eqn.context.map names.onSort
  result := names.onSort eqn.result
  input := names.formula eqn.input
  left := names.term eqn.left
  right := names.term eqn.right

/-- Rename the declared graph axiom and preserve the rule it states. -/
def graphAxiom (names : SignatureNames S T) : GraphAxiom S → GraphAxiom T
  | .functional op => .functional (names.operation op)
  | .totality f => .totality (names.onTotal f)
  | .quantityTotality q => .quantityTotality (names.onQuantity q)
  | .graphImpliesDomain p => .graphImpliesDomain (names.onPartial p)
  | .domainImpliesGraph p => .domainImpliesGraph (names.onPartial p)


/-- Read a renamed assignment in the required target context. -/
private def arguments (names : SignatureNames S T) {X : T.SortType → Type u}
    {Γ : List S.SortType} {Δ : List T.SortType} (same : Γ.map names.onSort = Δ)
    (e : Assignment (X ∘ names.onSort) Γ) : Assignment X Δ :=
  same ▸ e.mapSorts names.onSort

/-- Restrict an interpreted structure to the typed names in the selection. -/
def restrict (names : SignatureNames S T) (A : Structure T) : Structure S where
  carrier := A.carrier ∘ names.onSort
  total f xs := cast (congrArg (fun arity => A.carrier arity.output) (names.totalArity f).symm)
    (A.total (names.onTotal f) (names.arguments (congrArg Arity.inputs (names.totalArity f)) xs))
  relation r := {xs | names.arguments (names.relInputs r) xs ∈ A.relation (names.onRel r)}
  partialDomain p := {xs |
    names.arguments (congrArg Arity.inputs (names.partialArity p)) xs ∈ A.partialDomain (names.onPartial p)}
  partialValue p xs := cast (congrArg (fun arity => A.carrier arity.output) (names.partialArity p).symm)
    (A.partialValue (names.onPartial p)
      ⟨names.arguments (congrArg Arity.inputs (names.partialArity p)) xs.val, xs.property⟩)
  quantity q xs := cast (congrArg (fun arity => A.carrier arity.output) (names.quantityArity q).symm)
    (A.quantity (names.onQuantity q) (names.arguments (congrArg Arity.inputs (names.quantityArity q)) xs))

/-- Relation membership in the reduct tests the transported tuple in the ambient relation. -/
private theorem restrict_relation_iff (names : SignatureNames S T) (A : Structure T)
    (r : S.Rel) (xs : Assignment (names.restrict A).carrier (S.relInputs r)) :
    xs ∈ (names.restrict A).relation r ↔
      names.arguments (names.relInputs r) xs ∈ A.relation (names.onRel r) :=
  Iff.rfl

/-- Partial domain membership in the reduct tests the transported tuple in the ambient domain. -/
private theorem restrict_partialDomain_iff (names : SignatureNames S T) (A : Structure T)
    (p : S.Partial) (xs : Assignment (names.restrict A).carrier (S.partialArity p).inputs) :
    xs ∈ (names.restrict A).partialDomain p ↔
      names.arguments (congrArg Arity.inputs (names.partialArity p)) xs ∈ A.partialDomain (names.onPartial p) :=
  Iff.rfl

/-- The total interpretation in a named reduct uses the ambient function on the transported tuple. -/
theorem restrict_total_apply (names : SignatureNames S T) (A : Structure T) (f : S.Total)
    (xs : Assignment (names.restrict A).carrier (S.totalArity f).inputs) :
    (names.restrict A).total f xs =
      cast (congrArg (fun arity => A.carrier arity.output) (names.totalArity f).symm)
        (A.total (names.onTotal f)
          (congrArg Arity.inputs (names.totalArity f) ▸ xs.mapSorts names.onSort)) :=
  rfl

/-- Relation membership in a named reduct uses the ambient relation on the mapped tuple. -/
theorem restrict_relation_mem_iff (names : SignatureNames S T) (A : Structure T) (r : S.Rel)
    (xs : Assignment (names.restrict A).carrier (S.relInputs r)) :
    xs ∈ (names.restrict A).relation r ↔
      (names.relInputs r ▸ xs.mapSorts names.onSort) ∈ A.relation (names.onRel r) :=
  names.restrict_relation_iff A r xs

/-- Domain membership in a named reduct uses the ambient domain on the mapped tuple. -/
theorem restrict_partialDomain_mem_iff (names : SignatureNames S T) (A : Structure T) (p : S.Partial)
    (xs : Assignment (names.restrict A).carrier (S.partialArity p).inputs) :
    xs ∈ (names.restrict A).partialDomain p ↔
      (congrArg Arity.inputs (names.partialArity p) ▸ xs.mapSorts names.onSort) ∈
        A.partialDomain (names.onPartial p) :=
  names.restrict_partialDomain_iff A p xs

/-- The partial value in a named reduct is transported back from the ambient operation on its domain. -/
theorem restrict_partialValue_apply (names : SignatureNames S T) (A : Structure T) (p : S.Partial)
    (xs : (names.restrict A).partialDomain p) :
    (names.restrict A).partialValue p xs =
      cast (congrArg (fun arity => A.carrier arity.output) (names.partialArity p).symm)
        (A.partialValue (names.onPartial p)
          ⟨congrArg Arity.inputs (names.partialArity p) ▸ xs.val.mapSorts names.onSort,
            (names.restrict_partialDomain_mem_iff A p xs.val).1 xs.property⟩) :=
  rfl

/-- A quantity in a named reduct uses the ambient quantity on the transported tuple. -/
theorem restrict_quantity_apply (names : SignatureNames S T) (A : Structure T) (q : S.Quantity)
    (xs : Assignment (names.restrict A).carrier (S.quantityArity q).inputs) :
    (names.restrict A).quantity q xs =
      cast (congrArg (fun arity => A.carrier arity.output) (names.quantityArity q).symm)
        (A.quantity (names.onQuantity q)
          (congrArg Arity.inputs (names.quantityArity q) ▸ xs.mapSorts names.onSort)) :=
  rfl

/-- A retyped assignment can be read at its original positions without losing any coordinates. -/
private theorem arguments_surjective (names : SignatureNames S T) {X : T.SortType → Type u}
    {Γ : List S.SortType} :
    Function.Surjective (names.arguments (X := X) (Γ := Γ) rfl) := by
  intro e
  use ⟨fun i => e (i.mapSorts names.onSort)⟩
  apply Assignment.ext_mapSorts names.onSort
  intro s i
  exact Assignment.mapSorts_apply names.onSort ⟨fun j => e (j.mapSorts names.onSort)⟩ i

/-- Selecting positions in the mapped context gives the mapped subtuple. -/
private theorem arguments_pull (names : SignatureNames S T) {X : T.SortType → Type u}
    {Γ Λ : List S.SortType} {Δ : List T.SortType} (same : Λ.map names.onSort = Δ)
    (e : Assignment (X ∘ names.onSort) Γ) (ρ : Renaming Λ Γ) :
    (e.mapSorts names.onSort).pull (same ▸ ρ.mapSorts names.onSort) = names.arguments same (e.pull ρ) := by
  cases same
  exact Assignment.mapSorts_pull names.onSort e ρ

/-- A transported position selects the transported value. -/
private theorem arguments_read (names : SignatureNames S T) {X : T.SortType → Type u}
    {Γ : List S.SortType} {s : S.SortType} {t : T.SortType}
    (same : names.onSort s = t) (e : Assignment (X ∘ names.onSort) Γ) (i : Var Γ s) :
    (e.mapSorts names.onSort) (same ▸ i.mapSorts names.onSort) = cast (congrArg X same) (e i) := by
  cases same
  exact Assignment.mapSorts_apply names.onSort e i

/-- The equality of an operation's values is independent of the direction of transport. -/
private theorem cast_output_eq {X : T.SortType → Type u} {s t : T.SortType} (same : s = t)
    (x : X t) (y : X s) :
    cast (congrArg X same.symm) x = y ↔ x = cast (congrArg X same) y := by
  cases same
  rfl

/-- A primitive graph in a reduct is the ambient graph on the retyped tuple and value. -/
private theorem restrict_graph_iff (names : SignatureNames S T) (A : Structure T)
    (op : Operation S) (xs : Assignment (names.restrict A).carrier op.arity.inputs)
    (y : (names.restrict A).carrier op.arity.output) :
    (names.restrict A).Graph op xs y ↔ A.Graph (names.operation op)
      (names.arguments (congrArg Arity.inputs (names.operationArity op)) xs)
      (cast (congrArg (fun s => A.carrier s) (congrArg Arity.output (names.operationArity op))) y) := by
  cases op with
  | total f =>
    rw [Structure.graph_total_iff]
    exact (cast_output_eq (congrArg Arity.output (names.totalArity f)) _ _).trans
      (A.graph_total_iff _ _ _).symm
  | partialOp p =>
    rw [Structure.graph_partial_iff]
    refine (exists_congr fun hx => ?_).trans (A.graph_partial_iff _ _ _).symm
    exact cast_output_eq (congrArg Arity.output (names.partialArity p)) _ _
  | quantity q =>
    rw [Structure.graph_quantity_iff]
    exact (cast_output_eq (congrArg Arity.output (names.quantityArity q)) _ _).trans
      (A.graph_quantity_iff _ _ _).symm

/-- Atomic satisfaction in the reduct agrees with the renamed atom in the ambient structure. -/
private theorem restrict_atomic_iff (names : SignatureNames S T) (A : Structure T)
    {Γ : List S.SortType} (a : Atomic S Γ) (e : Assignment (names.restrict A).carrier Γ) :
    a.Holds (names.restrict A) e ↔ (names.atomic a).Holds A (e.mapSorts names.onSort) := by
  cases a with
  | eq x y =>
    simp only [names.atomic_eq, Atomic.holds_eq, Assignment.mapSorts_apply]
  | rel r ρ =>
    simp only [names.atomic_rel, Atomic.holds_rel, names.restrict_relation_iff, names.arguments_pull]
  | domain p ρ =>
    simp only [names.atomic_domain, Atomic.holds_domain, names.restrict_partialDomain_iff, names.arguments_pull]
  | graph op ρ y =>
    simp only [names.atomic_graph, Atomic.holds_graph, names.restrict_graph_iff,
      names.arguments_pull, names.arguments_read]

/-- A positive formula is satisfied in a reduct exactly when its renamed formula holds
at the corresponding assignment in the ambient structure. -/
theorem restrict_formula_iff (names : SignatureNames S T) (A : Structure T)
    {Γ : List S.SortType} (p : Formula S Γ) :
    ∀ e : Assignment (names.restrict A).carrier Γ,
      p.Holds (names.restrict A) e ↔ (names.formula p).Holds A (e.mapSorts names.onSort) := by
  induction p with
  | atom a => exact names.restrict_atomic_iff A a
  | truth => intro; rfl
  | falsehood => intro; rfl
  | conj p q hp hq =>
    intro e
    exact (Formula.holds_conj _ _ _ _).trans
      ((and_congr (hp e) (hq e)).trans (Formula.holds_conj _ _ _ _).symm)
  | disj p q hp hq =>
    intro e
    exact (Formula.holds_disj _ _ _ _).trans
      ((or_congr (hp e) (hq e)).trans (Formula.holds_disj _ _ _ _).symm)
  | ex p ih =>
    intro e
    refine (Formula.holds_ex _ _ _).trans ((exists_congr fun x => ?_).trans
      (Formula.holds_ex (names.formula p) A (e.mapSorts names.onSort)).symm)
    simpa only [Assignment.mapSorts_cons] using ih (Assignment.cons x e)

/-- An original Law holds in a reduct exactly when the renamed Law holds in the ambient structure. -/
theorem restrict_law_iff (names : SignatureNames S T) (A : Structure T) (ℓ : Law S) :
    ℓ.Holds (names.restrict A) ↔ (names.law ℓ).Holds A := by
  constructor
  · intro holds e input
    obtain ⟨original, rfl⟩ := names.arguments_surjective e
    exact (names.restrict_formula_iff A ℓ.conclusion original).1
      (holds original ((names.restrict_formula_iff A ℓ.input original).2 input))
  · intro holds e input
    exact (names.restrict_formula_iff A ℓ.conclusion e).2
      (holds (e.mapSorts names.onSort) ((names.restrict_formula_iff A ℓ.input e).1 input))

end SignatureNames

/-- Map a declaration along typed symbol names and Law names. -/
def Declaration.renameNames {P Q : PrimitivePresentation.{u}}
    (names : SignatureNames P.signature Q.signature) (laws : P.laws.LawName → Q.laws.LawName) :
    Declaration P → Declaration Q
  | .sort s => .sort (names.onSort s)
  | .total f => .total (names.onTotal f)
  | .relation r => .relation (names.onRel r)
  | .partialOp p => .partialOp (names.onPartial p)
  | .quantity q => .quantity (names.onQuantity q)
  | .law i => .law (laws i)

/-- A proof rule with its named symbol or variable-position data. -/
inductive ProofRuleData (S : Signature.{u}) (LawName : Type v) where
  | refl | cut
  | required (name : LawName)
  | graph (rule : GraphAxiom S)
  | rename (positions : List Nat)
  | truth | falsehood | andLeft | andRight | andIntro | orLeft | orRight | orElim
  | existsIntro (position : Nat)
  | existsElim | eqRefl
  | eqSubst (pattern : Law S) (left right : Nat)

/-- An ordered proof tree whose nodes carry their sequents and exact rules. -/
inductive RecordedDerivation (S : Signature.{u}) (LawName : Type v) where
  | node (statement : Law S) (rule : ProofRuleData S LawName)
      (premises : List (RecordedDerivation S LawName))

namespace Derivation
variable {T : Theory.{u}} {S : Signature.{u}} {L : Type v}

/-- Record the target position of each variable in the source context's order. -/
private def renamingPositions {Δ : List T.signature.SortType} :
    {Γ : List T.signature.SortType} → Renaming Γ Δ → List Nat
  | [], _ => []
  | _ :: _, ρ => (ρ .here).position :: renamingPositions (fun i => ρ (.there i))

/-- Record a derivation under typed symbol names and a map of required Law names. -/
def record (names : SignatureNames T.signature S) (lawName : T.LawName → L) :
    {Γ : List T.signature.SortType} → {p q : Formula T.signature Γ} →
    Derivation T p q → RecordedDerivation S L
  | Γ, p, q, proof =>
    let statement : Law S := ⟨Γ.map names.onSort, names.formula p, names.formula q⟩
    match proof with
    | .refl _ => .node statement .refl []
    | .cut l r => .node statement .cut [record names lawName l, record names lawName r]
    | .required i => .node statement (.required (lawName i)) []
    | .graph rule => .node statement (.graph (names.graphAxiom rule)) []
    | .rename ρ prior => .node statement (.rename (renamingPositions (T := T) ρ)) [record names lawName prior]
    | .truth _ => .node statement .truth []
    | .falsehood _ => .node statement .falsehood []
    | .andLeft _ _ => .node statement .andLeft []
    | .andRight _ _ => .node statement .andRight []
    | .andIntro l r => .node statement .andIntro [record names lawName l, record names lawName r]
    | .orLeft _ _ => .node statement .orLeft []
    | .orRight _ _ => .node statement .orRight []
    | .orElim l r => .node statement .orElim [record names lawName l, record names lawName r]
    | .existsIntro _ i => .node statement (.existsIntro i.position) []
    | .existsElim prior => .node statement .existsElim [record names lawName prior]
    | .eqRefl _ => .node statement .eqRefl []
    | @Derivation.eqSubst _ Γ s body x y =>
      .node statement (.eqSubst ⟨(s :: Γ).map names.onSort, .truth, names.formula body⟩ x.position y.position) []

end Derivation

/-- The primitive ring operations and named proof data at an ordered equality. -/
structure RingLawRecord (S : Signature.{u}) (L : Type u) where
  operations : List (Operation S)
  lawNames : Set L
  proofs : RingVocabulary.LawName → RecordedDerivation S L

/-- The ordered equality and proof data attached to a literal Law. -/
structure LawAttachments (S : Signature.{u}) (L : Type u) where
  equation : Option (OrderedEquation S)
  ring : Option (RingLawRecord S L)
  proof : Option (RecordedDerivation S L)

namespace PrimitivePresentation

variable {P : PrimitivePresentation.{u}} {S : Signature.{u}} {L : Type u}

/-- Read a named Law’s attachments under a map of names. -/
def lawAttachments (P : PrimitivePresentation.{u}) (signature : SignatureNames P.signature S)
    (lawName : P.laws.LawName → L) (name : P.laws.LawName) : LawAttachments S L where
  equation := (P.orderedEquation name).map (fun eqn => signature.equation eqn.written.equation)
  ring := (P.ringEquation name).map (fun eqn =>
    let ring := eqn.written.equation.ring
    ⟨[ring.zero.symbol.operation, ring.one.symbol.operation, ring.add.symbol.operation,
      ring.neg.symbol.operation, ring.mul.symbol.operation].map signature.operation,
      lawName '' eqn.axiomNames, fun law => Derivation.record (T := P.laws.select eqn.axiomNames) signature (fun n => lawName n.val)
        (eqn.axioms_derive law)⟩)
  proof := match h : P.laws.role name with
    | .derived => some (Derivation.record (T := P.theory) signature (fun n => lawName n.val) (P.derived name h))
    | .required | .additional => none

/-- Record inclusion operations in the order of the partial operation's inputs. -/
private def inclusionOperations (names : SignatureNames P.signature S) :
    {Γ : List P.signature.SortType} →
    (∀ {s}, Var Γ s → TotalSymbol P.signature) → List (Operation S)
  | [], _ => []
  | _ :: _, symbols =>
    names.operation (symbols .here).operation :: inclusionOperations names (fun i => symbols (.there i))

/-- Read the inclusion sort and its symbols in the order of the partial operation inputs. -/
def domainAttachment (P : PrimitivePresentation.{u}) (signature : SignatureNames P.signature S)
    (name : P.signature.Partial) : Option (S.SortType × List (Operation S)) :=
  (P.domainInclusions name).map (fun d =>
    (signature.onSort d.domainSort, inclusionOperations signature d.symbol))

end PrimitivePresentation

/-- The typed presentation selected from a dependency-closed ambient context. -/
structure ReadingOrigin (selected ambient : PrimitivePresentation.{u})
    (retained : DeclarationContext ambient) where
  /-- Sort and primitive names preserve their kinds and exact typed arities. -/
  signature : SignatureNames selected.signature ambient.signature
  /-- The ambient names of the selected Laws. -/
  lawName : selected.laws.LawName → ambient.laws.LawName
  /-- The typed naming maps identify exactly the retained declarations. -/
  names : Declaration selected ≃ retained.declarations
  /-- The equivalence uses the specified typed symbol and Law names. -/
  names_eq (d : Declaration selected) : (names d).val = d.renameNames signature lawName
  /-- Restriction retains each Law's literal syntax and its role. -/
  law_eq (i : selected.laws.LawName) :
    signature.law (selected.laws.statement i) = ambient.laws.statement (lawName i)
  /-- The selected Law has the same role. -/
  law_role (i : selected.laws.LawName) : selected.laws.role i = ambient.laws.role (lawName i)
  /-- Ordered terms, ring provenance and the actual derivation tree are retained. -/
  lawAttachments_eq (i : selected.laws.LawName) :
    selected.lawAttachments signature lawName i =
      ambient.lawAttachments (SignatureNames.identity _) id (lawName i)
  /-- Retain each inclusion-domain declaration with its ordered inclusion symbols. -/
  domainAttachment_eq (p : selected.signature.Partial) :
    selected.domainAttachment signature p = ambient.domainAttachment (SignatureNames.identity _) (signature.onPartial p)
  /-- Each retained declaration uses the same named dependencies. -/
  dependencies (a b : Declaration selected) :
    b ∈ Declaration.dependsOn selected a ↔ (names b).val ∈ Declaration.dependsOn ambient (names a).val

namespace ReadingOrigin

variable {P Q : PrimitivePresentation.{u}} {U : DeclarationContext Q}

/-- On the selected presentation, its entire declared language is available. -/
def whole (P : PrimitivePresentation.{u}) : DeclarationContext P :=
  ⟨Set.univ, fun _ _ _ => Set.mem_univ _⟩

/-- Read an ambient piece using the same names in the selected presentation. -/
def piece (origin : ReadingOrigin P Q U) (V : DeclarationContext Q) : DeclarationContext P where
  declarations := {d | (origin.names d).val ∈ V.declarations}
  closed ha b hb := V.closed ha ((origin.dependencies _ b).1 hb)

/-- Select the actual retained declarations of every ambient cover piece. -/
def cover (origin : ReadingOrigin P Q U) (cover : DeclarationCover U) : DeclarationCover (whole P) where
  Index := cover.Index
  piece i := origin.piece (cover.piece i)
  subset _ _ _ := Set.mem_univ _
  covers {a} _ := cover.covers (origin.names a).property

end ReadingOrigin

end SHIGURE
