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

private theorem operationArity (names : SignatureNames S T) (op : Operation S) :
    ⟨op.arity.inputs.map names.onSort, names.onSort op.arity.output⟩ = (names.operation op).arity := by
  cases op with
  | total f => exact names.totalArity f
  | partialOp p => exact names.partialArity p
  | quantity q => exact names.quantityArity q

private def atomic (names : SignatureNames S T) {Γ : List S.SortType} :
    Atomic S Γ → Atomic T (Γ.map names.onSort)
  | .eq x y => .eq (x.mapSorts names.onSort) (y.mapSorts names.onSort)
  | .rel r args => .rel (names.onRel r) (names.relInputs r ▸ args.mapSorts names.onSort)
  | .domain p args =>
    .domain (names.onPartial p) (congrArg Arity.inputs (names.partialArity p) ▸ args.mapSorts names.onSort)
  | .graph op args y => .graph (names.operation op)
      (congrArg Arity.inputs (names.operationArity op) ▸ args.mapSorts names.onSort)
      (congrArg Arity.output (names.operationArity op) ▸ y.mapSorts names.onSort)

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


private def arguments (names : SignatureNames S T) {X : T.SortType → Type u}
    {Γ : List S.SortType} {Δ : List T.SortType} (same : Γ.map names.onSort = Δ)
    (e : Assignment (X ∘ names.onSort) Γ) : Assignment X Δ :=
  same ▸ ⟨Var.reindex names.onSort (fun i => e i)⟩

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
