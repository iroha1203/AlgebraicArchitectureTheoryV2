import Formal.SHIGURE.Part1.DeclarationContexts
import Formal.SHIGURE.Part1.Interpretation

/-! # Names and syntax of a selected presentation

A selection preserves the arities, literal Law syntax and declaration roles.
Its structures can be given directly or obtained from ambient structures.
-/

universe u

namespace SHIGURE

/-- A change of names that preserves every input position and result sort. -/
structure SignatureNames (S T : Signature.{u}) where
  onSort : S.SortType → T.SortType
  onTotal : S.Total → T.Total
  onRel : S.Rel → T.Rel
  onPartial : S.Partial → T.Partial
  onQuantity : S.Quantity → T.Quantity
  totalArity (f : S.Total) :
    ⟨(S.totalArity f).inputs.map onSort, onSort (S.totalArity f).output⟩ = T.totalArity (onTotal f)
  relInputs (r : S.Rel) : (S.relInputs r).map onSort = T.relInputs (onRel r)
  partialArity (p : S.Partial) :
    ⟨(S.partialArity p).inputs.map onSort, onSort (S.partialArity p).output⟩ = T.partialArity (onPartial p)
  quantityArity (q : S.Quantity) :
    ⟨(S.quantityArity q).inputs.map onSort, onSort (S.quantityArity q).output⟩ = T.quantityArity (onQuantity q)

namespace SignatureNames

variable {S T : Signature.{u}}

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

/-- The typed presentation selected from a dependency-closed ambient context. -/
structure ReadingOrigin (selected ambient : PrimitivePresentation.{u})
    (retained : DeclarationContext ambient) where
  /-- Sort and primitive names preserve their kinds and exact typed arities. -/
  signature : SignatureNames selected.signature ambient.signature
  /-- The ambient names of the selected Laws. -/
  lawName : selected.laws.LawName → ambient.laws.LawName
  /-- The typed naming maps identify exactly the retained declarations. -/
  names : Declaration selected ≃ retained.declarations
  names_eq (d : Declaration selected) : (names d).val = d.renameNames signature lawName
  /-- Restriction retains each Law's literal syntax and its role. -/
  law_eq (i : selected.laws.LawName) :
    signature.law (selected.laws.statement i) = ambient.laws.statement (lawName i)
  law_role (i : selected.laws.LawName) : selected.laws.role i = ambient.laws.role (lawName i)
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
