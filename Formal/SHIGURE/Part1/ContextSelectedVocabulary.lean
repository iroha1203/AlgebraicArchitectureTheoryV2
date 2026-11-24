import Formal.SHIGURE.Part1.ContextEvaluation
import Formal.SHIGURE.Part1.SelectedPresentation

/-! # The actual selected vocabulary

The signature of a restriction has a subtype for each kind of retained
name. Its typed input lists are reindexed without changing variable
positions. The inclusion records the exact original names and arities.
-/

universe u

namespace SHIGURE
namespace DeclarationContext
namespace Selected

variable {P : PrimitivePresentation.{u}} (U : DeclarationContext P)

/-- Only retained sort names occur in the selected signature. -/
abbrev SortName := {s : P.signature.SortType // Declaration.sort s ∈ U.declarations}

/-- Only retained total operation names occur in the selected signature. -/
abbrev Total := {f : P.signature.Total // Declaration.total f ∈ U.declarations}

/-- Only retained relation names occur in the selected signature. -/
abbrev Rel := {r : P.signature.Rel // Declaration.relation r ∈ U.declarations}

/-- Only retained partial operations, including their domain and graph, are available. -/
abbrev Partial := {p : P.signature.Partial // Declaration.partialOp p ∈ U.declarations}

/-- Only retained quantity names occur in the selected signature. -/
abbrev Quantity := {q : P.signature.Quantity // Declaration.quantity q ∈ U.declarations}

variable {U}

/-- Select a list of retained sort names in exactly its original order. -/
def context : (Γ : List P.signature.SortType) → Declaration.sorts Γ ⊆ U.declarations → List (SortName U)
  | [], _ => []
  | s :: Γ, kept => ⟨s, kept ⟨s, List.mem_cons_self, rfl⟩⟩ ::
    context Γ ((tailSortsSubset s Γ).trans kept)

/-- Forgetting the retention proofs recovers the original input list. -/
@[simp] theorem map_context (Γ : List P.signature.SortType) (kept : Declaration.sorts Γ ⊆ U.declarations) :
    (context Γ kept).map Subtype.val = Γ := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih => exact congrArg (s :: ·) (ih _)

/-- Restrict an operation arity by selecting each of its retained sorts. -/
def arity (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) : Arity (SortName U) :=
  ⟨context op.arity.inputs (operationInputs op kept), ⟨op.arity.output, operationOutput op kept⟩⟩

/-- The actual signature of the restricted presentation has precisely the retained names. -/
def signature (U : DeclarationContext P) : Signature.{u} where
  SortType := SortName U
  Total := Total U
  totalArity f := arity (.total f.val) f.property
  Rel := Rel U
  relInputs r := context (P.signature.relInputs r.val) (relationInputs r.val r.property)
  Partial := Partial U
  partialArity p := arity (.partialOp p.val) p.property
  Quantity := Quantity U
  quantityArity q := arity (.quantity q.val) q.property

/-- Erasing the retention proofs recovers the original operation arity. -/
theorem map_arity (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    (⟨(arity op kept).inputs.map Subtype.val, (arity op kept).output.val⟩ : Arity P.signature.SortType) =
      op.arity :=
  congrArg (fun (c : List P.signature.SortType) => (⟨c, op.arity.output⟩ : Arity P.signature.SortType))
    (map_context op.arity.inputs (operationInputs op kept))

/-- The selected signature has an arity-preserving inclusion into the ambient signature. -/
def names (U : DeclarationContext P) : SignatureNames (signature U) P.signature where
  onSort := Subtype.val
  onTotal := Subtype.val
  onRel := Subtype.val
  onPartial := Subtype.val
  onQuantity := Subtype.val
  totalArity f := map_arity (.total f.val) f.property
  relInputs _ := map_context _ _
  partialArity p := map_arity (.partialOp p.val) p.property
  quantityArity q := map_arity (.quantity q.val) q.property

/-- Select an operation without changing whether it is total, partial, or a quantity. -/
def operation : (op : Operation P.signature) → Declaration.ofOperation op ∈ U.declarations → Operation (signature U)
  | .total f, kept => .total ⟨f, kept⟩
  | .partialOp p, kept => .partialOp ⟨p, kept⟩
  | .quantity q, kept => .quantity ⟨q, kept⟩

/-- The selected operation has exactly the corresponding selected arity. -/
theorem operation_arity (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    (operation op kept).arity = arity op kept := by
  cases op <;> rfl

/-- Inclusion sends a selected operation to the original operation. -/
theorem names_operation (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    (names U).operation (operation op kept) = op := by
  cases op <;> rfl

/-- Select the type of a variable and keep its position. -/
def selectVar : {Γ : List P.signature.SortType} → (kept : Declaration.sorts Γ ⊆ U.declarations) →
    {s : P.signature.SortType} → (v : Var Γ s) → Var (context Γ kept) ⟨s, varKept kept v⟩
  | _, _, _, .here => .here
  | t :: Γ, kept, _, .there v => .there (selectVar ((tailSortsSubset t Γ).trans kept) v)

/-- Erase the retention proof from a selected variable without changing its position. -/
def ambientVar : {Γ : List P.signature.SortType} → (kept : Declaration.sorts Γ ⊆ U.declarations) →
    {s : SortName U} → Var (context Γ kept) s → Var Γ s.val
  | [], _, _, v => nomatch v
  | _ :: _, _, _, .here => .here
  | t :: Γ, kept, _, .there v => .there (ambientVar ((tailSortsSubset t Γ).trans kept) v)

/-- A selected variable reads back to its original position. -/
@[simp] theorem ambientVar_selectVar {Γ : List P.signature.SortType}
    (kept : Declaration.sorts Γ ⊆ U.declarations) {s : P.signature.SortType} (v : Var Γ s) :
    ambientVar kept (selectVar kept v) = v := by
  induction v with
  | here => rfl
  | there v ih => exact congrArg Var.there (ih _)

/-- Erasing and selecting again keeps every selected variable. -/
@[simp] theorem selectVar_ambientVar {Γ : List P.signature.SortType}
    (kept : Declaration.sorts Γ ⊆ U.declarations) {s : SortName U} (v : Var (context Γ kept) s) :
    selectVar kept (ambientVar kept v) = v := by
  induction Γ with
  | nil => exact nomatch v
  | cons t Γ ih =>
    cases v with
    | here => rfl
    | there v => exact congrArg Var.there (ih _ v)

/-- Select both type lists of a variable map. -/
def selectRenaming {Γ Δ : List P.signature.SortType} (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (keepΔ : Declaration.sorts Δ ⊆ U.declarations) (ρ : Renaming Γ Δ) :
    Renaming (context Γ keepΓ) (context Δ keepΔ) :=
  fun i => selectVar keepΔ (ρ (ambientVar keepΓ i))

/-- A selected variable map actually maps the original position. -/
@[simp] theorem renaming_selectVar {Γ Δ : List P.signature.SortType} (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (keepΔ : Declaration.sorts Δ ⊆ U.declarations) (ρ : Renaming Γ Δ)
    {s : P.signature.SortType} (v : Var Γ s) :
    selectRenaming keepΓ keepΔ ρ (selectVar keepΓ v) = selectVar keepΔ (ρ v) := by
  rw [selectRenaming, ambientVar_selectVar keepΓ v]

end Selected
end DeclarationContext
end SHIGURE
