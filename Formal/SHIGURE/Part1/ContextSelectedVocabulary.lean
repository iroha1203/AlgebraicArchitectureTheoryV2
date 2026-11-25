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
  | s :: Γ, kept => ⟨s, kept (Declaration.sort_mem_sorts List.mem_cons_self)⟩ ::
    context Γ ((tailSortsSubset s Γ).trans kept)

/-- Selecting an empty context yields the empty list of sort names. -/
theorem context_nil (kept : Declaration.sorts (P := P) [] ⊆ U.declarations) :
    context [] kept = [] :=
  rfl

/-- Selecting a nonempty context preserves its head before selecting the tail. -/
theorem context_cons (s : P.signature.SortType) (Γ : List P.signature.SortType)
    (kept : Declaration.sorts (s :: Γ) ⊆ U.declarations) :
    context (s :: Γ) kept = ⟨s, kept (Declaration.sort_mem_sorts List.mem_cons_self)⟩ ::
      context Γ ((tailSortsSubset s Γ).trans kept) :=
  rfl

/-- Selecting a context with two head variables selects them in their original order. -/
theorem context_cons_cons (s t : P.signature.SortType) (Γ : List P.signature.SortType)
    (keep : Declaration.sorts (t :: s :: Γ) ⊆ U.declarations) :
    context (t :: s :: Γ) keep =
      ⟨t, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩ ::
      ⟨s, keep (Declaration.sort_mem_sorts (List.mem_cons_of_mem t List.mem_cons_self))⟩ ::
      context Γ ((tailSortsSubset s Γ).trans ((tailSortsSubset t (s :: Γ)).trans keep)) := by
  rw [context_cons, context_cons]

/-- Forgetting the retention proofs recovers the original input list. -/
@[simp] theorem map_context (Γ : List P.signature.SortType) (kept : Declaration.sorts Γ ⊆ U.declarations) :
    (context Γ kept).map Subtype.val = Γ := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih => exact congrArg (s :: ·) (ih _)

/-- Restrict an operation arity by selecting each of its retained sorts. -/
def arity (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) : Arity (SortName U) :=
  ⟨context op.arity.inputs (operationInputs op kept), ⟨op.arity.output, operationOutput op kept⟩⟩

/-- The input profile of a retained operation is the selection of its original input context. -/
theorem arity_inputs (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    (arity op kept).inputs = context op.arity.inputs (operationInputs op kept) :=
  rfl

/-- The retained output profile names the original output sort. -/
theorem arity_output (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    (arity op kept).output = ⟨op.arity.output, operationOutput op kept⟩ :=
  rfl

/-- The actual signature of the restricted presentation has precisely the retained names. -/
def signature (U : DeclarationContext P) : Signature.{u} where
  SortType := SortName U
  Total := Total U
  totalArity f := arity (.total f.val) (by simpa only [Declaration.ofOperation_total] using f.property)
  Rel := Rel U
  relInputs r := context (P.signature.relInputs r.val) (relationInputs r.val r.property)
  Partial := Partial U
  partialArity p := arity (.partialOp p.val) (by simpa only [Declaration.ofOperation_partialOp] using p.property)
  Quantity := Quantity U
  quantityArity q := arity (.quantity q.val) (by simpa only [Declaration.ofOperation_quantity] using q.property)

/-- The input positions of a retained relation are the selected original positions. -/
theorem signature_relInputs (r : Rel U) :
    (signature U).relInputs r = context (P.signature.relInputs r.val) (relationInputs r.val r.property) :=
  rfl

/-- The input positions of a retained partial domain are the selected original positions. -/
theorem signature_partialInputs (p : Partial U) :
    ((signature U).partialArity p).inputs = context (P.signature.partialArity p.val).inputs
      (operationInputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property)) :=
  (arity_inputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property))

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
  totalArity f := map_arity (.total f.val) (by simpa only [Declaration.ofOperation_total] using f.property)
  relInputs _ := map_context _ _
  partialArity p := map_arity (.partialOp p.val) (by simpa only [Declaration.ofOperation_partialOp] using p.property)
  quantityArity q := map_arity (.quantity q.val) (by simpa only [Declaration.ofOperation_quantity] using q.property)

/-- Select an operation without changing whether it is total, partial, or a quantity. -/
def operation : (op : Operation P.signature) → Declaration.ofOperation op ∈ U.declarations → Operation (signature U)
  | .total f, kept => .total ⟨f, by simpa only [Declaration.ofOperation_total] using kept⟩
  | .partialOp p, kept => .partialOp ⟨p, by simpa only [Declaration.ofOperation_partialOp] using kept⟩
  | .quantity q, kept => .quantity ⟨q, by simpa only [Declaration.ofOperation_quantity] using kept⟩

/-- Selecting a total operation retains its primitive tag and name. -/
theorem operation_total (f : P.signature.Total) (keep : Declaration.ofOperation (.total f) ∈ U.declarations) :
    operation (.total f) keep = .total ⟨f, by simpa only [Declaration.ofOperation_total] using keep⟩ :=
  rfl

/-- Selecting a partial operation retains its primitive tag and name. -/
theorem operation_partialOp (p : P.signature.Partial)
    (keep : Declaration.ofOperation (.partialOp p) ∈ U.declarations) :
    operation (.partialOp p) keep = .partialOp ⟨p, by simpa only [Declaration.ofOperation_partialOp] using keep⟩ :=
  rfl

/-- Selecting a quantity retains its primitive tag and name. -/
theorem operation_quantity (q : P.signature.Quantity)
    (keep : Declaration.ofOperation (.quantity q) ∈ U.declarations) :
    operation (.quantity q) keep = .quantity ⟨q, by simpa only [Declaration.ofOperation_quantity] using keep⟩ :=
  rfl

/-- The selected operation has exactly the corresponding selected arity. -/
theorem operation_arity (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    (operation op kept).arity = arity op kept := by
  cases op <;> rfl

/-- An equal selected operation has the same selected input and output profile. -/
theorem operation_arity_of_eq {op : Operation P.signature} {keep : Declaration.ofOperation op ∈ U.declarations}
    {selected : Operation (signature U)} (same : operation op keep = selected) :
    selected.arity = arity op keep :=
  (congrArg Operation.arity same).symm.trans (operation_arity op keep)

/-- Inclusion sends a selected operation to the original operation. -/
theorem names_operation (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    (names U).operation (operation op kept) = op := by
  cases op <;> rfl

/-- A named total symbol remains total and retains its original tag. -/
def selectTotalSymbol : (f : TotalSymbol P.signature) → Declaration.ofOperation f.operation ∈ U.declarations →
    TotalSymbol (signature U)
  | .ordinary f, keep => .ordinary ⟨f, by simpa only [TotalSymbol.operation_ordinary, Declaration.ofOperation_total] using keep⟩
  | .quantity q, keep => .quantity ⟨q, by simpa only [TotalSymbol.operation_quantity, Declaration.ofOperation_quantity] using keep⟩

/-- The selected total symbol has the arity read from its original declaration. -/
theorem selectTotalSymbol_arity (f : TotalSymbol P.signature) (keep : Declaration.ofOperation f.operation ∈ U.declarations) :
    (selectTotalSymbol f keep).operation.arity = arity f.operation keep := by
  cases f <;> simp only [selectTotalSymbol, TotalSymbol.operation_ordinary, TotalSymbol.operation_quantity] <;> rfl

/-- Selection preserves a declared total symbol's explicitly named profile. -/
def selectTypedTotal {profile : Arity P.signature.SortType} (f : TypedTotal P.signature profile)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (inputs : Declaration.sorts profile.inputs ⊆ U.declarations)
    (output : Declaration.sort profile.output ∈ U.declarations) :
    TypedTotal (signature U) ⟨context profile.inputs inputs, ⟨profile.output, output⟩⟩ where
  symbol := selectTotalSymbol f.symbol keep
  arity_eq := by
    rcases f with ⟨symbol, same⟩
    cases same
    exact selectTotalSymbol_arity symbol keep

/-- Selecting a typed total symbol selects the operation with the same primitive tag. -/
theorem selectTypedTotal_operation {profile : Arity P.signature.SortType} (f : TypedTotal P.signature profile)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (inputs : Declaration.sorts profile.inputs ⊆ U.declarations)
    (output : Declaration.sort profile.output ∈ U.declarations) :
    (selectTypedTotal f keep inputs output).symbol.operation = operation f.symbol.operation keep := by
  rcases f with ⟨symbol, same⟩
  cases symbol <;>
    simp only [selectTypedTotal, TotalSymbol.operation_ordinary, TotalSymbol.operation_quantity,
      selectTotalSymbol, operation_total, operation_quantity]

/-- Select the type of a variable and keep its position. -/
def selectVar : {Γ : List P.signature.SortType} → (kept : Declaration.sorts Γ ⊆ U.declarations) →
    {s : P.signature.SortType} → (v : Var Γ s) → Var (context Γ kept) ⟨s, varKept kept v⟩
  | _, _, _, .here => .here
  | t :: Γ, kept, _, .there v => .there (selectVar ((tailSortsSubset t Γ).trans kept) v)

/-- The first retained variable stays first when selecting its context. -/
theorem selectVar_here {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) :
    selectVar keep (Var.here : Var (s :: Γ) s) = .here :=
  rfl

/-- Selection of the head variable takes the head position in the explicit cons context. -/
theorem selectVar_cast_here {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) :
    cast (congrArg (fun ctx => Var ctx _) (context_cons s Γ keep))
      (selectVar keep (Var.here : Var (s :: Γ) s)) = .here :=
  selectVar_here keep

/-- A retained variable following the head stays in the selected tail. -/
theorem selectVar_there {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keep : Declaration.sorts (t :: Γ) ⊆ U.declarations) (i : Var Γ s) :
    selectVar keep (Var.there (t := t) i) = .there (selectVar ((tailSortsSubset t Γ).trans keep) i) :=
  rfl

/-- Selection past the first position commutes with transport to the explicit retained cons context. -/
theorem selectVar_cast_there {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (keep : Declaration.sorts (t :: Γ) ⊆ U.declarations) (i : Var Γ s) :
    cast (congrArg (fun ctx => Var ctx ⟨s, varKept keep (Var.there (t := t) i)⟩) (context_cons t Γ keep))
      (selectVar keep (Var.there (t := t) i)) = .there (selectVar ((tailSortsSubset t Γ).trans keep) i) :=
  selectVar_there keep i

/-- Erase the retention proof from a selected variable without changing its position. -/
def ambientVar : {Γ : List P.signature.SortType} → (kept : Declaration.sorts Γ ⊆ U.declarations) →
    {s : SortName U} → Var (context Γ kept) s → Var Γ s.val
  | [], _, _, v => nomatch v
  | _ :: _, _, _, .here => .here
  | t :: Γ, kept, _, .there v => .there (ambientVar ((tailSortsSubset t Γ).trans kept) v)

/-- Erasing the selected first position recovers the original first position. -/
theorem ambientVar_here {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) :
    ambientVar keep (Var.here : Var (context (s :: Γ) keep) _) = .here :=
  rfl

/-- Erasing a selected position past the head keeps it past the original head. -/
theorem ambientVar_there {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) {t : SortName U}
    (i : Var (context Γ ((tailSortsSubset s Γ).trans keep)) t) :
    ambientVar keep (Var.there i : Var (context (s :: Γ) keep) t) =
      .there (ambientVar ((tailSortsSubset s Γ).trans keep) i) :=
  rfl

/-- Erasure sends the transported head to the original head. -/
theorem ambientVar_cast_here {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) :
    ambientVar keep (cast (congrArg (fun ctx => Var ctx _) (context_cons s Γ keep).symm) Var.here) =
      .here :=
  ambientVar_here keep

/-- Erasure sends a transported tail position to the corresponding original tail position. -/
theorem ambientVar_cast_there {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) {t : SortName U}
    (i : Var (context Γ ((tailSortsSubset s Γ).trans keep)) t) :
    ambientVar keep (cast (congrArg (fun ctx => Var ctx t) (context_cons s Γ keep).symm) (Var.there i)) =
      .there (ambientVar ((tailSortsSubset s Γ).trans keep) i) :=
  ambientVar_there keep i

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

/-- A selected renaming reads the original variable, renames it, and selects
the target position. Both contexts contain the sorts of the original map. -/
theorem selectRenaming_apply {Γ Δ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepΔ : Declaration.sorts Δ ⊆ U.declarations)
    (ρ : Renaming Γ Δ) {s : SortName U} (i : Var (context Γ keepΓ) s) :
    selectRenaming keepΓ keepΔ ρ i = selectVar keepΔ (ρ (ambientVar keepΓ i)) :=
  rfl

/-- A selected variable map actually maps the original position. -/
@[simp] theorem renaming_selectVar {Γ Δ : List P.signature.SortType} (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (keepΔ : Declaration.sorts Δ ⊆ U.declarations) (ρ : Renaming Γ Δ)
    {s : P.signature.SortType} (v : Var Γ s) :
    selectRenaming keepΓ keepΔ ρ (selectVar keepΓ v) = selectVar keepΔ (ρ v) := by
  rw [selectRenaming, ambientVar_selectVar keepΓ v]

end Selected
end DeclarationContext
end SHIGURE
