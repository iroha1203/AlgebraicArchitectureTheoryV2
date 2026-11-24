import Formal.SHIGURE.Part1.ContextLogicalCore
import Formal.SHIGURE.Part1.ContextSelectedProofs
import Mathlib.Data.List.Basic

/-! # The restricted primitive presentation

The ordinary presentation retains the actual typed symbols, named written
Laws and their roles, the selected derivations, and the inclusion maps of
retained partial domains. The logical contexts use `PrimitivePresentation.logicalCore`,
so optional residual metadata does not impose declarations unrelated to a
Law's logical support.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- Erase the retention witnesses of a selected arity. -/
def ambientArity (a : Arity (SortName U)) : Arity P.signature.SortType :=
  ⟨a.inputs.map Subtype.val, a.output.val⟩

/-- Erasing retention witnesses keeps enough information to recover a selected arity. -/
theorem ambientArity_injective : Function.Injective (ambientArity (U := U)) := by
  intro a b same
  cases a with
  | mk xs x =>
    cases b with
    | mk ys y =>
      have inputs : xs.map Subtype.val = ys.map Subtype.val := congrArg Arity.inputs same
      have output : x.val = y.val := congrArg Arity.output same
      exact congrArg₂ Arity.mk (List.map_injective_iff.2 Subtype.val_injective inputs) (Subtype.ext output)

/-- A named total symbol remains total and retains its original tag. -/
def selectTotalSymbol : (f : TotalSymbol P.signature) → Declaration.ofOperation f.operation ∈ U.declarations →
    TotalSymbol (signature U)
  | .ordinary f, keep => .ordinary ⟨f, keep⟩
  | .quantity q, keep => .quantity ⟨q, keep⟩

/-- The selected total symbol has the arity read from its original declaration. -/
theorem selectTotalSymbol_arity (f : TotalSymbol P.signature) (keep : Declaration.ofOperation f.operation ∈ U.declarations) :
    (selectTotalSymbol f keep).operation.arity = arity f.operation keep := by
  cases f <;> rfl

/-- A retained partial declaration also retains its explicitly declared domain sort. -/
theorem domainSortKept (p : Partial U) (data : DomainInclusions p.val)
    (attached : P.domainInclusions p.val = some data) : Declaration.sort data.domainSort ∈ U.declarations := by
  apply U.closed p.property
  simp only [Declaration.dependsOn, attached]
  exact Or.inr (Or.inl (Set.mem_singleton _))

/-- A retained partial declaration also retains every named coordinate of its inclusion. -/
theorem domainSymbolKept (p : Partial U) (data : DomainInclusions p.val) (attached : P.domainInclusions p.val = some data)
    {s : P.signature.SortType} (i : Var (P.signature.partialArity p.val).inputs s) :
    Declaration.ofOperation (data.symbol i).operation ∈ U.declarations := by
  apply U.closed p.property
  simp only [Declaration.dependsOn, attached]
  exact Or.inr (Or.inr ⟨s, i, rfl⟩)

/-- Restrict the domain inclusion with its original sort and all ordered coordinate operations. -/
def selectDomainInclusions (p : Partial U) (data : DomainInclusions p.val)
    (attached : P.domainInclusions p.val = some data) : DomainInclusions (sig := signature U) p where
  domainSort := ⟨data.domainSort, domainSortKept p data attached⟩
  symbol i := selectTotalSymbol
    (data.symbol (ambientVar (operationInputs (.partialOp p.val) p.property) i))
    (domainSymbolKept p data attached (ambientVar (operationInputs (.partialOp p.val) p.property) i))
  arity_eq i := by
    apply ambientArity_injective
    change ambientArity (selectTotalSymbol _ _).operation.arity = _
    rw [selectTotalSymbol_arity]
    exact (map_arity _ _).trans (data.arity_eq (ambientVar (operationInputs (.partialOp p.val) p.property) i))

/-- Closedness supplies all the references of a retained derived Law's original proof. -/
theorem keepsDerived (name : U.RetainedLaw) (role : P.laws.role name.val = .derived) :
    Declaration.derivation (P.derived name.val role) ⊆ U.declarations := by
  intro a used
  apply U.closed name.property
  rw [Declaration.dependsOn]
  refine Or.inr (Or.inr ?_)
  split
  · exact used
  · rename_i otherRole
    cases role.symm.trans otherRole
  · rename_i otherRole
    cases role.symm.trans otherRole

/-- The selected names and proofs form an ordinary primitive presentation. -/
noncomputable def presentation (U : DeclarationContext P) : PrimitivePresentation.{u} where
  signature := signature U
  laws := laws U
  domainInclusions p := match attached : P.domainInclusions p.val with
    | none => none
    | some data => some (selectDomainInclusions p data attached)
  derived name role := selectDerivation (P.derived name.val role) (keepsDerived name role)

/-- The actual restricted presentation gives the ordinary theory over the selected signature. -/
theorem presentation_theory : (presentation U).theory = theory U :=
  rfl

end DeclarationContext.Selected

namespace ChapterContext

/-- The Chapter 3 restriction of a primitive presentation to a dependency-closed context. -/
noncomputable def restrict {P : PrimitivePresentation.{u}} (U : ChapterContext P) : PrimitivePresentation.{u} :=
  DeclarationContext.Selected.presentation U

end ChapterContext
end SHIGURE
