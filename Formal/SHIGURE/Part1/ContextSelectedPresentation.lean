import Formal.SHIGURE.Part1.ContextSelectedProofs
import Formal.SHIGURE.Part1.ContextSelectedRings
import Mathlib.Data.List.Basic

/-! # The restricted primitive presentation

The ordinary presentation retains the actual typed symbols, named written
Laws and their roles, the ordered syntax attached to each equality, the
selected derivations, and the inclusion maps of retained partial domains.
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

/-- A retained partial declaration also retains its explicitly declared domain sort. -/
theorem domainSortKept (p : Partial U) (data : DomainInclusions p.val)
    (attached : P.domainInclusions p.val = some data) : Declaration.sort data.domainSort ∈ U.declarations :=
  U.closed p.property (Declaration.partial_domainSort_mem_dependsOn data attached)

/-- A retained partial declaration also retains every named coordinate of its inclusion. -/
theorem domainSymbolKept (p : Partial U) (data : DomainInclusions p.val) (attached : P.domainInclusions p.val = some data)
    {s : P.signature.SortType} (i : Var (P.signature.partialArity p.val).inputs s) :
    Declaration.ofOperation (data.symbol i).operation ∈ U.declarations :=
  U.closed p.property (Declaration.partial_domainSymbol_mem_dependsOn data attached i)

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
    Declaration.derivation (P.derived name.val role) ⊆ U.declarations :=
  (Declaration.derivation_subset_dependsOn name.val role).trans (U.closed name.property)

/-- The selected names and proofs form an ordinary primitive presentation. -/
noncomputable def presentation (U : DeclarationContext P) : PrimitivePresentation.{u} where
  signature := signature U
  laws := laws U
  ringEquation := Selected.ringEquation
  otherOrderedEquation name := NamedRingEquation.otherOrdered (Selected.ringEquation name)
    ((P.orderedEquation name.val).map (selectNamedEquation name))
  domainInclusions p := match attached : P.domainInclusions p.val with
    | none => none
    | some data => some (selectDomainInclusions p data attached)
  derived name role := selectDerivation (P.derived name.val role) (keepsDerived name role)

/-- The actual restricted presentation gives the ordinary theory over the selected signature. -/
theorem presentation_theory : (presentation U).theory = theory U :=
  rfl

/-- The selected presentation has exactly the original retained declaration names. -/
def declarationNames (U : DeclarationContext P) : Declaration (presentation U) ≃ U.Retained where
  toFun
    | .sort s => ⟨.sort s.val, s.property⟩
    | .total f => ⟨.total f.val, f.property⟩
    | .relation r => ⟨.relation r.val, r.property⟩
    | .partialOp p => ⟨.partialOp p.val, p.property⟩
    | .quantity q => ⟨.quantity q.val, q.property⟩
    | .law n => ⟨.law n.val, n.property⟩
  invFun
    | ⟨.sort s, kept⟩ => .sort ⟨s, kept⟩
    | ⟨.total f, kept⟩ => .total ⟨f, kept⟩
    | ⟨.relation r, kept⟩ => .relation ⟨r, kept⟩
    | ⟨.partialOp p, kept⟩ => .partialOp ⟨p, kept⟩
    | ⟨.quantity q, kept⟩ => .quantity ⟨q, kept⟩
    | ⟨.law n, kept⟩ => .law ⟨n, kept⟩
  left_inv d := by cases d <;> rfl
  right_inv d := by rcases d with ⟨d, kept⟩; cases d <;> rfl

/-- The declaration equivalence agrees with the typed signature and Law name map of the selection. -/
theorem declarationNames_eq (d : Declaration (presentation U)) :
    (declarationNames U d).val = d.renameNames (names U) Subtype.val := by
  cases d <;> rfl

/-- The selected Law has exactly the original ordered text read into the selected signature. -/
theorem presentation_orderedEquation (name : U.RetainedLaw) :
    (presentation U).orderedEquation name = (P.orderedEquation name.val).map (selectNamedEquation name) := by
  rw [PrimitivePresentation.orderedEquation_eq (presentation U)]
  exact NamedRingEquation.ordered_otherOrdered _ _ (fun data h => by
    obtain ⟨original, attached, support, rfl⟩ := ringEquation_some name h
    have oldText := (PrimitivePresentation.orderedEquation_eq P name.val).trans
      (NamedRingEquation.ordered_of_some attached (P.otherOrderedEquation name.val))
    rw [oldText, Option.map_some, selectNamedRingEquation_toOrdered])

end DeclarationContext.Selected
end SHIGURE
