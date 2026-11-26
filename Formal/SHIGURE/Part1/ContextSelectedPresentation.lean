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

/-- Read a domain projection at its actual position in the selected partial arity. -/
private def ambientDomainInput (p : Partial U) {s : SortName U}
    (i : Var ((signature U).partialArity p).inputs s) :
    Var (P.signature.partialArity p.val).inputs s.val :=
  ambientVar (operationInputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property))
    (cast (congrArg (Var · s) (signature_partialInputs p)) i)

/-- Restrict the domain inclusion with its original sort and all ordered coordinate operations. -/
def selectDomainInclusions (p : Partial U) (data : DomainInclusions p.val)
    (attached : P.domainInclusions p.val = some data) : DomainInclusions (sig := signature U) p where
  domainSort := ⟨data.domainSort, domainSortKept p data attached⟩
  symbol i := selectTotalSymbol
    (data.symbol (ambientDomainInput p i))
    (domainSymbolKept p data attached (ambientDomainInput p i))
  arity_eq i := by
    apply ambientArity_injective
    change ambientArity (selectTotalSymbol _ _).operation.arity = _
    rw [selectTotalSymbol_arity]
    exact (map_arity _ _).trans (data.arity_eq (ambientDomainInput p i))

/-- Closedness supplies all the references of a retained derived Law's original proof. -/
theorem keepsDerived (name : U.RetainedLaw) (role : P.laws.role name.val = .derived) :
    Declaration.derivation (P.derived name.val role) ⊆ U.declarations :=
  (Declaration.derivation_subset_dependsOn name.val role).trans (U.closed name.property)

private def selectCoefficientQuantity (q : Quantities.QuantityDeclaration P.signature)
    (keep : Declaration.ofOperation q.operation ∈ U.declarations) :
    Quantities.QuantityDeclaration (signature U) :=
  match q with
  | .total name => .total ⟨name, by simpa [Quantities.QuantityDeclaration.operation] using keep⟩
  | .partialOp name => .partialOp ⟨name, by simpa [Quantities.QuantityDeclaration.operation] using keep⟩

private theorem selectCoefficientQuantity_operation (q : Quantities.QuantityDeclaration P.signature)
    (keep : Declaration.ofOperation q.operation ∈ U.declarations) :
    operation q.operation keep = (selectCoefficientQuantity q keep).operation := by
  cases q <;> rfl

/-- Retype a named quantity and its exact argument terms in a selected signature. -/
def selectCoefficientApplication {Γ : List P.signature.SortType}
    (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (a : Quantities.DeclaredApplication P.signature Γ)
    (support : Declaration.coefficientApplicationSupport (P := P) a ⊆ U.declarations) :
    Quantities.DeclaredApplication (signature U) (context Γ hΓ) := by
  let kept := support (Or.inl (Set.mem_singleton _))
  let hInputs := operationInputs a.1.operation kept
  let q := selectCoefficientQuantity a.1 kept
  have inputs : q.operation.arity.inputs = context a.1.operation.arity.inputs hInputs :=
    operation_selectedInputs (selectCoefficientQuantity_operation a.1 kept)
  let terms := selectSubstitution a.2 hInputs hΓ (fun i =>
    (termReferences_subset_graph (a.2 i)).trans fun _ used =>
      support (Or.inr ⟨_, i, Or.inr used⟩))
  exact ⟨q, cast (congrArg (fun Δ => Substitution (signature U) Δ (context Γ hΓ)) inputs.symm) terms⟩

/-- Retype both original coefficient expressions and retain their original coefficient type. -/
def selectCoefficientWriting (name : U.RetainedLaw)
    (writing : Quantities.RegisteredCoefficientEquation P.signature (P.laws.statement name.val).context)
    (registered : P.coefficientWriting name.val = some writing) :
    Quantities.RegisteredCoefficientEquation (signature U) ((laws U).statement name).context := by
  let kept := Declaration.lawBody_subset_of_mem name.property
  let hΓ := (Declaration.sorts_subset_lawBody (P.laws.statement name.val)).trans kept
  let support := Declaration.coefficientWritingSupport_subset_of_mem name.property registered
  exact ⟨writing.1,
    writing.2.1.compile (fun a used =>
      selectCoefficientApplication hΓ a (fun _ incoming => support ⟨a, Or.inl used, incoming⟩)),
    writing.2.2.compile (fun a used =>
      selectCoefficientApplication hΓ a (fun _ incoming => support ⟨a, Or.inr used, incoming⟩))⟩

private theorem selectLaw_conclusion_truth (law : Law P.signature)
    (kept : Declaration.lawBody law ⊆ U.declarations) (truth : law.conclusion = .truth) :
    (selectLaw law kept).conclusion = .truth := by
  obtain ⟨context, input, conclusion⟩ := law
  change conclusion = .truth at truth
  subst conclusion
  rfl

private theorem coefficientWriting_some (name : U.RetainedLaw)
    {e : P.laws.CoefficientConclusion name.val}
    (found : P.coefficientLaw name.val = some e) : P.coefficientWriting name.val = some e.val :=
  congrArg (Option.map Subtype.val) found

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
  coefficientLaw name := match found : P.coefficientLaw name.val with
    | none => none
    | some e => some ⟨selectCoefficientWriting name e.val (coefficientWriting_some name found),
        e.property.1, selectLaw_conclusion_truth _ (Declaration.lawBody_subset_of_mem name.property) e.property.2⟩

/-- A selected Law carries the original coefficient writing in its selected signature. -/
theorem presentation_coefficientWriting (name : U.RetainedLaw)
    {writing : Quantities.RegisteredCoefficientEquation P.signature (P.laws.statement name.val).context}
    (registered : P.coefficientWriting name.val = some writing) :
    (presentation U).coefficientWriting name = some (selectCoefficientWriting name writing registered) := by
  change Option.map Subtype.val
    (match found : P.coefficientLaw name.val with
      | none => none
      | some e => some (⟨selectCoefficientWriting name e.val (coefficientWriting_some name found),
          e.property.1, selectLaw_conclusion_truth _ (Declaration.lawBody_subset_of_mem name.property)
            e.property.2⟩ :
        (laws U).CoefficientConclusion name)) = _
  split
  · rename_i absent
    have impossible : (none : Option _) = some writing :=
      (congrArg (Option.map Subtype.val) absent).symm.trans registered
    cases impossible
  · rename_i e found
    have equal : e.val = writing :=
      Option.some.inj ((coefficientWriting_some name found).symm.trans registered)
    subst writing
    rfl

/-- The restricted presentation uses the signature of the retained vocabulary. -/
theorem presentation_signature : (presentation U).signature = signature U :=
  rfl

/-- The actual restricted presentation gives the ordinary theory over the selected signature. -/
theorem presentation_theory : (presentation U).theory = theory U :=
  rfl

/-- A retained name indexes the corresponding Law of the selected presentation. -/
def presentationLawName (name : U.RetainedLaw) : (presentation U).laws.LawName :=
  name

/-- A required name in the selected theory comes from a retained Law declaration. -/
def retainedTheoryName (name : (presentation U).theory.LawName) : U.RetainedLaw :=
  name.val

/-- The retained theory name identifies the same original declaration. -/
theorem retainedTheoryName_val (name : (presentation U).theory.LawName) :
    (retainedTheoryName name).val = name.val.val :=
  rfl

/-- A required Law of the selected presentation reads the statement at its retained name. -/
theorem presentation_theory_law (name : (presentation U).theory.LawName) :
    (presentation U).theory.law name =
      (presentation U).laws.statement (presentationLawName (retainedTheoryName name)) :=
  rfl

/-- The presentation registers the selected Law under the same retained name. -/
theorem presentation_law_eq_selected (name : U.RetainedLaw) :
    (presentation U).laws.statement name = (laws U).statement name :=
  rfl

/-- A retained Law in the selected presentation has the selected text of its original statement. -/
theorem presentation_law_statement (name : U.RetainedLaw) :
    (presentation U).laws.statement name =
      selectLaw (P.laws.statement name.val) (Declaration.lawBody_subset_of_mem name.property) :=
  rfl

/-- Transporting the restricted Law text along the signature comparison gives its selected form. -/
theorem presentation_law_cast (name : U.RetainedLaw) :
    cast (congrArg Law (presentation_signature (U := U)))
      ((presentation U).laws.statement (presentationLawName name)) =
      selectLaw (P.laws.statement name.val) (Declaration.lawBody_subset_of_mem name.property) :=
  rfl

/-- The selected display attaches the ring certificate retained at this Law. -/
theorem presentation_ringEquation (name : U.RetainedLaw) :
    (presentation U).ringEquation name = Selected.ringEquation name :=
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
