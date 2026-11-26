import Formal.SHIGURE.Part1.ContextSelectedPresentation
import Formal.SHIGURE.Part1.MarkedLawSupport
import Formal.SHIGURE.Part2.QuantityTransport.CoefficientSyntax
import Formal.SHIGURE.Part2.QuantityTransport.Coefficients
import Formal.SHIGURE.Part2.QuantityTransport.DeclarationStates
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Restriction of declared quantity Laws

Chapter 3 supplies the selected declarations and actual state reduct.
The ordered writing of each kept Law supplies its actual terms. The
coefficient presentation reads precisely their used primitive values
and applications of the designated quantities.

## Implementation notes

One may select coordinates after evaluating the state terms. The retained
writing used here also gives the original substitutions, primitive
symbols and antecedents, which the reduct can evaluate independently.
The selected domain of a partial quantity lies inside its native defined
domain. Coefficients come from actual state term evaluation on declared
inputs, including variables and fixed nullary operations. Readings of
attained equality results suffice for the comparison; unused carrier
values need no scalar identification. A specified native encoding gives
every coefficient its actual quantity graph. A retained Law evaluates
only these candidates at the quantity declarations it references.
When a reduct is extended, the Law's references ensure that those
representatives remain in scope.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

open DeclarationContext

/-- A written source term can retain a strict binder expanded by the polynomial compiler. -/
inductive SourceSide {sig : Signature.{u}} {Q : Set (QuantityDeclaration sig)}
    {Γ : List sig.SortType} {s : sig.SortType} (compiled : CoefficientTerm Q Γ s)
  | direct
  | inline (written : Term sig Γ s) (expands : written.inlineLets = compiled.toTerm)

namespace SourceSide

variable {sig : Signature.{u}} {Q : Set (QuantityDeclaration sig)}
variable {Γ : List sig.SortType} {s : sig.SortType} {compiled : CoefficientTerm Q Γ s}

/-- Read the original term, including any written strict binders. -/
def term : SourceSide compiled → Term sig Γ s
  | .direct => compiled.toTerm
  | .inline written _ => written

end SourceSide

/-- The original required coefficient equations in one primitive presentation.
Their terms are tied to the actual positive formulas by their ordered writings. -/
structure DeclaredQuantityLaws (P : PrimitivePresentation.{u}) where
  /-- Exactly the declared operations chosen to supply the varying scalar values. -/
  quantities : Set (QuantityDeclaration P.signature)
  /-- The original required Laws imposing the scalar equalities. -/
  quantityLaws : Set P.theory.LawName
  /-- Each equality may have its own value sort. -/
  valueSort : quantityLaws → P.signature.SortType
  /-- The two sides, over the original source context of each declaration. -/
  left (l : quantityLaws) : CoefficientTerm quantities (P.theory.law l.val).context (valueSort l)
  right (l : quantityLaws) : CoefficientTerm quantities (P.theory.law l.val).context (valueSort l)
  /-- The two original terms may use strict binders around their scalar expressions. -/
  leftSource (l : quantityLaws) : SourceSide (left l) := .direct
  rightSource (l : quantityLaws) : SourceSide (right l) := .direct
  /-- The existing Law is the ordered writing of these two original typed terms. -/
  expansion (l : quantityLaws) : OrderedEquation.Expansion
    ⟨(P.theory.law l.val).context, valueSort l, (P.theory.law l.val).input, (leftSource l).term, (rightSource l).term⟩
    (P.theory.law l.val).conclusion
  /-- When the declaration already has ordered syntax, its term pair and input are authoritative. -/
  registeredEquation (l : quantityLaws) (registered : NamedOrderedEquation P.laws l.val.val) :
    P.orderedEquation l.val.val = some registered →
      registered.written.equation =
        ⟨(P.theory.law l.val).context, valueSort l, (P.theory.law l.val).input,
          (leftSource l).term, (rightSource l).term⟩

namespace DeclaredQuantityLaws

variable {P : PrimitivePresentation.{u}} (L : DeclaredQuantityLaws P)
variable {U V : DeclarationContext P}

/-- The retained part of the designated varying quantities. -/
abbrev KeptQuantity (U : DeclarationContext P) :=
  {j : L.quantities // Declaration.ofOperation j.val.operation ∈ U.declarations}

/-- The retained part of the original required scalar Laws. -/
abbrev KeptLaw (U : DeclarationContext P) :=
  {l : L.quantityLaws // Declaration.law l.val.val ∈ U.declarations}

/-- The original equation with its full ordered writing. -/
def writing (l : L.quantityLaws) : OrderedEquation.Written P.signature :=
  ⟨⟨_, _, _, (L.leftSource l).term, (L.rightSource l).term⟩, (P.theory.law l.val).conclusion, L.expansion l⟩

/-- Its stored positive Law is exactly the declaration at the selected name. -/
theorem writing_toLaw (l : L.quantityLaws) : (L.writing l).toLaw = P.theory.law l.val :=
  rfl

/-- The compiler reads the same ordered equation whenever the source registers one. -/
theorem writing_eq_registered (l : L.quantityLaws) (registered : NamedOrderedEquation P.laws l.val.val)
    (attached : P.orderedEquation l.val.val = some registered) :
    (L.writing l).equation = registered.written.equation :=
  (L.registeredEquation l registered attached).symm

/-- The selected presentation retains the registered writing that supplies the compiled term pair. -/
theorem selected_writing_eq_registered (l : L.KeptLaw U)
    (registered : NamedOrderedEquation P.laws l.val.val.val)
    (attached : P.orderedEquation l.val.val.val = some registered) :
    (Selected.presentation U).orderedEquation ⟨l.val.val.val, l.property⟩ =
      some (Selected.selectNamedEquation ⟨l.val.val.val, l.property⟩ registered) ∧
    (L.writing l.val).equation = registered.written.equation := by
  constructor
  · rw [Selected.presentation_orderedEquation]
    change (P.orderedEquation l.val.val.val).map _ = _
    rw [attached]
    rfl
  · exact L.writing_eq_registered l.val registered attached

private theorem keptWriting_refs (l : L.KeptLaw U) :
    Declaration.sort (L.valueSort l.val) ∈ U.declarations ∧
      Selected.termReferences (L.leftSource l.val).term ⊆ U.declarations ∧
      Selected.termReferences (L.rightSource l.val).term ⊆ U.declarations := by
  cases attached : P.orderedEquation l.val.val.val with
  | none =>
    exact Selected.selectWritten_terms_kept (L.writing l.val)
      (by rw [L.writing_toLaw]; exact Declaration.lawBody_subset_of_mem l.property)
  | some registered =>
    have kept := Selected.selectWritten_terms_kept (U := U) registered.written
      (by rw [registered.statement_eq]; exact Declaration.lawBody_subset_of_mem l.property)
    have equation := L.writing_eq_registered l.val registered attached
    rw [← equation] at kept
    exact kept

private theorem compiledRefs_kept {Γ : List P.signature.SortType} {s : P.signature.SortType}
    {compiled : CoefficientTerm L.quantities Γ s} (source : SourceSide compiled)
    (keep : Selected.termReferences source.term ⊆ U.declarations) :
    Selected.termReferences compiled.toTerm ⊆ U.declarations := by
  cases source with
  | direct => exact keep
  | inline term expands =>
    rw [← expands]
    exact Selected.inlineLets_supported term keep

/-- Reading a retained Law keeps the result sort and each reference used by its compiled terms. -/
theorem keptLaw_refs (l : L.KeptLaw U) :
    Declaration.sort (L.valueSort l.val) ∈ U.declarations ∧
      Selected.termReferences (L.left l.val).toTerm ⊆ U.declarations ∧
      Selected.termReferences (L.right l.val).toTerm ⊆ U.declarations :=
  ⟨(L.keptWriting_refs l).1,
    L.compiledRefs_kept (L.leftSource l.val) (L.keptWriting_refs l).2.1,
    L.compiledRefs_kept (L.rightSource l.val) (L.keptWriting_refs l).2.2⟩

/-- The fixed coefficient terms and quantity applications used by either side after binder expansion. -/
abbrev UsedLeaf (l : L.quantityLaws) :=
  {a : CoefficientTerm.StateCoefficient P.signature (P.theory.law l.val).context ⊕
      CoefficientTerm.Application L.quantities (P.theory.law l.val).context //
    a ∈ (L.left l).leaves ∪ (L.right l).leaves}

/-- The original Law's support keeps every actual referenced leaf. -/
theorem keptLeaf_refs (l : L.KeptLaw U) (a : L.UsedLeaf l.val) :
    Selected.termReferences (CoefficientTerm.leafTerm a.val).2 ⊆ U.declarations :=
  a.property.elim
    (fun h => (CoefficientTerm.leafReferences_subset _ h).trans (L.keptLaw_refs l).2.1)
    (fun h => (CoefficientTerm.leafReferences_subset _ h).trans (L.keptLaw_refs l).2.2)

/-- An arithmetic application occurring in either side after binder expansion. -/
abbrev UsedArithmetic (l : L.quantityLaws) :=
  {a : ArithmeticApplication P.signature (P.theory.law l.val).context //
    a ∈ (L.left l).arithmeticApplications ∪ (L.right l).arithmeticApplications}

/-- Every reference of a used arithmetic application survives selection. -/
theorem keptArithmetic_refs (l : L.KeptLaw U) (a : L.UsedArithmetic l.val) :
    Selected.termReferences (a.val.1.symbol.term (fun i => a.val.2 i)) ⊆ U.declarations :=
  a.property.elim
    (fun h => ((L.left l.val).arithmeticApplication_references h).trans (L.keptLaw_refs l).2.1)
    (fun h => ((L.right l.val).arithmeticApplication_references h).trans (L.keptLaw_refs l).2.2)

/-- The operator at each used arithmetic application survives selection. -/
theorem keptArithmetic (l : L.KeptLaw U) (a : L.UsedArithmetic l.val) :
    Declaration.ofOperation a.val.1.operation ∈ U.declarations :=
  L.keptArithmetic_refs l a (CoefficientTerm.coefficientHead_ref a.val.1.symbol (fun i => a.val.2 i))

/-- A designated quantity application occurring in either expanded side. -/
abbrev UsedApplication (l : L.quantityLaws) :=
  {a : CoefficientTerm.Application L.quantities (P.theory.law l.val).context //
    Sum.inr a ∈ (L.left l).leaves ∪ (L.right l).leaves}

/-- An actual fixed coefficient term occurring in either expanded side. -/
abbrev UsedCoefficient (l : L.quantityLaws) :=
  {a : CoefficientTerm.StateCoefficient P.signature (P.theory.law l.val).context //
    Sum.inl a ∈ (L.left l).leaves ∪ (L.right l).leaves}

/-- The original Law's support keeps the operation of every applied quantity. -/
def keptApplication (l : L.KeptLaw U) (a : L.UsedApplication l.val) : L.KeptQuantity U :=
  ⟨a.val.1, L.keptLeaf_refs l ⟨.inr a.val, a.property⟩ (Or.inl (Set.mem_singleton _))⟩

/-- Every argument term of an actual application is written in the retained context. -/
private theorem keptTerm_support (l : L.KeptLaw U) (a : L.UsedApplication l.val)
    {s : P.signature.SortType} (i : Var a.val.1.val.operation.arity.inputs s) :
    Declaration.termContext (a.val.2 i) ≤ U := by
  let t := a.val.2 i
  have input := lawSortSupport (Declaration.lawBody_subset_of_mem l.property)
  have result := varKept
    (operationInputs a.val.1.val.operation (L.keptApplication l a).property) i
  have termRefs : Selected.termReferences t ⊆ U.declarations :=
    fun _ h => L.keptLeaf_refs l ⟨.inr a.val, a.property⟩ (Or.inr ⟨_, i, h⟩)
  exact Selected.termContext_le_of_references t input result termRefs

/-- The retained state argument denotes precisely its original term. -/
def keptTerm (l : L.KeptLaw U) (a : L.UsedApplication l.val) {s : P.signature.SortType}
    (i : Var a.val.1.val.operation.arity.inputs s) : U.TermIn (P.theory.law l.val.val).context s :=
  ⟨a.val.2 i, L.keptTerm_support l a i⟩

/-- The input of the Law is read from its actual fixed-state antecedent. -/
def lawInput (A : ContextStructure U) (l : L.KeptLaw U) :
    Set (Assignment A.carrier (P.theory.law l.val.val).context) :=
  {e | A.evaluation.holds (P.theory.law l.val.val).input
    (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e}

/-- The input sorts survive along with the original required Law. -/
theorem keptLaw_sorts (l : L.KeptLaw U) :
    Declaration.sorts (P.theory.law l.val.val).context ⊆ U.declarations :=
  lawSortSupport (Declaration.lawBody_subset_of_mem l.property)

/-- The original term that supplies a coefficient survives together with its Law. -/
def keptCoefficient (l : L.KeptLaw U) (a : L.UsedCoefficient l.val) :
    U.TermIn (P.theory.law l.val.val).context a.val.1 :=
  let refs := L.keptLeaf_refs l ⟨.inl a.val, a.property⟩
  let context := L.keptLaw_sorts l
  ⟨a.val.2, Selected.termContext_le_of_references a.val.2 context
    (Selected.termResult_mem_of_references a.val.2 context refs) refs⟩

/-- Keep the original argument term at the given position of a used arithmetic application. -/
def keptArithmeticArgument (l : L.KeptLaw U) (a : L.UsedArithmetic l.val) {s : P.signature.SortType}
    (i : Var a.val.1.profile.inputs s) : U.TermIn (P.theory.law l.val.val).context s :=
  ⟨a.val.2 i, Selected.termContext_le_of_references _ (L.keptLaw_sorts l)
    (varKept (a.val.1.symbol.keepsInputs (L.keptArithmetic l a)) i)
    ((CoefficientTerm.coefficientArg_refs a.val.1.symbol (fun j => a.val.2 j) i).trans
      (L.keptArithmetic_refs l a))⟩

/-- The left term of the actual declared Law is supported in the retained context. -/
def keptLeftSource (l : L.KeptLaw U) : U.TermIn (P.theory.law l.val.val).context (L.valueSort l.val) :=
  ⟨(L.leftSource l.val).term, Selected.termContext_le_of_references _ (L.keptLaw_sorts l)
    (L.keptWriting_refs l).1 (L.keptWriting_refs l).2.1⟩

/-- The right term of the actual declared Law is supported in the retained context. -/
def keptRightSource (l : L.KeptLaw U) : U.TermIn (P.theory.law l.val.val).context (L.valueSort l.val) :=
  ⟨(L.rightSource l.val).term, Selected.termContext_le_of_references _ (L.keptLaw_sorts l)
    (L.keptWriting_refs l).1 (L.keptWriting_refs l).2.2⟩

private theorem evaluates_compiledSide (B : ContextStructure U)
    {Γ : List P.signature.SortType} {s : P.signature.SortType} {compiled : CoefficientTerm L.quantities Γ s}
    (source : SourceSide compiled) (originalKept : Declaration.termContext source.term ≤ U)
    (compiledKept : Declaration.termContext compiled.toTerm ≤ U)
    (e : Assignment B.carrier Γ) (y : B.carrier s)
    (original : B.evaluates ⟨source.term, originalKept⟩ e y) :
    B.evaluates ⟨compiled.toTerm, compiledKept⟩ e y := by
  cases source with
  | direct => exact original
  | inline term expands =>
    have inlineKept : Declaration.termContext term.inlineLets ≤ U := expands.symm ▸ compiledKept
    exact (B.evaluates_congr expands inlineKept compiledKept e y).1
      (B.evaluates_inlineLets ⟨term, originalKept⟩ inlineKept e y original)

/-- Each retained quantity preserves its typed input positions. -/
theorem keptQuantity_sorts (j : L.KeptQuantity U) :
    Declaration.sorts j.val.val.operation.arity.inputs ⊆ U.declarations :=
  operationInputs j.val.val.operation j.property

/-- The context inclusion keeps the same chosen quantity with its original operation tag. -/
def includeQuantity (inside : V ≤ U) (j : L.KeptQuantity V) : L.KeptQuantity U :=
  ⟨j.val, inside j.property⟩

/-- The context inclusion keeps the same required Law and its original writing. -/
def includeLaw (inside : V ≤ U) (l : L.KeptLaw V) : L.KeptLaw U :=
  ⟨l.val, inside l.property⟩

/-- Each varying marked operation comes from its original chosen declaration. -/
private theorem variableQuantity_iff (j : P.signature.Quantity) :
    Operation.quantity j ∈ QuantityDeclaration.operation '' L.quantities ↔
      QuantityDeclaration.total j ∈ L.quantities := by
  constructor
  · rintro ⟨op, chosen, eq⟩
    cases op with
    | total q => cases eq; exact chosen
    | partialOp p => cases eq
  · intro chosen
    exact ⟨.total j, chosen, rfl⟩

/-- Each varying partial operation comes from its original chosen declaration. -/
private theorem variablePartial_iff (p : P.signature.Partial) :
    Operation.partialOp p ∈ QuantityDeclaration.operation '' L.quantities ↔
      QuantityDeclaration.partialOp p ∈ L.quantities := by
  constructor
  · rintro ⟨op, chosen, eq⟩
    cases op with
    | total q => cases eq
    | partialOp q => cases eq; exact chosen
  · intro chosen
    exact ⟨.partialOp p, chosen, rfl⟩

/-- A selected argument for a partial quantity must belong to its native defined domain. -/
def fixedDomain (A : ContextStructure U)
    (selected : ∀ j : L.KeptQuantity U, Set (Assignment A.carrier j.val.val.operation.arity.inputs)) :
    (j : L.KeptQuantity U) → Set (Assignment A.carrier j.val.val.operation.arity.inputs)
  | ⟨⟨.total name, chosen⟩, keep⟩ => selected ⟨⟨.total name, chosen⟩, keep⟩
  | ⟨⟨.partialOp name, chosen⟩, keep⟩ =>
    {e | A.evaluation.domain name keep e ∧ e ∈ selected ⟨⟨.partialOp name, chosen⟩, keep⟩}

variable {k : Type u} [CommRing k]

/-- A replacement keeps the state and all native values outside the designated argument sets. -/
structure SameDeclarationState (A : ContextStructure U)
    (selected : ∀ j : L.KeptQuantity U, Set (Assignment A.carrier j.val.val.operation.arity.inputs))
    (B : RestrictedEvaluation U A.carrier) : Prop
    extends SameStateEvaluation (QuantityDeclaration.operation '' L.quantities) A.evaluation B where
  /-- Candidate outputs are actual functions on the same total and partial domains. -/
  structural : B.Structural
  /-- Native values outside the selected arguments are fixed. -/
  outside (j : L.KeptQuantity U) (input : Assignment A.carrier j.val.val.operation.arity.inputs)
    (fixed : input ∉ L.fixedDomain A selected j) (y : A.carrier j.val.val.operation.arity.output) :
    A.evaluation.graph j.val.val.operation j.property input y ↔
      B.graph j.val.val.operation j.property input y

/-- The original evaluation is itself an allowed replacement with no change of values. -/
theorem SameDeclarationState.refl (A : ContextStructure U)
    (selected : ∀ j : L.KeptQuantity U, Set (Assignment A.carrier j.val.val.operation.arity.inputs)) :
    L.SameDeclarationState A selected A.evaluation where
  structural := A.structural
  relation _ _ _ := Iff.rfl
  domain _ _ _ := Iff.rfl
  graph _ _ _ _ _ := Iff.rfl
  outside _ _ _ _ := Iff.rfl

private abbrev termGraph {X : P.signature.SortType → Type u} (B : RestrictedEvaluation U X)
    {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : U.TermIn Γ s) (e : Assignment X Γ) (y : X s) : Prop :=
  B.holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property) (Assignment.cons y e)

/-- A native representative is chosen for each scalar at each designated argument. -/
abbrev OutputRepresentation (A : ContextStructure U)
    (selected : ∀ j : L.KeptQuantity U, Set (Assignment A.carrier j.val.val.operation.arity.inputs)) :=
  (j : L.KeptQuantity U) → L.fixedDomain A selected j → k → A.carrier j.val.val.operation.arity.output

/-- An evaluation realizes scalar candidates for all quantities used by the given Law. -/
def RepresentsLaw (A : ContextStructure U)
    {selected : ∀ j : L.KeptQuantity U, Set (Assignment A.carrier j.val.val.operation.arity.inputs)}
    (output : L.OutputRepresentation (k := k) A selected)
    (l : L.KeptLaw U) (B : RestrictedEvaluation U A.carrier) : Prop :=
  ∀ (j : L.KeptQuantity U),
    Declaration.ofOperation j.val.val.operation ∈ Declaration.lawBody (P.theory.law l.val.val) →
    ∀ e : L.fixedDomain A selected j, ∃ r, B.graph j.val.val.operation j.property e.val (output j e r)

/-- Read the fixed state where the declared coefficient equations use it.
Scalar quantity candidates assign values on the selected arguments independently of the native output carriers. -/
structure Reading (A : ContextStructure U) where
  /-- Read the coefficient value of an element of a retained carrier. -/
  read : CarrierMap U A.carrier (fun _ => k)
  /-- Select the arguments designated by each quantity on its state carriers. -/
  selectedDomain (j : L.KeptQuantity U) : Set (Assignment A.carrier j.val.val.operation.arity.inputs)
  /-- Each fixed coefficient term is defined on the original state at the declared input. -/
  coefficientDefined (l : L.KeptLaw U) (a : L.UsedCoefficient l.val) (e : L.lawInput A l) :
    ∃ z, termGraph A.evaluation (L.keptCoefficient l a) e.val z
  /-- The evaluated state argument tuple of each used quantity is in its fixed domain. -/
  value (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val) :
    L.fixedDomain A selectedDomain (L.keptApplication l a)
  /-- The fixed-state argument tuple is computed from the actual source terms. -/
  argumentState (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val)
    {s : P.signature.SortType} (i : Var a.val.1.val.operation.arity.inputs s) :
    termGraph A.evaluation (L.keptTerm l a i) e.val ((value l e a).val i)

/-- Interpret the scalar equation as a native Law on candidate structures. -/
structure Interpretation (A : ContextStructure U) extends L.Reading (k := k) A where
  /-- Choose the native encoding of scalar candidate values. -/
  quantityOutput : L.OutputRepresentation (k := k) A selectedDomain
  /-- Native representatives retain their proposed scalar values. -/
  quantityOutput_read (j : L.KeptQuantity U) (e : L.fixedDomain A selectedDomain j) (r : k) :
    read _ (operationOutput j.val.val.operation j.property) (quantityOutput j e r) = r
  /-- Scalar readings distinguish the native values attained by either side on a declared input. -/
  lawRead (l : L.KeptLaw U) (e : L.lawInput A l) (B : RestrictedEvaluation U A.carrier)
    (_ : L.SameDeclarationState A selectedDomain B) (_ : L.RepresentsLaw A quantityOutput l B) :
    Set.InjOn (read _ (L.keptLaw_refs l).1)
      {y | termGraph B (L.keptLeftSource l) e.val y ∨ termGraph B (L.keptRightSource l) e.val y}
  /-- A reached arithmetic application reads as its scalar operation on the evaluated child terms. -/
  arithmeticAt (l : L.KeptLaw U) (a : L.UsedArithmetic l.val) (e : L.lawInput A l)
    (B : RestrictedEvaluation U A.carrier) (same : L.SameDeclarationState A selectedDomain B)
    (_ : L.RepresentsLaw A quantityOutput l B)
    (x : Assignment A.carrier a.val.1.profile.inputs) (y : A.carrier a.val.1.profile.output) :
    (∀ {s} (i : Var a.val.1.profile.inputs s), termGraph B (L.keptArithmeticArgument l a i) e.val (x i)) →
      a.val.1.symbol.graph ⟨A.carrier, A.omitted, B, same.structural⟩ (L.keptArithmetic l a) x y →
      a.val.1.ReadsValue ⟨A.carrier, A.omitted, B, same.structural⟩ (L.keptArithmetic l a) read x y
  /-- The scalar value read from a coefficient term at a named input is independent of the candidate. -/
  coefficientIndependent (l : L.KeptLaw U) (a : L.UsedCoefficient l.val) (e : L.lawInput A l)
    (B : RestrictedEvaluation U A.carrier) (_ : L.SameDeclarationState A selectedDomain B)
    (_ : L.RepresentsLaw A quantityOutput l B)
    (original replacement : A.carrier a.val.1) :
    termGraph A.evaluation (L.keptCoefficient l a) e.val original →
      termGraph B (L.keptCoefficient l a) e.val replacement →
      read _ (ContextStructure.termResultSupport (L.keptCoefficient l a)) replacement =
        read _ (ContextStructure.termResultSupport (L.keptCoefficient l a)) original
  /-- The original antecedent is independent of the candidate values. -/
  inputIndependent (l : L.KeptLaw U) (B : RestrictedEvaluation U A.carrier)
    (same : L.SameDeclarationState A selectedDomain B) (_ : L.RepresentsLaw A quantityOutput l B)
    (e : Assignment A.carrier (P.theory.law l.val.val).context) :
    e ∈ L.lawInput A l ↔ B.holds (P.theory.law l.val.val).input
      (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e
  /-- The already evaluated state arguments have the same values for every candidate. -/
  argumentIndependent (l : L.KeptLaw U) (B : RestrictedEvaluation U A.carrier)
    (same : L.SameDeclarationState A selectedDomain B) (_ : L.RepresentsLaw A quantityOutput l B)
    (e : L.lawInput A l) (a : L.UsedApplication l.val)
    {s : P.signature.SortType} (i : Var a.val.1.val.operation.arity.inputs s) :
    B.holds (L.keptTerm l a i).val.graph
      ((Declaration.termContext_le_iff (L.keptTerm l a i).val).1 (L.keptTerm l a i).property)
      (Assignment.cons ((value l e a).val i) e.val)

  /-- The required original terms are defined on every declared input with every candidate. -/
  definedSides (l : L.KeptLaw U) (e : L.lawInput A l) (B : RestrictedEvaluation U A.carrier)
    (same : L.SameDeclarationState A selectedDomain B) (_ : L.RepresentsLaw A quantityOutput l B) :
    (∃ y, termGraph B (L.keptLeftSource l) e.val y) ∧
    (∃ y, termGraph B (L.keptRightSource l) e.val y)


namespace Reading

variable {L} {A : ContextStructure U} (I : L.Reading (k := k) A)

/-- The fixed argument set in the retained state for a designated quantity. -/
abbrev domain (j : L.KeptQuantity U) := L.fixedDomain A I.selectedDomain j

omit [CommRing k] in
/-- The designated argument is the actual value of the original state term. -/
theorem evaluates (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val)
    {s : P.signature.SortType} (i : Var a.val.1.val.operation.arity.inputs s) :
    A.evaluates (L.keptTerm l a i) e.val ((I.value l e a).val i) :=
  I.argumentState l e a i

/-- The actual value of a fixed coefficient term at a designated Law input. -/
private def actualCoefficient (l : L.KeptLaw U) (e : L.lawInput A l)
    (a : L.UsedCoefficient l.val) : A.carrier a.val.1 :=
  (I.coefficientDefined l a e).choose

/-- Read the scalar from the coefficient term at the actual Law input. -/
def coefficientValue (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedCoefficient l.val) : k :=
  I.read a.val.1 (ContextStructure.termResultSupport (L.keptCoefficient l a)) (I.actualCoefficient l e a)

omit [CommRing k] in
/-- Evaluating the actual coefficient term gives the coefficient selected by the compiler. -/
theorem coefficientValue_eq_of_evaluates (l : L.KeptLaw U) (e : L.lawInput A l)
    (a : L.UsedCoefficient l.val) (z : A.carrier a.val.1) (held : A.evaluates (L.keptCoefficient l a) e.val z) :
    I.coefficientValue l e a = I.read a.val.1 (ContextStructure.termResultSupport (L.keptCoefficient l a)) z :=
  congrArg _ (A.evaluates_unique (L.keptCoefficient l a) e.val
    (I.coefficientDefined l a e).choose_spec held)

/-- A leaf compiles to its original coefficient value or its actual quantity coordinate. -/
private def readLeaf (l : L.KeptLaw U) (e : L.lawInput A l) :
    (a : L.UsedLeaf l.val) →
      CoefficientTerm.LeafValue k (Σ j : L.KeptQuantity U, I.domain j) a.val
  | ⟨.inl coefficient, used⟩ => I.coefficientValue l e ⟨coefficient, used⟩
  | ⟨.inr app, used⟩ => ⟨L.keptApplication l ⟨app, used⟩, I.value l e ⟨app, used⟩⟩

/-- Compile the classified coefficient expressions surviving in the context.
Native satisfaction for these expressions uses an `Interpretation`. -/
def presentation : Presentation k (Selected.readStructure A) where
  Quantity := L.KeptQuantity U
  Domain := fun j => I.domain j
  Law := L.KeptLaw U
  Input := fun l => L.lawInput A l
  left l e := (L.left l.val).compile (fun a h => I.readLeaf l e ⟨a, Or.inl h⟩)
  right l e := (L.right l.val).compile (fun a h => I.readLeaf l e ⟨a, Or.inr h⟩)

end Reading

namespace Interpretation

variable {L} {A : ContextStructure U} (I : L.Interpretation (k := k) A)

/-- The designated domain inherited from the fixed-state reading. -/
abbrev domain (j : L.KeptQuantity U) := I.toReading.domain j

/-- The scalar presentation whose equations this interpretation compares with native satisfaction. -/
abbrev presentation := I.toReading.presentation

/-- The actual restricted operations obtained by replacing the chosen quantity values.
The replacement reads native domains from the state and preserves values outside the selected arguments. -/
private def candidateOperations (q : I.presentation.Candidate k) : RestrictedStructure U where
  carrier := A.carrier
  total := A.toRestrictedStructure.total
  relation := A.toRestrictedStructure.relation
  partialDomain := A.toRestrictedStructure.partialDomain
  quantity j keep e := by
    classical
    exact if chosen : QuantityDeclaration.total j ∈ L.quantities then
      if domain : e ∈ I.selectedDomain ⟨⟨.total j, chosen⟩, keep⟩ then
        I.quantityOutput ⟨⟨.total j, chosen⟩, keep⟩ ⟨e, domain⟩
          (q ⟨⟨.total j, chosen⟩, keep⟩ ⟨e, domain⟩)
      else A.toRestrictedStructure.quantity j keep e
    else A.toRestrictedStructure.quantity j keep e
  partialValue p keep e := by
    classical
    exact if chosen : QuantityDeclaration.partialOp p ∈ L.quantities then
      if selected : e.val ∈ I.selectedDomain ⟨⟨.partialOp p, chosen⟩, keep⟩ then
        I.quantityOutput ⟨⟨.partialOp p, chosen⟩, keep⟩ ⟨e.val, e.property, selected⟩
          (q ⟨⟨.partialOp p, chosen⟩, keep⟩ ⟨e.val, e.property, selected⟩)
      else A.toRestrictedStructure.partialValue p keep e
    else A.toRestrictedStructure.partialValue p keep e

/-- Interpret the candidate in the original context using its actual quantity graphs. -/
def candidateStructure (q : I.presentation.Candidate k) : ContextStructure U where
  carrier := A.carrier
  omitted := A.omitted
  evaluation := (I.candidateOperations q).evaluation
  structural := (I.candidateOperations q).evaluation_structural

/-- Candidate replacement preserves each fixed primitive and the actual partial domains. -/
theorem candidateStructure_sameState (q : I.presentation.Candidate k) :
    L.SameDeclarationState A I.selectedDomain (I.candidateStructure q).evaluation where
  structural := (I.candidateStructure q).structural
  relation _ _ _ := Iff.rfl
  domain _ _ _ := Iff.rfl
  graph op fixed keep e y := by
    classical
    rw [← A.toRestrictedStructure_evaluation]
    change A.toRestrictedStructure.graph op keep e y ↔ (I.candidateOperations q).graph op keep e y
    cases op with
    | total f => rfl
    | quantity j =>
      simp only [RestrictedStructure.graph_quantity_iff, candidateOperations,
        dif_neg (fun chosen => fixed ((L.variableQuantity_iff j).2 chosen))]
    | partialOp p =>
      simp only [RestrictedStructure.graph_partial_iff, candidateOperations,
        dif_neg (fun chosen => fixed ((L.variablePartial_iff p).2 chosen))]
  outside j e fixed y := by
    classical
    rw [← A.toRestrictedStructure_evaluation]
    change A.toRestrictedStructure.graph j.val.val.operation j.property e y ↔
      (I.candidateOperations q).graph j.val.val.operation j.property e y
    rcases j with ⟨⟨name, chosen⟩, keep⟩
    cases name with
    | total j =>
      change e ∉ I.selectedDomain ⟨⟨.total j, chosen⟩, keep⟩ at fixed
      simp only [QuantityDeclaration.operation, RestrictedStructure.graph_quantity_iff,
        candidateOperations, dif_pos chosen, dif_neg fixed]
    | partialOp p =>
      simp only [QuantityDeclaration.operation, RestrictedStructure.graph_partial_iff]
      apply exists_congr
      intro native
      have unselected : e ∉ I.selectedDomain ⟨⟨.partialOp p, chosen⟩, keep⟩ :=
        fun selected => fixed ⟨native, selected⟩
      simp only [candidateOperations, dif_pos chosen, dif_neg unselected]

/-- At a designated argument the original quantity graph has the candidate's coefficient value. -/
theorem candidateStructure_graph (q : I.presentation.Candidate k) (j : L.KeptQuantity U) (e : I.domain j) :
    (I.candidateStructure q).evaluation.graph j.val.val.operation j.property e.val
      (I.quantityOutput j e (q j e)) := by
  classical
  rcases j with ⟨⟨j, chosen⟩, keep⟩
  cases j with
  | total j =>
    change (I.candidateOperations q).graph (.quantity j) keep e.val _
    rw [RestrictedStructure.graph_quantity_iff]
    have inputDomain : e.val ∈ I.selectedDomain ⟨⟨.total j, chosen⟩, keep⟩ := e.property
    simp only [candidateOperations, dif_pos chosen, dif_pos inputDomain]
  | partialOp p =>
    change (I.candidateOperations q).graph (.partialOp p) keep e.val _
    rw [RestrictedStructure.graph_partial_iff]
    refine ⟨e.property.1, ?_⟩
    have selected : e.val ∈ I.selectedDomain ⟨⟨.partialOp p, chosen⟩, keep⟩ := e.property.2
    simp only [candidateOperations, dif_pos chosen, dif_pos selected]

/-- Candidate structures use the specified native representatives on every selected argument. -/
theorem candidateStructure_representsLaw (q : I.presentation.Candidate k) (l : L.KeptLaw U) :
    L.RepresentsLaw A I.quantityOutput l (I.candidateStructure q).evaluation :=
  fun j _ e => ⟨q j e, I.candidateStructure_graph q j e⟩

private theorem compiledValue_read (l : L.KeptLaw U) (e : L.lawInput A l)
    (q : I.presentation.Candidate k)
    (t : CoefficientTerm L.quantities (P.theory.law l.val.val).context (L.valueSort l.val))
    (keep : Selected.termReferences t.toTerm ⊆ U.declarations)
    (used : t.leaves ⊆ (L.left l.val).leaves ∪ (L.right l.val).leaves)
    (arithmetic : t.arithmeticApplications ⊆
      (L.left l.val).arithmeticApplications ∪ (L.right l.val).arithmeticApplications)
    (supported : Declaration.termContext t.toTerm ≤ U) (y : A.carrier (L.valueSort l.val))
    (evaluated : (I.candidateStructure q).evaluates ⟨t.toTerm, supported⟩ e.val y) :
    I.read _ (L.keptLaw_refs l).1 y =
      (t.compile (fun a h => I.toReading.readLeaf l e ⟨a, used h⟩)).eval (fun x => q x.1 x.2) := by
  let B := I.candidateStructure q
  have fixed := I.candidateStructure_sameState q
  have represents := I.candidateStructure_representsLaw q l
  apply t.evaluates_read B I.read e.val keep (L.keptLaw_refs l).1 _ _ ?_ ?_ supported y evaluated
  · intro a h hTerm z value
    cases a with
    | inl coefficient =>
      let leaf : L.UsedCoefficient l.val := ⟨coefficient, used h⟩
      exact I.coefficientIndependent l leaf e B.evaluation fixed represents
        (I.toReading.actualCoefficient l e leaf) z (I.coefficientDefined l leaf e).choose_spec value
    | inr application =>
      let a : L.UsedApplication l.val := ⟨application, used h⟩
      let j := L.keptApplication l a
      let input := I.value l e a
      let op := application.1.val.operation
      have keepOp := j.property
      obtain ⟨args, each, edge⟩ := (B.evaluates_app_iff op (fun i => application.2 i)
        ⟨_, hTerm⟩ rfl e.val keepOp z).1 value
      have agreed : args = input.val := by
        apply Assignment.ext
        intro s i
        obtain ⟨_, witness⟩ := each i
        exact B.evaluates_unique (L.keptTerm l a i) e.val witness
          (I.argumentIndependent l B.evaluation fixed represents e a i)
      have same := B.graph_rightUnique op keepOp (agreed ▸ edge) (I.candidateStructure_graph q j input)
      exact (congrArg (I.read _ (operationOutput op keepOp)) same).trans (I.quantityOutput_read j input _)
  · intro a h x y each edge
    let applied : L.UsedArithmetic l.val := ⟨a, arithmetic h⟩
    refine I.arithmeticAt l applied e B.evaluation fixed represents x y ?_ edge
    intro _ i
    obtain ⟨_, holds⟩ := each i
    exact holds

/-- On the original guard, the declared conclusion holds exactly when its compiled residual is zero. -/
theorem candidate_conclusion_iff (l : L.KeptLaw U) (e : L.lawInput A l)
    (q : I.presentation.Candidate k) :
    (I.candidateStructure q).evaluation.holds (P.theory.law l.val.val).conclusion
      (lawConclusionSupport (Declaration.lawBody_subset_of_mem l.property)) e.val ↔
    I.presentation.evaluate q (I.presentation.residual l e) = 0 := by
  let B := I.candidateStructure q
  let w := L.writing l.val
  have fixed := I.candidateStructure_sameState q
  have represents := I.candidateStructure_representsLaw q l
  have guard := (I.inputIndependent l B.evaluation fixed represents e.val).1 e.property
  obtain ⟨⟨x, originalLeft⟩, ⟨y, originalRight⟩⟩ := I.definedSides l e B.evaluation fixed represents
  have leftKept := Selected.termContext_le_of_references (L.left l.val).toTerm
    (L.keptLaw_sorts l) (L.keptLaw_refs l).1 (L.keptLaw_refs l).2.1
  have rightKept := Selected.termContext_le_of_references (L.right l.val).toTerm
    (L.keptLaw_sorts l) (L.keptLaw_refs l).1 (L.keptLaw_refs l).2.2
  have compared := B.holds_written_iff_of_evaluates w (Declaration.lawBody_subset_of_mem l.property)
    e.val guard originalLeft originalRight
  have leftValue := I.compiledValue_read l e q _ (L.keptLaw_refs l).2.1 Set.subset_union_left Set.subset_union_left
    leftKept x (L.evaluates_compiledSide B (L.leftSource l.val) (L.keptLeftSource l).property leftKept e.val x originalLeft)
  have rightValue := I.compiledValue_read l e q _ (L.keptLaw_refs l).2.2 Set.subset_union_right Set.subset_union_right
    rightKept y (L.evaluates_compiledSide B (L.rightSource l.val) (L.keptRightSource l).property rightKept e.val y originalRight)
  change I.read _ (L.keptLaw_refs l).1 x = (I.presentation.left l e).eval (fun a => q a.1 a.2) at leftValue
  change I.read _ (L.keptLaw_refs l).1 y = (I.presentation.right l e).eval (fun a => q a.1 a.2) at rightValue
  have readsEq : I.read _ (L.keptLaw_refs l).1 x = I.read _ (L.keptLaw_refs l).1 y ↔ x = y :=
    ⟨I.lawRead l e B.evaluation fixed represents (Or.inl originalLeft) (Or.inr originalRight), congrArg _⟩
  rw [I.presentation.evaluate_residual, sub_eq_zero, ← leftValue, ← rightValue]
  exact compared.trans readsEq.symm

/-- The actual original Law of each retained declaration is satisfied exactly when all its
compiled residuals vanish for the same candidate. -/
theorem candidate_satisfies_iff (l : L.KeptLaw U) (q : I.presentation.Candidate k) :
    (I.candidateStructure q).evaluation.satisfies (P.theory.law l.val.val)
      (Declaration.lawBody_subset_of_mem l.property) ↔
    ∀ e : L.lawInput A l, I.presentation.evaluate q (I.presentation.residual l e) = 0 := by
  let B := I.candidateStructure q
  have fixed := I.candidateStructure_sameState q
  have represents := I.candidateStructure_representsLaw q l
  constructor
  · intro satisfies e
    exact (I.candidate_conclusion_iff l e q).1
      (satisfies e.val ((I.inputIndependent l B.evaluation fixed represents e.val).1 e.property))
  · intro residuals e inputHeld
    let original : L.lawInput A l := ⟨e, (I.inputIndependent l B.evaluation fixed represents e).2 inputHeld⟩
    exact (I.candidate_conclusion_iff l original q).2 (residuals original)

/-- Native points of the compiled presentation obey exactly the original retained Laws. -/
theorem candidate_holds_iff (q : I.presentation.Candidate k) :
    I.presentation.Holds q ↔ ∀ l : L.KeptLaw U,
      (I.candidateStructure q).evaluation.satisfies (P.theory.law l.val.val)
        (Declaration.lawBody_subset_of_mem l.property) := by
  constructor
  · intro holds l
    apply (I.candidate_satisfies_iff l q).2
    intro e
    rw [I.presentation.evaluate_residual, sub_eq_zero]
    exact holds l e
  · intro satisfies l e
    have h := (I.candidate_satisfies_iff l q).1 (satisfies l) e
    rwa [I.presentation.evaluate_residual, sub_eq_zero] at h

end Interpretation

namespace Reading

variable {L} {A : ContextStructure U} (I : L.Reading (k := k) A)

variable (inside : V ≤ U)

/-- The retained carriers identify the same scalar value before and after forgetting. -/
private def restrictRead : CarrierMap V (A.restrict inside).carrier (fun _ => k) :=
  fun s keep x => I.read s (inside keep) (selectedMap V A.carrier s keep x)

/-- Choose the corresponding argument set on the retained state carriers. -/
private def restrictSelectedDomain (j : L.KeptQuantity V) :
    Set (Assignment (A.restrict inside).carrier j.val.val.operation.arity.inputs) :=
  (A.restrictAssignmentEquiv inside (L.keptQuantity_sorts j)) ⁻¹'
    I.selectedDomain (L.includeQuantity inside j)

omit [CommRing k] in
/-- Selected arguments and native partial domains restrict on the same carrier identification. -/
private theorem restrict_domain_iff (j : L.KeptQuantity V)
    (e : Assignment (A.restrict inside).carrier j.val.val.operation.arity.inputs) :
    e ∈ L.fixedDomain (A.restrict inside) (I.restrictSelectedDomain inside) j ↔
      A.restrictAssignmentEquiv inside (L.keptQuantity_sorts j) e ∈ I.domain (L.includeQuantity inside j) := by
  rcases j with ⟨⟨j, chosen⟩, keep⟩
  cases j <;> rfl

/-- The original antecedent has the same truth on the corresponding ambient assignment. -/
theorem restrict_lawInput_iff (l : L.KeptLaw V)
    (e : Assignment (A.restrict inside).carrier (P.theory.law l.val.val).context) :
    e ∈ L.lawInput (A.restrict inside) l ↔
      mapAssignment (selectedMap V A.carrier) (L.keptLaw_sorts l) e ∈ L.lawInput A (L.includeLaw inside l) :=
  A.restrict_holds_iff inside _ _ e

/-- The image of a retained input in the original antecedent's input set. -/
def includeInput (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l) :
    L.lawInput A (L.includeLaw inside l) :=
  ⟨A.restrictAssignmentEquiv inside (L.keptLaw_sorts l) e.val,
    (restrict_lawInput_iff inside l e.val).1 e.property⟩

/-- Return the original evaluated tuple through the actual reduct's carrier identification. -/
private def restrictValue (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l)
    (a : L.UsedApplication l.val) :
    L.fixedDomain (A.restrict inside) (I.restrictSelectedDomain inside) (L.keptApplication l a) := by
  let original := I.value (L.includeLaw inside l) (includeInput inside l e) a
  let reads := A.restrictAssignmentEquiv inside (L.keptQuantity_sorts (L.keptApplication l a))
  refine ⟨reads.symm original.val, (I.restrict_domain_iff inside _ _).2 ?_⟩
  change reads (reads.symm original.val) ∈ I.domain (L.keptApplication (L.includeLaw inside l) a)
  rw [reads.apply_symm_apply]
  exact original.property

private def retainedCarrierEquiv (s : P.signature.SortType) (keep : Declaration.sort s ∈ V.declarations) :
    (A.restrict inside).carrier s ≃ A.carrier s :=
  Equiv.ofBijective (selectedMap V A.carrier s keep) (selectedMap_bijective A.carrier s keep)

/-- Restrict the fixed-state reading to the actual declaration reduct. -/
def restrict : L.Reading (k := k) (A.restrict inside) where
  read := I.restrictRead inside
  selectedDomain := I.restrictSelectedDomain inside
  value := I.restrictValue inside
  coefficientDefined l a e := by
    obtain ⟨z, held⟩ := I.coefficientDefined (L.includeLaw inside l) a (includeInput inside l e)
    let t := L.keptCoefficient l a
    let E := retainedCarrierEquiv (A := A) inside _ (ContextStructure.termResultSupport t)
    refine ⟨E.symm z, (A.restrict_evaluates_iff inside t e.val (E.symm z)).2 ?_⟩
    change A.evaluates ⟨t.val, t.property.trans inside⟩ (includeInput inside l e).val (E (E.symm z))
    rw [E.apply_symm_apply]
    exact held
  argumentState l e a := by
    intro s i
    let input := includeInput inside l e
    let t := L.keptTerm l a i
    let v := (I.restrictValue inside l e a).val
    let original := (I.value (L.includeLaw inside l) input a).val
    have atIndex := congrArg (fun x : Assignment A.carrier _ => x i)
      ((A.restrictAssignmentEquiv inside (L.keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply original)
    apply (A.restrict_evaluates_iff inside t e.val (v i)).2
    change A.evaluates ⟨t.val, t.property.trans inside⟩ input.val
      ((A.restrictAssignmentEquiv inside (L.keptQuantity_sorts (L.keptApplication l a))) v i)
    change ((A.restrictAssignmentEquiv inside (L.keptQuantity_sorts (L.keptApplication l a))) v i) =
      original i at atIndex
    rw [atIndex]
    exact I.argumentState (L.includeLaw inside l) input a i

end Reading

namespace Interpretation

open Reading

variable {L} {A : ContextStructure U} (I : L.Interpretation (k := k) A)
variable (inside : V ≤ U)

private def restoreEvaluation (B : RestrictedEvaluation V (A.restrict inside).carrier) :
    RestrictedEvaluation V A.carrier :=
  B.pullback (le_refl V) (fun s keep => (retainedCarrierEquiv (A := A) inside s keep).symm)

private theorem restoreEvaluation_cancel (B : RestrictedEvaluation V (A.restrict inside).carrier) :
    (restoreEvaluation (A := A) inside B).pullback (le_refl V) (selectedMap V A.carrier) = B := by
  rw [restoreEvaluation, RestrictedEvaluation.pullback_comp]
  refine (RestrictedEvaluation.pullback_congr _ _ ?_).trans B.pullback_id
  intro s keep x
  exact (retainedCarrierEquiv (A := A) inside s keep).symm_apply_apply x

private theorem restoreEvaluation_original :
    restoreEvaluation (A := A) inside (A.restrict inside).evaluation =
      A.evaluation.pullback inside (fun _ _ x => x) := by
  rw [restoreEvaluation, ContextStructure.restrict_evaluation, RestrictedEvaluation.pullback_comp]
  apply RestrictedEvaluation.pullback_congr
  intro s keep x
  exact (retainedCarrierEquiv (A := A) inside s keep).apply_symm_apply x

private def extendEvaluation (B : RestrictedEvaluation V (A.restrict inside).carrier) :
    RestrictedEvaluation U A.carrier :=
  A.evaluation.replaceRetainedGraphs (restoreEvaluation (A := A) inside B)

private theorem restoreEvaluation_domain
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (same : L.SameDeclarationState (A.restrict inside) (I.toReading.restrictSelectedDomain inside) B)
    (p : P.signature.Partial) (keep : Declaration.partialOp p ∈ V.declarations)
    (e : Assignment A.carrier (P.signature.partialArity p).inputs) :
    (restoreEvaluation (A := A) inside B).domain p keep e ↔ A.evaluation.domain p (inside keep) e := by
  have inOriginal := (same.domain p keep
    (mapAssignment (fun s h => (retainedCarrierEquiv (A := A) inside s h).symm)
      (operationInputs (.partialOp p) keep) e)).symm
  change (restoreEvaluation (A := A) inside B).domain p keep e ↔
    (restoreEvaluation (A := A) inside (A.restrict inside).evaluation).domain p keep e at inOriginal
  rw [restoreEvaluation_original (A := A) inside, RestrictedEvaluation.pullback_domain, mapAssignment_id] at inOriginal
  exact inOriginal

private theorem restoreEvaluation_graph
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ V.declarations)
    (e : Assignment A.carrier op.arity.inputs) (y : A.carrier op.arity.output)
    (agrees : let f : CarrierMap V A.carrier (A.restrict inside).carrier :=
      fun s h => (retainedCarrierEquiv (A := A) inside s h).symm
      (A.restrict inside).evaluation.graph op keep (mapAssignment f (operationInputs op keep) e)
        (f _ (operationOutput op keep) y) ↔
      B.graph op keep (mapAssignment f (operationInputs op keep) e) (f _ (operationOutput op keep) y)) :
    A.evaluation.graph op (inside keep) e y ↔ (restoreEvaluation (A := A) inside B).graph op keep e y := by
  change (restoreEvaluation (A := A) inside (A.restrict inside).evaluation).graph op keep e y ↔
    (restoreEvaluation (A := A) inside B).graph op keep e y at agrees
  rw [restoreEvaluation_original (A := A) inside, RestrictedEvaluation.pullback_graph, mapAssignment_id] at agrees
  exact agrees

/-- A structural replacement in the reduct extends by leaving all forgotten operations fixed. -/
private theorem extendEvaluation_sameState
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (same : L.SameDeclarationState (A.restrict inside) (I.toReading.restrictSelectedDomain inside) B) :
    L.SameDeclarationState A I.selectedDomain (extendEvaluation (A := A) inside B) where
  structural := A.evaluation.replaceRetainedGraphs_structural _ inside A.structural
    (B.structural_pullback (le_refl V) _ (fun s keep =>
      (retainedCarrierEquiv (A := A) inside s keep).symm.bijective) same.structural)
    (I.restoreEvaluation_domain inside B same)
  relation _ _ _ := Iff.rfl
  domain _ _ _ := Iff.rfl
  graph op fixed keep e y := by
    classical
    by_cases retained : Declaration.ofOperation op ∈ V.declarations
    · apply (restoreEvaluation_graph inside B op retained e y (same.graph op fixed retained _ _)).trans
      exact (A.evaluation.replaceRetainedGraphs_graph _ op keep retained e y).symm
    · exact (A.evaluation.replaceRetainedGraphs_graph_of_omitted _ op keep retained e y).symm
  outside j e fixed y := by
    classical
    let op := j.val.val.operation
    by_cases retained : Declaration.ofOperation op ∈ V.declarations
    · let localName : L.KeptQuantity V := ⟨j.val, retained⟩
      let localArgs := mapAssignment (fun s keep => (retainedCarrierEquiv (A := A) inside s keep).symm)
        (operationInputs op retained) e
      have localFixed : localArgs ∉ L.fixedDomain (A.restrict inside) (I.toReading.restrictSelectedDomain inside) localName := by
        intro h
        apply fixed
        have mapped := (I.toReading.restrict_domain_iff inside localName localArgs).1 h
        change mapAssignment (selectedMap V A.carrier) (operationInputs op retained) localArgs ∈ I.domain j at mapped
        have argsRestored : mapAssignment (selectedMap V A.carrier) (operationInputs op retained)
            localArgs = e := by
          apply Assignment.ext
          intro s i
          exact (retainedCarrierEquiv (A := A) inside s
            (varKept (operationInputs op retained) i)).apply_symm_apply (e i)
        exact argsRestored ▸ mapped
      have retainedAgrees := restoreEvaluation_graph inside B op retained e y
        (same.outside localName localArgs localFixed _)
      exact retainedAgrees.trans (A.evaluation.replaceRetainedGraphs_graph _ op j.property retained e y).symm
    · exact (A.evaluation.replaceRetainedGraphs_graph_of_omitted _ op j.property retained e y).symm

/-- Reading the extended replacement on the smaller context recovers its input evaluation. -/
private theorem extendEvaluation_restrict
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (same : L.SameDeclarationState (A.restrict inside) (I.toReading.restrictSelectedDomain inside) B) :
    (extendEvaluation (A := A) inside B).pullback inside (selectedMap V A.carrier) = B := by
  apply RestrictedEvaluation.ext
  · exact same.relation
  · exact same.domain
  · intro op keep e y
    let image := mapAssignment (selectedMap V A.carrier) (operationInputs op keep) e
    let result := selectedMap V A.carrier _ (operationOutput op keep) y
    have comparison := A.evaluation.replaceRetainedGraphs_graph
      (restoreEvaluation (A := A) inside B) op (inside keep) keep image result
    have cancel := restoreEvaluation_cancel (A := A) inside B
    change _ ↔ (B.graph op keep e y)
    refine comparison.trans ?_
    change ((restoreEvaluation (A := A) inside B).pullback
      (le_refl V) (selectedMap V A.carrier)).graph op keep e y ↔ _
    rw [cancel]

private theorem termDefined_restrict
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (same : L.SameDeclarationState (A.restrict inside) (I.toReading.restrictSelectedDomain inside) B)
    {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : V.TermIn Γ s) (e : Assignment (A.restrict inside).carrier Γ)
    (original : ∃ y, termGraph (extendEvaluation (A := A) inside B) ⟨t.val, t.property.trans inside⟩
      (mapAssignment (selectedMap V A.carrier) ((tailSortsSubset s Γ).trans (ContextStructure.termSortSupport t)) e) y) :
    ∃ y, termGraph B t e y := by
  obtain ⟨y, held⟩ := original
  let keep := (Declaration.termContext_le_iff t.val).1 t.property
  have hs : Declaration.sort s ∈ V.declarations :=
    ContextStructure.termSortSupport t (Declaration.sort_mem_sorts (by simp))
  let selected := retainedCarrierEquiv (A := A) inside s hs
  let localResult := selected.symm y
  let extended := extendEvaluation (A := A) inside B
  refine ⟨localResult, ?_⟩
  have transfer := extended.holds_pullback_iff inside (selectedMap V A.carrier)
    (selectedMap_bijective A.carrier) t.val.graph keep (Assignment.cons localResult e)
  rw [I.extendEvaluation_restrict inside B same] at transfer
  apply transfer.2
  have witness :
      mapAssignment (selectedMap V A.carrier) ((Declaration.sorts_subset_formulaSupport _).trans keep)
        (Assignment.cons localResult e) =
      Assignment.cons y (mapAssignment (selectedMap V A.carrier)
        ((tailSortsSubset s Γ).trans (ContextStructure.termSortSupport t)) e) := by
    apply Assignment.ext
    intro s i
    cases i with
    | here => exact selected.apply_symm_apply y
    | there i => rfl
  rw [witness]
  exact held

/-- Passing to the extended evaluation preserves the graph of every supported term. -/
private theorem termGraph_extend_iff
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (same : L.SameDeclarationState (A.restrict inside) (I.toReading.restrictSelectedDomain inside) B)
    {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : V.TermIn Γ s) (e : Assignment (A.restrict inside).carrier Γ)
    (y : (A.restrict inside).carrier s)
    (keepΓ : Declaration.sorts Γ ⊆ V.declarations) (keepS : Declaration.sort s ∈ V.declarations) :
    termGraph B t e y ↔ termGraph (extendEvaluation (A := A) inside B) ⟨t.val, t.property.trans inside⟩
      (mapAssignment (selectedMap V A.carrier) keepΓ e) (selectedMap V A.carrier s keepS y) := by
  let keep := (Declaration.termContext_le_iff t.val).1 t.property
  have transfer := (extendEvaluation (A := A) inside B).holds_pullback_iff inside
    (selectedMap V A.carrier) (selectedMap_bijective A.carrier) t.val.graph keep (Assignment.cons y e)
  rw [I.extendEvaluation_restrict inside B same] at transfer
  rw [mapAssignment_cons (selectedMap V A.carrier) keepS keepΓ y e] at transfer
  exact transfer

/-- Identify the ambient coordinate corresponding to a designated argument of the reduct. -/
def includeArgument (j : L.KeptQuantity V)
    (e : L.fixedDomain (A.restrict inside) (I.toReading.restrictSelectedDomain inside) j) :
    I.domain (L.includeQuantity inside j) :=
  ⟨A.restrictAssignmentEquiv inside (L.keptQuantity_sorts j) e.val,
    (I.toReading.restrict_domain_iff inside j e.val).1 e.property⟩

/-- Restriction transports the chosen output through the actual carrier identification. -/
private def restrictOutput :
    L.OutputRepresentation (k := k) (A.restrict inside) (I.toReading.restrictSelectedDomain inside) :=
  fun j e r =>
    (retainedCarrierEquiv (A := A) inside _ (operationOutput j.val.val.operation j.property)).symm
      (I.quantityOutput (L.includeQuantity inside j) (I.includeArgument inside j e) r)

/-- A Law in the reduct retains every graph it uses, so extension preserves its candidate representatives. -/
private theorem extendEvaluation_representsLaw (l : L.KeptLaw V)
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (same : L.SameDeclarationState (A.restrict inside) (I.toReading.restrictSelectedDomain inside) B)
    (represents : L.RepresentsLaw (A.restrict inside) (I.restrictOutput inside) l B) :
    L.RepresentsLaw A I.quantityOutput (L.includeLaw inside l) (extendEvaluation (A := A) inside B) := by
  intro j relevant e
  let op := j.val.val.operation
  have keep : Declaration.ofOperation op ∈ V.declarations :=
    Declaration.lawBody_subset_of_mem l.property relevant
  let localName : L.KeptQuantity V := ⟨j.val, keep⟩
  let readArgs := A.restrictAssignmentEquiv inside (L.keptQuantity_sorts localName)
  let localArg : L.fixedDomain (A.restrict inside) (I.toReading.restrictSelectedDomain inside) localName :=
    ⟨readArgs.symm e.val, (I.toReading.restrict_domain_iff inside localName _).2 (by
      change readArgs (readArgs.symm e.val) ∈ I.domain j
      rw [readArgs.apply_symm_apply]
      exact e.property)⟩
  obtain ⟨r, graph⟩ := represents localName relevant localArg
  let E := retainedCarrierEquiv (A := A) inside op.arity.output (operationOutput op keep)
  have sameInput : I.includeArgument inside localName localArg = e :=
    Subtype.ext (readArgs.apply_symm_apply e.val)
  refine ⟨r, ?_⟩
  change B.graph op keep localArg.val (E.symm (I.quantityOutput j (I.includeArgument inside localName localArg) r)) at graph
  rw [← I.extendEvaluation_restrict inside B same, RestrictedEvaluation.pullback_graph] at graph
  change (extendEvaluation (A := A) inside B).graph op j.property (readArgs (readArgs.symm e.val))
    (E (E.symm (I.quantityOutput j (I.includeArgument inside localName localArg) r))) at graph
  rw [E.apply_symm_apply, sameInput, readArgs.apply_symm_apply] at graph
  exact graph

/-- The actual reduct retains the coefficient meanings and fixed-state evaluations of the original Laws. -/
def restrict : L.Interpretation (k := k) (A.restrict inside) where
  toReading := I.toReading.restrict inside
  quantityOutput := I.restrictOutput inside
  quantityOutput_read j e r := by
    let E := retainedCarrierEquiv (A := A) inside _ (operationOutput j.val.val.operation j.property)
    let n := I.quantityOutput (L.includeQuantity inside j) (I.includeArgument inside j e) r
    change I.read _ (inside (operationOutput j.val.val.operation j.property)) (E (E.symm n)) = r
    rw [E.apply_symm_apply]
    exact I.quantityOutput_read (L.includeQuantity inside j) (I.includeArgument inside j e) r
  lawRead l e B same represents := by
    intro x hx y hy agrees
    let keepS := (L.keptLaw_refs l).1
    let keepΓ := L.keptLaw_sorts l
    have reached (z : (A.restrict inside).carrier (L.valueSort l.val))
        (edge : termGraph B (L.keptLeftSource l) e.val z ∨ termGraph B (L.keptRightSource l) e.val z) :
        termGraph (extendEvaluation (A := A) inside B) (L.keptLeftSource (L.includeLaw inside l))
            (includeInput inside l e).val (selectedMap V A.carrier _ keepS z) ∨
          termGraph (extendEvaluation (A := A) inside B) (L.keptRightSource (L.includeLaw inside l))
            (includeInput inside l e).val (selectedMap V A.carrier _ keepS z) :=
      edge.imp
        (I.termGraph_extend_iff inside B same (L.keptLeftSource l) e.val z keepΓ keepS).1
        (I.termGraph_extend_iff inside B same (L.keptRightSource l) e.val z keepΓ keepS).1
    apply (selectedMap_bijective A.carrier _ keepS).1
    exact I.lawRead (L.includeLaw inside l) (includeInput inside l e) (extendEvaluation (A := A) inside B)
      (I.extendEvaluation_sameState inside B same)
      (I.extendEvaluation_representsLaw inside l B same represents) (reached x hx) (reached y hy) agrees
  arithmeticAt l a e B same represents x y each edge := by
    let extended := extendEvaluation (A := A) inside B
    let ambientState := I.extendEvaluation_sameState inside B same
    let ambientCandidate : ContextStructure U := ⟨A.carrier, A.omitted, extended, ambientState.structural⟩
    let originalInput := includeInput inside l e
    let op := a.val.1
    let kept := L.keptArithmetic l a
    let keepInputs := op.symbol.keepsInputs kept
    let keepResult := op.symbol.keepsResult kept
    let x' := mapAssignment (selectedMap V A.carrier) keepInputs x
    let y' := selectedMap V A.carrier _ keepResult y
    have edges := op.symbol.graph_restrict_iff ambientCandidate inside kept x y
    have reduced : (ambientCandidate.restrict inside).evaluation = B := I.extendEvaluation_restrict inside B same
    have edge' : op.symbol.graph ambientCandidate (inside kept) x' y' := by
      apply edges.1
      simpa only [CoefficientSymbol.graph, reduced] using edge
    have each' : ∀ {s} (i : Var op.profile.inputs s),
        termGraph extended (L.keptArithmeticArgument (L.includeLaw inside l) a i) originalInput.val (x' i) := by
      intro s i
      let t := L.keptArithmeticArgument l a i
      let keep := (Declaration.termContext_le_iff t.val).1 t.property
      have transfer := extended.holds_pullback_iff inside (selectedMap V A.carrier)
        (selectedMap_bijective A.carrier) t.val.graph keep (Assignment.cons (x i) e.val)
      rw [I.extendEvaluation_restrict inside B same] at transfer
      have transport :=
        mapAssignment_cons (selectedMap V A.carrier) (varKept keepInputs i) (L.keptLaw_sorts l) (x i) e.val
      have result := transfer.1 (each i)
      rw [transport] at result
      exact result
    have held := I.arithmeticAt (L.includeLaw inside l) a originalInput extended ambientState
      (I.extendEvaluation_representsLaw inside l B same represents) x' y' each' edge'
    unfold ArithmeticOperation.ReadsValue at held ⊢
    change I.read _ (inside keepResult) y' = op.scalar (mapAssignment (I.toReading.restrictRead inside) keepInputs x)
    exact held.trans (congrArg op.scalar
      (mapAssignment_comp (selectedMap V A.carrier) I.read inside keepInputs x))
  coefficientIndependent l a e B same represents x y original replacement := by
    let t := L.keptCoefficient l a
    let keepΓ := L.keptLaw_sorts l
    let keepS := ContextStructure.termResultSupport t
    have hx := (A.restrict_evaluates_iff inside t e.val x).1 original
    have hy := (I.termGraph_extend_iff inside B same t e.val y keepΓ keepS).1 replacement
    exact I.coefficientIndependent (L.includeLaw inside l) a (includeInput inside l e)
      (extendEvaluation (A := A) inside B) (I.extendEvaluation_sameState inside B same)
      (I.extendEvaluation_representsLaw inside l B same represents) (selectedMap V A.carrier _ keepS x) (selectedMap V A.carrier _ keepS y) hx hy
  inputIndependent l B same represents e := by
    let extended := extendEvaluation (A := A) inside B
    let e' := mapAssignment (selectedMap V A.carrier) (L.keptLaw_sorts l) e
    have independent := I.inputIndependent (L.includeLaw inside l) extended
      (I.extendEvaluation_sameState inside B same) (I.extendEvaluation_representsLaw inside l B same represents) e'
    refine (restrict_lawInput_iff inside l e).trans (independent.trans ?_)
    have transfer := extended.holds_pullback_iff inside (selectedMap V A.carrier)
      (selectedMap_bijective A.carrier) _ (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e
    rw [I.extendEvaluation_restrict inside B same] at transfer
    exact transfer.symm
  argumentIndependent l B same represents e a := by
    intro s i
    let extended := extendEvaluation (A := A) inside B
    let originalInput := includeInput inside l e
    let originalValue := I.value (L.includeLaw inside l) originalInput a
    let term := L.keptTerm l a i
    let localValue := (I.toReading.restrictValue inside l e a).val i
    let witness := Assignment.cons localValue e.val
    let keep := (Declaration.termContext_le_iff term.val).1 term.property
    have preserved := I.argumentIndependent (L.includeLaw inside l) extended
      (I.extendEvaluation_sameState inside B same) (I.extendEvaluation_representsLaw inside l B same represents)
      originalInput a i
    have transfer := extended.holds_pullback_iff inside (selectedMap V A.carrier)
      (selectedMap_bijective A.carrier) term.val.graph keep witness
    rw [I.extendEvaluation_restrict inside B same] at transfer
    apply transfer.2
    have sameValue := (A.restrictAssignmentEquiv inside (L.keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply originalValue.val
    have atIndex := congrArg (fun x : Assignment A.carrier _ => x i) sameValue
    have witnessMapped :
        mapAssignment (selectedMap V A.carrier) ((Declaration.sorts_subset_formulaSupport _).trans keep) witness =
          Assignment.cons (originalValue.val i) originalInput.val := by
      apply Assignment.ext
      intro t j
      cases j with
      | here => exact atIndex
      | there j => rfl
    rw [witnessMapped]
    exact preserved

  definedSides l e B same represents := by
    let extended := extendEvaluation (A := A) inside B
    have old := I.definedSides (L.includeLaw inside l) (includeInput inside l e) extended
      (I.extendEvaluation_sameState inside B same) (I.extendEvaluation_representsLaw inside l B same represents)
    exact ⟨I.termDefined_restrict inside B same (L.keptLeftSource l) e.val old.1,
      I.termDefined_restrict inside B same (L.keptRightSource l) e.val old.2⟩

/-- Restricting an interpretation preserves the actual native representative of every scalar. -/
theorem quantityOutput_restrict (j : L.KeptQuantity V)
    (e : (I.restrict inside).domain j) (r : k) :
    selectedMap V A.carrier _ (operationOutput j.val.val.operation j.property)
        ((I.restrict inside).quantityOutput j e r) =
      I.quantityOutput (L.includeQuantity inside j) (I.includeArgument inside j e) r :=
  (retainedCarrierEquiv (A := A) inside _ (operationOutput j.val.val.operation j.property)).apply_symm_apply _

end Interpretation

namespace Reading

variable {L} {A : ContextStructure U} (I : L.Reading (k := k) A)
variable (inside : V ≤ U)

/-- Read a retained quantity and its designated argument in the ambient context. -/
private def declarationQuantityMap : QuantityMap (I.restrict inside).presentation I.presentation where
  name := L.includeQuantity inside
  argument j x := ⟨A.restrictAssignmentEquiv inside (L.keptQuantity_sorts j) x.val,
    (I.restrict_domain_iff inside j x.val).1 x.property⟩

omit [CommRing k] in
/-- Restricting reads the same actual coefficient on the corresponding Law input. -/
theorem coefficientValue_restrict (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l)
    (a : L.UsedCoefficient l.val) :
    (I.restrict inside).coefficientValue l e a = I.coefficientValue (L.includeLaw inside l) (includeInput inside l e) a := by
  let t := L.keptCoefficient l a
  let z := (I.restrict inside).actualCoefficient l e a
  have mapped := (A.restrict_evaluates_iff inside t e.val z).1
    ((I.restrict inside).coefficientDefined l a e).choose_spec
  exact (I.coefficientValue_eq_of_evaluates (L.includeLaw inside l) (includeInput inside l e)
    a (selectedMap V A.carrier _ (ContextStructure.termResultSupport t) z) mapped).symm

omit [CommRing k] in
/-- The declaration comparison sends each evaluated argument to the original one. -/
private theorem declarationCoordinate (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l)
    (a : L.UsedApplication l.val) :
    (I.declarationQuantityMap inside).coordinate ⟨L.keptApplication l a, I.restrictValue inside l e a⟩ =
      ⟨L.keptApplication (L.includeLaw inside l) a,
        I.value (L.includeLaw inside l) (includeInput inside l e) a⟩ := by
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  exact (A.restrictAssignmentEquiv inside (L.keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply _

omit [CommRing k] in
/-- Reading a compiled leaf commutes with the comparison of declaration contexts. -/
private theorem declarationReadLeaf (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l)
    (a : L.UsedLeaf l.val) :
    CoefficientTerm.mapLeafValue (I.declarationQuantityMap inside).coordinate a.val
      ((I.restrict inside).readLeaf l e a) =
    I.readLeaf (L.includeLaw inside l) (includeInput inside l e) a := by
  rcases a with ⟨literal | app, used⟩
  · exact I.coefficientValue_restrict inside l e ⟨literal, used⟩
  · exact I.declarationCoordinate inside l e ⟨app, used⟩

/-- The actual context inclusion induces a comparison of the original retained scalar equations. -/
private def declarationLawMap : LawMap (I.restrict inside).presentation I.presentation where
  toQuantityMap := I.declarationQuantityMap inside
  law := L.includeLaw inside
  input := fun l e => includeInput (A := A) inside l e
  left l e := by
    change ((L.left l.val).compile (fun a h => (I.restrict inside).readLeaf l e ⟨a, Or.inl h⟩)).rename
      (I.declarationQuantityMap inside).coordinate = _
    rw [CoefficientTerm.rename_compile]
    congr 1
    funext a h
    exact I.declarationReadLeaf inside l e ⟨a, Or.inl h⟩
  right l e := by
    change ((L.right l.val).compile (fun a h => (I.restrict inside).readLeaf l e ⟨a, Or.inr h⟩)).rename
      (I.declarationQuantityMap inside).coordinate = _
    rw [CoefficientTerm.rename_compile]
    congr 1
    funext a h
    exact I.declarationReadLeaf inside l e ⟨a, Or.inr h⟩

/-- Declaration restriction along the Chapter 3 context inclusion commutes with changing coefficients. -/
private theorem declarationLawMap_baseChange (R : Type u) [CommRing R] [Algebra k R] :
    let F := (I.restrict inside).presentation
    let ι := I.declarationLawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  (I.declarationLawMap inside).extendedEquationMap_natural R

end Reading

namespace Interpretation

variable {L} {A : ContextStructure U} (I : L.Interpretation (k := k) A)
variable (inside : V ≤ U)

/-- The declaration comparison of native coefficient readings with a satisfaction interpretation. -/
def declarationLawMap : LawMap (I.restrict inside).presentation I.presentation :=
  I.toReading.declarationLawMap inside

/-- The native equations, read with the original satisfaction comparison, commute with coefficient change. -/
theorem declarationLawMap_baseChange (R : Type u) [CommRing R] [Algebra k R] :
    let F := (I.restrict inside).presentation
    let ι := I.declarationLawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  I.toReading.declarationLawMap_baseChange inside R

/-- The native declaration comparison commutes with principal-open localization. -/
theorem declarationLawMap_localization (r : k) :
    let R := Localization.Away r
    let F := (I.restrict inside).presentation
    let ι := I.declarationLawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  I.declarationLawMap_baseChange inside (Localization.Away r)

end Interpretation

end DeclaredQuantityLaws
end SHIGURE.Quantities
