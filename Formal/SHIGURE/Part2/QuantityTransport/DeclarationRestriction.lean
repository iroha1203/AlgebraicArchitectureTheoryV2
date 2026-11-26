import Formal.SHIGURE.Part1.ContextSelectedEquations
import Formal.SHIGURE.Part1.MarkedLawSupport
import Formal.SHIGURE.Part2.QuantityTransport.CoefficientSyntax
import Formal.SHIGURE.Part2.QuantityTransport.Coefficients
import Formal.SHIGURE.Part2.QuantityTransport.DeclarationStates
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Restriction of declared quantity Laws

Chapter 3 supplies the selected declarations and actual state reduct.
The ordered writing of each kept Law supplies its literal terms. The
coefficient presentation reads precisely their used primitive values
and applications of the designated quantities.

## Implementation notes

One may select coordinates after evaluating the state terms. The retained
writing used here also gives the original substitutions, primitive
symbols and antecedents, which the reduct can evaluate independently.
The selected domain of a partial quantity is read from its own domain
declaration. Ordinary literal values come from their declared operations.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

open DeclarationContext

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
  /-- The existing Law is the ordered writing of these two original typed terms. -/
  expansion (l : quantityLaws) : OrderedEquation.Expansion
    ⟨(P.theory.law l.val).context, valueSort l, (P.theory.law l.val).input, (left l).toTerm, (right l).toTerm⟩
    (P.theory.law l.val).conclusion

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
  ⟨⟨_, _, _, (L.left l).toTerm, (L.right l).toTerm⟩, (P.theory.law l.val).conclusion, L.expansion l⟩

/-- Its stored positive Law is exactly the declaration at the selected name. -/
theorem writing_toLaw (l : L.quantityLaws) : (L.writing l).toLaw = P.theory.law l.val :=
  rfl

/-- The reduced context keeps the result sort and all references of both actual written sides. -/
theorem keptLaw_refs (l : L.KeptLaw U) :
    Declaration.sort (L.valueSort l.val) ∈ U.declarations ∧
      Selected.termReferences (L.left l.val).toTerm ⊆ U.declarations ∧
      Selected.termReferences (L.right l.val).toTerm ⊆ U.declarations :=
  Selected.selectWritten_terms_kept (L.writing l.val)
    (by rw [L.writing_toLaw]; exact Declaration.lawBody_subset_of_mem l.property)

/-- Only literal symbols and applications present in the two original terms are compiled. -/
abbrev UsedLeaf (l : L.quantityLaws) :=
  {a : CoefficientTerm.Literal P.signature ⊕
      CoefficientTerm.Application L.quantities (P.theory.law l.val).context //
    a ∈ (L.left l).leaves ∪ (L.right l).leaves}

/-- The original Law's support keeps every actual referenced leaf. -/
theorem keptLeaf_refs (l : L.KeptLaw U) (a : L.UsedLeaf l.val) :
    Selected.termReferences (CoefficientTerm.leafTerm a.val).2 ⊆ U.declarations :=
  a.property.elim
    (fun h => (CoefficientTerm.leafReferences_subset _ h).trans (L.keptLaw_refs l).2.1)
    (fun h => (CoefficientTerm.leafReferences_subset _ h).trans (L.keptLaw_refs l).2.2)

/-- The selected Law's arithmetic symbols are also retained. -/
theorem keptArithmetic (l : L.KeptLaw U) {a : ArithmeticOperation P.signature}
    (used : a ∈ (L.left l.val).arithmetic ∪ (L.right l.val).arithmetic) :
    Declaration.ofOperation a.operation ∈ U.declarations :=
  used.elim
    (fun h => (L.keptLaw_refs l).2.1 (CoefficientTerm.arithmetic_reference _ h))
    (fun h => (L.keptLaw_refs l).2.2 (CoefficientTerm.arithmetic_reference _ h))

/-- A designated quantity application occurring in either original side. -/
abbrev UsedApplication (l : L.quantityLaws) :=
  {a : CoefficientTerm.Application L.quantities (P.theory.law l.val).context //
    Sum.inr a ∈ (L.left l).leaves ∪ (L.right l).leaves}

/-- An original coefficient literal occurring in either original side. -/
abbrev UsedLiteral (l : L.quantityLaws) :=
  {a : CoefficientTerm.Literal P.signature //
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

/-- A literal's nullary operation survives selection of its written Law. -/
private theorem keptLiteral_name (l : L.KeptLaw U) (a : L.UsedLiteral l.val) :
    Declaration.ofOperation a.val.2.symbol.operation ∈ U.declarations := by
  let op := a.val.2
  have kept := L.keptLeaf_refs l ⟨.inl a.val, a.property⟩
  change Selected.termReferences (op.term (Γ := (P.theory.law l.val.val).context) Term.argsNil) ⊆
    U.declarations at kept
  exact kept (CoefficientTerm.coefficientHead_ref op Term.argsNil)

/-- The input of the Law is read from its actual fixed-state antecedent. -/
def lawInput (A : ContextStructure U) (l : L.KeptLaw U) :
    Set (Assignment A.carrier (P.theory.law l.val.val).context) :=
  {e | A.evaluation.holds (P.theory.law l.val.val).input
    (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e}

/-- The input sorts survive along with the original required Law. -/
theorem keptLaw_sorts (l : L.KeptLaw U) :
    Declaration.sorts (P.theory.law l.val.val).context ⊆ U.declarations :=
  lawSortSupport (Declaration.lawBody_subset_of_mem l.property)

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

/-- A marked total quantity has a designated argument set in the state structure. -/
abbrev KeptTotal (U : DeclarationContext P) :=
  {j : P.signature.Quantity //
    QuantityDeclaration.total j ∈ L.quantities ∧ Declaration.quantity j ∈ U.declarations}

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

/-- For a partial quantity the argument set is its declared domain in the state structure. -/
def fixedDomain (A : ContextStructure U)
    (total : ∀ j : L.KeptTotal U, Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs)) :
    (j : L.KeptQuantity U) → Set (Assignment A.carrier j.val.val.operation.arity.inputs)
  | ⟨⟨.total j, chosen⟩, keep⟩ => total ⟨j, chosen, keep⟩
  | ⟨⟨.partialOp j, _⟩, keep⟩ => {e | A.evaluation.domain j keep e}

variable {k : Type u} [CommRing k]

/-- A value replacement has structural graphs and keeps the fixed state and all
values of marked total operations outside their designated argument sets. -/
structure SameDeclarationState (A : ContextStructure U)
    (total : ∀ j : L.KeptTotal U, Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs))
    (B : RestrictedEvaluation U A.carrier) : Prop
    extends SameStateEvaluation (QuantityDeclaration.operation '' L.quantities) A.evaluation B where
  /-- Candidate outputs are actual functions on the same total and partial domains. -/
  structural : B.Structural
  /-- Values outside the selected arguments of marked total quantities are fixed. -/
  outside (j : L.KeptTotal U) (input : Assignment A.carrier (P.signature.quantityArity j.val).inputs)
    (fixed : input ∉ total j) (y : A.carrier (P.signature.quantityArity j.val).output) :
    A.evaluation.graph (.quantity j.val) j.property.2 input y ↔
      B.graph (.quantity j.val) j.property.2 input y

/-- Interpret scalar meanings and the defined state arguments in a fixed context structure. -/
structure Interpretation (A : ContextStructure U) where
  /-- Read the coefficient value of an element of a retained carrier. -/
  read : CarrierMap U A.carrier (fun _ => k)
  /-- A retained Law's native value carrier is identified faithfully with the coefficient ring. -/
  lawRead (l : L.KeptLaw U) : Function.Bijective (read _ (L.keptLaw_refs l).1)
  /-- A retained varying quantity takes values in the coefficient ring. -/
  quantityRead (j : L.KeptQuantity U) :
    Function.Bijective (read _ (operationOutput j.val.val.operation j.property))
  /-- The designated argument sets of marked total quantities. -/
  totalDomain (j : L.KeptTotal U) : Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs)
  /-- The actual declared operations at arithmetic nodes realize their written meanings. -/
  arithmetic (l : L.KeptLaw U) (a : ArithmeticOperation P.signature)
    (used : a ∈ (L.left l.val).arithmetic ∪ (L.right l.val).arithmetic) :
    a.realizes A read (L.keptArithmetic l used)
  /-- Each coefficient operation keeps its original values as the candidate quantities vary. -/
  fixedArithmetic (l : L.KeptLaw U) (a : ArithmeticOperation P.signature)
    (used : a ∈ (L.left l.val).arithmetic ∪ (L.right l.val).arithmetic) :
    a.operation ∉ QuantityDeclaration.operation '' L.quantities
  /-- Each literal keeps the value of its original nullary operation. -/
  fixedLiteral (l : L.KeptLaw U) (a : L.UsedLiteral l.val) :
    a.val.2.symbol.operation ∉ QuantityDeclaration.operation '' L.quantities
  /-- The evaluated state argument tuple of each used quantity is in its fixed domain. -/
  value (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val) :
    L.fixedDomain A totalDomain (L.keptApplication l a)
  /-- Its components are the actual evaluations of the original fixed state terms. -/
  evaluates (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val)
    {s : P.signature.SortType} (i : Var a.val.1.val.operation.arity.inputs s) :
    A.evaluates (L.keptTerm l a i) e.val ((value l e a).val i)
  /-- The original antecedent is independent of the candidate values. -/
  inputIndependent (l : L.KeptLaw U) (B : RestrictedEvaluation U A.carrier)
    (same : L.SameDeclarationState A totalDomain B)
    (e : Assignment A.carrier (P.theory.law l.val.val).context) :
    e ∈ L.lawInput A l ↔ B.holds (P.theory.law l.val.val).input
      (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e
  /-- The already evaluated state arguments have the same values for every candidate. -/
  argumentIndependent (l : L.KeptLaw U) (B : RestrictedEvaluation U A.carrier)
    (same : L.SameDeclarationState A totalDomain B)
    (e : L.lawInput A l) (a : L.UsedApplication l.val)
    {s : P.signature.SortType} (i : Var a.val.1.val.operation.arity.inputs s) :
    B.holds (L.keptTerm l a i).val.graph
      ((Declaration.termContext_le_iff (L.keptTerm l a i).val).1 (L.keptTerm l a i).property)
      (Assignment.cons ((value l e a).val i) e.val)


namespace Interpretation

variable {L} {A : ContextStructure U} (I : L.Interpretation (k := k) A)

/-- The fixed argument set in the retained state for a designated quantity. -/
abbrev domain (j : L.KeptQuantity U) := L.fixedDomain A I.totalDomain j

/-- The actual value of the original retained nullary operation. -/
private def actualLiteral (l : L.KeptLaw U) (a : L.UsedLiteral l.val) : A.carrier a.val.1 :=
  a.val.2.nativeValue A (L.keptLiteral_name l a) Assignment.empty

/-- Read the scalar from the actual value of its declared nullary symbol. -/
def literalValue (l : L.KeptLaw U) (a : L.UsedLiteral l.val) : k :=
  I.read a.val.1 (a.val.2.keepsResult (L.keptLiteral_name l a)) (actualLiteral (A := A) l a)

/-- A leaf compiles to its original coefficient value or its actual quantity coordinate. -/
private def readLeaf (l : L.KeptLaw U) (e : L.lawInput A l) :
    (a : L.UsedLeaf l.val) →
      CoefficientTerm.LeafValue k (Σ j : L.KeptQuantity U, I.domain j) a.val
  | ⟨.inl literal, used⟩ => I.literalValue l ⟨literal, used⟩
  | ⟨.inr app, used⟩ => ⟨L.keptApplication l ⟨app, used⟩, I.value l e ⟨app, used⟩⟩

/-- Compile exactly the originally designated quantity equations surviving in the context. -/
def presentation : Presentation k (Selected.readStructure A) where
  Quantity := L.KeptQuantity U
  Domain := fun j => I.domain j
  Law := L.KeptLaw U
  Input := fun l => L.lawInput A l
  left l e := (L.left l.val).compile (fun a h => I.readLeaf l e ⟨a, Or.inl h⟩)
  right l e := (L.right l.val).compile (fun a h => I.readLeaf l e ⟨a, Or.inr h⟩)

/-- Reading an element after retyping its sort uses the same retained carrier. -/
private theorem read_cast {s t : P.signature.SortType} (eq : s = t)
    (hs : Declaration.sort s ∈ U.declarations) (ht : Declaration.sort t ∈ U.declarations)
    (x : A.carrier s) : I.read t ht (cast (congrArg A.carrier eq) x) = I.read s hs x := by
  cases eq
  rfl

/-- The native value of a leaf is its actual literal value or the selected candidate quantity. -/
private def nativeLeaf (l : L.KeptLaw U) (e : L.lawInput A l)
    (q : I.presentation.Candidate k) (lift : k → A.carrier (L.valueSort l.val))
    (t : CoefficientTerm L.quantities (P.theory.law l.val.val).context (L.valueSort l.val))
    (used : t.leaves ⊆ (L.left l.val).leaves ∪ (L.right l.val).leaves) :
    ∀ a ∈ t.leaves, A.carrier (L.valueSort l.val)
  | .inl literal, h =>
    cast (congrArg A.carrier (t.leafSort_eq h))
      (actualLiteral (A := A) l ⟨literal, used h⟩)
  | .inr app, h =>
    let a : L.UsedApplication l.val := ⟨app, used h⟩
    lift (q (L.keptApplication l a) (I.value l e a))

/-- Both native sides evaluate their actual declared arithmetic at the same fixed state input. -/
def nativeSides (l : L.KeptLaw U) (e : L.lawInput A l) (q : I.presentation.Candidate k)
    (lift : k → A.carrier (L.valueSort l.val)) :
    A.carrier (L.valueSort l.val) × A.carrier (L.valueSort l.val) :=
  ⟨(L.left l.val).evalNative A (L.keptLaw_refs l).2.1
    (I.nativeLeaf l e q lift (L.left l.val) Set.subset_union_left),
    (L.right l.val).evalNative A (L.keptLaw_refs l).2.2
      (I.nativeLeaf l e q lift (L.right l.val) Set.subset_union_right)⟩

/-- The original native term actions give the compiled value on each side. -/
private theorem nativeSide_read (l : L.KeptLaw U) (e : L.lawInput A l) (q : I.presentation.Candidate k)
    (lift : k → A.carrier (L.valueSort l.val))
    (readsLift : ∀ x, I.read _ (L.keptLaw_refs l).1 (lift x) = x)
    (t : CoefficientTerm L.quantities (P.theory.law l.val.val).context (L.valueSort l.val))
    (keep : Selected.termReferences t.toTerm ⊆ U.declarations)
    (used : t.leaves ⊆ (L.left l.val).leaves ∪ (L.right l.val).leaves)
    (usedArithmetic : t.arithmetic ⊆ (L.left l.val).arithmetic ∪ (L.right l.val).arithmetic) :
    I.read _ (L.keptLaw_refs l).1 (t.evalNative A keep (I.nativeLeaf l e q lift t used)) =
      (t.compile (fun a h => I.readLeaf l e ⟨a, used h⟩)).eval (fun x => q x.1 x.2) := by
  apply CoefficientTerm.evalNative_read
  · intro a h
    cases a with
    | inl literal =>
      exact I.read_cast (t.leafSort_eq h) _ _ _
    | inr app => exact readsLift _
  · intro op h
    exact I.arithmetic l op (usedArithmetic h)

/-- Reading both original native sides agrees with evaluation of their compiled equations. -/
theorem nativeSides_read (l : L.KeptLaw U) (e : L.lawInput A l) (q : I.presentation.Candidate k)
    (lift : k → A.carrier (L.valueSort l.val))
    (readsLift : ∀ x, I.read _ (L.keptLaw_refs l).1 (lift x) = x) :
    let result := I.nativeSides l e q lift
    (I.read _ (L.keptLaw_refs l).1 result.1, I.read _ (L.keptLaw_refs l).1 result.2) =
      ((I.presentation.left l e).eval (fun x => q x.1 x.2),
        (I.presentation.right l e).eval (fun x => q x.1 x.2)) :=
  Prod.ext
    (I.nativeSide_read l e q lift readsLift _ _ Set.subset_union_left Set.subset_union_left)
    (I.nativeSide_read l e q lift readsLift _ _ Set.subset_union_right Set.subset_union_right)

/-- The identification of the original equality's value sort with the coefficient ring. -/
def lawCoefficients (l : L.KeptLaw U) : A.carrier (L.valueSort l.val) ≃ k :=
  Equiv.ofBijective _ (I.lawRead l)

/-- The identification of a candidate quantity's actual output carrier with the coefficient ring. -/
def quantityCoefficients (j : L.KeptQuantity U) : A.carrier j.val.val.operation.arity.output ≃ k :=
  Equiv.ofBijective _ (I.quantityRead j)

/-- The actual restricted operations obtained by replacing the chosen quantity values.
Relations, ordinary operations, partial domains and total values outside the designated
argument sets remain those of the state. -/
private def candidateOperations (q : I.presentation.Candidate k) : RestrictedStructure U where
  carrier := A.carrier
  total := A.toRestrictedStructure.total
  relation := A.toRestrictedStructure.relation
  partialDomain := A.toRestrictedStructure.partialDomain
  quantity j keep e := by
    classical
    exact if chosen : QuantityDeclaration.total j ∈ L.quantities then
      if domain : e ∈ I.totalDomain ⟨j, chosen, keep⟩ then
        (I.quantityCoefficients ⟨⟨.total j, chosen⟩, keep⟩).symm
          (q ⟨⟨.total j, chosen⟩, keep⟩ ⟨e, domain⟩)
      else A.toRestrictedStructure.quantity j keep e
    else A.toRestrictedStructure.quantity j keep e
  partialValue p keep e := by
    classical
    exact if chosen : QuantityDeclaration.partialOp p ∈ L.quantities then
      (I.quantityCoefficients ⟨⟨.partialOp p, chosen⟩, keep⟩).symm
        (q ⟨⟨.partialOp p, chosen⟩, keep⟩ e)
    else A.toRestrictedStructure.partialValue p keep e

/-- Interpret the candidate in the original context using its actual quantity graphs. -/
def candidateStructure (q : I.presentation.Candidate k) : ContextStructure U where
  carrier := A.carrier
  omitted := A.omitted
  evaluation := (I.candidateOperations q).evaluation
  structural := (I.candidateOperations q).evaluation_structural

/-- Candidate replacement preserves each fixed primitive and the actual partial domains. -/
theorem candidateStructure_sameState (q : I.presentation.Candidate k) :
    L.SameDeclarationState A I.totalDomain (I.candidateStructure q).evaluation where
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
    change A.toRestrictedStructure.graph (.quantity j.val) j.property.2 e y ↔
      (I.candidateOperations q).graph (.quantity j.val) j.property.2 e y
    simp only [RestrictedStructure.graph_quantity_iff, candidateOperations, dif_pos j.property.1, dif_neg fixed]

/-- At a designated argument the original quantity graph has the candidate's coefficient value. -/
theorem candidateStructure_graph (q : I.presentation.Candidate k) (j : L.KeptQuantity U) (e : I.domain j) :
    (I.candidateStructure q).evaluation.graph j.val.val.operation j.property e.val
      ((I.quantityCoefficients j).symm (q j e)) := by
  classical
  rcases j with ⟨⟨j, chosen⟩, keep⟩
  cases j with
  | total j =>
    change (I.candidateOperations q).graph (.quantity j) keep e.val _
    rw [RestrictedStructure.graph_quantity_iff]
    have inputDomain : e.val ∈ I.totalDomain ⟨j, chosen, keep⟩ := e.property
    simp only [candidateOperations, dif_pos chosen, dif_pos inputDomain]
  | partialOp p =>
    change (I.candidateOperations q).graph (.partialOp p) keep e.val _
    rw [RestrictedStructure.graph_partial_iff]
    refine ⟨e.property, ?_⟩
    simp only [candidateOperations, dif_pos chosen]
    rfl

/-- The compiled equation holds exactly when the two interpreted original sides are equal. -/
theorem nativeEquation_iff (l : L.KeptLaw U) (e : L.lawInput A l) (q : I.presentation.Candidate k) :
    let native := I.nativeSides l e q (I.lawCoefficients l).symm
    native.1 = native.2 ↔
      (I.presentation.left l e).eval (fun x => q x.1 x.2) =
        (I.presentation.right l e).eval (fun x => q x.1 x.2) := by
  have equality := I.nativeSides_read l e q (I.lawCoefficients l).symm
    (I.lawCoefficients l).apply_symm_apply
  have lh := congrArg Prod.fst equality
  have rh := congrArg Prod.snd equality
  dsimp only at lh rh ⊢
  rw [← lh, ← rh, (I.lawRead l).1.eq_iff]

/-- The universal polynomial residual specializes to the interpreted difference of the native sides. -/
theorem nativeResidual_eq (l : L.KeptLaw U) (e : L.lawInput A l) (q : I.presentation.Candidate k) :
    I.presentation.evaluate q (I.presentation.residual l e) =
      let sides := I.nativeSides l e q (I.lawCoefficients l).symm
      I.read _ (L.keptLaw_refs l).1 sides.1 - I.read _ (L.keptLaw_refs l).1 sides.2 := by
  rw [I.presentation.evaluate_residual]
  exact congrArg (fun values : k × k => values.1 - values.2)
    (I.nativeSides_read l e q (I.lawCoefficients l).symm (I.lawCoefficients l).apply_symm_apply).symm

private theorem nativeSide_evaluates (l : L.KeptLaw U) (e : L.lawInput A l)
    (q : I.presentation.Candidate k)
    (t : CoefficientTerm L.quantities (P.theory.law l.val.val).context (L.valueSort l.val))
    (keep : Selected.termReferences t.toTerm ⊆ U.declarations)
    (used : t.leaves ⊆ (L.left l.val).leaves ∪ (L.right l.val).leaves)
    (arithmetic : t.arithmetic ⊆ (L.left l.val).arithmetic ∪ (L.right l.val).arithmetic) :
    ∃ hTerm, (I.candidateStructure q).evaluates ⟨t.toTerm, hTerm⟩ e.val
      (t.evalNative A keep (I.nativeLeaf l e q (I.lawCoefficients l).symm t used)) := by
  let B := I.candidateStructure q
  have fixed := I.candidateStructure_sameState q
  apply t.evalNative_evaluates A B.evaluation B.structural _ (L.keptLaw_sorts l) (L.keptLaw_refs l).1
  · dsimp only
    intro a h
    cases a with
    | inl literal =>
      let leaf : L.UsedLiteral l.val := ⟨literal, used h⟩
      let op := literal.2
      let kept := L.keptLiteral_name l leaf
      have support := Selected.termContext_le_of_references
        (op.term (Γ := (P.theory.law l.val.val).context) Term.argsNil)
        (L.keptLaw_sorts l) (op.keepsResult kept) (L.keptLeaf_refs l ⟨.inl literal, leaf.property⟩)
      refine ⟨support, ?_⟩
      have trivialCast : cast (congrArg A.carrier (t.leafSort_eq h).symm)
          (I.nativeLeaf l e q (I.lawCoefficients l).symm t used (.inl literal) h) =
          op.nativeValue A kept Assignment.empty := by
        simp only [nativeLeaf, actualLiteral, cast_cast, cast_eq]
        rfl
      rw [trivialCast]
      refine op.evaluates_term B _ support e.val Assignment.empty
        (fun i => nomatch i) kept _ ?_
      exact (fixed.graph op.symbol.operation (I.fixedLiteral l leaf) kept _ _).1
        (op.nativeValue_graph A kept Assignment.empty)
    | inr application =>
      let a : L.UsedApplication l.val := ⟨application, used h⟩
      let j := L.keptApplication l a
      let input := I.value l e a
      let op := application.1.val.operation
      have support := Selected.termContext_le_of_references (Term.app op (fun i => application.2 i))
        (L.keptLaw_sorts l) (operationOutput op j.property) (L.keptLeaf_refs l ⟨.inr application, a.property⟩)
      refine ⟨support, ?_⟩
      have result :
          cast (congrArg A.carrier (t.leafSort_eq h).symm)
            (I.nativeLeaf l e q (I.lawCoefficients l).symm t used (.inr application) h) =
            (I.quantityCoefficients j).symm (q j input) := by
        apply (I.quantityCoefficients j).injective
        change I.read _ (operationOutput op j.property)
          (cast (congrArg A.carrier (t.leafSort_eq h).symm) ((I.lawCoefficients l).symm (q j input))) =
          I.quantityCoefficients j ((I.quantityCoefficients j).symm (q j input))
        have sortEq : op.arity.output = L.valueSort l.val := t.leafSort_eq h
        exact (I.read_cast sortEq.symm (L.keptLaw_refs l).1 (operationOutput op j.property)
          ((I.lawCoefficients l).symm (q j input))).trans
          (((I.lawCoefficients l).apply_symm_apply (q j input)).trans
            ((I.quantityCoefficients j).apply_symm_apply (q j input)).symm)
      rw [result]
      refine B.evaluates_app_of_graph op (fun i => application.2 i) ⟨_, support⟩ rfl e.val input.val
        (fun i => ⟨(L.keptTerm l a i).property, I.argumentIndependent l B.evaluation fixed e a i⟩) j.property _ ?_
      exact I.candidateStructure_graph q j input
  · intro op h keep args y
    exact (fixed.graph op.operation (I.fixedArithmetic l op (arithmetic h)) keep args y).1

/-- On the original guard, the declared conclusion holds exactly when its compiled residual is zero. -/
theorem candidate_conclusion_iff (l : L.KeptLaw U) (e : L.lawInput A l)
    (q : I.presentation.Candidate k) :
    (I.candidateStructure q).evaluation.holds (P.theory.law l.val.val).conclusion
      (lawConclusionSupport (Declaration.lawBody_subset_of_mem l.property)) e.val ↔
    I.presentation.evaluate q (I.presentation.residual l e) = 0 := by
  let B := I.candidateStructure q
  let w := L.writing l.val
  have guard := (I.inputIndependent l B.evaluation (I.candidateStructure_sameState q) e.val).1 e.property
  obtain ⟨hl, actualLeft⟩ := I.nativeSide_evaluates l e q _ (L.keptLaw_refs l).2.1
    Set.subset_union_left Set.subset_union_left
  obtain ⟨hr, actualRight⟩ := I.nativeSide_evaluates l e q _ (L.keptLaw_refs l).2.2
    Set.subset_union_right Set.subset_union_right
  have compared := B.holds_written_iff_of_evaluates w
    (Declaration.lawBody_subset_of_mem l.property) e.val guard actualLeft actualRight
  refine compared.trans ((I.nativeEquation_iff l e q).trans ?_)
  rw [I.presentation.evaluate_residual, sub_eq_zero]

/-- The actual original Law of each retained declaration is satisfied exactly when all its
compiled residuals vanish for the same candidate. -/
theorem candidate_satisfies_iff (l : L.KeptLaw U) (q : I.presentation.Candidate k) :
    (I.candidateStructure q).evaluation.satisfies (P.theory.law l.val.val)
      (Declaration.lawBody_subset_of_mem l.property) ↔
    ∀ e : L.lawInput A l, I.presentation.evaluate q (I.presentation.residual l e) = 0 := by
  let B := I.candidateStructure q
  have fixed := I.candidateStructure_sameState q
  constructor
  · intro satisfies e
    exact (I.candidate_conclusion_iff l e q).1
      (satisfies e.val ((I.inputIndependent l B.evaluation fixed e.val).1 e.property))
  · intro residuals e inputHeld
    let original : L.lawInput A l := ⟨e, (I.inputIndependent l B.evaluation fixed e).2 inputHeld⟩
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

variable (inside : V ≤ U)

/-- A supported tuple in the actual reduct has the same assigned values in the ambient structure. -/
private def assignmentEquiv {Γ : List P.signature.SortType}
    (support : Declaration.sorts Γ ⊆ V.declarations) :
    Assignment (A.restrict inside).carrier Γ ≃ Assignment A.carrier Γ :=
  Equiv.ofBijective (mapAssignment (selectedMap V A.carrier) support) (by
    refine ⟨?_, mapAssignment_surjective _ (fun s hs => (selectedMap_bijective A.carrier s hs).2) _⟩
    intro a b same
    apply Assignment.ext
    intro s i
    exact (selectedMap_bijective A.carrier s (varKept support i)).1
      (congrArg (fun e : Assignment A.carrier Γ => e i) same))

/-- The retained carriers identify the same scalar value before and after forgetting. -/
private def restrictRead : CarrierMap V (A.restrict inside).carrier (fun _ => k) :=
  fun s keep x => I.read s (inside keep) (selectedMap V A.carrier s keep x)

/-- The argument set of each marked total quantity is read on its retained carriers. -/
private def restrictTotal (j : L.KeptTotal V) :
    Set (Assignment (A.restrict inside).carrier (P.signature.quantityArity j.val).inputs) :=
  (assignmentEquiv (A := A) inside (operationInputs (.quantity j.val) j.property.2)) ⁻¹'
    I.totalDomain ⟨j.val, j.property.1, inside j.property.2⟩

/-- Total argument sets and genuine partial domains both restrict along the carrier identification. -/
private theorem restrict_domain_iff (j : L.KeptQuantity V)
    (e : Assignment (A.restrict inside).carrier j.val.val.operation.arity.inputs) :
    e ∈ L.fixedDomain (A.restrict inside) (I.restrictTotal inside) j ↔
      assignmentEquiv (A := A) inside (L.keptQuantity_sorts j) e ∈ I.domain (L.includeQuantity inside j) := by
  rcases j with ⟨⟨j, chosen⟩, keep⟩
  cases j <;> rfl

/-- The original antecedent has the same truth on the corresponding ambient assignment. -/
theorem restrict_lawInput_iff (l : L.KeptLaw V)
    (e : Assignment (A.restrict inside).carrier (P.theory.law l.val.val).context) :
    e ∈ L.lawInput (A.restrict inside) l ↔
      mapAssignment (selectedMap V A.carrier) (L.keptLaw_sorts l) e ∈ L.lawInput A (L.includeLaw inside l) :=
  A.restrict_holds_iff inside _ _ e

/-- The image of a retained input in the original antecedent's input set. -/
private def includeInput (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l) :
    L.lawInput A (L.includeLaw inside l) :=
  ⟨assignmentEquiv (A := A) inside (L.keptLaw_sorts l) e.val,
    (restrict_lawInput_iff inside l e.val).1 e.property⟩

/-- Return the original evaluated tuple through the actual reduct's carrier identification. -/
private def restrictValue (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l)
    (a : L.UsedApplication l.val) :
    L.fixedDomain (A.restrict inside) (I.restrictTotal inside) (L.keptApplication l a) := by
  let original := I.value (L.includeLaw inside l) (includeInput inside l e) a
  let reads := assignmentEquiv (A := A) inside (L.keptQuantity_sorts (L.keptApplication l a))
  refine ⟨reads.symm original.val, (I.restrict_domain_iff inside _ _).2 ?_⟩
  change reads (reads.symm original.val) ∈ I.domain (L.keptApplication (L.includeLaw inside l) a)
  rw [reads.apply_symm_apply]
  exact original.property

private def retainedCarrierEquiv (s : P.signature.SortType) (keep : Declaration.sort s ∈ V.declarations) :
    (A.restrict inside).carrier s ≃ A.carrier s :=
  Equiv.ofBijective (selectedMap V A.carrier s keep) (selectedMap_bijective A.carrier s keep)

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
    (same : L.SameDeclarationState (A.restrict inside) (I.restrictTotal inside) B)
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
    (same : L.SameDeclarationState (A.restrict inside) (I.restrictTotal inside) B) :
    L.SameDeclarationState A I.totalDomain (extendEvaluation (A := A) inside B) where
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
    by_cases retained : Declaration.quantity j.val ∈ V.declarations
    · let localName : L.KeptTotal V := ⟨j.val, j.property.1, retained⟩
      let localArgs := mapAssignment (fun s keep => (retainedCarrierEquiv (A := A) inside s keep).symm)
        (operationInputs (.quantity j.val) retained) e
      have localFixed : localArgs ∉ I.restrictTotal inside localName := by
        intro h
        apply fixed
        change mapAssignment (selectedMap V A.carrier) (operationInputs (.quantity j.val) retained) localArgs ∈
          I.totalDomain j at h
        have argsRestored : mapAssignment (selectedMap V A.carrier) (operationInputs (.quantity j.val) retained)
            localArgs = e := by
          apply Assignment.ext
          intro s i
          exact (retainedCarrierEquiv (A := A) inside s
            (varKept (operationInputs (.quantity j.val) retained) i)).apply_symm_apply (e i)
        exact argsRestored ▸ h
      have retainedAgrees := restoreEvaluation_graph inside B (.quantity j.val) retained e y
        (same.outside localName localArgs localFixed _)
      exact retainedAgrees.trans (A.evaluation.replaceRetainedGraphs_graph _ (.quantity j.val) j.property.2 retained e y).symm
    · exact (A.evaluation.replaceRetainedGraphs_graph_of_omitted _ (.quantity j.val) j.property.2 retained e y).symm

/-- Reading the extended replacement on the smaller context recovers its input evaluation. -/
private theorem extendEvaluation_restrict
    (B : RestrictedEvaluation V (A.restrict inside).carrier)
    (same : L.SameDeclarationState (A.restrict inside) (I.restrictTotal inside) B) :
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

/-- The actual reduct retains the coefficient meanings and fixed-state evaluations of the original Laws. -/
def restrict : L.Interpretation (k := k) (A.restrict inside) where
  read := I.restrictRead inside
  lawRead l := (I.lawRead (L.includeLaw inside l)).comp (selectedMap_bijective A.carrier _ _)
  quantityRead j := (I.quantityRead (L.includeQuantity inside j)).comp (selectedMap_bijective A.carrier _ _)
  totalDomain := I.restrictTotal inside
  arithmetic l a used :=
    a.realizes_restrict inside (L.keptArithmetic l used) I.read (I.arithmetic (L.includeLaw inside l) a used)
  fixedArithmetic l a used := I.fixedArithmetic (L.includeLaw inside l) a used
  fixedLiteral l a := I.fixedLiteral (L.includeLaw inside l) a
  value := I.restrictValue inside
  evaluates l e a := by
    intro s i
    apply (A.restrict_evaluates_iff inside (L.keptTerm l a i) _ _).2
    have same := (assignmentEquiv (A := A) inside (L.keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply
      (I.value (L.includeLaw inside l) (includeInput inside l e) a).val
    have atIndex := congrArg (fun x : Assignment A.carrier _ => x i) same
    change selectedMap V A.carrier s (varKept (L.keptQuantity_sorts (L.keptApplication l a)) i)
      ((I.restrictValue inside l e a).val i) =
        (I.value (L.includeLaw inside l) (includeInput inside l e) a).val i at atIndex
    rw [atIndex]
    exact I.evaluates (L.includeLaw inside l) (includeInput inside l e) a i

  inputIndependent l B same e := by
    let extended := extendEvaluation (A := A) inside B
    let e' := mapAssignment (selectedMap V A.carrier) (L.keptLaw_sorts l) e
    have independent := I.inputIndependent (L.includeLaw inside l) extended
      (I.extendEvaluation_sameState inside B same) e'
    refine (restrict_lawInput_iff inside l e).trans (independent.trans ?_)
    have transfer := extended.holds_pullback_iff inside (selectedMap V A.carrier)
      (selectedMap_bijective A.carrier) _ (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e
    rw [I.extendEvaluation_restrict inside B same] at transfer
    exact transfer.symm
  argumentIndependent l B same e a := by
    intro s i
    let extended := extendEvaluation (A := A) inside B
    let originalInput := includeInput inside l e
    let originalValue := I.value (L.includeLaw inside l) originalInput a
    let term := L.keptTerm l a i
    let localValue := (I.restrictValue inside l e a).val i
    let witness := Assignment.cons localValue e.val
    let keep := (Declaration.termContext_le_iff term.val).1 term.property
    have preserved := I.argumentIndependent (L.includeLaw inside l) extended
      (I.extendEvaluation_sameState inside B same) originalInput a i
    have transfer := extended.holds_pullback_iff inside (selectedMap V A.carrier)
      (selectedMap_bijective A.carrier) term.val.graph keep witness
    rw [I.extendEvaluation_restrict inside B same] at transfer
    apply transfer.2
    have sameValue := (assignmentEquiv (A := A) inside (L.keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply originalValue.val
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

/-- Read a retained quantity and its designated argument in the ambient context. -/
private def declarationQuantityMap : QuantityMap (I.restrict inside).presentation I.presentation where
  name := L.includeQuantity inside
  argument j x := ⟨assignmentEquiv (A := A) inside (L.keptQuantity_sorts j) x.val,
    (I.restrict_domain_iff inside j x.val).1 x.property⟩

/-- Restricting a literal does not change the coefficient read from its actual declaration. -/
theorem literalValue_restrict (l : L.KeptLaw V) (a : L.UsedLiteral l.val) :
    (I.restrict inside).literalValue l a = I.literalValue (L.includeLaw inside l) a := by
  let op := a.val.2
  let keep := L.keptLiteral_name l a
  change I.read _ _ (selectedMap V A.carrier _ (op.keepsResult keep)
      (op.nativeValue (A.restrict inside) keep Assignment.empty)) =
    I.read _ _ (op.nativeValue A (inside keep) Assignment.empty)
  rw [op.nativeValue_restrict]
  congr 2
  exact Assignment.eq_empty _

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
  exact (assignmentEquiv (A := A) inside (L.keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply _

/-- Reading a compiled leaf commutes with the comparison of declaration contexts. -/
private theorem declarationReadLeaf (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l)
    (a : L.UsedLeaf l.val) :
    CoefficientTerm.mapLeafValue (I.declarationQuantityMap inside).coordinate a.val
      ((I.restrict inside).readLeaf l e a) =
    I.readLeaf (L.includeLaw inside l) (includeInput inside l e) a := by
  rcases a with ⟨literal | app, used⟩
  · exact I.literalValue_restrict inside l ⟨literal, used⟩
  · exact I.declarationCoordinate inside l e ⟨app, used⟩

/-- The actual context inclusion induces a comparison of the original retained scalar equations. -/
def declarationLawMap : LawMap (I.restrict inside).presentation I.presentation where
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
theorem declarationLawMap_baseChange (R : Type u) [CommRing R] [Algebra k R] :
    let F := (I.restrict inside).presentation
    let ι := I.declarationLawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  (I.declarationLawMap inside).extendedEquationMap_natural R

/-- The same square for the coefficient restriction to the principal open of `r`. -/
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
