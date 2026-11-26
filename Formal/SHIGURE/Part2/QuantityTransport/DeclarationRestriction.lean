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
  /-- The antecedent reads the fixed state, allowing domains of partial quantities. -/
  stateInput (l : quantityLaws) :
    StateFormula (QuantityDeclaration.operation '' quantities) (P.theory.law l.val).input
  /-- Every actual quantity argument only reads fixed state values. -/
  stateArgument (l : quantityLaws) (a : CoefficientTerm.Application quantities (P.theory.law l.val).context)
    (used : Sum.inr a ∈ (left l).leaves ∪ (right l).leaves)
    {s} (i : Var a.1.val.operation.arity.inputs s) :
    StateTerm (QuantityDeclaration.operation '' quantities) (a.2 i)

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
    Declaration.total a.name ∈ U.declarations :=
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
  have equality := lawConclusionSupport (Marked.equality_law_support t t operationInputs input result termRefs termRefs)
  change Declaration.formulaSupport (Formula.termEq t t) ⊆ U.declarations at equality
  rw [Formula.termEq_eq_ex] at equality
  apply (Declaration.termContext_le_iff t).2
  exact (Declaration.binarySupport_left (Declaration.formula_conj t.graph t.graph)).trans
    ((Declaration.formulaSupport_ex_body _).trans equality)

/-- The retained state argument denotes precisely its original term. -/
def keptTerm (l : L.KeptLaw U) (a : L.UsedApplication l.val) {s : P.signature.SortType}
    (i : Var a.val.1.val.operation.arity.inputs s) : U.TermIn (P.theory.law l.val.val).context s :=
  ⟨a.val.2 i, L.keptTerm_support l a i⟩

/-- A literal's nullary ordinary operation survives selection of its written Law. -/
private theorem keptLiteral_name (l : L.KeptLaw U) (a : L.UsedLiteral l.val) :
    Declaration.total a.val.2.name ∈ U.declarations := by
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

/-- For a partial quantity the argument set is its declared domain in the state structure. -/
def fixedDomain (A : ContextStructure U)
    (total : ∀ j : L.KeptTotal U, Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs)) :
    (j : L.KeptQuantity U) → Set (Assignment A.carrier j.val.val.operation.arity.inputs)
  | ⟨⟨.total j, chosen⟩, keep⟩ => total ⟨j, chosen, keep⟩
  | ⟨⟨.partialOp j, _⟩, keep⟩ => {e | A.evaluation.domain j keep e}

variable {k : Type u} [CommRing k]

/-- Interpret scalar meanings and the defined state arguments in a fixed context structure. -/
structure Interpretation (A : ContextStructure U) where
  /-- Read the coefficient value of an element of a retained carrier. -/
  read : CarrierMap U A.carrier (fun _ => k)
  /-- The designated argument sets of marked total quantities. -/
  totalDomain (j : L.KeptTotal U) : Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs)
  /-- The actual declared operations at arithmetic nodes realize their written meanings. -/
  arithmetic (l : L.KeptLaw U) (a : ArithmeticOperation P.signature)
    (used : a ∈ (L.left l.val).arithmetic ∪ (L.right l.val).arithmetic) :
    a.realizes A read (L.keptArithmetic l used)
  /-- The evaluated state argument tuple of each used quantity is in its fixed domain. -/
  value (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val) :
    L.fixedDomain A totalDomain (L.keptApplication l a)
  /-- Its components are the actual evaluations of the original fixed state terms. -/
  evaluates (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val)
    {s : P.signature.SortType} (i : Var a.val.1.val.operation.arity.inputs s) :
    A.evaluates (L.keptTerm l a i) e.val ((value l e a).val i)

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

/-- The original guard is independent of the candidate value graphs, with all domains fixed. -/
theorem lawInput_fixed (l : L.KeptLaw U) (B : RestrictedEvaluation U A.carrier)
    (same : SameStateEvaluation (QuantityDeclaration.operation '' L.quantities) A.evaluation B)
    (e : Assignment A.carrier (P.theory.law l.val.val).context) :
    e ∈ L.lawInput A l ↔ B.holds (P.theory.law l.val.val).input
      (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e :=
  same.holds_iff _ (L.stateInput l.val) _ e

/-- Replacing the candidate values leaves every evaluated state argument unchanged. -/
theorem argument_fixed (l : L.KeptLaw U) (B : RestrictedEvaluation U A.carrier)
    (same : SameStateEvaluation (QuantityDeclaration.operation '' L.quantities) A.evaluation B)
    (e : L.lawInput A l) (a : L.UsedApplication l.val) {s : P.signature.SortType}
    (i : Var a.val.1.val.operation.arity.inputs s) :
    B.holds (L.keptTerm l a i).val.graph
        ((Declaration.termContext_le_iff (L.keptTerm l a i).val).1 (L.keptTerm l a i).property)
        (Assignment.cons ((I.value l e a).val i) e.val) :=
  (same.evaluates_iff (L.keptTerm l a i) (L.stateArgument l.val a.val a.property i) _ _).1
    (I.evaluates l e a i)

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

/-- When the native value carrier is identified with the coefficient ring, the compiled
equation holds exactly when the two interpreted original sides are equal. -/
theorem nativeEquation_iff (l : L.KeptLaw U) (e : L.lawInput A l) (q : I.presentation.Candidate k)
    (coefficients : A.carrier (L.valueSort l.val) ≃ k)
    (reads : ∀ x, I.read _ (L.keptLaw_refs l).1 x = coefficients x) :
    let native := I.nativeSides l e q coefficients.symm
    native.1 = native.2 ↔
      (I.presentation.left l e).eval (fun x => q x.1 x.2) =
        (I.presentation.right l e).eval (fun x => q x.1 x.2) := by
  have equality := I.nativeSides_read l e q coefficients.symm
    (fun x => (reads _).trans (coefficients.apply_symm_apply x))
  have lh := congrArg Prod.fst equality
  have rh := congrArg Prod.snd equality
  dsimp only at lh rh ⊢
  rw [← lh, ← rh, reads, reads, coefficients.injective.eq_iff]

/-- The universal polynomial residual specializes to the interpreted difference of the native sides. -/
theorem nativeResidual_eq (l : L.KeptLaw U) (e : L.lawInput A l) (q : I.presentation.Candidate k)
    (lift : k → A.carrier (L.valueSort l.val))
    (readsLift : ∀ x, I.read _ (L.keptLaw_refs l).1 (lift x) = x) :
    I.presentation.evaluate q (I.presentation.residual l e) =
      let sides := I.nativeSides l e q lift
      I.read _ (L.keptLaw_refs l).1 sides.1 - I.read _ (L.keptLaw_refs l).1 sides.2 := by
  rw [I.presentation.evaluate_residual]
  exact congrArg (fun values : k × k => values.1 - values.2)
    (I.nativeSides_read l e q lift readsLift).symm

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

/-- The actual reduct retains the coefficient meanings and fixed-state evaluations of the original Laws. -/
def restrict : L.Interpretation (k := k) (A.restrict inside) where
  read := I.restrictRead inside
  totalDomain := I.restrictTotal inside
  arithmetic l a used :=
    a.realizes_restrict inside (L.keptArithmetic l used) I.read (I.arithmetic (L.includeLaw inside l) a used)
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
