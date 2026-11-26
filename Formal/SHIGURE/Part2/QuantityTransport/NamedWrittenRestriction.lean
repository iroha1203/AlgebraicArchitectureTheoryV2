import Formal.SHIGURE.Part1.ContextSelectedPresentation
import Formal.SHIGURE.Part2.QuantityTransport.CoefficientSyntax
import Formal.SHIGURE.Part2.QuantityTransport.WrittenRestriction

/-! # Coefficient equations with names in a primitive presentation

A primitive presentation can register coefficient equations at its Law
names. The comparison uses the registered expressions and the actual
antecedent of each retained Law.

## Implementation notes

The two sides are read from the primitive presentation. Each used
application provides its original quantity name and argument terms.
The coefficient dependencies are part of the same declaration closure
that retains the native guard. The actual selected primitive presentation
keeps the same writing retyped in the selected signature.
-/

namespace SHIGURE.Quantities

open DeclarationContext

noncomputable section

universe u

/-- Every required Law with an authored equation over the fixed coefficient type. -/
def registeredCoefficientLaws (k : Type u) (P : PrimitivePresentation.{u}) : Set P.theory.LawName :=
  {l | (P.coefficientEquation k l.val).isSome}

/-- The quantity coordinates used by the registered coefficient Laws of the fixed type. -/
structure NamedWrittenLaws (k : Type u) (P : PrimitivePresentation.{u}) where
  /-- The primitive quantities that supply scalar coordinates. -/
  quantities : Set (QuantityDeclaration P.signature)
  /-- Every used application in any required coefficient Law belongs to a designated quantity. -/
  hasQuantity (l : registeredCoefficientLaws k P)
    (a : DeclaredApplication P.signature (P.theory.law l.val).context)
    (used : let e := (P.coefficientEquation k l.val.val).get l.property
      a ∈ e.1.occurrences ∪ e.2.occurrences) : a.1 ∈ quantities

namespace NamedWrittenLaws

variable {k : Type u} {P : PrimitivePresentation.{u}} (L : NamedWrittenLaws k P)
variable {U V : DeclarationContext P}

/-- The complete family of required coefficient Laws used by this presentation. -/
abbrev laws (_ : NamedWrittenLaws k P) := registeredCoefficientLaws k P

/-- The registered coefficient equation exists at each Law name in the family. -/
theorem hasEquation (l : L.laws) : (P.coefficientEquation k l.val.val).isSome :=
  l.property

/-- Read the two authored expressions directly from their original registration. -/
def equation (l : L.laws) : WrittenCoefficientEquation k P.signature (P.theory.law l.val).context :=
  (P.coefficientEquation k l.val.val).get (L.hasEquation l)

/-- Reading a coefficient Law recovers the original registered syntax. -/
theorem coefficientWriting_eq (l : L.laws) :
    P.coefficientWriting l.val.val = some ⟨k, L.equation l⟩ :=
  PrimitivePresentation.coefficientWriting_of_equation (Option.some_get (L.hasEquation l)).symm

/-- All and only the applications used by either side in its original syntax. -/
abbrev Occurrence (l : L.laws) :=
  {a // a ∈ (L.equation l).1.occurrences ∪ (L.equation l).2.occurrences}

/-- The original named equation with the actual typed applications in its two sides. -/
def written : WrittenLaws k P.signature where
  Quantity := L.quantities
  domainContext j := j.val.operation.arity.inputs
  Law := L.laws
  inputContext l := (P.theory.law l.val).context
  Occurrence := L.Occurrence
  application l a := ⟨⟨a.val.1, L.hasQuantity l a.val a.property⟩, a.val.2⟩
  left l := (L.equation l).1.compile (fun a ha => ⟨a, Or.inl ha⟩)
  right l := (L.equation l).2.compile (fun a ha => ⟨a, Or.inr ha⟩)

private theorem occurrence_kept {l : L.laws} (keep : Declaration.law l.val.val ∈ U.declarations)
    (a : L.Occurrence l) : Declaration.coefficientApplicationSupport (P := P) a.val ⊆ U.declarations :=
  fun _ used => Declaration.coefficientWritingSupport_subset_of_mem keep (L.coefficientWriting_eq l)
    ⟨a.val, a.property, used⟩

/-- Actual declaration closure supplies the names and terms of every retained coefficient equation. -/
def selection (U : DeclarationContext P) : L.written.DeclarationSelection where
  context := U
  quantities := {j | Declaration.ofOperation j.val.operation ∈ U.declarations}
  laws := {l | Declaration.law l.val.val ∈ U.declarations}
  domainSorts {j} keep := operationInputs j.val.operation keep
  inputSorts {l} keep :=
    (Declaration.sorts_subset_lawBody (P.theory.law l.val)).trans (Declaration.lawBody_subset_of_mem keep)
  applicationKept keep a :=
    L.occurrence_kept keep a.val (Or.inl (Set.mem_singleton _))
  termKept keep a := by
    intro s i
    exact (Declaration.termContext_le_iff _).2
      (fun _ used => L.occurrence_kept keep a.val (Or.inr ⟨s, i, used⟩))

/-- The selected primitive presentation reads the original coefficient equation in the smaller signature. -/
theorem selected_coefficientWriting (l : (L.selection U).laws) :
    (Selected.presentation U).coefficientWriting ⟨l.val.val.val, l.property⟩ =
      some (Selected.selectCoefficientWriting ⟨l.val.val.val, l.property⟩
        ⟨k, L.equation l.val⟩ (L.coefficientWriting_eq l.val)) :=
  Selected.presentation_coefficientWriting _ (L.coefficientWriting_eq l.val)

/-- An actual inclusion of primitive contexts retains the same named coefficient expressions. -/
def inclusion (inside : V ≤ U) : (L.selection V).Inclusion (L.selection U) where
  context := inside
  quantities := fun _ keep => inside keep
  laws := fun _ keep => inside keep

/-- A coefficient equation keeps the exact antecedent of its named Law. -/
def nativeInput (A : ContextStructure U) (l : (L.selection U).laws) :
    Set (Assignment A.carrier (L.written.inputContext l.val)) :=
  {e | A.evaluation.holds (P.theory.law l.val.val).input
    (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e}

/-- The actual antecedent is preserved and reflected on retained state assignments. -/
theorem nativeInput_restrict_iff (A : ContextStructure U) (inside : V ≤ U)
    (l : (L.selection V).laws) (e : Assignment (A.restrict inside).carrier (L.written.inputContext l.val)) :
    e ∈ L.nativeInput (A.restrict inside) l ↔
      A.restrictAssignmentEquiv inside ((L.selection V).inputSorts l.property) e ∈
        L.nativeInput A (Set.inclusion (L.inclusion inside).laws l) :=
  A.restrict_holds_iff inside _ _ e

/-- Guards and state terms can read relations and fixed partial domains, while the
values of the designated quantities are supplied by the coefficient model. -/
structure FixedState (U : DeclarationContext P) : Prop where
  /-- The original antecedent only observes the fixed state. -/
  guard (l : (L.selection U).laws) :
    StateFormula (QuantityDeclaration.operation '' L.quantities) (P.theory.law l.val.val).input
  /-- The original argument terms only observe the fixed state. -/
  argument (l : (L.selection U).laws) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s) :
    StateTerm (QuantityDeclaration.operation '' L.quantities) ((L.selection U).applicationTerm l a i).val

/-- Read the state with the varying value graphs hidden. The domains of partial
quantities remain available through the domain component. -/
def fixedStateEvaluation (A : ContextStructure U) : RestrictedEvaluation U A.carrier where
  relation := A.evaluation.relation
  domain := A.evaluation.domain
  graph op keep x y :=
    op ∉ QuantityDeclaration.operation '' L.quantities ∧ A.evaluation.graph op keep x y

/-- Hiding the varying values preserves the fixed state, including every partial domain. -/
theorem fixedStateEvaluation_agrees (A : ContextStructure U) :
    SameStateEvaluation (QuantityDeclaration.operation '' L.quantities) A.evaluation (L.fixedStateEvaluation A) where
  relation _ _ _ := Iff.rfl
  domain _ _ _ := Iff.rfl
  graph _ fixed _ _ _ := ⟨fun holds => ⟨fixed, holds⟩, And.right⟩

/-- Evaluate a retained antecedent on the fixed state. -/
def fixedStateInput (A : ContextStructure U) (l : (L.selection U).laws) :
    Set (Assignment A.carrier (L.written.inputContext l.val)) :=
  {e | (L.fixedStateEvaluation A).holds (P.theory.law l.val.val).input
    (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e}

/-- The original antecedent has the same truth with varying value graphs hidden. -/
theorem FixedState.input_eq_native {L : NamedWrittenLaws k P} (S : L.FixedState U)
    (A : ContextStructure U) (l : (L.selection U).laws) :
    L.fixedStateInput A l = L.nativeInput A l :=
  Set.ext fun e => ((L.fixedStateEvaluation_agrees A).holds_iff _ (S.guard l) _ e).symm

/-- Evaluate a retained term on the fixed state, keeping its original typed arguments. -/
def fixedStateEvaluatesArgument (A : ContextStructure U)
    (l : (L.selection U).laws) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s)
    (e : Assignment A.carrier (L.written.inputContext l.val)) (y : A.carrier s) : Prop :=
  let t := (L.selection U).applicationTerm l a i
  (L.fixedStateEvaluation A).holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)
    (Assignment.cons y e)

/-- Reading a state term gives its actual value, whether the varying values are visible or hidden. -/
theorem FixedState.argument_evaluates_iff {L : NamedWrittenLaws k P} (S : L.FixedState U)
    (A : ContextStructure U) (l : (L.selection U).laws) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s)
    (e : Assignment A.carrier (L.written.inputContext l.val)) (y : A.carrier s) :
    L.fixedStateEvaluatesArgument A l a i e y ↔ A.evaluates ((L.selection U).applicationTerm l a i) e y :=
  ((L.fixedStateEvaluation_agrees A).evaluates_iff _ (S.argument l a i) e y).symm

/-- Prescribed quantity domains and evaluated arguments at the actual guards. -/
structure GuardedInterpretation (A : ContextStructure U) where
  /-- The retained formulas use only the fixed part of the state. -/
  fixedState : L.FixedState U
  /-- The prescribed domain on the fixed state for every retained quantity. -/
  domain (j : (L.selection U).quantities) : Set (Assignment A.carrier (L.written.domainContext j.val))
  /-- Evaluate each used application at a genuine input of its registered Law. -/
  value (l : (L.selection U).laws) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val) :
    domain ((L.selection U).applicationQuantity l a)
  /-- Each stored argument is read by evaluating the original typed term on the fixed state. -/
  argument (l : (L.selection U).laws) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s) :
    L.fixedStateEvaluatesArgument A l a i e.val ((value l e a).val i)

/-- Read the prescribed values and the actual original antecedent as a written interpretation. -/
def GuardedInterpretation.toInterpretation {A : ContextStructure U} (I : L.GuardedInterpretation A) :
    (L.selection U).Interpretation A where
  domain := I.domain
  input := L.fixedStateInput A
  value l e := I.value l ⟨e.val, (I.fixedState.input_eq_native A l) ▸ e.property⟩
  argument l e a := by
    intro s i
    exact (I.fixedState.argument_evaluates_iff A l a i _ _).mp
      (I.argument l ⟨e.val, (I.fixedState.input_eq_native A l) ▸ e.property⟩ a i)

/-- The reduct of a guarded interpretation evaluates the original antecedents in the reduced state. -/
theorem restrict_input_eq_native {A : ContextStructure U} (I : L.GuardedInterpretation A) (inside : V ≤ U)
    (l : (L.selection V).laws) :
    (I.toInterpretation.restrict (L.inclusion inside)).input l = L.nativeInput (A.restrict inside) l := by
  rw [I.toInterpretation.restrict_input]
  change {e | A.restrictAssignmentEquiv inside ((L.selection V).inputSorts l.property) e ∈
    L.fixedStateInput A (Set.inclusion (L.inclusion inside).laws l)} = L.nativeInput (A.restrict inside) l
  rw [I.fixedState.input_eq_native]
  exact Set.ext fun e => (L.nativeInput_restrict_iff A inside l e).symm

/-- The application type used by the actual selected registration at this Law. -/
abbrev SelectedApplication (l : (L.selection V).laws) :=
  DeclaredApplication (Selected.signature V) ((Selected.laws V).statement ⟨l.val.val.val, l.property⟩).context

variable {A : ContextStructure U} (I : L.GuardedInterpretation A) (inside : V ≤ U)

/-- The written model of the actual declaration reduct with retained domains and inputs. -/
abbrev restrictedInterpretation := I.toInterpretation.restrict (L.inclusion inside)

private def pairApplication (l : (L.selection V).laws) (e : (L.restrictedInterpretation I inside).input l)
    (a : L.written.UsedOccurrence l.val) :
    L.SelectedApplication l × (L.restrictedInterpretation I inside).presentation.Coordinate :=
  ⟨Selected.selectCoefficientApplication ((L.selection V).inputSorts l.property) a.val.val
      (L.occurrence_kept l.property a.val),
    ⟨(L.selection V).applicationQuantity l a, (L.restrictedInterpretation I inside).value l e a⟩⟩

private def pairedLeft (l : (L.selection V).laws) (e : (L.restrictedInterpretation I inside).input l) :
    Expression k (L.SelectedApplication l × (L.restrictedInterpretation I inside).presentation.Coordinate) :=
  (L.equation l.val).1.compile fun a ha =>
    let name : L.Occurrence l.val := ⟨a, Or.inl ha⟩
    have used : name ∈ (L.written.left l.val).occurrences :=
      (L.equation l.val).1.mem_compile_occurrences _ ha
    L.pairApplication I inside l e ⟨name, Or.inl used⟩

private def pairedRight (l : (L.selection V).laws) (e : (L.restrictedInterpretation I inside).input l) :
    Expression k (L.SelectedApplication l × (L.restrictedInterpretation I inside).presentation.Coordinate) :=
  (L.equation l.val).2.compile fun a ha =>
    let name : L.Occurrence l.val := ⟨a, Or.inr ha⟩
    have used : name ∈ (L.written.right l.val).occurrences :=
      (L.equation l.val).2.mem_compile_occurrences _ ha
    L.pairApplication I inside l e ⟨name, Or.inr used⟩

/-- Each leaf of the retained Law pairs its trusted selected declaration with its evaluated coordinate.

The first projections read the literal writing from the actual selected presentation.
The second projections are precisely the compiled sides used to define the comparison.
-/
theorem registeredSides_compile (l : (L.selection V).laws) (e : (L.restrictedInterpretation I inside).input l) :
    ∃ (left right : Expression k (L.SelectedApplication l × (L.restrictedInterpretation I inside).presentation.Coordinate)),
      (Selected.presentation V).coefficientEquation k ⟨l.val.val.val, l.property⟩ =
        some (left.rename Prod.fst, right.rename Prod.fst) ∧
      (L.restrictedInterpretation I inside).presentation.left l e = left.rename Prod.snd ∧
      (L.restrictedInterpretation I inside).presentation.right l e = right.rename Prod.snd := by
  refine ⟨L.pairedLeft I inside l e, L.pairedRight I inside l e, ?_, ?_, ?_⟩
  · rw [PrimitivePresentation.coefficientEquation, L.selected_coefficientWriting l, Option.bind_some]
    simp only [pairedLeft, pairedRight, Expression.rename_compile]
    exact RegisteredCoefficientEquation.atType_mk _ _
  · simp only [WrittenLaws.DeclarationSelection.Interpretation.presentation, written, pairedLeft,
      Expression.rename_compile, Expression.compile_compile]
    rfl
  · simp only [WrittenLaws.DeclarationSelection.Interpretation.presentation, written, pairedRight,
      Expression.rename_compile, Expression.compile_compile]
    rfl

/-- The residual used by the comparison evaluates both sides of the selected registration at its real guard. -/
theorem registeredResidual [CommRing k] (l : (L.selection V).laws) (e : L.nativeInput (A.restrict inside) l) :
    let J := L.restrictedInterpretation I inside
    let F := J.presentation
    ∃ (left right : Expression k (L.SelectedApplication l × F.Coordinate)),
      (Selected.presentation V).declaredConclusion ⟨l.val.val.val, l.property⟩ =
        .coefficient ⟨k, left.rename Prod.fst, right.rename Prod.fst⟩ ∧
      ∃ input : F.Input l, input.val = e.val ∧
        F.residual l input =
          left.eval (fun a => F.universalQuantity a.2.1 a.2.2) -
            right.eval (fun a => F.universalQuantity a.2.1 a.2.2) := by
  let input : (L.restrictedInterpretation I inside).input l :=
    ⟨e.val, (L.restrict_input_eq_native I inside l).symm ▸ e.property⟩
  obtain ⟨left, right, selected, leftCompiled, rightCompiled⟩ := L.registeredSides_compile I inside l input
  refine ⟨left, right, PrimitivePresentation.declaredConclusion_of_coefficientEquation selected, input, rfl, ?_⟩
  rw [Presentation.residual, leftCompiled, rightCompiled, Expression.eval_rename, Expression.eval_rename]
  rfl

/-- The actual primitive restriction of registered scalar equations commutes with changing coefficients. -/
theorem lawMap_baseChange [CommRing k] {A : ContextStructure U} (I : L.GuardedInterpretation A)
    (inside : V ≤ U) (R : Type u) [CommRing R] [Algebra k R] :
    let F := (I.toInterpretation.restrict (L.inclusion inside)).presentation
    let ι := I.toInterpretation.lawMap (L.inclusion inside)
    (baseChangeQuotient (R := k) R I.toInterpretation.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  I.toInterpretation.lawMap_baseChange (L.inclusion inside) R

/-- The same registered equation and guard give the comparison on a principal open. -/
theorem lawMap_localization [CommRing k] {A : ContextStructure U} (I : L.GuardedInterpretation A)
    (inside : V ≤ U) (r : k) :
    let R := Localization.Away r
    let F := (I.toInterpretation.restrict (L.inclusion inside)).presentation
    let ι := I.toInterpretation.lawMap (L.inclusion inside)
    (baseChangeQuotient (R := k) R I.toInterpretation.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  L.lawMap_baseChange I inside (Localization.Away r)

end NamedWrittenLaws

end

end SHIGURE.Quantities
