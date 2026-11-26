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

/-- For a partial quantity, the selected inputs must also lie in its actual declared domain. -/
def fixedDomain (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))) :
    (j : (L.selection U).quantities) → Set (Assignment A.carrier (L.written.domainContext j.val))
  | ⟨⟨.total q, chosen⟩, keep⟩ => selected ⟨⟨.total q, chosen⟩, keep⟩
  | ⟨⟨.partialOp p, chosen⟩, keep⟩ =>
    {e | A.evaluation.domain p keep e ∧ e ∈ selected ⟨⟨.partialOp p, chosen⟩, keep⟩}

/-- Interpretations over the same state can differ only at the selected inputs
of the designated quantities. The actual partial domains stay fixed. -/
structure SameFixedState (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (B : RestrictedEvaluation U A.carrier) : Prop
    extends SameStateEvaluation (QuantityDeclaration.operation '' L.quantities) A.evaluation B where
  /-- All graphs still represent functions, with partial values only on their domains. -/
  structural : B.Structural
  /-- The graphs outside the selected inputs keep their original values. -/
  outside (j : (L.selection U).quantities) (x : Assignment A.carrier (L.written.domainContext j.val))
    (unselected : x ∉ L.fixedDomain A selected j) (y : A.carrier j.val.val.operation.arity.output) :
    A.evaluation.graph j.val.val.operation j.property x y ↔ B.graph j.val.val.operation j.property x y

/-- The actual state determines the antecedents and argument values. A
replacement must still interpret its graphs as functions on the same domains. -/
structure FixedState (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (admissible : RestrictedEvaluation U A.carrier → Prop := fun _ => True) : Prop where
  /-- Replacing quantity values preserves the truth of the original antecedent. -/
  guard (l : (L.selection U).laws) (B : RestrictedEvaluation U A.carrier) (same : L.SameFixedState A selected B)
    (allowed : admissible B) (e : Assignment A.carrier (L.written.inputContext l.val)) :
    e ∈ L.nativeInput A l ↔ B.holds (P.theory.law l.val.val).input
      (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e
  /-- A state argument has the same evaluation on each actual Law input. -/
  argument (l : (L.selection U).laws) (B : RestrictedEvaluation U A.carrier) (same : L.SameFixedState A selected B)
    (allowed : admissible B) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s)
    (y : A.carrier s) :
    let t := (L.selection U).applicationTerm l a i
    A.evaluates t e.val y ↔ B.holds t.val.graph
      ((Declaration.termContext_le_iff t.val).1 t.property) (Assignment.cons y e.val)

/-- State-only syntax supplies the semantic invariance required of a fixed state. -/
theorem FixedState.ofSyntax {L : NamedWrittenLaws k P} (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (guard : ∀ l : (L.selection U).laws,
      StateFormula (QuantityDeclaration.operation '' L.quantities) (P.theory.law l.val.val).input)
    (argument : ∀ (l : (L.selection U).laws) (a : L.written.UsedOccurrence l.val)
      {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s),
      StateTerm (QuantityDeclaration.operation '' L.quantities) ((L.selection U).applicationTerm l a i).val) :
    L.FixedState A selected where
  guard l _ same _ e := same.toSameStateEvaluation.holds_iff _ (guard l) _ e
  argument l _ same _ e a := by
    intro s i y
    exact same.toSameStateEvaluation.evaluates_iff _ (argument l a i) e.val y

/-- A family of values at the designated native quantity coordinates. -/
abbrev SelectedOutput (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))) :=
  ∀ j : (L.selection U).quantities, L.fixedDomain A selected j → A.carrier j.val.val.operation.arity.output

private def candidateStructure (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (value : L.SelectedOutput A selected) : RestrictedStructure U := by
  classical
  exact { A.toRestrictedStructure with
    quantity := fun q keep e =>
      if chosen : QuantityDeclaration.total q ∈ L.quantities then
        if present : e ∈ selected ⟨⟨.total q, chosen⟩, keep⟩ then
          value ⟨⟨.total q, chosen⟩, keep⟩ ⟨e, present⟩
        else A.toRestrictedStructure.quantity q keep e
      else A.toRestrictedStructure.quantity q keep e
    partialValue := fun p keep e =>
      if chosen : QuantityDeclaration.partialOp p ∈ L.quantities then
        if present : e.val ∈ selected ⟨⟨.partialOp p, chosen⟩, keep⟩ then
          value ⟨⟨.partialOp p, chosen⟩, keep⟩ ⟨e.val, e.property, present⟩
        else A.toRestrictedStructure.partialValue p keep e
      else A.toRestrictedStructure.partialValue p keep e }

/-- Replace only the output at each designated coordinate, preserving its native domain. -/
def candidateEvaluation (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (value : L.SelectedOutput A selected) : RestrictedEvaluation U A.carrier :=
  (L.candidateStructure A selected value).evaluation

/-- The representative evaluation preserves the actual domains and all unselected values. -/
theorem candidateEvaluation_agrees (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (value : L.SelectedOutput A selected) :
    L.SameFixedState A selected (L.candidateEvaluation A selected value) where
  structural := (L.candidateStructure A selected value).evaluation_structural
  relation _ _ _ := Iff.rfl
  domain _ _ _ := Iff.rfl
  graph op fixed keep x y := by
    rw [← A.toRestrictedStructure_evaluation]
    cases op with
    | total _ => rfl
    | quantity q =>
      have notChosen : QuantityDeclaration.total q ∉ L.quantities :=
        fun chosen => fixed ⟨.total q, chosen, rfl⟩
      simp [candidateEvaluation, candidateStructure, RestrictedStructure.evaluation_graph,
        RestrictedStructure.graph_quantity_iff, notChosen]
    | partialOp p =>
      have notChosen : QuantityDeclaration.partialOp p ∉ L.quantities :=
        fun chosen => fixed ⟨.partialOp p, chosen, rfl⟩
      simp [candidateEvaluation, candidateStructure, RestrictedStructure.evaluation_graph,
        RestrictedStructure.graph_partial_iff, notChosen]
  outside j x unselected y := by
    rw [← A.toRestrictedStructure_evaluation]
    rcases j with ⟨⟨q, chosen⟩, keep⟩
    cases q with
    | total q =>
      have absent : x ∉ selected ⟨⟨.total q, chosen⟩, keep⟩ := unselected
      simp [QuantityDeclaration.operation, candidateEvaluation, candidateStructure,
        RestrictedStructure.evaluation_graph, RestrictedStructure.graph_quantity_iff, chosen, absent]
    | partialOp p =>
      simp only [QuantityDeclaration.operation, RestrictedStructure.evaluation_graph,
        RestrictedStructure.graph_partial_iff, candidateEvaluation, candidateStructure, dif_pos chosen]
      apply exists_congr
      intro defined
      have absent : x ∉ selected ⟨⟨.partialOp p, chosen⟩, keep⟩ :=
        fun present => unselected ⟨defined, present⟩
      simp only [dif_neg absent]

/-- The structural candidate has precisely the supplied output at every selected coordinate. -/
theorem candidateEvaluation_graph (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (value : L.SelectedOutput A selected)
    (j : (L.selection U).quantities) (x : L.fixedDomain A selected j) :
    (L.candidateEvaluation A selected value).graph j.val.val.operation j.property x.val (value j x) := by
  rcases j with ⟨⟨q, chosen⟩, keep⟩
  cases q with
  | total q =>
    have present : x.val ∈ selected ⟨⟨.total q, chosen⟩, keep⟩ := x.property
    simp [QuantityDeclaration.operation, candidateEvaluation, candidateStructure,
      RestrictedStructure.evaluation_graph, RestrictedStructure.graph_quantity_iff, chosen, present]
  | partialOp p =>
    have domain := x.property.1
    have present := x.property.2
    simp only [QuantityDeclaration.operation, candidateEvaluation, RestrictedStructure.evaluation_graph,
      RestrictedStructure.graph_partial_iff]
    exact ⟨domain, by simp [candidateStructure, chosen, present]⟩

/-- Independent scalar values at the selected coordinates. -/
abbrev ScalarCandidate (R : Type u) (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))) :=
  (j : (L.selection U).quantities) → L.fixedDomain A selected j → R

/-- A faithful native encoding of scalars at each selected coordinate. -/
abbrev NativeEncoding (R : Type u) (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))) :=
  (j : (L.selection U).quantities) → L.fixedDomain A selected j → R ↪ A.carrier j.val.val.operation.arity.output

/-- The candidate evaluation uses the encoded scalar values in its actual graphs. -/
def RepresentsScalars {R : Type u} {A : ContextStructure U}
    {selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))}
    (encode : L.NativeEncoding R A selected) (q : L.ScalarCandidate R A selected)
    (B : RestrictedEvaluation U A.carrier) : Prop :=
  ∀ j x, B.graph j.val.val.operation j.property x.val (encode j x (q j x))

/-- Every scalar candidate can be evaluated with its prescribed native encoding. -/
theorem candidateEvaluation_represents {R : Type u} {A : ContextStructure U}
    {selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))}
    (encode : L.NativeEncoding R A selected) (q : L.ScalarCandidate R A selected) :
    L.RepresentsScalars encode q
      (L.candidateEvaluation A selected (fun j x => encode j x (q j x))) :=
  L.candidateEvaluation_graph A selected _

private theorem outputNonempty (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (j : (L.selection U).quantities) (x : L.fixedDomain A selected j) :
    Nonempty (A.carrier j.val.val.operation.arity.output) := by
  rcases j with ⟨⟨q, chosen⟩, keep⟩
  cases q with
  | total q => exact ⟨A.toRestrictedStructure.quantity q keep x.val⟩
  | partialOp p => exact ⟨A.toRestrictedStructure.partialValue p keep ⟨x.val, x.property.1⟩⟩

/-- Evaluate using fixed representatives at the selected inputs. The choice
at each coordinate depends only on the output type and its inhabitation. -/
def fixedStateEvaluation (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))) :
    RestrictedEvaluation U A.carrier :=
  L.candidateEvaluation A selected fun j x => Classical.choice (L.outputNonempty A selected j x)

/-- The fixed representative is a structural evaluation of the original state. -/
theorem fixedStateEvaluation_agrees (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))) :
    L.SameFixedState A selected (L.fixedStateEvaluation A selected) :=
  L.candidateEvaluation_agrees A selected _

/-- Evaluate a retained antecedent on the fixed state. -/
def fixedStateInput (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (l : (L.selection U).laws) :
    Set (Assignment A.carrier (L.written.inputContext l.val)) :=
  {e | (L.fixedStateEvaluation A selected).holds (P.theory.law l.val.val).input
    (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e}

/-- The original antecedent gives the fixed input set under a structural replacement. -/
theorem FixedState.input_eq_native {L : NamedWrittenLaws k P} {A : ContextStructure U}
    {selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))}
    (S : L.FixedState A selected) (l : (L.selection U).laws) :
    L.fixedStateInput A selected l = L.nativeInput A l :=
  Set.ext fun e => (S.guard l _ (L.fixedStateEvaluation_agrees A selected) trivial e).symm

/-- Evaluate a retained term on the fixed state, keeping its original typed arguments. -/
def fixedStateEvaluatesArgument (A : ContextStructure U)
    (selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val)))
    (l : (L.selection U).laws) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s)
    (e : Assignment A.carrier (L.written.inputContext l.val)) (y : A.carrier s) : Prop :=
  let t := (L.selection U).applicationTerm l a i
  (L.fixedStateEvaluation A selected).holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)
    (Assignment.cons y e)

/-- Evaluating a state term at an original Law input gives its actual value. -/
theorem FixedState.argument_evaluates_iff {L : NamedWrittenLaws k P} {A : ContextStructure U}
    {selected : ∀ j : (L.selection U).quantities, Set (Assignment A.carrier (L.written.domainContext j.val))}
    (S : L.FixedState A selected) (l : (L.selection U).laws) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s)
    (y : A.carrier s) :
    L.fixedStateEvaluatesArgument A selected l a i e.val y ↔ A.evaluates ((L.selection U).applicationTerm l a i) e.val y :=
  (S.argument l _ (L.fixedStateEvaluation_agrees A selected) trivial e a i y).symm

/-- Read the registered coefficient Law at the fixed source state. Candidates
take values in the coefficient algebra, independently of the native output
carrier. Each application reads its actual state terms on the original input. -/
structure GuardedInterpretation (A : ContextStructure U) where
  /-- The prescribed inputs at which each retained quantity varies. -/
  selectedDomain (j : (L.selection U).quantities) : Set (Assignment A.carrier (L.written.domainContext j.val))
  /-- Evaluate each used application at a genuine input of its registered Law. -/
  value (l : (L.selection U).laws) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val) :
    L.fixedDomain A selectedDomain ((L.selection U).applicationQuantity l a)
  /-- Each stored argument is the value of the original typed term in the source state. -/
  argument (l : (L.selection U).laws) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s) :
    A.evaluates ((L.selection U).applicationTerm l a i) e.val ((value l e a).val i)

/-- A candidate-independent evaluation also yields a reading of the actual source state. -/
def GuardedInterpretation.ofFixedState {A : ContextStructure U}
    {selected : ∀ j : (L.selection U).quantities,
      Set (Assignment A.carrier (L.written.domainContext j.val))}
    (S : L.FixedState A selected)
    (value : ∀ (l : (L.selection U).laws) (_ : L.nativeInput A l) (a : L.written.UsedOccurrence l.val),
      L.fixedDomain A selected ((L.selection U).applicationQuantity l a))
    (argument : ∀ (l : (L.selection U).laws) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val)
      {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s),
      L.fixedStateEvaluatesArgument A selected l a i e.val ((value l e a).val i)) :
    L.GuardedInterpretation A where
  selectedDomain := selected
  value := value
  argument l e a := by
    intro s i
    exact (S.argument_evaluates_iff l e a i _).mp (argument l e a i)

/-- Read the prescribed coordinates and the actual original antecedent. -/
def GuardedInterpretation.toInterpretation {A : ContextStructure U} (I : L.GuardedInterpretation A) :
    (L.selection U).Interpretation A where
  domain := L.fixedDomain A I.selectedDomain
  input := L.nativeInput A
  value := I.value
  argument := I.argument

/-- The abstract source input agrees with the antecedent in every represented
scalar candidate, when the original antecedent is invariant on those candidates. -/
theorem GuardedInterpretation.nativeCandidateInput {R : Type u} {A : ContextStructure U}
    (I : L.GuardedInterpretation A) (encode : L.NativeEncoding R A I.selectedDomain)
    (S : L.FixedState A I.selectedDomain (fun B => ∃ q, L.RepresentsScalars encode q B))
    (l : (L.selection U).laws) (q : L.ScalarCandidate R A I.selectedDomain)
    (B : RestrictedEvaluation U A.carrier) (same : L.SameFixedState A I.selectedDomain B)
    (represents : L.RepresentsScalars encode q B) :
    I.toInterpretation.input l = {e | B.holds (P.theory.law l.val.val).input
      (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e} :=
  Set.ext fun e => S.guard l B same ⟨q, represents⟩ e

/-- The registered application arguments are also evaluated correctly in
each candidate realizing the chosen native encoding. -/
theorem GuardedInterpretation.nativeCandidateArgument {R : Type u} {A : ContextStructure U}
    (I : L.GuardedInterpretation A) (encode : L.NativeEncoding R A I.selectedDomain)
    (S : L.FixedState A I.selectedDomain (fun B => ∃ q, L.RepresentsScalars encode q B))
    (l : (L.selection U).laws) (e : L.nativeInput A l) (a : L.written.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.written.domainContext (L.written.application l.val a.val).1) s)
    (q : L.ScalarCandidate R A I.selectedDomain)
    (B : RestrictedEvaluation U A.carrier) (same : L.SameFixedState A I.selectedDomain B)
    (represents : L.RepresentsScalars encode q B) :
    let t := (L.selection U).applicationTerm l a i
    B.holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)
      (Assignment.cons ((I.value l e a).val i) e.val) :=
  (S.argument l B same ⟨q, represents⟩ e a i _).mp (I.argument l e a i)

/-- The reduct of a guarded interpretation evaluates the original antecedents in the reduced state. -/
theorem restrict_input_eq_native {A : ContextStructure U} (I : L.GuardedInterpretation A) (inside : V ≤ U)
    (l : (L.selection V).laws) :
    (I.toInterpretation.restrict (L.inclusion inside)).input l = L.nativeInput (A.restrict inside) l := by
  rw [I.toInterpretation.restrict_input]
  change {e | A.restrictAssignmentEquiv inside ((L.selection V).inputSorts l.property) e ∈
    L.nativeInput A (Set.inclusion (L.inclusion inside).laws l)} = L.nativeInput (A.restrict inside) l
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
