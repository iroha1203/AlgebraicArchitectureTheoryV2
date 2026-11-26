import Formal.SHIGURE.Part2.QuantityTransport.DeclarationRestriction

/-! # Declared quantity restriction over the integers

The original Law uses a strict binder and has distinct input and output
sorts for addition. The marked addition may vary off the diagonal.
Subtraction and the coefficient one are partial operations.
The partial sample is defined at two integers. A fixed relation selects one,
and the Law guard also asks whether the sample graph has an output there.
-/

namespace SHIGURE.Quantities.DeclaredRestrictionExample

open DeclarationContext

noncomputable section

private inductive Partial
  | sample
  | one
  | difference

private def signature : Signature where
  SortType := Bool
  Total := Unit
  Rel := Unit
  Partial := Partial
  Quantity := Unit
  totalArity _ := ⟨[], true⟩
  relInputs _ := [false]
  partialArity
    | .sample => ⟨[false], false⟩
    | .one => ⟨[], true⟩
    | .difference => ⟨[true, true], true⟩
  quantityArity _ := ⟨[false, false], true⟩

private def varying : Set (QuantityDeclaration signature) :=
  {j | j = .partialOp .sample ∨ j = .total ()}

private def sample : varying := ⟨.partialOp .sample, Or.inl rfl⟩

private def application : CoefficientTerm.Application varying [false] := ⟨sample, ⟨.var⟩⟩

private def oneSymbol : CoefficientSymbol signature ⟨[], true⟩ := ⟨.partialOp .one, rfl⟩

private def addSymbol : CoefficientSymbol signature ⟨[false, false], true⟩ := ⟨.quantity (), rfl⟩

private def differenceSymbol : CoefficientSymbol signature ⟨[true, true], true⟩ :=
  ⟨.partialOp .difference, rfl⟩

private def sampleTerm : CoefficientTerm varying [false] false := .quantity sample application.2

private def left : CoefficientTerm varying [false] true :=
  .add addSymbol sampleTerm sampleTerm

private def oneTerm {Γ : List signature.SortType} : Term signature Γ true :=
  oneSymbol.term Term.argsNil

private def right : CoefficientTerm varying [false] true :=
  .sub differenceSymbol (.scalar oneTerm) (.scalar oneTerm)

private def bound : Term signature [false, false] false := .var .here

private def addition {Γ : List signature.SortType} (t u : Term signature Γ false) : Term signature Γ true :=
  addSymbol.term (fun i => t.argsCons (u.argsCons Term.argsNil) i)

private def difference {Γ : List signature.SortType} (t u : Term signature Γ true) : Term signature Γ true :=
  differenceSymbol.term (fun i => t.argsCons (u.argsCons Term.argsNil) i)

private def originalLeft : Term signature [false] true :=
  sampleTerm.toTerm.letBind (addition bound bound)

private def guard : Formula signature [false] :=
  .conj (.atom (.rel () (fun i => i)))
    (.ex (.atom (.graph (.partialOp .sample) (fun i => .there i) .here)))

private def declarations : LawDeclarations signature where
  LawName := Unit
  statement _ := ⟨[false], guard, Formula.termEq originalLeft right.toTerm⟩
  role _ := .required

private def primitive : PrimitivePresentation where
  signature := signature
  laws := declarations
  otherOrderedEquation _ :=
    some ⟨(⟨[false], true, guard, originalLeft, right.toTerm⟩ : OrderedEquation signature).write, rfl⟩
  derived _ impossible := by cases impossible

private def written : DeclaredQuantityLaws primitive where
  quantities := varying
  quantityLaws := Set.univ
  valueSort _ := true
  left _ := left
  right _ := right
  leftSource _ := .inline originalLeft (by
    change Term.app (sig := signature) (.quantity ()) _ = Term.app (.quantity ()) _
    congr 1
    funext s i
    cases i with
    | here => rfl
    | there i =>
      cases i with
      | here => rfl
      | there i => nomatch i)
  expansion _ := .original _
  registeredEquation l registered attached := by
    cases l.val.val
    cases Option.some.inj attached
    rfl

private def base : Structure signature where
  carrier _ := ℤ
  total _ _ := 0
  relation _ := {e | e .here = 2}
  partialDomain
    | .sample => {e | e .here = 2 ∨ e .here = 3}
    | .one | .difference => Set.univ
  partialValue
    | .sample, _ => 0
    | .one, _ => 1
    | .difference, e => e.val .here - e.val (.there .here)
  quantity _ e := e .here + e (.there .here)

private abbrev Full := DeclarationContext.full primitive

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full base

private def supported {Γ : List signature.SortType} {s : signature.SortType}
    (t : Term signature Γ s) : Full.TermIn Γ s :=
  ⟨t, fun _ _ => Set.mem_univ _⟩

private def carrierRead (s : signature.SortType) : ambient.carrier s ≃ ℤ :=
  Equiv.ofBijective (selectedMap Full base.carrier s (Set.mem_univ _))
    (selectedMap_bijective (U := Full) base.carrier s (Set.mem_univ _))

/-- The guard is its fixed relation together with existence in the native sample domain. -/
private theorem domainGuard (B : RestrictedEvaluation Full ambient.carrier) (valid : B.Structural)
    (e : Assignment ambient.carrier [false]) :
    B.holds guard (Set.subset_univ _) e ↔
      B.relation () (Set.mem_univ _) e ∧ B.domain .sample (Set.mem_univ _) e := by
  change B.relation () (Set.mem_univ _) (e.pull (fun i => i)) ∧
    (∃ y, B.graph (.partialOp .sample) (Set.mem_univ _)
      ((Assignment.cons y e).pull (fun i => .there i)) ((Assignment.cons y e) .here)) ↔ _
  simp only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]
  have structural := RestrictedEvaluation.partial_graph_valid valid .sample (Set.mem_univ _)
  exact and_congr Iff.rfl ⟨fun ⟨y, h⟩ => structural.2.1 e y h, structural.2.2 e⟩

private theorem application_eq (a : CoefficientTerm.Application varying [false])
    (used : Sum.inr a ∈ left.leaves ∪ right.leaves) : a = application := by
  simpa [left, right, sampleTerm, CoefficientTerm.leaves, application] using used

private theorem coefficient_eq (a : CoefficientTerm.StateCoefficient signature [false])
    (used : Sum.inl a ∈ left.leaves ∪ right.leaves) : a = ⟨true, oneTerm⟩ := by
  simpa [left, right, sampleTerm, CoefficientTerm.leaves] using used

private def plusApplication : ArithmeticApplication signature [false] :=
  ⟨.add addSymbol, ⟨fun i => sampleTerm.toTerm.argsCons (sampleTerm.toTerm.argsCons Term.argsNil) i⟩⟩

private def subtractApplication : ArithmeticApplication signature [false] :=
  ⟨.sub differenceSymbol, ⟨fun i => oneTerm.argsCons (oneTerm.argsCons Term.argsNil) i⟩⟩

private theorem arithmetic_eq (a : ArithmeticApplication signature [false])
    (used : a ∈ left.arithmeticApplications ∪ right.arithmeticApplications) :
    a = plusApplication ∨ a = subtractApplication := by
  have found : a = subtractApplication ∨ a = plusApplication := by
    simpa [left, right, sampleTerm, CoefficientTerm.arithmeticApplications, CoefficientTerm.toTerm,
      plusApplication, subtractApplication, oneTerm] using used
  exact found.symm

/-- The marked addition changes off diagonal and the partial sample changes only at selected inputs. -/
private def varyingDomain :
    (j : written.KeptQuantity Full) → Set (Assignment ambient.carrier j.val.val.operation.arity.inputs)
  | ⟨⟨.total _, _⟩, _⟩ => {x | x .here ≠ x (.there .here)}
  | ⟨⟨.partialOp .sample, _⟩, _⟩ => {x | ambient.evaluation.relation () (Set.mem_univ _) x}
  | ⟨⟨.partialOp .one, _⟩, _⟩ => Set.univ
  | ⟨⟨.partialOp .difference, _⟩, _⟩ => Set.univ

private theorem fixedPartial (p : Partial) (notSample : p ≠ .sample)
    (B : RestrictedEvaluation Full ambient.carrier)
    (same : written.SameDeclarationState ambient varyingDomain B)
    (keep : Declaration.ofOperation (.partialOp (sig := signature) p) ∈ Full.declarations)
    (x : Assignment ambient.carrier (signature.partialArity p).inputs) (y : ambient.carrier (signature.partialArity p).output) :
    ambient.evaluation.graph (.partialOp p) keep x y ↔ B.graph (.partialOp p) keep x y := by
  apply same.graph
  rintro ⟨declaration, h, eq⟩
  change declaration = .partialOp .sample ∨ declaration = .total () at h
  rcases h with rfl | rfl
  · exact notSample (Operation.partialOp.inj eq).symm
  · cases eq

private theorem addRealizes :
    addSymbol.Realizes ambient (Set.mem_univ _) (selectedMap Full base.carrier)
      (fun a => a .here + a (.there .here)) := by
  intro a z graph
  have actual := (ContextStructure.ofStructure_graph_iff Full base (.quantity ())
    (Set.mem_univ _) a z).1 graph
  rw [Structure.graph_quantity_iff] at actual
  exact actual.symm

private theorem differenceRealizes :
    differenceSymbol.Realizes ambient (Set.mem_univ _) (selectedMap Full base.carrier)
      (fun a => a .here - a (.there .here)) := by
  intro a z graph
  have actual := (ContextStructure.ofStructure_graph_iff Full base (.partialOp .difference)
    (Set.mem_univ _) a z).1 graph
  obtain ⟨_, value⟩ := (Structure.graph_partial_iff _ _ _ _).1 actual
  exact value.symm

set_option maxHeartbeats 600000 in
private theorem sourceDefined (l : written.KeptLaw Full) (e : written.lawInput ambient l)
    (B : RestrictedEvaluation Full ambient.carrier)
    (same : written.SameDeclarationState ambient varyingDomain B) :
    (∃ y, B.holds originalLeft.graph (Set.subset_univ _) (Assignment.cons y e.val)) ∧
      (∃ y, B.holds right.toTerm.graph (Set.subset_univ _) (Assignment.cons y e.val)) := by
  let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
  have hz : B.domain .one (Set.mem_univ _) Assignment.empty :=
    (same.domain .one (Set.mem_univ _) Assignment.empty).1 (Set.mem_univ _)
  obtain ⟨z, oneEdge⟩ := (C.partial_graph_valid .one (Set.mem_univ _)).2.2 _ hz
  have oneEval {Γ : List signature.SortType} (a : Assignment ambient.carrier Γ) :
      C.evaluates (supported (oneTerm (Γ := Γ))) a z := by
    apply (CoefficientSymbol.evaluates_term_iff (P := primitive) (U := Full) oneSymbol C
      (@Term.argsNil signature Γ) (supported oneTerm).property a (Set.mem_univ _) z).2
    refine ⟨Assignment.empty, ?_, oneEdge⟩
    intro s i
    nomatch i
  have hs : B.domain .sample (Set.mem_univ _) e.val :=
    (same.domain .sample (Set.mem_univ _) e.val).1
      ((domainGuard ambient.evaluation ambient.structural e.val).1 e.property).2
  obtain ⟨x, sampleEdge⟩ := (C.partial_graph_valid .sample (Set.mem_univ _)).2.2 _ hs
  have init : C.evaluates (supported sampleTerm.toTerm) e.val x :=
    C.evaluates_app_of_graph (.partialOp .sample) (fun i => .var i) _ rfl e.val e.val
      (fun i => ⟨(supported (.var i)).property, rfl⟩) (Set.mem_univ _) x sampleEdge
  let extended := Assignment.cons x e.val
  let sumInput := Assignment.cons x (Assignment.cons x Assignment.empty)
  obtain ⟨sum, sumEdge⟩ := (C.quantity_graph_valid () (Set.mem_univ _)).2 sumInput
  have sumEval : C.evaluates (supported (addition bound bound)) extended sum :=
    C.evaluates_app_of_graph (.quantity ()) (fun i => bound.argsCons (bound.argsCons Term.argsNil) i)
      _ rfl extended sumInput (by
        intro s i
        cases i with
        | here => exact ⟨(supported bound).property, rfl⟩
        | there i =>
          cases i with
          | here => exact ⟨(supported bound).property, rfl⟩
          | there i => nomatch i) (Set.mem_univ _) sum sumEdge
  let inputs := Assignment.cons z (Assignment.cons z Assignment.empty)
  have hd : B.domain .difference (Set.mem_univ _) inputs :=
    (same.domain .difference (Set.mem_univ _) inputs).1 (Set.mem_univ _)
  obtain ⟨y, diffEdge⟩ := (C.partial_graph_valid .difference (Set.mem_univ _)).2.2 _ hd
  have rhs : C.evaluates (supported (difference oneTerm oneTerm)) e.val y :=
    C.evaluates_app_of_graph (.partialOp .difference)
      (fun i => oneTerm.argsCons (oneTerm.argsCons Term.argsNil) i)
      _ rfl e.val inputs (by
        intro s i
        cases i with
        | here => exact ⟨(supported oneTerm).property, oneEval e.val⟩
        | there i =>
          cases i with
          | here => exact ⟨(supported oneTerm).property, oneEval e.val⟩
          | there i => nomatch i) (Set.mem_univ _) y diffEdge
  exact ⟨⟨sum, C.evaluates_let_of_values (supported sampleTerm.toTerm) (supported (addition bound bound))
      (supported originalLeft).property e.val x sum init sumEval⟩,
    ⟨y, rhs⟩⟩

private def interpretation : written.Interpretation (k := ℤ) ambient where
  read := selectedMap Full base.carrier
  selectedDomain := varyingDomain
  quantityOutput j _ r := (carrierRead j.val.val.operation.arity.output).symm r
  quantityOutput_read j _ r := (carrierRead j.val.val.operation.arity.output).apply_symm_apply r
  lawRead l _ _ _ _ := by
    intro _ _ _ _ equals
    exact (selectedMap_bijective (U := Full) base.carrier (written.valueSort l.val) _).1 equals
  arithmeticAt l a e B same _ x y each edge := by
    obtain ⟨a, used⟩ := a
    change a ∈ left.arithmeticApplications ∪ right.arithmeticApplications at used
    rcases arithmetic_eq a used with rfl | rfl
    · let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
      have first : C.evaluates (supported sampleTerm.toTerm) e.val (x .here) :=
        each (.here : Var [false, false] false)
      have second : C.evaluates (supported sampleTerm.toTerm) e.val (x (.there .here)) :=
        each (.there .here : Var [false, false] false)
      have diagonal := C.evaluates_unique (supported sampleTerm.toTerm) e.val first second
      have fixed := (same.outside ⟨⟨.total (), Or.inr rfl⟩, Set.mem_univ _⟩ x (fun neq => neq diagonal) y).2 edge
      exact addRealizes x y fixed
    · exact differenceRealizes x y ((fixedPartial .difference (by intro eq; cases eq) B same _ x y).2 edge)
  coefficientDefined l a e := by
    have fixed := coefficient_eq a.val a.property
    rcases a with ⟨term, used⟩
    change term = ⟨true, oneTerm⟩ at fixed
    subst term
    obtain ⟨z, graph⟩ := (ambient.partial_graph_valid .one (Set.mem_univ _)).2.2
      Assignment.empty (Set.mem_univ _)
    refine ⟨z, (CoefficientSymbol.evaluates_term_iff (P := primitive) (U := Full) oneSymbol ambient
      Term.argsNil _ e.val (Set.mem_univ _) z).2 ⟨Assignment.empty, ?_, graph⟩⟩
    intro _ i
    nomatch i
  coefficientIndependent l a e B same _ x y original replacement := by
    have fixed := coefficient_eq a.val a.property
    rcases a with ⟨term, used⟩
    change term = ⟨true, oneTerm⟩ at fixed
    subst term
    let t := supported (oneTerm (Γ := [false]))
    have state : StateTerm (QuantityDeclaration.operation '' varying) t.val := by
      refine ⟨?_, fun i => nomatch i⟩
      rintro ⟨declaration, chosen, eq⟩
      change declaration = .partialOp .sample ∨ declaration = .total () at chosen
      rcases chosen with rfl | rfl <;> cases eq
    have localValue := (same.toSameStateEvaluation.evaluates_iff t state e.val y).2 replacement
    exact congrArg _ (ambient.evaluates_unique t e.val localValue original)
  value l e a := by
    have actual := application_eq a.val a.property
    obtain ⟨stored, used⟩ := a
    change stored = application at actual
    subst stored
    have holds := (domainGuard ambient.evaluation ambient.structural e.val).1 e.property
    exact ⟨e.val, holds.2, holds.1⟩
  inputIndependent _ B same _ e :=
    (domainGuard ambient.evaluation ambient.structural e).trans
      ((and_congr (same.relation () (Set.mem_univ _) e) (same.domain .sample (Set.mem_univ _) e)).trans
        (domainGuard B same.structural e).symm)
  argumentState l e a s i := by
    have actual := application_eq a.val a.property
    obtain ⟨stored, used⟩ := a
    change stored = application at actual
    subst stored
    exact rfl
  argumentIndependent l B same _ e a s i := by
    have actual := application_eq a.val a.property
    obtain ⟨stored, used⟩ := a
    change stored = application at actual
    subst stored
    exact rfl
  definedSides l e B same _ := sourceDefined l e B same

private def law : written.KeptLaw Full :=
  ⟨⟨⟨(), rfl⟩, Set.mem_univ _⟩, Set.mem_univ _⟩

private def input : written.lawInput ambient law := by
  let e := Assignment.cons ((carrierRead false).symm 2) Assignment.empty
  refine ⟨e, (domainGuard ambient.evaluation ambient.structural e).2 ?_⟩
  change carrierRead false ((carrierRead false).symm 2) = 2 ∧
    (carrierRead false ((carrierRead false).symm 2) = 2 ∨ carrierRead false ((carrierRead false).symm 2) = 3)
  simp

private def oneLeaf : written.UsedCoefficient law.val :=
  ⟨⟨true, oneTerm⟩, by simp [written, left, right, sampleTerm, CoefficientTerm.leaves]⟩

private theorem literal_one (e : written.lawInput ambient law) :
    interpretation.coefficientValue law e oneLeaf = 1 := by
  let z := (carrierRead true).symm 1
  have graph : oneSymbol.graph ambient (Set.mem_univ _) Assignment.empty z := by
    apply (ContextStructure.ofStructure_graph_iff Full base (.partialOp .one)
      (Set.mem_univ _) Assignment.empty z).2
    exact ⟨Set.mem_univ _, ((carrierRead true).apply_symm_apply 1).symm⟩
  have held : ambient.evaluates (written.keptCoefficient law oneLeaf) e.val z := by
    apply (oneSymbol.evaluates_term_iff ambient Term.argsNil _ e.val (Set.mem_univ _) z).2
    refine ⟨Assignment.empty, ?_, graph⟩
    intro _ i
    nomatch i
  exact (interpretation.coefficientValue_eq_of_evaluates law e oneLeaf z held).trans
    ((carrierRead true).apply_symm_apply 1)

/-- The guard reads the fixed relation and native domain in every candidate structure. -/
theorem guard_reads_fixed_domain (q : interpretation.presentation.Candidate ℤ)
    (e : Assignment ambient.carrier [false]) :
    (interpretation.candidateStructure q).evaluation.holds guard (Set.subset_univ _) e ↔
      ambient.evaluation.relation () (Set.mem_univ _) e ∧ ambient.evaluation.domain .sample (Set.mem_univ _) e :=
  (domainGuard _ (interpretation.candidateStructure q).structural e).trans
    ((and_congr ((interpretation.candidateStructure_sameState q).relation () (Set.mem_univ _) e)
      ((interpretation.candidateStructure_sameState q).domain .sample (Set.mem_univ _) e)).symm)

/-- The original written guard actually refers to the varying graph. -/
theorem guard_mentions_varying_graph :
    ¬ StateFormula (QuantityDeclaration.operation '' varying) guard := by
  intro state
  exact state.2 ⟨.partialOp .sample, Or.inl rfl, rfl⟩

/-- An atomic domain query is a fixed-state formula for the same varying sample. -/
theorem sample_domain_is_state_formula :
    StateFormula (QuantityDeclaration.operation '' varying)
      (Formula.atom (.domain (sig := signature) .sample (fun i => i))) :=
  trivial

/-- A variable is a fixed-state term of the written argument sort. -/
theorem variable_is_state_term :
    StateTerm (QuantityDeclaration.operation '' varying) (Term.var (sig := signature) (.here : Var [false] false)) :=
  trivial

/-- The compiled sample is a genuine varying application. -/
theorem sample_is_not_state_term :
    ¬ StateTerm (QuantityDeclaration.operation '' varying) sampleTerm.toTerm := by
  intro state
  exact state.1 ⟨.partialOp .sample, Or.inl rfl, rfl⟩

private def additionQuantity : written.KeptQuantity Full :=
  ⟨⟨.total (), Or.inr rfl⟩, Set.mem_univ _⟩

private def offDiagonal : interpretation.domain additionQuantity := by
  refine ⟨Assignment.cons ((carrierRead false).symm 1)
    (Assignment.cons ((carrierRead false).symm 2) Assignment.empty), ?_⟩
  change (carrierRead false).symm 1 ≠ (carrierRead false).symm 2
  intro eq
  have : (1 : ℤ) = 2 := (carrierRead false).symm.injective eq
  norm_num at this

/-- A candidate preserving the declared state can replace the same marked addition off the diagonal. -/
theorem off_diagonal_addition_changes :
    let B := interpretation.candidateStructure (fun _ _ => 0)
    written.SameDeclarationState ambient interpretation.selectedDomain B.evaluation ∧
      B.evaluation.graph (.quantity ()) (Set.mem_univ _) offDiagonal.val ((carrierRead true).symm 0) ∧
      ¬ ambient.evaluation.graph (.quantity ()) (Set.mem_univ _) offDiagonal.val ((carrierRead true).symm 0) := by
  dsimp only
  refine ⟨interpretation.candidateStructure_sameState _, ?_, ?_⟩
  · have value := interpretation.quantityOutput_read additionQuantity offDiagonal 0
    have exactValue : interpretation.quantityOutput additionQuantity offDiagonal 0 = (carrierRead true).symm 0 := by
      apply (carrierRead true).injective
      exact value.trans ((carrierRead true).apply_symm_apply 0).symm
    rw [← exactValue]
    exact interpretation.candidateStructure_graph (fun _ _ => 0) additionQuantity offDiagonal
  · intro old
    have reading := addRealizes offDiagonal.val ((carrierRead true).symm 0) old
    change carrierRead true ((carrierRead true).symm 0) =
      carrierRead false ((carrierRead false).symm 1) + carrierRead false ((carrierRead false).symm 2) at reading
    simp at reading

/-- The off-diagonal candidate need not realize addition on its entire graph. -/
theorem candidate_addition_fails_global_realization :
    ¬ addSymbol.Realizes (interpretation.candidateStructure (fun _ _ => 0)) (Set.mem_univ _)
      (selectedMap Full base.carrier) (fun a => a .here + a (.there .here)) := by
  intro realizes
  have edge := off_diagonal_addition_changes.2.1
  have read := realizes offDiagonal.val ((carrierRead true).symm 0) edge
  change carrierRead true ((carrierRead true).symm 0) =
    carrierRead false ((carrierRead false).symm 1) + carrierRead false ((carrierRead false).symm 2) at read
  simp at read

/-- Keeping all domains is part of fixed-state agreement. -/
theorem removing_sample_domain_changes_state :
    let B : RestrictedEvaluation Full ambient.carrier := { ambient.evaluation with domain := fun _ _ _ => False }
    ¬ SameStateEvaluation (QuantityDeclaration.operation '' varying) ambient.evaluation B := by
  dsimp only
  intro same
  exact (same.domain .sample (Set.mem_univ _) input.val).1
    ((domainGuard ambient.evaluation ambient.structural input.val).1 input.property).2

/-- Declaring every addition input fixed would exclude a valid off-diagonal replacement. -/
theorem off_diagonal_replacement_violates_empty_varying_domain :
    ¬ written.SameDeclarationState ambient (fun _ => ∅)
      (interpretation.candidateStructure (fun _ _ => 0)).evaluation := by
  intro same
  obtain ⟨_, candidate, absent⟩ := off_diagonal_addition_changes
  exact absent ((same.outside additionQuantity offDiagonal.val
    (Set.notMem_empty _) ((carrierRead true).symm 0)).2 candidate)

/-- The native partial graph stays defined at 3, outside the chosen argument set. -/
theorem partial_defined_outside_selection (q : interpretation.presentation.Candidate ℤ) :
    let e := Assignment.cons ((carrierRead false).symm 3) Assignment.empty
    let j : written.KeptQuantity Full := ⟨sample, Set.mem_univ _⟩
    e ∉ interpretation.domain j ∧
      (interpretation.candidateStructure q).evaluation.graph (.partialOp .sample) (Set.mem_univ _) e
        ((carrierRead false).symm 0) := by
  dsimp only
  let e := Assignment.cons ((carrierRead false).symm 3) Assignment.empty
  let j : written.KeptQuantity Full := ⟨sample, Set.mem_univ _⟩
  have excluded : e ∉ interpretation.domain j := by
    intro selected
    have h : carrierRead false ((carrierRead false).symm 3) = 2 := selected.2
    norm_num at h
  have old : ambient.evaluation.graph (.partialOp .sample) (Set.mem_univ _) e ((carrierRead false).symm 0) := by
    apply (ContextStructure.ofStructure_graph_iff Full base (.partialOp .sample) (Set.mem_univ _) e
      ((carrierRead false).symm 0)).2
    rw [Structure.graph_partial_iff]
    refine ⟨Or.inr ((carrierRead false).apply_symm_apply 3), ?_⟩
    exact ((carrierRead false).apply_symm_apply 0).symm
  exact ⟨excluded, ((interpretation.candidateStructure_sameState q).outside j e excluded
    ((carrierRead false).symm 0)).1 old⟩

/-- The original bound equality holds when the varying sample is zero. -/
theorem candidate_zero_holds :
    (interpretation.candidateStructure (fun _ _ => (0 : ℤ))).evaluation.satisfies
      (primitive.theory.law law.val.val) (Declaration.lawBody_subset_of_mem law.property) := by
  apply (interpretation.candidate_satisfies_iff law _).2
  intro e
  rw [Presentation.evaluate_residual]
  let c := algebraMap ℤ ℤ (interpretation.coefficientValue law e oneLeaf)
  change (0 + 0 : ℤ) - (c + -c) = 0
  simp [c, literal_one]

/-- The same original equality fails when the sample is one. -/
theorem candidate_one_fails :
    ¬ (interpretation.candidateStructure (fun _ _ => (1 : ℤ))).evaluation.satisfies
      (primitive.theory.law law.val.val) (Declaration.lawBody_subset_of_mem law.property) := by
  intro held
  have atInput := (interpretation.candidate_satisfies_iff law (fun _ _ => (1 : ℤ))).1 held input
  rw [Presentation.evaluate_residual] at atInput
  let c := algebraMap ℤ ℤ (interpretation.coefficientValue law input oneLeaf)
  change (1 + 1 : ℤ) - (c + -c) = 0 at atInput
  norm_num [c, literal_one] at atInput

end

end SHIGURE.Quantities.DeclaredRestrictionExample
