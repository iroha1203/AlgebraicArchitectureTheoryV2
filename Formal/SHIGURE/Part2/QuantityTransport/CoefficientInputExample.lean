import Formal.SHIGURE.Part2.QuantityTransport.DeclarationRestriction
import Mathlib.Data.ZMod.Basic

/-! # Reading a coefficient from a registered input

The single registered Law reads its coefficient from the input variable.
Both sides return values in the image of `Option.some`. Their scalar
readings are faithful there even though the result carrier has an extra
point and cannot inject into the coefficient ring.
-/

namespace SHIGURE.Quantities.CoefficientInputExample

open DeclarationContext

noncomputable section

/-- The finite field used for the coefficients and quantity values. -/
private abbrev Scalar := ZMod 3

/-- A quantity has scalar result. Addition records its result in a separate carrier. -/
private def signature : Signature where
  SortType := Bool
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Unit
  totalArity _ := ⟨[false, false], true⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity _ := ⟨[false], false⟩

/-- The argument of the sole quantity is the source variable. -/
private def varying : Set (QuantityDeclaration signature) := {.total ()}

/-- The variable is read as a state coefficient at each named input. -/
private def stateVariable : Term signature [false] false := .var .here

/-- The only designated varying symbol. -/
private def quantityName : varying := ⟨.total (), Set.mem_singleton _⟩

/-- The original typed application of the only varying quantity. -/
private def quantityTerm : CoefficientTerm varying [false] false :=
  .quantity quantityName ⟨.var⟩

/-- The fixed binary operation adds the scalar readings. -/
private def plusSymbol : CoefficientSymbol signature ⟨[false, false], true⟩ := ⟨.total (), rfl⟩

/-- The written residual is `q(x) + x - (x + x)`. -/
private def left : CoefficientTerm varying [false] true :=
  .add plusSymbol quantityTerm (.scalar stateVariable)

/-- The same variable supplies both coefficients on the right. -/
private def right : CoefficientTerm varying [false] true :=
  .add plusSymbol (.scalar stateVariable) (.scalar stateVariable)

/-- Preserve one registered Law for every value of the input variable. -/
private def equation : OrderedEquation signature :=
  ⟨[false], true, .truth, left.toTerm, right.toTerm⟩

/-- The presentation registers the original typed term pair. -/
private def primitive : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => equation.toLaw, fun _ => .required⟩
  otherOrderedEquation _ := some ⟨equation.write, rfl⟩
  derived _ impossible := by cases impossible

/-- Use the registered syntax directly as the polynomial reading. -/
private def written : DeclaredQuantityLaws primitive where
  quantities := varying
  quantityLaws := Set.univ
  valueSort _ := true
  left _ := left
  right _ := right
  expansion _ := .original _
  registeredEquation l registered attached := by
    cases l.val.val
    cases Option.some.inj attached
    rfl

/-- The `none` point belongs to the actual carrier but addition never returns it. -/
private abbrev carrier : Bool → Type
  | false => Scalar
  | true => Option Scalar

/-- The original addition computes the sum inside the attained part of the result carrier. -/
private def base : Structure signature where
  carrier := carrier
  total _ args := some (args .here + args (.there .here))
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity _ args := args .here

/-- The full declaration context for the input example. -/
private abbrev Full := DeclarationContext.full primitive

/-- Evaluate the literal original declarations. -/
private def ambient : ContextStructure Full := ContextStructure.ofStructure Full base

/-- All terms in this example belong to the full context. -/
private def supported {Γ : List signature.SortType} {s : signature.SortType}
    (t : Term signature Γ s) : Full.TermIn Γ s :=
  ⟨t, fun _ _ => Set.mem_univ _⟩

/-- Identify the retained input or result with its carrier in the supplied structure. -/
private def readCarrier (s : signature.SortType) : ambient.carrier s ≃ carrier s :=
  Equiv.ofBijective (selectedMap Full base.carrier s (Set.mem_univ _))
    (selectedMap_bijective (U := Full) base.carrier s (Set.mem_univ _))

/-- The extra result has a default reading, outside the values attained by the Law. -/
private def read (s : signature.SortType) (x : ambient.carrier s) : Scalar :=
  match s with
  | false => readCarrier false x
  | true => (readCarrier true x).getD 0

/-- A replacement leaves the fixed arithmetic primitive unchanged. -/
private theorem fixed_plus (B : RestrictedEvaluation Full ambient.carrier)
    (same : written.SameDeclarationState ambient (fun _ => Set.univ) B)
    (xs : Assignment ambient.carrier [false, false]) (y : ambient.carrier true)
    (edge : B.graph (.total ()) (Set.mem_univ _) xs y) :
    readCarrier true y = some (readCarrier false (xs .here) + readCarrier false (xs (.there .here))) := by
  have noQuantity : Operation.total (sig := signature) () ∉ QuantityDeclaration.operation '' varying := by
    rintro ⟨j, hj, equal⟩
    cases Set.mem_singleton_iff.mp hj
    cases equal
  have original := (same.graph (.total ()) noQuantity (Set.mem_univ _) xs y).2 edge
  have actual := (ContextStructure.ofStructure_graph_iff Full base (.total ()) (Set.mem_univ _) xs y).1 original
  rw [Structure.graph_total_iff] at actual
  exact actual.symm

/-- An evaluated plus term returns a value in the attained part of the native carrier. -/
private theorem reached_plus (B : RestrictedEvaluation Full ambient.carrier)
    (same : written.SameDeclarationState ambient (fun _ => Set.univ) B)
    (t u : Term signature [false] false) (input : Assignment ambient.carrier [false])
    (y : ambient.carrier true)
    (held : B.holds (plusSymbol.term (fun i => t.argsCons (u.argsCons Term.argsNil) i)).graph
      (Set.subset_univ _) (Assignment.cons y input)) :
    readCarrier true y = some (read true y) := by
  let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
  have ⟨args, _, edge⟩ := (CoefficientSymbol.evaluates_term_iff (P := primitive) (U := Full) plusSymbol C
    (fun i => t.argsCons (u.argsCons Term.argsNil) i) (supported _).property input (Set.mem_univ _) y).1 held
  have actual := fixed_plus B same args y edge
  change readCarrier true y = some ((readCarrier true y).getD 0)
  rw [actual]
  rfl

/-- A variable evaluates to the argument at its original position. -/
private theorem variable_eval (B : ContextStructure Full) (e : Assignment B.carrier [false]) :
    B.evaluates (supported stateVariable) e (e .here) := rfl

/-- Every evaluation of the original written arithmetic is within the attained result image. -/
private theorem sides_defined (l : written.KeptLaw Full) (e : written.lawInput ambient l)
    (B : RestrictedEvaluation Full ambient.carrier) (same : written.SameDeclarationState ambient (fun _ => Set.univ) B) :
    (∃ y, B.holds left.toTerm.graph (Set.subset_univ _) (Assignment.cons y e.val)) ∧
      (∃ y, B.holds right.toTerm.graph (Set.subset_univ _) (Assignment.cons y e.val)) := by
  let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
  obtain ⟨value, edge⟩ := (C.quantity_graph_valid () (Set.mem_univ _)).2 e.val
  have quantityValue : C.evaluates (supported quantityTerm.toTerm) e.val value :=
    C.evaluates_app_of_graph (.quantity ()) (fun i => .var i) _ rfl e.val e.val
      (fun i => by cases i with
        | here => exact ⟨(supported stateVariable).property, variable_eval C e.val⟩
        | there i => nomatch i) (Set.mem_univ _) value edge
  have add {t u : Term signature [false] false} {a b : ambient.carrier false}
      (first : C.evaluates (supported t) e.val a) (second : C.evaluates (supported u) e.val b) :
      ∃ y, C.evaluates (supported (plusSymbol.term (fun i => t.argsCons (u.argsCons Term.argsNil) i))) e.val y := by
    let args := Assignment.cons a (Assignment.cons b Assignment.empty)
    obtain ⟨z, edge⟩ := (C.total_graph_valid () (Set.mem_univ _)).2 args
    refine ⟨z, (CoefficientSymbol.evaluates_term_iff (P := primitive) (U := Full) plusSymbol C
      (fun i => t.argsCons (u.argsCons Term.argsNil) i) (supported _).property e.val (Set.mem_univ _) z).2
        ⟨args, ?_, edge⟩⟩
    intro s i
    cases i with
    | here => exact ⟨(supported t).property, first⟩
    | there i =>
      cases i with
      | here => exact ⟨(supported u).property, second⟩
      | there i => nomatch i
  exact ⟨add quantityValue (variable_eval C e.val), add (variable_eval C e.val) (variable_eval C e.val)⟩

/-- Confirm the singleton state term occurring as the coefficient in both written sides. -/
private theorem state_coefficient_eq (a : CoefficientTerm.StateCoefficient signature [false])
    (h : Sum.inl a ∈ left.leaves ∪ right.leaves) : a = ⟨false, stateVariable⟩ := by
  simpa [left, right, quantityTerm, CoefficientTerm.leaves] using h

/-- Compile the actual fixed input and the equality on reached native outputs. -/
private def interpretation : written.Interpretation (k := Scalar) ambient where
  read s _ := read s
  quantityRead j _ := by
    cases j.val.val with
    | total q => exact (readCarrier false).surjective
    | partialOp p => nomatch p
  selectedDomain _ := Set.univ
  lawRead l e B same := by
    let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
    have reached (y : ambient.carrier true)
        (h : C.evaluates (supported left.toTerm) e.val y ∨ C.evaluates (supported right.toTerm) e.val y) :
        readCarrier true y = some (read true y) :=
      h.elim (reached_plus B same quantityTerm.toTerm stateVariable e.val y)
        (reached_plus B same stateVariable stateVariable e.val y)
    intro x hx y hy equal
    exact (readCarrier true).injective ((reached x hx).trans ((congrArg some equal).trans (reached y hy).symm))
  arithmeticAt l a e B same x y _ edge := by
    have op : a.val.1 = .add plusSymbol := by
      obtain ⟨⟨op, args⟩, used⟩ := a
      change ⟨op, args⟩ ∈ left.arithmeticApplications ∪ right.arithmeticApplications at used
      have one := used
      simp [left, right, quantityTerm, CoefficientTerm.arithmeticApplications] at one
      rcases one with eq | eq <;> exact eq.1
    obtain ⟨⟨name, args⟩, used⟩ := a
    change name = .add plusSymbol at op
    subst name
    have actual := fixed_plus B same x y edge
    change (readCarrier true y).getD 0 = _
    rw [actual]
    rfl
  coefficientIndependent l a e B same x y original replacement := by
    obtain ⟨a, used⟩ := a
    have eq := state_coefficient_eq a used
    subst a
    let C : ContextStructure Full := ⟨ambient.carrier, ambient.omitted, B, same.structural⟩
    have originalValue := ambient.evaluates_unique (supported stateVariable) e.val original (variable_eval ambient e.val)
    have replacementValue := C.evaluates_unique (supported stateVariable) e.val replacement (variable_eval C e.val)
    exact congrArg (read false) (replacementValue.trans originalValue.symm)
  value _ e a := by
    obtain ⟨⟨⟨j, chosen⟩, args⟩, used⟩ := a
    change j ∈ varying at chosen
    obtain rfl := Set.mem_singleton_iff.mp chosen
    exact ⟨e.val, Set.mem_univ _⟩
  inputIndependent _ _ _ _ := Iff.rfl
  argumentIndependent l B same e a := by
    obtain ⟨⟨j, args⟩, used⟩ := a
    have found : (⟨j, args⟩ : CoefficientTerm.Application varying [false]) =
        ⟨quantityName, ⟨.var⟩⟩ := by
      change Sum.inr ⟨j, args⟩ ∈ left.leaves ∪ right.leaves at used
      simpa [left, right, quantityTerm, CoefficientTerm.leaves] using used
    cases found
    intro s i
    cases i with
    | here => rfl
    | there i => nomatch i
  definedSides := sides_defined

/-- There cannot be a globally injective read of the actual equality carrier into the coefficient ring. -/
theorem no_global_read : ¬ ∃ f : ambient.carrier true → Scalar, Function.Injective f := by
  rintro ⟨f, injective⟩
  let g : Option Scalar → Scalar := f ∘ (readCarrier true).symm
  have bound := Fintype.card_le_of_injective g (injective.comp (readCarrier true).symm.injective)
  norm_num [Scalar] at bound

/-- The named quantity is retained in the full declaration context. -/
private def appliedQuantity : written.KeptQuantity Full :=
  ⟨quantityName, Set.mem_univ _⟩

/-- The coordinate at an input is the one obtained by evaluating the named quantity argument. -/
private def atInput {l : written.KeptLaw Full} (e : written.lawInput ambient l) :
    interpretation.domain appliedQuantity := ⟨e.val, Set.mem_univ _⟩

/-- The actual registered Law is satisfied exactly when the candidate quantity equals the input. -/
theorem scalar_input_law
    (l : written.KeptLaw Full) (e : written.lawInput ambient l) (q : interpretation.presentation.Candidate Scalar) :
    (interpretation.candidateStructure q).evaluation.holds (primitive.theory.law l.val.val).conclusion
        (lawConclusionSupport (Declaration.lawBody_subset_of_mem l.property)) e.val ↔
      q appliedQuantity (atInput e) = read false (e.val .here) := by
  rw [interpretation.candidate_conclusion_iff l e q, Presentation.evaluate_residual]
  let coefficient : written.UsedCoefficient l.val := ⟨⟨false, stateVariable⟩, by
    change Sum.inl ⟨false, stateVariable⟩ ∈ left.leaves ∪ right.leaves
    simp [left, right, quantityTerm, CoefficientTerm.leaves]⟩
  have value := interpretation.coefficientValue_eq_of_evaluates l e coefficient (e.val .here)
    (variable_eval ambient e.val)
  let c := algebraMap Scalar Scalar (interpretation.coefficientValue l e coefficient)
  change (q appliedQuantity (atInput e) + c) - (c + c) = 0 ↔ _
  change interpretation.coefficientValue l e coefficient = read false (e.val .here) at value
  dsimp [c]
  rw [value]
  exact ⟨fun h => add_right_cancel (sub_eq_zero.mp h), fun h => sub_eq_zero.mpr (congrArg (· + _) h)⟩

/-- The identity candidate reads the original argument, preserving the same Law for every input. -/
private def identityCandidate : interpretation.presentation.Candidate Scalar
  | ⟨⟨.total _, _⟩, _⟩, a => read false (a.val .here)
  | ⟨⟨.partialOp name, _⟩, _⟩, _ => nomatch name

/-- The registered input-dependent equation has a native solution. -/
theorem identity_candidate_satisfies (l : written.KeptLaw Full) :
    (interpretation.candidateStructure identityCandidate).evaluation.satisfies (primitive.theory.law l.val.val)
      (Declaration.lawBody_subset_of_mem l.property) := by
  intro a guard
  exact (scalar_input_law l ⟨a, guard⟩ identityCandidate).2 rfl

/-- The sole required Law is retained by the full context. -/
private def exampleLaw : written.KeptLaw Full :=
  ⟨⟨⟨(), rfl⟩, Set.mem_univ _⟩, Set.mem_univ _⟩

/-- A constant shift of the candidate breaks the same equation even at zero. -/
theorem shifted_candidate_fails :
    ¬ (interpretation.candidateStructure (fun j a => identityCandidate j a + 1)).evaluation.satisfies
      (primitive.theory.law exampleLaw.val.val) (Declaration.lawBody_subset_of_mem exampleLaw.property) := by
  intro holds
  let e := Assignment.cons ((readCarrier false).symm 0) Assignment.empty
  have guard : e ∈ written.lawInput ambient exampleLaw := trivial
  have evaluated := (scalar_input_law exampleLaw ⟨e, guard⟩ _).1 (holds e guard)
  change readCarrier false ((readCarrier false).symm 0) + 1 = readCarrier false ((readCarrier false).symm 0) at evaluated
  simp at evaluated

end

end SHIGURE.Quantities.CoefficientInputExample
