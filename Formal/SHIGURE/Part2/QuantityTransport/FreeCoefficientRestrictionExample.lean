import Formal.SHIGURE.Part2.QuantityTransport.DeclarationRestriction

/-! # A free scalar coordinate on a singleton native carrier

The written equation constrains one nullary quantity to zero. Another
retained quantity has native carrier `PUnit` and supplies a free
integer coordinate. Forgetting a third quantity gives a genuine
declaration restriction with the same retained equation.
-/

namespace SHIGURE.Quantities.FreeCoefficientRestrictionExample

open DeclarationContext

noncomputable section

private inductive Name
  | free | constrained | forgotten

private def signature : Signature where
  SortType := Bool
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Name
  totalArity _ := ⟨[], true⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := ⟨[], match q with | .free => false | _ => true⟩

private def quantities : Set (QuantityDeclaration signature) := Set.univ
private def zeroArgs : ∀ {s}, Var (signature.totalArity ()).inputs s → Term signature [] s :=
  fun i => nomatch i

private def zeroTerm : Term signature [] true := .app (.total ()) zeroArgs
private def constrainedName : quantities := ⟨.total .constrained, Set.mem_univ _⟩
private def left : CoefficientTerm quantities [] true := .quantity constrainedName ⟨fun {_} i => nomatch i⟩
private def right : CoefficientTerm quantities [] true := .scalar zeroTerm

private def equation : OrderedEquation signature := ⟨[], true, .truth, left.toTerm, right.toTerm⟩

private def primitive : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => equation.toLaw, fun _ => .required⟩
  otherOrderedEquation _ := some ⟨equation.write, rfl⟩
  derived _ impossible := by cases impossible

private def written : DeclaredQuantityLaws primitive where
  quantities := quantities
  quantityLaws := Set.univ
  valueSort _ := true
  left _ := left
  right _ := right
  expansion _ := .original _
  registeredEquation l registered attached := by
    cases l.val.val
    cases Option.some.inj attached
    rfl

private abbrev Full := DeclarationContext.full primitive

private def retained : DeclarationContext primitive where
  declarations := {d | d ≠ .quantity .forgotten}
  closed {a} ha := by
    intro d hd h
    subst d
    cases a with
    | sort => exact hd
    | total => obtain ⟨_, _, h⟩ := hd; cases h
    | relation r => exact nomatch r
    | partialOp p => exact nomatch p
    | quantity q => obtain ⟨_, _, h⟩ := hd; cases h
    | law l =>
      change Declaration.quantity Name.forgotten ∈
        (Declaration.lawBody equation.toLaw ∪ (∅ : Set (Declaration primitive))) at hd
      simp only [Set.union_empty, Declaration.lawBody_eq, equation, OrderedEquation.toLaw,
        Declaration.formula_truth, Set.union_empty, Formula.termEq_eq_ex, Declaration.formula_ex,
        Declaration.formula_conj] at hd
      simp [left, right, zeroTerm, constrainedName, CoefficientTerm.toTerm, Term.graph, Term.graphAt, QuantityDeclaration.operation,
        signature, Operation.arity, Formula.existsMany, Formula.conjoin,
        Declaration.formula, Declaration.atomic, Declaration.sorts,
        Declaration.ofOperation] at hd

private theorem inside : retained ≤ Full := fun _ _ => Set.mem_univ _

private abbrev Carrier : Bool → Type
  | false => PUnit
  | true => ℤ

private def base : Structure signature where
  carrier := Carrier
  total _ _ := (0 : ℤ)
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q _ := match q with | .free => PUnit.unit | .constrained => (0 : ℤ) | .forgotten => (0 : ℤ)

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full base

private def read (s : Bool) (keep : Declaration.sort s ∈ Full.declarations) (x : ambient.carrier s) : ℤ :=
  match s with
  | false => 0
  | true => selectedMap Full base.carrier true keep x

private def supported {s : signature.SortType} (t : Term signature [] s) : Full.TermIn [] s :=
  ⟨t, fun _ _ => Set.mem_univ _⟩

private theorem zero_defined (e : Assignment ambient.carrier []) :
    ∃ z, ambient.evaluates (supported zeroTerm) e z := by
  have fn := (ambient.total_graph_valid () (Set.mem_univ _)).2 Assignment.empty
  obtain ⟨z, hz⟩ := fn
  exact ⟨z, ambient.evaluates_app_of_graph (.total ()) zeroArgs (supported zeroTerm) rfl e Assignment.empty
    (fun i => nomatch i) (Set.mem_univ _) z hz⟩

private theorem zero_read {e : Assignment ambient.carrier []} {z : ambient.carrier true}
    (evaluated : ambient.evaluates (supported zeroTerm) e z) :
    read true (Set.mem_univ _) z = 0 := by
  obtain ⟨args, _, graph⟩ := (ambient.evaluates_app_iff (.total ()) zeroArgs
    (supported zeroTerm) rfl e (Set.mem_univ _) z).1 evaluated
  have native := (ContextStructure.ofStructure_graph_iff Full base (.total ()) (Set.mem_univ _) args z).1 graph
  rw [Structure.graph_total_iff] at native
  exact native.symm

private def reading : written.Reading (k := ℤ) ambient where
  read := read
  selectedDomain _ := Set.univ
  coefficientDefined l a e := by
    rcases a with ⟨⟨s, t⟩, used⟩
    simp only [written, right, left, CoefficientTerm.leaves, Set.mem_union, Set.mem_singleton_iff] at used
    rcases used with impossible | fixed
    · cases impossible
    · simp only [Sum.inl.injEq] at fixed
      cases fixed
      exact zero_defined e.val
  value _ _ a := by
    rcases a with ⟨⟨⟨q, chosen⟩, terms⟩, used⟩
    cases q with
    | total q => exact ⟨Assignment.empty, Set.mem_univ _⟩
    | partialOp p => exact nomatch p
  argumentState _ _ a := by
    intro s i
    rcases a with ⟨⟨⟨q, chosen⟩, terms⟩, used⟩
    cases q with
    | total q => exact nomatch i
    | partialOp p => exact nomatch p

private def free : written.KeptQuantity Full := ⟨⟨.total .free, Set.mem_univ _⟩, Set.mem_univ _⟩
private def freeInput : reading.domain free := ⟨Assignment.empty, Set.mem_univ _⟩

private def scalarCandidate (r : ℤ) : reading.presentation.Candidate ℤ
  | ⟨⟨.total .free, _⟩, _⟩, _ => r
  | ⟨⟨.total .constrained, _⟩, _⟩, _ => 0
  | ⟨⟨.total .forgotten, _⟩, _⟩, _ => 0
  | ⟨⟨.partialOp p, _⟩, _⟩, _ => nomatch p

/-- Every integral value of the free coordinate extends to a solution of the registered equation. -/
theorem free_scalar_model (r : ℤ) :
    ∃ q : reading.presentation.Model ℤ, q.val free freeInput = r := by
  refine ⟨⟨scalarCandidate r, ?_⟩, rfl⟩
  intro l e
  let a : written.UsedCoefficient l.val := ⟨⟨true, zeroTerm⟩, by
    change Sum.inl ⟨true, zeroTerm⟩ ∈ left.leaves ∪ right.leaves
    simp [left, right, CoefficientTerm.leaves]⟩
  change (0 : ℤ) = reading.coefficientValue l e a
  obtain ⟨z, evaluated⟩ := zero_defined e.val
  exact ((reading.coefficientValue_eq_of_evaluates l e a z evaluated).trans (zero_read evaluated)).symm

/-- A free scalar coordinate has no representation of all coefficients in its singleton carrier. -/
theorem free_native_output_impossible :
    ¬ ∃ output : written.OutputRepresentation (k := ℤ) ambient reading.selectedDomain,
      ∀ r : ℤ, reading.read false (operationOutput free.val.val.operation free.property)
        (output free freeInput r) = r := by
  rintro ⟨output, reads⟩
  have impossible := reads 1
  change (0 : ℤ) = 1 at impossible
  exact zero_ne_one impossible

private def retainedFree : written.KeptQuantity retained :=
  ⟨⟨.total .free, Set.mem_univ _⟩, by intro same; cases same⟩

/-- The comparison keeps the free coordinate and forgets the third quantity. -/
theorem free_coordinate_retained :
    (reading.declarationLawMap inside).name retainedFree = free ∧
      ¬ ∃ j : written.KeptQuantity retained,
        ((reading.declarationLawMap inside).name j).val.val = .total .forgotten := by
  refine ⟨rfl, ?_⟩
  rintro ⟨⟨⟨j, chosen⟩, keep⟩, equal⟩
  change j = .total .forgotten at equal
  subst j
  exact keep rfl

/-- Even with the retained free coordinate, the actual coefficient-change square commutes. -/
theorem free_coefficient_baseChange (R : Type) [CommRing R] [Algebra ℤ R] :
    let F := (reading.restrict inside).presentation
    let ι := reading.declarationLawMap inside
    (baseChangeQuotient (R := ℤ) R reading.presentation.residualIdeal).symm.toAlgHom.comp
        (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := ℤ) R F.residualIdeal).symm.toAlgHom :=
  reading.declarationLawMap_baseChange inside R

end

end SHIGURE.Quantities.FreeCoefficientRestrictionExample
