import Formal.SHIGURE.Part2.QuantityTransport.NamedWrittenRestriction

/-! # A literal coefficient equation with a declared guard

The native state has one point. Its declared guarded Law names a
quantity read at that point. The written scalar equation prescribes
the external coefficient `1`. A second quantity is independent and
is forgotten, while the guarded Law retains its relation.
-/

namespace SHIGURE.Quantities.NamedWrittenRestrictionExample

open DeclarationContext

noncomputable section

private def signature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Unit
  Partial := Empty
  Quantity := Bool
  totalArity _ := ⟨[()], ()⟩
  relInputs _ := [()]
  partialArity p := nomatch p
  quantityArity _ := ⟨[()], ()⟩

private def quantityTerm : Term signature [()] () := .app (.quantity false) (fun i => .var i)
private def oneTerm : Term signature [()] () := .app (.total ()) (fun i => .var i)
private def guard : Formula signature [()] := .atom (.rel () (fun i => i))
private def equation : OrderedEquation signature := ⟨[()], (), guard, quantityTerm, oneTerm⟩

private def registeredEquation : WrittenCoefficientEquation ℤ signature [()] :=
  (.quantity ⟨.total false, ⟨.var⟩⟩, .scalar 1)

private def primitive : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => equation.toLaw, fun _ => .required⟩
  otherOrderedEquation _ := some ⟨equation.write, rfl⟩
  derived _ impossible := by cases impossible
  coefficientEquation k _ := by
    classical
    exact if same : k = ℤ then some (same.symm ▸ registeredEquation) else none

private def written : NamedWrittenLaws ℤ primitive where
  quantities := Set.univ
  laws := Set.univ
  Occurrence _ := Unit
  application _ _ := ⟨⟨.total false, Set.mem_univ _⟩, ⟨.var⟩⟩
  left _ := .quantity ()
  right _ := .scalar 1
  registered _ := by
    simp [primitive, registeredEquation, Expression.rename]
  supports _ _ _ := by
    constructor
    · apply Or.inr
      change Declaration.ofOperation (P := primitive) (.quantity false) ∈
        Declaration.formula (Formula.termEq quantityTerm oneTerm)
      rw [Formula.termEq_eq_ex, Declaration.formula_ex, Declaration.formula_conj]
      exact Or.inr (Or.inl (Selected.termReferences_subset_graph (P := primitive) quantityTerm
        (Or.inl (Set.mem_singleton _))))
    · intro s i
      rw [Declaration.formulaSupport_eq]
      apply Set.union_subset
      · apply Declaration.sorts_cons_subset _ (Declaration.sorts_subset_lawBody (P := primitive) equation.toLaw)
        exact Declaration.sorts_subset_lawBody (P := primitive) equation.toLaw
          (Declaration.sort_mem_sorts (by
            change s ∈ ([()] : List Unit)
            cases s
            exact List.mem_cons_self))
      · exact Set.empty_subset _

private abbrev Full := DeclarationContext.full primitive

private def retained : DeclarationContext primitive where
  declarations := {d | d ≠ .quantity true}
  closed {a} ha := by
    intro d hd equal
    subst d
    cases a with
    | sort => exact hd
    | total => obtain ⟨_, _, h⟩ := hd; cases h
    | relation => obtain ⟨_, _, h⟩ := hd; cases h
    | partialOp p => exact nomatch p
    | quantity q => obtain ⟨_, _, h⟩ := hd; cases h
    | law l =>
      change Declaration.quantity true ∈
        (Declaration.lawBody equation.toLaw ∪ (∅ : Set (Declaration primitive))) at hd
      simp [Declaration.lawBody, equation, guard, OrderedEquation.toLaw, Formula.termEq_eq_ex,
        quantityTerm, oneTerm, Term.graphAt, Term.graph, signature, Operation.arity, Formula.existsMany,
        Formula.conjoin, Declaration.formula, Declaration.atomic, Declaration.sorts, Declaration.ofOperation] at hd

private theorem inside : retained ≤ Full := fun _ _ => Set.mem_univ _

private def state : Structure signature where
  carrier _ := PUnit
  total _ _ := PUnit.unit
  relation _ := Set.univ
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity _ _ := PUnit.unit

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full state

private def reading : written.GuardedInterpretation ambient :=
  ⟨{ domain := fun _ => Set.univ
     input := written.nativeInput ambient
     value := fun _ e _ => ⟨e.val, Set.mem_univ _⟩
     argument := fun _ _ _ _ _ => rfl }, fun _ => rfl⟩

private def l : (written.selection Full).laws :=
  ⟨⟨⟨(), rfl⟩, Set.mem_univ _⟩, Set.mem_univ _⟩

private def point : Assignment ambient.carrier [()] :=
  Assignment.cons
    ((Equiv.ofBijective (selectedMap Full state.carrier () (Set.mem_univ _))
      (selectedMap_bijective (U := Full) state.carrier () (Set.mem_univ _))).symm PUnit.unit) Assignment.empty

private theorem inGuard : point ∈ written.nativeInput ambient l := by
  change ambient.evaluation.holds (.atom (.rel () (fun i => i))) (Set.subset_univ _) point
  rw [RestrictedEvaluation.holds_atom_iff, RestrictedEvaluation.atomic_rel_iff]
  exact Set.mem_univ _

/-- A context keeping the actual Law declaration also keeps the guard relation. -/
theorem named_law_keeps_guard (U : DeclarationContext primitive) (l : (written.selection U).laws) :
    Declaration.relation () ∈ U.declarations :=
  Declaration.lawBody_subset_of_mem l.property (Or.inl (Or.inr (Set.mem_singleton _)))

/-- The same original declaration cannot register zero in place of the written coefficient one. -/
theorem named_law_retains_literal :
    primitive.coefficientEquation ℤ () ≠ some (registeredEquation.1, .scalar 0) := by
  simp [primitive, registeredEquation]

/-- The actual named scalar Law excludes zero even though the native carrier has one point. -/
theorem named_law_rejects_zero :
    ¬ reading.val.presentation.Holds (R := ℤ) (fun _ _ => 0) := by
  intro holds
  have eq := holds l ⟨point, inGuard⟩
  change (0 : ℤ) = algebraMap ℤ ℤ 1 at eq
  exact zero_ne_one (eq.trans (map_one _))

/-- The retained equation uses the guard evaluated in the actual reduct. -/
theorem named_restriction_reads_guard (l : (written.selection retained).laws) :
    (reading.val.restrict (written.inclusion inside)).input l = written.nativeInput (ambient.restrict inside) l :=
  written.restrict_input_eq_native reading inside l

/-- The structural reduct forgetting the independent quantity commutes with arbitrary coefficient change. -/
theorem named_restriction_baseChange (R : Type) [CommRing R] [Algebra ℤ R] :
    let F := (reading.val.restrict (written.inclusion inside)).presentation
    let ι := reading.val.lawMap (written.inclusion inside)
    (baseChangeQuotient (R := ℤ) R reading.val.presentation.residualIdeal).symm.toAlgHom.comp
        (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := ℤ) R F.residualIdeal).symm.toAlgHom :=
  written.lawMap_baseChange reading inside R

end

end SHIGURE.Quantities.NamedWrittenRestrictionExample
