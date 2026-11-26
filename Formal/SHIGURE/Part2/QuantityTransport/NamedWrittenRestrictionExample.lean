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

private def guard : Formula signature [()] := .atom (.rel () (fun i => i))
private def law : Law signature := ⟨[()], guard, .truth⟩

private def application : DeclaredApplication signature [()] :=
  ⟨.total false, ⟨.var⟩⟩

private def registeredEquation : WrittenCoefficientEquation ℤ signature [()] :=
  (.quantity application, .scalar 1)

private def primitive : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => law, fun _ => .required⟩
  derived _ impossible := by cases impossible
  coefficientLaw _ := some ⟨⟨ℤ, registeredEquation⟩, rfl, rfl⟩

private theorem coefficientEquation_eq (n : primitive.laws.LawName) :
    primitive.coefficientEquation ℤ n = some registeredEquation := by
  change (some ⟨ℤ, registeredEquation⟩ : Option (RegisteredCoefficientEquation signature [()])).bind
    (·.atType ℤ) = _
  simp

private def written : NamedWrittenLaws ℤ primitive where
  quantities := Set.univ
  laws := Set.univ
  hasEquation l := by simp [coefficientEquation_eq l.val.val]
  hasQuantity _ _ _ := Set.mem_univ _

private theorem equation_eq (l : written.laws) : written.equation l = registeredEquation := by
  apply Option.some.inj
  exact (Option.some_get (written.hasEquation l)).trans (coefficientEquation_eq l.val.val)

private theorem used_eq (l : written.laws) (a : written.Occurrence l) : a.val = application := by
  obtain ⟨a, used⟩ := a
  change a ∈ (written.equation l).1.occurrences ∪ (written.equation l).2.occurrences at used
  rw [equation_eq] at used
  exact Set.mem_singleton_iff.mp (by simpa [registeredEquation, Expression.occurrences] using used)

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
      change Declaration.quantity true ∈ Declaration.declaredLawSupport (P := primitive) l ∪ ∅ at hd
      rcases hd with (native | coefficient) | impossible
      · change Declaration.quantity true ∈ Declaration.lawBody (P := primitive) law at native
        simp [Declaration.lawBody, law, guard, Declaration.formula, Declaration.atomic,
          Declaration.sorts] at native
      · change (∃ a ∈ ({application} ∪ ∅ : Set _),
          Declaration.quantity true ∈ Declaration.coefficientApplicationSupport (P := primitive) a) at coefficient
        obtain ⟨a, used, support⟩ := coefficient
        rw [Set.union_empty] at used
        obtain rfl := Set.mem_singleton_iff.mp used
        rcases support with named | ⟨s, i, arg⟩
        · have same := Set.mem_singleton_iff.mp named
          cases same
        · simp [Declaration.formulaSupport, application, Term.graph_eq_graphAt, Term.graphAt,
            Declaration.formula, Declaration.atomic, Declaration.sorts] at arg
      · exact impossible

private theorem inside : retained ≤ Full := fun _ _ => Set.mem_univ _

private def state : Structure signature where
  carrier _ := PUnit
  total _ _ := PUnit.unit
  relation _ := Set.univ
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity _ _ := PUnit.unit

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full state

private def reading : written.GuardedInterpretation ambient where
  domain _ := Set.univ
  value l e a := by
    obtain ⟨⟨a, support⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨a, support⟩
    exact ⟨e.val, Set.mem_univ _⟩
  argument l _ a := by
    intro s i
    obtain ⟨⟨a, support⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨a, support⟩
    rfl

private abbrev interpreted := reading.toInterpretation

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
  rw [coefficientEquation_eq]
  simp [registeredEquation]

/-- The coefficient equation keeps its quantity in every selected declaration context. -/
theorem named_law_keeps_quantity (U : DeclarationContext primitive) (l : (written.selection U).laws) :
    Declaration.quantity false ∈ U.declarations := by
  apply Declaration.coefficientWritingSupport_subset_of_mem l.property
    (show primitive.coefficientWriting l.val.val.val = some ⟨ℤ, registeredEquation⟩ from rfl)
  exact ⟨application, Or.inl (Set.mem_singleton _), Or.inl (Set.mem_singleton _)⟩

/-- The actual selected presentation retains the literal one in the original Law. -/
theorem named_restriction_retains_literal (l : (written.selection retained).laws) :
    ∃ left, (Selected.presentation retained).declaredConclusion
      ⟨l.val.val.val, l.property⟩ = .coefficient ⟨ℤ, left, .scalar 1⟩ := by
  have reg : primitive.coefficientWriting l.val.val.val = some ⟨ℤ, registeredEquation⟩ := rfl
  let name : retained.RetainedLaw := ⟨l.val.val.val, l.property⟩
  let selected := Selected.selectCoefficientWriting name ⟨ℤ, registeredEquation⟩ reg
  refine ⟨selected.2.1, PrimitivePresentation.declaredConclusion_of_coefficientEquation ?_⟩
  rw [PrimitivePresentation.coefficientEquation, Selected.presentation_coefficientWriting _ reg]
  change (some selected).bind (·.atType ℤ) = some (selected.2.1, .scalar 1)
  rw [Option.bind_some]
  exact RegisteredCoefficientEquation.atType_mk ℤ (selected.2.1, .scalar 1)

/-- The actual named scalar Law excludes zero even though the native carrier has one point. -/
theorem named_law_rejects_zero :
    ¬ interpreted.presentation.Holds (R := ℤ) (fun _ _ => 0) := by
  intro holds
  have eq := holds l ⟨point, inGuard⟩
  simp only [WrittenLaws.DeclarationSelection.Interpretation.presentation, NamedWrittenLaws.written,
    Expression.eval_compile_const] at eq
  rw [equation_eq l.val] at eq
  simp [registeredEquation, Expression.eval] at eq

/-- The retained equation uses the guard evaluated in the actual reduct. -/
theorem named_restriction_reads_guard (l : (written.selection retained).laws) :
    (interpreted.restrict (written.inclusion inside)).input l = written.nativeInput (ambient.restrict inside) l :=
  written.restrict_input_eq_native reading inside l

/-- The structural reduct forgetting the independent quantity commutes with arbitrary coefficient change. -/
theorem named_restriction_baseChange (R : Type) [CommRing R] [Algebra ℤ R] :
    let F := (interpreted.restrict (written.inclusion inside)).presentation
    let ι := interpreted.lawMap (written.inclusion inside)
    (baseChangeQuotient (R := ℤ) R interpreted.presentation.residualIdeal).symm.toAlgHom.comp
        (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := ℤ) R F.residualIdeal).symm.toAlgHom :=
  written.lawMap_baseChange reading inside R


private def literalOnly (r : ℤ) : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => ⟨[], .truth, .truth⟩, fun _ => .required⟩
  derived _ impossible := by cases impossible
  coefficientLaw _ := some ⟨⟨ℤ, .scalar r, .scalar 0⟩, rfl, rfl⟩

/-- A reading origin cannot replace the registered literals, even with identical dependency sets. -/
theorem reading_origin_rejects_replaced_literal
    (U : DeclarationContext (literalOnly 1)) : IsEmpty (ReadingOrigin (literalOnly 0) (literalOnly 1) U) where
  false origin := by
    have same := eq_of_heq (origin.coefficientWriting_eq ())
    change some (⟨ℤ, .scalar (0 : ℤ), .scalar 0⟩ : RegisteredCoefficientEquation signature []) =
      some ⟨ℤ, .scalar (1 : ℤ), .scalar 0⟩ at same
    simp at same

end

end SHIGURE.Quantities.NamedWrittenRestrictionExample
