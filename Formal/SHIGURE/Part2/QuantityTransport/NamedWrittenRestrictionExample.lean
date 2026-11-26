import Formal.SHIGURE.Part2.QuantityTransport.NamedWrittenRestriction

/-! # A literal coefficient equation with a declared guard

The written scalar equation prescribes the external coefficient `1` on
a partial quantity whose fixed domain consists of the input `true`.
The original guard tests output existence and a relation. Forgetting an
independent quantity leaves the registered equation and its guard intact.
-/

namespace SHIGURE.Quantities.NamedWrittenRestrictionExample

open DeclarationContext

noncomputable section

private def signature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Unit
  Partial := Unit
  Quantity := Bool
  totalArity _ := ⟨[()], ()⟩
  relInputs _ := [()]
  partialArity _ := ⟨[()], ()⟩
  quantityArity _ := ⟨[()], ()⟩

private def guard : Formula signature [()] :=
  (Formula.atom (sig := signature) (.rel () (fun i => i))).conj (GraphAxiom.hasOutput (.partialOp ()))
private def law : Law signature := ⟨[()], guard, .truth⟩

private def application : DeclaredApplication signature [()] :=
  ⟨.partialOp (), ⟨.var⟩⟩

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
    | partialOp p =>
      rw [Declaration.partial_dependencies] at hd
      change Declaration.quantity (P := primitive) true ∈ Declaration.sorts [(), ()] ∪ ∅ at hd
      rcases hd with ⟨_, _, h⟩ | impossible
      · cases h
      · exact impossible
    | quantity q => obtain ⟨_, _, h⟩ := hd; cases h
    | law l =>
      change Declaration.quantity true ∈ Declaration.declaredLawSupport (P := primitive) l ∪ ∅ at hd
      rcases hd with (native | coefficient) | impossible
      · change Declaration.quantity true ∈ Declaration.lawBody (P := primitive) law at native
        simp [Declaration.lawBody, law, guard, Declaration.formula, Declaration.atomic,
          Declaration.sorts, GraphAxiom.hasOutput, Declaration.ofOperation_partialOp] at native
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
  carrier _ := Bool
  total _ _ := false
  relation _ := Set.univ
  partialDomain _ := {x | x .here = true}
  partialValue _ _ := false
  quantity _ _ := false

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full state

private def selectedDomain (j : (written.selection Full).quantities) :
    Set (Assignment ambient.carrier (written.written.domainContext j.val)) := Set.univ

private def fixedDomain : Set (Assignment ambient.carrier [()]) :=
  {x | selectedMap Full state.carrier () (Set.mem_univ _) (x .here) = true}

private theorem guard_iff_domain (B : RestrictedEvaluation Full ambient.carrier) (valid : B.Structural)
    (e : Assignment ambient.carrier [()]) :
    B.holds guard (Set.subset_univ _) e ↔
      B.relation () (Set.mem_univ _) e ∧ B.domain () (Set.mem_univ _) e := by
  change B.relation () (Set.mem_univ _) (e.pull (fun i => i)) ∧
    (∃ y, B.graph (.partialOp ()) (Set.mem_univ _)
      ((Assignment.cons y e).pull (fun i => .there i)) ((Assignment.cons y e) .here)) ↔ _
  simp only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]
  have structural := RestrictedEvaluation.partial_graph_valid valid () (Set.mem_univ _)
  exact and_congr Iff.rfl ⟨fun ⟨y, h⟩ => structural.2.1 e y h, structural.2.2 e⟩

private theorem nativeInput_iff_domain (l : (written.selection Full).laws)
    (e : Assignment ambient.carrier [()]) :
    e ∈ written.nativeInput ambient l ↔ e ∈ fixedDomain := by
  change ambient.evaluation.holds guard (Set.subset_univ _) e ↔ e ∈ fixedDomain
  rw [guard_iff_domain ambient.evaluation ambient.structural]
  change (True ∧ e ∈ fixedDomain) ↔ e ∈ fixedDomain
  exact ⟨And.right, fun input => ⟨trivial, input⟩⟩

private def fixedState : written.FixedState ambient selectedDomain where
  guard l B same _ e := by
    change ambient.evaluation.holds guard (Set.subset_univ _) e ↔ B.holds guard (Set.subset_univ _) e
    rw [guard_iff_domain ambient.evaluation ambient.structural, guard_iff_domain B same.structural]
    exact and_congr (same.relation () (Set.mem_univ _) e) (same.domain () (Set.mem_univ _) e)
  argument l _ same _ e a := by
    intro s i y
    apply same.toSameStateEvaluation.evaluates_iff
    obtain ⟨⟨application, support⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨application, support⟩
    trivial

private def reading : written.GuardedInterpretation ambient :=
  NamedWrittenLaws.GuardedInterpretation.ofFixedState written fixedState (fun l e a => by
    obtain ⟨⟨a, support⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨a, support⟩
    exact ⟨e.val, (nativeInput_iff_domain l e.val).mp e.property, Set.mem_univ _⟩) (fun l e a => by
    intro s i
    apply (fixedState.argument_evaluates_iff l e a i _).mpr
    obtain ⟨⟨a, support⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨a, support⟩
    rfl)

private abbrev interpreted := reading.toInterpretation

private def l : (written.selection Full).laws :=
  ⟨⟨⟨(), rfl⟩, by simp [NamedWrittenLaws.laws, registeredCoefficientLaws, coefficientEquation_eq]⟩, Set.mem_univ _⟩

private def point (x : Bool) : Assignment ambient.carrier [()] :=
  Assignment.cons
    ((Equiv.ofBijective (selectedMap Full state.carrier () (Set.mem_univ _))
      (selectedMap_bijective (U := Full) state.carrier () (Set.mem_univ _))).symm x) Assignment.empty

private theorem point_mem_fixedDomain_iff (x : Bool) : point x ∈ fixedDomain ↔ x = true := by
  unfold fixedDomain point
  exact Iff.of_eq (congrArg (· = true) (Equiv.apply_symm_apply
    (Equiv.ofBijective (selectedMap Full state.carrier () (Set.mem_univ _))
      (selectedMap_bijective (U := Full) state.carrier () (Set.mem_univ _))) x))

/-- The input of the registered equation is the actual fixed partial domain. -/
theorem named_law_input_iff_fixed_domain (x : Bool) :
    point x ∈ written.fixedStateInput ambient selectedDomain l ↔ x = true := by
  rw [fixedState.input_eq_native, nativeInput_iff_domain, point_mem_fixedDomain_iff]

private def partialAmount : (written.selection Full).quantities :=
  ⟨⟨.partialOp (), Set.mem_univ _⟩, Set.mem_univ _⟩

/-- Even a full selection leaves the coefficient candidate defined only at the native input. -/
theorem named_law_partial_domain_iff (x : Bool) :
    point x ∈ interpreted.domain partialAmount ↔ x = true := by
  change (point x ∈ fixedDomain ∧ True) ↔ x = true
  rw [and_true, point_mem_fixedDomain_iff]

/-- A context keeping the actual Law declaration also keeps the guard relation. -/
theorem named_law_keeps_guard (U : DeclarationContext primitive) (l : (written.selection U).laws) :
    Declaration.relation () ∈ U.declarations :=
  Declaration.lawBody_subset_of_mem l.property (Or.inl (Or.inr (Or.inl (Set.mem_singleton _))))

/-- The same original declaration cannot register zero in place of the written coefficient one. -/
theorem named_law_retains_literal :
    primitive.coefficientEquation ℤ () ≠ some (registeredEquation.1, .scalar 0) := by
  rw [coefficientEquation_eq]
  simp [registeredEquation]

/-- The coefficient equation keeps its quantity in every selected declaration context. -/
theorem named_law_keeps_quantity (U : DeclarationContext primitive) (l : (written.selection U).laws) :
    Declaration.partialOp () ∈ U.declarations := by
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

/-- The registered scalar Law excludes the zero candidate on its fixed domain. -/
theorem named_law_rejects_zero :
    ¬ interpreted.presentation.Holds (R := ℤ) (fun _ _ => 0) := by
  intro holds
  have input := (named_law_input_iff_fixed_domain true).mpr rfl
  have native : point true ∈ written.nativeInput ambient l := (fixedState.input_eq_native l) ▸ input
  have eq := holds l ⟨point true, native⟩
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

/-- A retained required coefficient Law with no quantity occurrences is still read. -/
theorem literal_only_law_is_read (L : NamedWrittenLaws ℤ (literalOnly 1))
    (U : DeclarationContext (literalOnly 1)) (kept : Declaration.law () ∈ U.declarations) :
    Nonempty (L.selection U).laws := by
  refine ⟨⟨⟨⟨(), rfl⟩, ?_⟩, kept⟩⟩
  change ((some (⟨ℤ, .scalar 1, .scalar 0⟩ : RegisteredCoefficientEquation signature [])).bind
    (fun e => RegisteredCoefficientEquation.atType e ℤ)).isSome
  simp

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
