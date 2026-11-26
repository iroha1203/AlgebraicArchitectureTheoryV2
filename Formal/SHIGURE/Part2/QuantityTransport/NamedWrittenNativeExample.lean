import Formal.SHIGURE.Part2.QuantityTransport.NamedWrittenRestriction

/-! # A fixed antecedent on represented scalar candidates

A native output in `Option ℤ` represents an integer by `some`. The
registered antecedent accepts every represented candidate, while the
output `none` is a structurally valid change of native output that
makes the antecedent false. The abstract coefficient model and its
comparison still use the original registered equation.
-/

namespace SHIGURE.Quantities.NamedWrittenNativeExample

open DeclarationContext

noncomputable section

private def signature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Unit
  Partial := Unit
  Quantity := Empty
  totalArity := Empty.elim
  relInputs _ := [()]
  partialArity _ := ⟨[()], ()⟩
  quantityArity := Empty.elim

private def outputVariable : {s : Unit} → Var [()] s → Var [(), ()] s
  | _, .here => .here
  | _, .there i => nomatch i

private def guard : Formula signature [()] :=
  .ex ((Formula.atom (sig := signature) (.graph (.partialOp ()) (fun i => .there i) .here)).conj
    (.atom (.rel () outputVariable)))

private def application : DeclaredApplication signature [()] :=
  ⟨.partialOp (), ⟨.var⟩⟩

private def equation : WrittenCoefficientEquation ℤ signature [()] :=
  (.quantity application, .scalar 1)

private def primitive : PrimitivePresentation where
  signature := signature
  laws := ⟨Unit, fun _ => ⟨[()], guard, .truth⟩, fun _ => .required⟩
  derived _ impossible := by cases impossible
  coefficientLaw _ := some ⟨⟨ℤ, equation⟩, rfl, rfl⟩

private theorem coefficientEquation_eq (n : primitive.laws.LawName) :
    primitive.coefficientEquation ℤ n = some equation := by
  change (some ⟨ℤ, equation⟩ : Option (RegisteredCoefficientEquation signature [()])).bind
    (·.atType ℤ) = _
  simp

private def written : NamedWrittenLaws ℤ primitive where
  quantities := Set.univ
  hasQuantity _ _ _ := Set.mem_univ _

private theorem used_eq (l : written.laws) (a : written.Occurrence l) : a.val = application := by
  have eq : written.equation l = equation :=
    Option.some.inj ((Option.some_get (written.hasEquation l)).trans (coefficientEquation_eq l.val.val))
  obtain ⟨a, used⟩ := a
  change a ∈ (written.equation l).1.occurrences ∪ (written.equation l).2.occurrences at used
  rw [eq] at used
  exact Set.mem_singleton_iff.mp (by simpa [equation, Expression.occurrences] using used)

private abbrev Full := DeclarationContext.full primitive

private def state : Structure signature where
  carrier _ := Option ℤ
  total q _ := nomatch q
  relation _ := {x | ∃ r : ℤ, x .here = some r}
  partialDomain _ := Set.univ
  partialValue _ _ := some 0
  quantity q _ := nomatch q

private def ambient : ContextStructure Full := ContextStructure.ofStructure Full state

private def readCarrier (s : signature.SortType) : ambient.carrier s ≃ Option ℤ :=
  Equiv.ofBijective (selectedMap Full state.carrier s (Set.mem_univ _))
    (selectedMap_bijective (U := Full) state.carrier s (Set.mem_univ _))

private def selectedDomain (j : (written.selection Full).quantities) :
    Set (Assignment ambient.carrier (written.written.domainContext j.val)) := Set.univ

private def amount : (written.selection Full).quantities :=
  ⟨⟨.partialOp (), Set.mem_univ _⟩, Set.mem_univ _⟩

private def encoding : written.NativeEncoding ℤ ambient selectedDomain := fun j _ =>
  ⟨fun r => (readCarrier j.val.val.operation.arity.output).symm (some r), fun _ _ eq =>
    Option.some.inj ((readCarrier j.val.val.operation.arity.output).symm.injective eq)⟩

private theorem fullDomain (e : Assignment ambient.carrier [()]) :
    e ∈ written.fixedDomain ambient selectedDomain amount :=
  ⟨Set.mem_univ _, Set.mem_univ _⟩

private theorem guard_iff (B : RestrictedEvaluation Full ambient.carrier)
    (e : Assignment ambient.carrier [()]) :
    B.holds guard (Set.subset_univ _) e ↔
      ∃ y, B.graph (.partialOp ()) (Set.mem_univ _) e y ∧
        B.relation () (Set.mem_univ _) (Assignment.cons y Assignment.empty) := by
  change (∃ y, B.graph (.partialOp ()) (Set.mem_univ _)
    ((Assignment.cons y e).pull (fun i => .there i)) ((Assignment.cons y e) .here) ∧
    B.relation () (Set.mem_univ _) ((Assignment.cons y e).pull outputVariable)) ↔ _
  have pulls (y : ambient.carrier ()) :
      (Assignment.cons y e).pull outputVariable =
        Assignment.cons y Assignment.empty := by
    ext s i
    cases i with
    | here => rfl
    | there impossible => cases impossible
  simp only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]
  apply exists_congr
  intro y
  exact and_congr Iff.rfl
    (Iff.of_eq (congrArg (B.relation () (Set.mem_univ _)) (pulls y)))

private theorem relation_iff (y : ambient.carrier ()) :
    ambient.evaluation.relation () (Set.mem_univ _) (Assignment.cons y Assignment.empty) ↔
      ∃ r : ℤ, readCarrier () y = some r := Iff.rfl

private theorem ambientGuard (e : Assignment ambient.carrier [()]) :
    ambient.evaluation.holds guard (Set.subset_univ _) e := by
  apply (guard_iff ambient.evaluation e).2
  refine ⟨(readCarrier ()).symm (some 0), ?_, (relation_iff _).2 ⟨0, Equiv.apply_symm_apply _ _⟩⟩
  change ∃ h : True, some 0 = readCarrier () ((readCarrier ()).symm (some 0))
  exact ⟨trivial, (Equiv.apply_symm_apply _ _).symm⟩

private theorem representedGuard (B : RestrictedEvaluation Full ambient.carrier)
    (same : written.SameFixedState ambient selectedDomain B)
    (q : written.ScalarCandidate ℤ ambient selectedDomain) (represented : written.RepresentsScalars encoding q B)
    (e : Assignment ambient.carrier [()]) :
    B.holds guard (Set.subset_univ _) e := by
  let x : written.fixedDomain ambient selectedDomain amount := ⟨e, fullDomain e⟩
  let y : ambient.carrier () := encoding amount x (q amount x)
  apply (guard_iff B e).2
  refine ⟨y, represented amount x, ?_⟩
  apply (same.relation () (Set.mem_univ _) _).1
  exact (relation_iff y).2 ⟨q amount x, Equiv.apply_symm_apply _ _⟩

/-- Every represented integer candidate retains the native antecedent and typed arguments. -/
theorem representedFixedState :
    written.FixedState ambient selectedDomain (fun B => ∃ q, written.RepresentsScalars encoding q B) where
  guard l B same allowed e := by
    obtain ⟨q, represented⟩ := allowed
    exact ⟨fun _ => representedGuard B same q represented e, fun _ => ambientGuard e⟩
  argument l _ same _ e a := by
    intro s i y
    apply same.toSameStateEvaluation.evaluates_iff
    obtain ⟨⟨a, supported⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨a, supported⟩
    trivial

private def reading : written.GuardedInterpretation ambient where
  selectedDomain := selectedDomain
  value l e a := by
    obtain ⟨⟨a, support⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨a, support⟩
    exact ⟨e.val, fullDomain e.val⟩
  argument l e a := by
    intro s i
    obtain ⟨⟨a, support⟩, used⟩ := a
    obtain rfl := used_eq l.val ⟨a, support⟩
    rfl

private def lawName : (written.selection Full).laws :=
  ⟨⟨⟨(), rfl⟩, by simp [NamedWrittenLaws.laws, registeredCoefficientLaws, coefficientEquation_eq]⟩,
    Set.mem_univ _⟩

/-- The actual abstract input agrees with the antecedent of the native
structure built from any independent integer candidate. -/
theorem every_scalar_candidate_reads_input (q : written.ScalarCandidate ℤ ambient selectedDomain)
    (e : Assignment ambient.carrier [()]) :
    e ∈ reading.toInterpretation.input lawName ↔
      (written.candidateEvaluation ambient selectedDomain (fun j x => encoding j x (q j x))).holds
        guard (Set.subset_univ _) e := by
  let B := written.candidateEvaluation ambient selectedDomain (fun j x => encoding j x (q j x))
  have same := written.candidateEvaluation_agrees ambient selectedDomain (fun j x => encoding j x (q j x))
  have represented := written.candidateEvaluation_represents encoding q
  have equal := NamedWrittenLaws.GuardedInterpretation.nativeCandidateInput written reading encoding representedFixedState lawName q B same represented
  exact Set.ext_iff.mp equal e

private def point : Assignment ambient.carrier [()] :=
  Assignment.cons ((readCarrier ()).symm (some 0)) Assignment.empty

private def noScalar : written.SelectedOutput ambient selectedDomain :=
  fun j _ => (readCarrier j.val.val.operation.arity.output).symm none

/-- The unrestricted native-output condition fails when the candidate includes `none`. -/
theorem not_unrestrictedFixedState : ¬ written.FixedState ambient selectedDomain := by
  intro stable
  let B := written.candidateEvaluation ambient selectedDomain noScalar
  have same := written.candidateEvaluation_agrees ambient selectedDomain noScalar
  have native : point ∈ written.nativeInput ambient lawName := ambientGuard point
  have kept := (stable.guard lawName B same trivial point).1 native
  obtain ⟨y, edge, rel⟩ := (guard_iff B point).1 kept
  let x : written.fixedDomain ambient selectedDomain amount := ⟨point, fullDomain point⟩
  have noneEdge := written.candidateEvaluation_graph ambient selectedDomain noScalar amount x
  have output : y = (readCarrier ()).symm none :=
    RestrictedEvaluation.graph_rightUnique same.structural (.partialOp ()) (Set.mem_univ _) edge noneEdge
  obtain ⟨r, someOutput⟩ := (relation_iff y).1 ((same.relation () (Set.mem_univ _) _).2 rel)
  rw [output, Equiv.apply_symm_apply] at someOutput
  cases someOutput

private def emptyDomain : RestrictedStructure Full :=
  { ambient.toRestrictedStructure with
    partialDomain := fun _ _ => ∅
    partialValue := fun _ _ x => (False.elim x.property) }

/-- Changing an original partial domain fails the fixed-state comparison. -/
theorem not_sameFixedState_emptyDomain :
    ¬ written.SameFixedState ambient selectedDomain emptyDomain.evaluation := by
  intro same
  have lost := (same.domain () (Set.mem_univ _) point).1 (fullDomain point).1
  exact lost

end

end SHIGURE.Quantities.NamedWrittenNativeExample
