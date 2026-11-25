import Formal.SHIGURE.Part1.ContextReading
import Formal.SHIGURE.Part1.ContextExamples
import Formal.SHIGURE.Part1.PreservationExamples

/-! # Ordered equalities and the support of residual data -/

namespace SHIGURE.Chapter3.OrderedRestriction

open DeclarationContext

/-- Start the ordered-equation witness with two distinct variables of the same sort. -/
private def simplePair : OrderedEquation OmittedLaw.signature where
  context := [(), ()]
  result := ()
  input := .truth
  left := .var .here
  right := .var (.there .here)

/-- Use the equality of the two bare variables as the first writing of the equation. -/
private def atomicWriting : OrderedEquation.Written OmittedLaw.signature :=
  simplePair.writeVariables .here (.there .here) rfl rfl

/-- The first writing retains the original ordered pair. -/
private theorem atomicWriting_equation : atomicWriting.equation = simplePair :=
  OrderedEquation.writeVariables_equation simplePair .here (.there .here) rfl rfl

/-- Exercise strict substitution by replacing one variable with a bound operation and the other with a variable. -/
private def replacement : Substitution OmittedLaw.signature [(), ()] [(), ()] :=
  ⟨fun i => match i with
    | .here => .letBind (Term.app (sig := OmittedLaw.signature) (.total false)
        (fun j => match j with | .here => .var (.there .here))) (.var .here)
    | .there .here => .var .here⟩

/-- Retain both substitution steps in the provenance of the written equation. -/
private def writtenTwice : OrderedEquation.Written OmittedLaw.signature :=
  (atomicWriting.substitute replacement).substitute replacement

/-- This display attaches the actual twice-substituted Law and its ordered equality. -/
def twicePresentation : PrimitivePresentation where
  signature := OmittedLaw.signature
  laws := ⟨Unit, fun _ => writtenTwice.toLaw, fun _ => .additional⟩
  otherOrderedEquation _ := some ⟨writtenTwice, rfl⟩
  derived _ role := by cases role

/-- The complete substitution history still produces a registered ordered equality. -/
theorem twice_ordered_some :
    ((Selected.presentation (full twicePresentation)).orderedEquation ⟨(), Set.mem_univ _⟩).isSome := by
  rw [Selected.presentation_orderedEquation, PrimitivePresentation.orderedEquation_eq]
  simp only [twicePresentation, NamedRingEquation.ordered_none, Option.map_some, Option.isSome_some]

/-- The selected side is transported along an equality of the original ordered pairs. -/
private theorem selectPairSide_congr
    (side : (eqn : OrderedEquation OmittedLaw.signature) → Term OmittedLaw.signature eqn.context eqn.result)
    {p q : OrderedEquation OmittedLaw.signature} (same : p = q) :
    HEq (Selected.selectTerm (U := full twicePresentation) (side p)
      (Set.subset_univ _) (Set.mem_univ _) (Set.subset_univ _))
      (Selected.selectTerm (U := full twicePresentation) (side q)
        (Set.subset_univ _) (Set.mem_univ _) (Set.subset_univ _)) := by
  cases same
  rfl

/-- The two different starting positions remain in their original order after selection. -/
theorem positions_unchanged :
    let selected := Selected.selectWritten (U := full twicePresentation) atomicWriting (Set.subset_univ _)
    selected.equation.left = .var .here ∧ selected.equation.right = .var (.there .here) := by
  let hs : Declaration.sort atomicWriting.equation.result ∈ (full twicePresentation).declarations :=
    Set.mem_univ _
  constructor
  · refine (eq_of_heq (Selected.selectWritten_left atomicWriting (Set.subset_univ _) hs (Set.subset_univ _))).trans ?_
    refine (eq_of_heq (selectPairSide_congr OrderedEquation.left atomicWriting_equation)).trans ?_
    change Selected.selectTerm (.var .here) _ _ _ = _
    rw [Selected.selectTerm_var, Selected.selectVar_here]
  · refine (eq_of_heq (Selected.selectWritten_right atomicWriting (Set.subset_univ _) hs (Set.subset_univ _))).trans ?_
    refine (eq_of_heq (selectPairSide_congr OrderedEquation.right atomicWriting_equation)).trans ?_
    change Selected.selectTerm (.var (.there .here)) _ _ _ = _
    rw [Selected.selectTerm_var, Selected.selectVar_there, Selected.selectVar_here]

open Chapter1.ResidualTransport (paddedPresentation padded_integer_axioms
  paddedPresentation_ring_isSome paddedPresentation_ring_axiomNames)

/-- Read the named ring attachment from the original padded presentation at its equality Law. -/
private def sourceRing : NamedRingEquation paddedPresentation.laws (.inl ()) :=
  (paddedPresentation.ringEquation (.inl ())).get paddedPresentation_ring_isSome

/-- This is the attachment registered at the original equality. -/
private theorem sourceRing_registered :
    paddedPresentation.ringEquation (.inl ()) = some sourceRing :=
  (Option.some_get paddedPresentation_ring_isSome).symm

/-- Retain the ordered equality and every primitive, forgetting the other named ring Laws. -/
def equalityContext : DeclarationContext paddedPresentation where
  declarations := {d | ∀ i : RingVocabulary.LawName, d ≠ .law (.inr i)}
  closed {a} kept := by
    intro d used i banned
    subst d
    cases a with
    | sort s => rw [Declaration.sort_dependencies] at used; exact used
    | total f =>
      rw [Declaration.total_dependencies, Declaration.sorts_eq_image] at used
      rcases used with ⟨s, hs, same⟩
      cases same
    | relation r => exact nomatch r
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q
    | law n =>
      cases n with
      | inl n =>
        have rule := Declaration.nonderived_dependencies (P := paddedPresentation) (.inl n)
          (fun h => LawRole.noConfusion h)
        rw [rule] at used
        exact Declaration.law_notMem_lawBody _ _ used
      | inr n => exact kept n rfl

/-- Select the ordered-equality Law while omitting the separate ring-axiom names. -/
private theorem equalityKept :
    Declaration.law (P := paddedPresentation) (.inl ()) ∈ equalityContext.declarations := by
  intro i equal
  cases equal

/-- The exact logical restriction can omit a ring axiom named in the source attachment. -/
theorem ringLaw_omitted : Declaration.law (P := paddedPresentation) (.inr .zeroAdd) ∉ equalityContext.declarations :=
  fun kept => kept .zeroAdd rfl

/-- Retaining only the logical dependencies still keeps the ordered equality itself. -/
theorem equality_ordered_some :
    ((Selected.presentation equalityContext).orderedEquation ⟨.inl (), equalityKept⟩).isSome := by
  rw [Selected.presentation_orderedEquation, PrimitivePresentation.orderedEquation_eq,
    NamedRingEquation.ordered_of_some sourceRing_registered, Option.map_some]
  rfl

/-- All names of the optional residual presentation are available in the full context. -/
theorem full_retains_ring_support : (full paddedPresentation).RetainsRingSupport (.inl ()) :=
  ((full paddedPresentation).retainsRingSupport_iff (.inl ())).2 (Set.subset_univ _)

/-- The exact logical context does not supply this optional residual presentation. -/
theorem equality_lacks_ring_support : ¬ equalityContext.RetainsRingSupport (.inl ()) := by
  intro support
  have kept := (equalityContext.retainsRingSupport_iff (.inl ())).1 support
  apply ringLaw_omitted
  exact kept (Declaration.ringLaw_mem_ringEquationSupport (P := paddedPresentation)
    (name := .inl ()) sourceRing_registered (by
      change _ ∈ ((paddedPresentation.ringEquation (.inl ())).get paddedPresentation_ring_isSome).axiomNames
      rw [paddedPresentation_ring_axiomNames]
      exact ⟨.zeroAdd, rfl⟩))

/-- The omitted ring axiom rules out the named certificate while the ordered text survives. -/
theorem equality_ring_none :
    (Selected.presentation equalityContext).ringEquation ⟨.inl (), equalityKept⟩ = none := by
  rw [Selected.presentation_ringEquation]
  exact Selected.ringEquation_of_unsupported (U := equalityContext) ⟨.inl (), equalityKept⟩ equality_lacks_ring_support

/-- The full context includes the residual's named axioms and the proofs from those axioms. -/
theorem full_ring_some :
    ((Selected.presentation (full paddedPresentation)).ringEquation ⟨.inl (), Set.mem_univ _⟩).isSome := by
  let name : (full paddedPresentation).RetainedLaw := ⟨.inl (), Set.mem_univ _⟩
  change ((Selected.presentation (full paddedPresentation)).ringEquation name).isSome
  rw [Selected.presentation_ringEquation]
  rw [Selected.ringEquation_of_supported name sourceRing sourceRing_registered full_retains_ring_support]
  rfl

open Chapter1.RingModule (realization scalarOne scalarZero Symbol SortName signature)

/-- An integer reading selects the original padded ring-axiom presentations. -/
def integerReading : Reading.{0, 0, 0, 0} where
  presentation := paddedPresentation
  structureData := realization Int Int
  observation := StateObservation.ofSort .scalar Int id
  context := full paddedPresentation
  cover := DeclarationCover.identity _
  Family := Unit
  realize _ := realization Int Int
  familyObservation := none
  ValueStructure _ := PUnit
  valueStructure := PUnit.unit
  coefficients := none

/-- Name the retained equality in the full context of the integer reading. -/
private def equationName : integerReading.context.RetainedLaw := ⟨.inl (), Set.mem_univ _⟩

/-- The selected reading uses the original named proofs to supply the seven ring axioms. -/
theorem integerReading_ring_axioms :
    let attached := Selected.selectNamedRingEquation equationName sourceRing sourceRing_registered full_retains_ring_support
    ∀ i, (attached.written.equation.ring.law i).Holds integerReading.selectedStructure :=
  integerReading.selectedRing_axioms equationName sourceRing sourceRing_registered full_retains_ring_support padded_integer_axioms

/-- The selected reading keeps the original false equality as the same test on the integer structure. -/
theorem integerReading_fails_equation :
    ¬ (integerReading.selectedPresentation.laws.statement equationName).Holds integerReading.selectedStructure := by
  intro selected
  have original := (integerReading.selectedLaw_iff equationName).1 selected
  have bad := (Law.holds_equality_totalValue_iff scalarOne scalarZero (realization Int Int)).1 original
    Assignment.empty
  change (1 : Int) = 0 at bad
  exact Int.one_ne_zero bad

/-- A caller-supplied presentation retains every primitive and the ordered equality Law. -/
private def equalityPresentation : PrimitivePresentation where
  signature := paddedPresentation.signature
  laws := ⟨Unit, fun _ => paddedPresentation.laws.statement (.inl ()), fun _ => .additional⟩
  otherOrderedEquation _ := some ⟨sourceRing.toNamedOrderedEquation.written,
    sourceRing.toNamedOrderedEquation.statement_eq⟩
  derived _ role := by cases role

/-- The one-law presentation attaches the ordered view of the original equality. -/
private theorem equalityPresentation_ordered :
    equalityPresentation.orderedEquation () =
      some ⟨sourceRing.toNamedOrderedEquation.written, sourceRing.toNamedOrderedEquation.statement_eq⟩ :=
  (PrimitivePresentation.orderedEquation_eq equalityPresentation ()).trans (NamedRingEquation.ordered_none _)

/-- Send the one-law presentation's names to the matching names of the padded presentation. -/
private def toName (d : Declaration equalityPresentation) : Declaration paddedPresentation :=
  d.renameNames (P := equalityPresentation) (Q := paddedPresentation) (.identity _) (fun _ => .inl ())

/-- The equality context retains each original sort name. -/
private theorem toName_sort (s : equalityPresentation.signature.SortType) :
    toName (.sort s) = .sort s :=
  rfl

/-- The equality context retains each original total symbol's name. -/
private theorem toName_total (f : equalityPresentation.signature.Total) :
    toName (.total f) = .total f :=
  rfl

/-- Its sole Law is the equality in the left summand of the padded presentation. -/
private theorem toName_law (name : equalityPresentation.laws.LawName) :
    toName (.law name) = .law (.inl ()) :=
  rfl

/-- The naming map reaches only declarations retained in the equality context. -/
private theorem toName_kept (d : Declaration equalityPresentation) : toName d ∈ equalityContext.declarations := by
  intro i h
  cases d <;> cases h

/-- Recover primitive names and the single equality name from their selected ambient names. -/
private def fromName : equalityContext.Retained → Declaration equalityPresentation
  | ⟨.sort s, _⟩ => .sort s
  | ⟨.total f, _⟩ => .total f
  | ⟨.relation r, _⟩ => .relation r
  | ⟨.partialOp p, _⟩ => .partialOp p
  | ⟨.quantity q, _⟩ => .quantity q
  | ⟨.law (.inl _), _⟩ => .law ()
  | ⟨.law (.inr i), kept⟩ => (kept i rfl).elim

/-- Identify the caller's names with all and only the retained names of the padded presentation. -/
private def equalityNames : Declaration equalityPresentation ≃ equalityContext.Retained where
  toFun d := ⟨toName d, toName_kept d⟩
  invFun := fromName
  left_inv d := by cases d <;> rfl
  right_inv := by
    rintro ⟨d, hd⟩
    cases d with
    | law n =>
      cases n with
      | inl n =>
        cases n
        rfl
      | inr n => exact (hd n rfl).elim
    | sort s => rfl
    | total f => rfl
    | relation r => rfl
    | partialOp p => rfl
    | quantity q => rfl

/-- Describe the scalar witness as the output of the named unit operation. -/
private def oneGraph : Formula signature [SortName.scalar] :=
  .conj .truth (.atom (.graph (Operation.total (sig := signature) Symbol.scalarOne)
    (Var.inLeft [SortName.scalar]) .here))

/-- Describe the same scalar witness as the output of the named zero operation. -/
private def zeroGraph : Formula signature [SortName.scalar] :=
  .conj .truth (.atom (.graph (Operation.total (sig := signature) Symbol.scalarZero)
    (Var.inLeft [SortName.scalar]) .here))

/-- Write the equation using the shared value of the unit and zero operations. -/
private def literalLaw : Law signature := ⟨[], .truth, (oneGraph.conj zeroGraph).ex⟩

/-- Show that renaming the retained equality preserves its declaration dependency relation. -/
private theorem equalityDependencies (a b : Declaration equalityPresentation) :
    b ∈ Declaration.dependsOn equalityPresentation a ↔
      toName b ∈ Declaration.dependsOn paddedPresentation (toName a) := by
  cases a with
  | sort s => simp only [toName_sort, Declaration.sort_dependencies, Set.mem_empty_iff_false]
  | relation r => exact nomatch r
  | partialOp p => exact nomatch p
  | quantity q => exact nomatch q
  | total f =>
    cases b with
    | sort | total | law =>
      simp [toName_sort, toName_total, toName_law, Declaration.total_dependencies, Declaration.sorts_eq_image] <;> rfl
    | relation r => exact nomatch r
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q
  | law n =>
    change b ∈ Declaration.dependsOn equalityPresentation (.law n) ↔
      toName b ∈ Declaration.dependsOn paddedPresentation (.law (.inl ()))
    rw [Declaration.nonderived_dependencies n (fun h => LawRole.noConfusion h),
      Declaration.nonderived_dependencies (P := paddedPresentation) (.inl ()) (fun h => LawRole.noConfusion h)]
    change b ∈ Declaration.lawBody (P := equalityPresentation) literalLaw ↔
      toName b ∈ Declaration.lawBody (P := paddedPresentation) literalLaw
    cases b with
    | sort | total =>
      simp [literalLaw, oneGraph, zeroGraph, Declaration.lawBody_eq, Declaration.sorts_eq_image,
        Declaration.formula_truth, Declaration.formula_ex, Declaration.formula_conj, Declaration.formula_atom,
        toName_sort, toName_total]
      all_goals
        erw [Declaration.atomic_graph (P := equalityPresentation), Declaration.atomic_graph (P := equalityPresentation),
          Declaration.atomic_graph (P := paddedPresentation), Declaration.atomic_graph (P := paddedPresentation)]
        simp [Declaration.ofOperation_total]
    | law m =>
      rw [toName_law]
      exact iff_of_false (Declaration.law_notMem_lawBody m literalLaw)
        (Declaration.law_notMem_lawBody (P := paddedPresentation) (.inl ()) literalLaw)
    | relation r => exact nomatch r
    | partialOp p => exact nomatch p
    | quantity q => exact nomatch q

/-- The named equality can be selected as a reading when its optional ring axioms are omitted. -/
noncomputable def equalityReadingOrigin : ReadingOrigin equalityPresentation paddedPresentation equalityContext where
  signature := .identity _
  lawName _ := .inl ()
  names := equalityNames
  names_eq _ := rfl
  law_eq _ := by
    change (SignatureNames.identity signature).law ⟨[], .truth, (oneGraph.conj zeroGraph).ex⟩ =
      ⟨[], .truth, (oneGraph.conj zeroGraph).ex⟩
    simp only [SignatureNames.law_eq, SignatureNames.formula_truth,
      SignatureNames.formula_ex, SignatureNames.formula_conj, List.map_nil]
    suffices h : (SignatureNames.identity signature).formula oneGraph = oneGraph ∧
        (SignatureNames.identity signature).formula zeroGraph = zeroGraph by
      rw [h.1, h.2]
    constructor <;> simp [oneGraph, zeroGraph, SignatureNames.formula_conj,
      SignatureNames.formula_truth, SignatureNames.formula_totalGraph, SignatureNames.identity_onTotal,
      Var.mapSorts_here]
    all_goals
      funext s i
      exact nomatch i
  law_role _ := rfl
  lawAttachments_eq _ := by
    let A := paddedPresentation.lawAttachments (SignatureNames.identity _) id (.inl ())
    change equalityPresentation.lawAttachments (SignatureNames.identity _) (fun _ => .inl ()) () =
      A.withSupportedRing (equalityContext.RetainsRingSupport (.inl ()))
    rw [LawAttachments.withSupportedRing_of_unsupported A equality_lacks_ring_support]
    apply LawAttachments.ext
    · change (equalityPresentation.lawAttachments (SignatureNames.identity _)
        (fun _ => (Sum.inl () : paddedPresentation.laws.LawName)) ()).equation = A.equation
      have original := (PrimitivePresentation.orderedEquation_eq paddedPresentation (.inl ())).trans
        (NamedRingEquation.ordered_of_some sourceRing_registered _)
      simp only [A, PrimitivePresentation.lawAttachments_equation, equalityPresentation_ordered, original]
      rfl
    · exact PrimitivePresentation.lawAttachments_ring_of_none equalityPresentation _ _ () rfl
    · let names := SignatureNames.identity paddedPresentation.signature
      exact (PrimitivePresentation.lawAttachments_proof_of_additional equalityPresentation names
        (fun _ => Sum.inl ()) () rfl).trans
        (PrimitivePresentation.lawAttachments_proof_of_additional paddedPresentation names id (.inl ()) rfl).symm
  domainAttachment_eq p := nomatch p
  dependencies := equalityDependencies

/-- Use the integer realization after selecting the equality and keeping the observation external. -/
private def ambientEqualityReading : Reading.{0, 0, 0, 0} :=
  { integerReading with
    context := equalityContext
    cover := DeclarationCover.identity equalityContext
    coefficients := none
    observationPlacement := .external
    observationDeclared := by
      intro f h
      cases h }

/-- The usual reading restriction carries the observation and family into the selected presentation. -/
noncomputable def restrictedIntegerReading : Reading.{0, 0, 0, 0} :=
  ambientEqualityReading.restrict equalityReadingOrigin
    (StateObservation.ofSort SortName.scalar Int id) PUnit.unit

/-- The restricted reading keeps the ordered equality and records its source context. -/
theorem restrictedIntegerReading_attachment :
    (restrictedIntegerReading.presentation.orderedEquation ()).isSome ∧
      restrictedIntegerReading.presentation.ringEquation () = none ∧
      restrictedIntegerReading.origin.isSome := by
  have attachments := Reading.restrict_equations ambientEqualityReading equalityReadingOrigin
    (StateObservation.ofSort SortName.scalar Int id) PUnit.unit none (.empty _) ()
  have ordered : restrictedIntegerReading.presentation.orderedEquation () = equalityPresentation.orderedEquation () :=
    attachments.1
  refine ⟨?_, attachments.2, ?_⟩
  · rw [ordered, equalityPresentation_ordered]
    rfl
  · simp only [restrictedIntegerReading, Reading.restrict_origin, Option.isSome_some]

end SHIGURE.Chapter3.OrderedRestriction
