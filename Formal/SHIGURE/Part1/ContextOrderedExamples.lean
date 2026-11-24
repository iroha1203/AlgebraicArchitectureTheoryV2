import Formal.SHIGURE.Part1.ContextReading
import Formal.SHIGURE.Part1.ContextExamples
import Formal.SHIGURE.Part1.PreservationExamples

/-! # Ordered equalities and the support of residual data -/

namespace SHIGURE.Chapter3.OrderedRestriction

open DeclarationContext

private def simplePair : OrderedEquation OmittedLaw.signature where
  context := [(), ()]
  result := ()
  input := .truth
  left := .var .here
  right := .var (.there .here)

private def atomicWriting : OrderedEquation.Written OmittedLaw.signature :=
  simplePair.writeVariables .here (.there .here) rfl rfl

private def replacement : Substitution OmittedLaw.signature [(), ()] [(), ()] :=
  ⟨fun i => match i with
    | .here => .letBind (Term.app (sig := OmittedLaw.signature) (.total false)
        (fun j => match j with | .here => .var (.there .here))) (.var .here)
    | .there .here => .var .here⟩

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
    ((Selected.presentation (full twicePresentation)).orderedEquation ⟨(), Set.mem_univ _⟩).isSome :=
  rfl

/-- The two different starting positions remain in their original order after selection. -/
theorem positions_unchanged :
    let selected := Selected.selectWritten (U := full twicePresentation) atomicWriting (Set.subset_univ _)
    selected.equation.left = .var .here ∧ selected.equation.right = .var (.there .here) :=
  ⟨rfl, rfl⟩

open Chapter1.ResidualTransport (paddedPresentation padded_integer_axioms)

/-- Retain the ordered equality and every primitive, forgetting the other named ring Laws. -/
def equalityContext : DeclarationContext paddedPresentation where
  declarations := {d | ∀ i : RingVocabulary.LawName, d ≠ .law (.inr i)}
  closed {a} kept := by
    intro d used i banned
    subst d
    cases a with
    | sort s => exact used
    | total f => rcases used with ⟨s, hs, same⟩; cases same
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
  rw [Selected.presentation_orderedEquation]
  rfl

/-- All names of the optional residual presentation are available in the full context. -/
theorem full_retains_ring_support : (full paddedPresentation).RetainsRingSupport (.inl ()) :=
  Set.subset_univ _

/-- The exact logical context does not supply this optional residual presentation. -/
theorem equality_lacks_ring_support : ¬ equalityContext.RetainsRingSupport (.inl ()) := by
  intro support
  apply ringLaw_omitted
  exact support (Declaration.ringLaw_mem_ringEquationSupport (P := paddedPresentation)
    (name := .inl ()) rfl (by exact ⟨.zeroAdd, rfl⟩))

/-- The omitted ring axiom rules out the named certificate while the ordered text survives. -/
theorem equality_ring_none :
    (Selected.presentation equalityContext).ringEquation ⟨.inl (), equalityKept⟩ = none :=
  Selected.ringEquation_of_unsupported (U := equalityContext) ⟨.inl (), equalityKept⟩ equality_lacks_ring_support

/-- The full context includes the residual's named axioms and the proofs from those axioms. -/
theorem full_ring_some :
    ((Selected.presentation (full paddedPresentation)).ringEquation ⟨.inl (), Set.mem_univ _⟩).isSome := by
  let name : (full paddedPresentation).RetainedLaw := ⟨.inl (), Set.mem_univ _⟩
  have original : ∃ data, paddedPresentation.ringEquation name.val = some data := ⟨_, rfl⟩
  obtain ⟨data, registered⟩ := original
  change (Selected.ringEquation name).isSome
  rw [Selected.ringEquation_of_supported name data registered full_retains_ring_support]
  rfl

open Chapter1.RingModule (realization scalarOne scalarZero Symbol SortName signature)

private def sourceRing : NamedRingEquation paddedPresentation.laws (.inl ()) :=
  (paddedPresentation.ringEquation (.inl ())).get (by rfl)

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

private def equationName : integerReading.context.RetainedLaw := ⟨.inl (), Set.mem_univ _⟩

/-- The selected reading uses the original named proofs to supply the seven ring axioms. -/
theorem integerReading_ring_axioms :
    let attached := Selected.selectNamedRingEquation equationName sourceRing rfl full_retains_ring_support
    ∀ i, (attached.written.equation.ring.law i).Holds integerReading.selectedStructure :=
  integerReading.selectedRing_axioms equationName sourceRing rfl full_retains_ring_support padded_integer_axioms

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
  otherOrderedEquation _ := some ⟨sourceRing.toNamedOrderedEquation.written, sourceRing.statement_eq⟩
  derived _ role := by cases role

private def toName (d : Declaration equalityPresentation) : Declaration paddedPresentation :=
  d.renameNames (P := equalityPresentation) (Q := paddedPresentation) (.identity _) (fun _ => .inl ())

private theorem toName_kept (d : Declaration equalityPresentation) : toName d ∈ equalityContext.declarations := by
  intro i h
  cases d <;> cases h

private def fromName : equalityContext.Retained → Declaration equalityPresentation
  | ⟨.sort s, _⟩ => .sort s
  | ⟨.total f, _⟩ => .total f
  | ⟨.relation r, _⟩ => .relation r
  | ⟨.partialOp p, _⟩ => .partialOp p
  | ⟨.quantity q, _⟩ => .quantity q
  | ⟨.law (.inl _), _⟩ => .law ()
  | ⟨.law (.inr i), kept⟩ => (kept i rfl).elim

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

private def oneGraph : Formula signature [SortName.scalar] :=
  .conj .truth (.atom (.graph (Operation.total (sig := signature) Symbol.scalarOne)
    (Var.inLeft [SortName.scalar]) .here))

private def zeroGraph : Formula signature [SortName.scalar] :=
  .conj .truth (.atom (.graph (Operation.total (sig := signature) Symbol.scalarZero)
    (Var.inLeft [SortName.scalar]) .here))

private def literalLaw : Law signature := ⟨[], .truth, (oneGraph.conj zeroGraph).ex⟩

private theorem equalityDependencies (a b : Declaration equalityPresentation) :
    b ∈ Declaration.dependsOn equalityPresentation a ↔
      toName b ∈ Declaration.dependsOn paddedPresentation (toName a) := by
  cases a with
  | sort s => exact Iff.rfl
  | relation r => exact nomatch r
  | partialOp p => exact nomatch p
  | quantity q => exact nomatch q
  | total f =>
    cases b <;> simp [Declaration.dependsOn, Declaration.sorts, toName,
      Declaration.renameNames, SignatureNames.identity, equalityPresentation]
  | law n =>
    change b ∈ Declaration.dependsOn equalityPresentation (.law n) ↔
      toName b ∈ Declaration.dependsOn paddedPresentation (.law (.inl ()))
    rw [Declaration.nonderived_dependencies n (fun h => LawRole.noConfusion h),
      Declaration.nonderived_dependencies (P := paddedPresentation) (.inl ()) (fun h => LawRole.noConfusion h)]
    change b ∈ Declaration.lawBody (P := equalityPresentation) literalLaw ↔
      toName b ∈ Declaration.lawBody (P := paddedPresentation) literalLaw
    cases b <;>
      simp [literalLaw, oneGraph, zeroGraph, Declaration.lawBody, Declaration.sorts, Declaration.formula,
        Declaration.atomic, Declaration.ofOperation, Declaration.renameNames, SignatureNames.identity, toName]

/-- The named equality can be selected as a reading when its optional ring axioms are omitted. -/
noncomputable def equalityReadingOrigin : ReadingOrigin equalityPresentation paddedPresentation equalityContext where
  signature := .identity _
  lawName _ := .inl ()
  names := equalityNames
  names_eq _ := rfl
  law_eq _ := by
    change (SignatureNames.identity signature).law ⟨[], .truth, (oneGraph.conj zeroGraph).ex⟩ =
      ⟨[], .truth, (oneGraph.conj zeroGraph).ex⟩
    change Law.mk [] .truth
      (((SignatureNames.identity signature).formula oneGraph).conj
        ((SignatureNames.identity signature).formula zeroGraph)).ex = _
    suffices h : (SignatureNames.identity signature).formula oneGraph = oneGraph ∧
        (SignatureNames.identity signature).formula zeroGraph = zeroGraph by
      rw [h.1, h.2]
    constructor <;> simp [oneGraph, zeroGraph, SignatureNames.formula]
    all_goals
      first
      | apply congrArg (fun (ρ : Renaming [] [SortName.scalar]) =>
          Atomic.graph (sig := signature) (.total Symbol.scalarOne) ρ .here)
      | apply congrArg (fun (ρ : Renaming [] [SortName.scalar]) =>
          Atomic.graph (sig := signature) (.total Symbol.scalarZero) ρ .here)
    all_goals
      funext s i
      exact nomatch i
  law_role _ := rfl
  lawAttachments_eq _ := by
    let A := paddedPresentation.lawAttachments (SignatureNames.identity _) id (.inl ())
    change equalityPresentation.lawAttachments (SignatureNames.identity _) (fun _ => .inl ()) () =
      A.withSupportedRing (equalityContext.RetainsRingSupport (.inl ()))
    simp [LawAttachments.withSupportedRing, equality_lacks_ring_support]
    rfl
  domainAttachment_eq p := nomatch p
  dependencies := equalityDependencies

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
      restrictedIntegerReading.origin.isSome :=
  ⟨rfl, rfl, rfl⟩

end SHIGURE.Chapter3.OrderedRestriction
