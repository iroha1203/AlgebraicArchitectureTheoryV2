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

open Chapter1.RingModule (realization scalarOne scalarZero)

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

end SHIGURE.Chapter3.OrderedRestriction
