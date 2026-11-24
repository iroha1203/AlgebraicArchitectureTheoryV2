import Formal.SHIGURE.Part1.ContextSelectedPresentation
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

open Chapter1.ResidualTransport (paddedPresentation)

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
    ((Selected.presentation equalityContext).orderedEquation ⟨.inl (), equalityKept⟩).isSome :=
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

end SHIGURE.Chapter3.OrderedRestriction
