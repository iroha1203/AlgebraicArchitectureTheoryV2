import ResearchLean.AG.TransportCoherence.FiniteWitnesses
import Formal.Util.AssertStandardAxioms

/-!
# Parameter-relative finite references for AAT realization syntax

This module starts G-123(A) without moving any completed reconstruction map
into the input.  `AATParameterSignature` records the primitive dependent
sorts needed by an AAT presentation.  A `FiniteReferenceSkeleton` selects
finitely many typed occurrences from those sorts while the parameter and
coefficient carriers themselves remain arbitrary.

In particular, the skeleton contains no `PackageTotalHom`,
`SignedExactCoreReadingHom`, `GeomReadHom`, `GeometryTotalHom`, decoder image,
extension certificate, or comparison-group element.  Later modules must still
construct the semantic realization, syntax congruence, evaluator, and the
global object/operation/context maps required by `res` and `ext`.
-/

namespace AAT.AG.RealizationReconstruction

universe u v

/-- The dependent primitive sorts that one parameter-relative AAT syntax must
retain.  None of the carriers is required to be finite. -/
structure AATParameterSignature where
  Parameter : Type u
  Atom : Parameter → Type u
  Object : Parameter → Type u
  Operation : ∀ θ, Object θ → Object θ → Type u
  Law : ∀ θ, Object θ → Type u
  Context : ∀ θ, Object θ → Type u
  Support : ∀ {θ X}, Context θ X → Type u
  Axis : ∀ {θ X}, Context θ X → Type u
  Observable : ∀ {θ X}, Context θ X → Type u
  Coefficient : Parameter → Type v
  Coordinate : ∀ {θ X}, Context θ X → Type u
  Relation : ∀ {θ X}, Context θ X → Type u
  Restriction : ∀ {θ X}, Context θ X → Context θ X → Type u

namespace AATParameterSignature

variable (S : AATParameterSignature.{u, v}) (θ : S.Parameter)

/-- An operation occurrence retains both endpoints as well as its primitive
operation name. -/
structure NamedOperation where
  source : S.Object θ
  target : S.Object θ
  operation : S.Operation θ source target

/-- A law occurrence retains the object on which the law is read. -/
structure NamedLaw where
  object : S.Object θ
  law : S.Law θ object

/-- A context occurrence retains its ambient object. -/
structure NamedContext where
  object : S.Object θ
  context : S.Context θ object

/-- A support occurrence retains its object and context. -/
structure NamedSupport where
  object : S.Object θ
  context : S.Context θ object
  support : S.Support context

/-- An axis occurrence retains its object and context. -/
structure NamedAxis where
  object : S.Object θ
  context : S.Context θ object
  axis : S.Axis context

/-- An observable occurrence retains its object and context. -/
structure NamedObservable where
  object : S.Object θ
  context : S.Context θ object
  observable : S.Observable context

/-- A raw coordinate occurrence retains its object and context. -/
structure NamedCoordinate where
  object : S.Object θ
  context : S.Context θ object
  coordinate : S.Coordinate context

/-- A raw relation occurrence retains its object and context. -/
structure NamedRelation where
  object : S.Object θ
  context : S.Context θ object
  relation : S.Relation context

/-- A restriction occurrence retains its object and both context endpoints. -/
structure NamedRestriction where
  object : S.Object θ
  source : S.Context θ object
  target : S.Context θ object
  restriction : S.Restriction source target

end AATParameterSignature

/-- A genuinely finite table of references into an arbitrary carrier.  The
carrier need not be finite and no completeness proof is stored in the table. -/
structure FiniteReferenceTable (α : Type u) where
  card : ℕ
  value : Fin card → α

namespace FiniteReferenceTable

variable {α : Type u}

/-- A reference table contains a value when one of its finite entries names
that value. -/
def Contains (T : FiniteReferenceTable α) (x : α) : Prop :=
  ∃ i, T.value i = x

/-- Completeness is a separately proved property, not an input field. -/
def Complete (T : FiniteReferenceTable α) : Prop :=
  ∀ x, T.Contains x

end FiniteReferenceTable

/-- A finite, parameter-relative reference surface.  Each dependent value is
stored together with the object or context that types it.  The coefficient
field is only a finite list of primitive coefficient references; it does not
encode a completed coefficient map. -/
structure FiniteReferenceSkeleton
    (S : AATParameterSignature.{u, v}) (θ : S.Parameter) where
  atoms : FiniteReferenceTable (S.Atom θ)
  objects : FiniteReferenceTable (S.Object θ)
  operations : FiniteReferenceTable (S.NamedOperation θ)
  laws : FiniteReferenceTable (S.NamedLaw θ)
  contexts : FiniteReferenceTable (S.NamedContext θ)
  supports : FiniteReferenceTable (S.NamedSupport θ)
  axes : FiniteReferenceTable (S.NamedAxis θ)
  observables : FiniteReferenceTable (S.NamedObservable θ)
  coefficients : FiniteReferenceTable (S.Coefficient θ)
  coordinates : FiniteReferenceTable (S.NamedCoordinate θ)
  relations : FiniteReferenceTable (S.NamedRelation θ)
  restrictions : FiniteReferenceTable (S.NamedRestriction θ)

open TransportCoherence

/-- The fixed finite-axis-fold two-cell family is covered by a two-entry
primitive reference table. -/
def finiteAxisFoldTwoCellReferences :
    FiniteReferenceTable (DoubleDiamondTwoCell PUnit) where
  card := 2
  value i := Fin.cases .first (fun _ ↦ .second) i

/-- The same two fixed generators are both present in the reference table. -/
theorem finiteAxisFoldTwoCellReferences_complete :
    finiteAxisFoldTwoCellReferences.Complete := by
  unfold FiniteReferenceTable.Complete FiniteReferenceTable.Contains
  simp only [finiteAxisFoldTwoCellReferences]
  intro x
  cases x with
  | first =>
      refine ⟨0, ?_⟩
      rfl
  | second =>
      refine ⟨1, ?_⟩
      rfl

/-- A one-entry table is deliberately insufficient for the fixed two-cell
family, showing that completeness is not hidden in the table definition. -/
def firstOnlyTwoCellReferences :
    FiniteReferenceTable (DoubleDiamondTwoCell PUnit) where
  card := 1
  value _ := .first

theorem firstOnlyTwoCellReferences_not_complete :
    ¬ firstOnlyTwoCellReferences.Complete := by
  change ¬ (∀ x, ∃ i : Fin 1, DoubleDiamondTwoCell.first = x)
  intro h
  rcases h (.second) with ⟨i, hi⟩
  cases hi

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
