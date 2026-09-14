import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses
import Formal.Util.AssertStandardAxioms

/-!
# Parameter-relative finite references for AAT realization syntax

This module supplies a dependency-shape scaffold for a later G-123(A)
declaration.  `AATReferenceShape` lists the source, configuration, object,
operation, Law, and complete-geometry reference sorts which a presentation
must type.  A `FiniteReferenceSkeleton` selects finitely many typed
occurrences while the parameter and coefficient carriers remain arbitrary.

This generic scaffold does not establish that an arbitrary instantiation has
primitive AAT provenance: its carriers are intentionally unrestricted.  The
future closed declaration and interpretation must establish that provenance
from the permitted source data and must exclude completed core/geometry maps,
decoder images, extension certificates, and comparison-group elements.  It
must then construct the semantic realization, syntax congruence, evaluator,
and the global object/operation/context maps required by `res` and `ext`.
-/

namespace AAT.AG.RealizationReconstruction

universe u v

/-- The dependent reference-sort shape used to type a future closed AAT
parameter declaration.  This is not itself the final G-123 `Σ`: no primitive
provenance or interpretation is asserted for an arbitrary inhabitant. -/
structure AATReferenceShape where
  Parameter : Type u
  Atom : Parameter → Type u
  Source : Parameter → Type u
  Configuration : Parameter → Type u
  Object : Parameter → Type u
  Structure : ∀ θ, Object θ → Type u
  Quantity : ∀ θ, Object θ → Type u
  Operation : ∀ θ, Object θ → Object θ → Type u
  Law : ∀ θ, Object θ → Type u
  Invariant : ∀ θ, Object θ → Type u
  SignatureAxis : Parameter → Type u
  Context : ∀ θ, Object θ → Type u
  Coverage : ∀ {θ X}, Context θ X → Type u
  Overlap : ∀ {θ X}, Context θ X → Context θ X → Type u
  Support : ∀ {θ X}, Context θ X → Type u
  Axis : ∀ {θ X}, Context θ X → Type u
  Observable : ∀ {θ X}, Context θ X → Type u
  Coefficient : Parameter → Type v
  Coordinate : ∀ {θ X}, Context θ X → Type u
  Relation : ∀ {θ X}, Context θ X → Type u
  Restriction : ∀ {θ X}, Context θ X → Context θ X → Type u

namespace AATReferenceShape

variable (S : AATReferenceShape.{u, v}) (θ : S.Parameter)

/-- An object-formation occurrence retains its configuration, structure, and
selected quantity references. -/
structure NamedObjectFormation where
  object : S.Object θ
  configuration : S.Configuration θ
  structureRef : S.Structure θ object
  quantity : S.Quantity θ object

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

/-- An invariant occurrence retains its ambient object. -/
structure NamedInvariant where
  object : S.Object θ
  invariant : S.Invariant θ object

/-- A context occurrence retains its ambient object. -/
structure NamedContext where
  object : S.Object θ
  context : S.Context θ object

/-- A coverage occurrence retains the context in which it is imposed. -/
structure NamedCoverage where
  object : S.Object θ
  context : S.Context θ object
  coverage : S.Coverage context

/-- An overlap occurrence retains both context endpoints. -/
structure NamedOverlap where
  object : S.Object θ
  left : S.Context θ object
  right : S.Context θ object
  overlap : S.Overlap left right

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

end AATReferenceShape

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
    (S : AATReferenceShape.{u, v}) (θ : S.Parameter) where
  atoms : FiniteReferenceTable (S.Atom θ)
  sources : FiniteReferenceTable (S.Source θ)
  configurations : FiniteReferenceTable (S.Configuration θ)
  objects : FiniteReferenceTable (S.Object θ)
  objectFormations : FiniteReferenceTable (S.NamedObjectFormation θ)
  operations : FiniteReferenceTable (S.NamedOperation θ)
  laws : FiniteReferenceTable (S.NamedLaw θ)
  invariants : FiniteReferenceTable (S.NamedInvariant θ)
  signatureAxes : FiniteReferenceTable (S.SignatureAxis θ)
  contexts : FiniteReferenceTable (S.NamedContext θ)
  coverages : FiniteReferenceTable (S.NamedCoverage θ)
  overlaps : FiniteReferenceTable (S.NamedOverlap θ)
  supports : FiniteReferenceTable (S.NamedSupport θ)
  axes : FiniteReferenceTable (S.NamedAxis θ)
  observables : FiniteReferenceTable (S.NamedObservable θ)
  coefficients : FiniteReferenceTable (S.Coefficient θ)
  coordinates : FiniteReferenceTable (S.NamedCoordinate θ)
  relations : FiniteReferenceTable (S.NamedRelation θ)
  restrictions : FiniteReferenceTable (S.NamedRestriction θ)

open CategoryTheory DoctrineFiberProduct TransportCoherence

local instance finiteAxisFoldReferenceAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The actual context-object type of the fixed G-122 finite-axis-fold datum is
covered by a two-entry reference table. -/
noncomputable def finiteAxisFoldContextReferences :
    FiniteReferenceTable finiteAxisFoldBCDatumSquare.context.Category where
  card := 2
  value i := Discrete.mk
    (Fin.cases DoubleDiamondTwoCell.first (fun _ ↦ DoubleDiamondTwoCell.second) i)

/-- Both context objects of the fixed G-122 datum occur in its table. -/
theorem finiteAxisFoldContextReferences_complete :
    finiteAxisFoldContextReferences.Complete := by
  unfold FiniteReferenceTable.Complete FiniteReferenceTable.Contains
  simp only [finiteAxisFoldContextReferences]
  intro x
  rcases x with ⟨x⟩
  cases x with
  | first =>
      refine ⟨0, ?_⟩
      rfl
  | second =>
      refine ⟨1, ?_⟩
      rfl

/-- A one-entry table is deliberately insufficient for the fixed G-122
context-object family. -/
noncomputable def firstOnlyFiniteAxisFoldContextReferences :
    FiniteReferenceTable finiteAxisFoldBCDatumSquare.context.Category where
  card := 1
  value _ := Discrete.mk DoubleDiamondTwoCell.first

/-- The fixed second context object witnesses incompleteness of the one-entry
table, so `Complete` is not hidden in the table structure. -/
theorem firstOnlyFiniteAxisFoldContextReferences_not_complete :
    ¬ firstOnlyFiniteAxisFoldContextReferences.Complete := by
  change ¬ (∀ x, ∃ i : Fin 1,
    Discrete.mk DoubleDiamondTwoCell.first = x)
  intro h
  rcases h (Discrete.mk DoubleDiamondTwoCell.second) with ⟨i, hi⟩
  cases congrArg Discrete.as hi

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
