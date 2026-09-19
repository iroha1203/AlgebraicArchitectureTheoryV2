import ResearchLean.AG.LocalSemanticReconstruction.IndependentCoreTableAssembly
import ResearchLean.AG.LocalSemanticReconstruction.IndependentOverlapCandidateReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentCoveragePrimitiveReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawCandidateReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeneratedObjectMatching
import Formal.Util.AssertStandardAxioms

/-!
# One primitive query declaration for complete geometry objects

All candidate addresses and response types are declared before choosing any
realization or primitive generating table. The declaration combines the native
primitive field roles, derived reference-matching flags, and candidate-object
rows. Inactive object candidates have a unique absent response. Each active
row contains only a primitive point response; complete core/site/ring/raw
structures are constructed after reading those rows.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive

noncomputable section

universe u v

open IndependentCorePrimitive

variable {U : AtomCarrier.{u}}

/-- The five primitive field families whose input contexts refer to a candidate architecture object. -/
inductive DependentQuery (A : ArchitectureObject U) where
  /-- Refinement and selected context-morphism points. -/
  | context (q : IndependentContextPrimitive.Query A)
  /-- Equation roles, observable rings, restrictions, and coordinate values. -/
  | equation (q : IndependentEquationPrimitive.Query A)
  /-- Primitive fields of each selected overlap context. -/
  | overlap (q : IndependentOverlapCandidate.Query A)
  /-- The nine native coverage-predicate roles. -/
  | coverage (q : IndependentCoveragePrimitive.Query A)
  /-- Raw type declarations, labels, finite polynomials, and variable images. -/
  | raw (q : IndependentRawCandidate.Query.{u, v} A)

/-- Dependent responses keep their original role-specific point types. -/
def DependentQuery.Value {A : ArchitectureObject U} :
    DependentQuery.{u, v} A → Type (max (u + 1) (v + 1))
  | .context q => ULift.{max (u + 1) (v + 1)} q.Value
  | .equation q => ULift.{max (u + 1) (v + 1)} q.Value
  | .overlap q => ULift.{max (u + 1) (v + 1)} q.Value
  | .coverage _ => ULift.{max (u + 1) (v + 1)} Prop
  | .raw q => q.Value

/-- Complete primitive point responses at one candidate object, without any semantic structure fields. -/
abbrev DependentTable (A : ArchitectureObject U) := (q : DependentQuery.{u, v} A) → q.Value

/-- The common closed declaration for every native complete-geometry object primitive. -/
inductive Query (U : AtomCarrier.{u}) where
  /-- Selected extraction roles, admissions, and normalization points. -/
  | extraction (q : Extraction.Query U)
  /-- Pointwise composition relations on supplied finite families. -/
  | composition (q : Composition.Query U)
  /-- Primitive type/value pairs of object formation. -/
  | formation (q : ObjectFormation.Query U)
  /-- Invariant indices, types, function values, and predicates. -/
  | invariant (q : IndependentInvariantSignaturePrimitive.Invariants.Query U)
  /-- Signature axes, selected axes, coordinate types, and values. -/
  | signature (q : IndependentInvariantSignaturePrimitive.Signature.Query U)
  /-- Operation carrier references and single-Atom actions. -/
  | operation (q : Operations.Query U)
  /-- One finite detector code at a candidate equation index. -/
  | circuit (q : IndependentEquationPrimitive.Circuit.Query.{u})
  /-- Primitive coefficient carrier and ring-operation points. -/
  | coefficient (q : IndependentRingPrimitive.Carrier.Query.{v})
  /-- Derived typing metadata comparing candidate primitive references. -/
  | matching (q : IndependentGeneratedObjectMatching.Query U)
  /-- A primitive row at a candidate architecture object; activation is decided by its matching flag. -/
  | atObject (A : ArchitectureObject U) (q : DependentQuery.{u, v} A)

/-- Local values are primitive points, finite syntax, type references, or normalized optional rows. -/
def Query.Value : Query.{u, v} U → Type (max (u + 1) (v + 1))
  | .extraction q => ULift.{max (u + 1) (v + 1)} q.Value
  | .composition _ => ULift.{max (u + 1) (v + 1)} Prop
  | .formation _ => ULift.{max (u + 1) (v + 1)} SelectedValue.{u}
  | .invariant q => ULift.{max (u + 1) (v + 1)} q.Value
  | .signature q => ULift.{max (u + 1) (v + 1)} q.Value
  | .operation q => ULift.{max (u + 1) (v + 1)} q.Value
  | .circuit _ => ULift.{max (u + 1) (v + 1)} (Option (CircuitDetectorCode U))
  | .coefficient q => ULift.{max (u + 1) (v + 1)} q.Value
  | .matching _ => ULift.{max (u + 1) (v + 1)} Bool
  | .atObject _ q => Option q.Value

/-- One dependent table on indices fixed before selecting any realization. -/
abbrev Table (U : AtomCarrier.{u}) := (q : Query.{u, v} U) → q.Value

/-- Extraction points are direct projections of the common table. -/
def extraction (t : Table.{u, v} U) : Extraction.Table U := fun q => (t (.extraction q)).down

/-- Composition points are direct projections of the common table. -/
def composition (t : Table.{u, v} U) : Composition.Table U := fun q => (t (.composition q)).down

/-- Object-formation values are direct projections of the common table. -/
def formation (t : Table.{u, v} U) : ObjectFormation.Table U := fun q => (t (.formation q)).down

/-- Invariant points are direct projections of the common table. -/
def invariant (t : Table.{u, v} U) : IndependentInvariantSignaturePrimitive.Invariants.Table U :=
  fun q => (t (.invariant q)).down

/-- Signature points are direct projections of the common table. -/
def signature (t : Table.{u, v} U) : IndependentInvariantSignaturePrimitive.Signature.Table U :=
  fun q => (t (.signature q)).down

/-- Operation points are direct projections of the common table. -/
def operation (t : Table.{u, v} U) : Operations.Table U := fun q => (t (.operation q)).down

/-- Finite circuit codes are direct projections of the common table. -/
def circuit (t : Table.{u, v} U) : IndependentEquationPrimitive.Circuit.Table U :=
  fun q => (t (.circuit q)).down

/-- Coefficient points are direct projections of the common table. -/
def coefficient (t : Table.{u, v} U) : IndependentRingPrimitive.Carrier.Table.{v} :=
  fun q => (t (.coefficient q)).down

/-- Candidate-reference matching flags are direct projections of the common table. -/
def matching (t : Table.{u, v} U) : IndependentGeneratedObjectMatching.Table U :=
  fun q => (t (.matching q)).down

/-- Object-indexed primitive rows are active exactly when their reference matches. -/
def IsActiveTyped (t : Table.{u, v} U) : Prop :=
  ∀ A (q : DependentQuery.{u, v} A), (t (.atObject A q)).isSome ↔ matching t (.object A) = true

/-- Extract each primitive point of an active object row after its single Boolean guard is known. -/
def dependent (t : Table.{u, v} U) (ht : IsActiveTyped t) (A : ArchitectureObject U)
    (ha : matching t (.object A) = true) : DependentTable.{u, v} A :=
  fun q => (t (.atObject A q)).get ((ht A q).2 ha)

/-- No arbitrary values survive in an inactive architecture-object row. -/
theorem inactive_eq_none (t : Table.{u, v} U) (ht : IsActiveTyped t)
    (A : ArchitectureObject U) (ha : matching t (.object A) = false)
    (q : DependentQuery.{u, v} A) : t (.atObject A q) = none := by
  apply IndependentRawLocal.option_eq_none_of_inactive
  intro hp
  exact Bool.noConfusion (ha.symm.trans ((ht A q).1 hp))

/-- Rewrapping an extracted active point returns the complete original optional response. -/
theorem some_dependent (t : Table.{u, v} U) (ht : IsActiveTyped t) (A : ArchitectureObject U)
    (ha : matching t (.object A) = true) (q : DependentQuery.{u, v} A) :
    some (dependent t ht A ha q) = t (.atObject A q) := Option.some_get _

/-- The context table is reconstructed from primitive context rows alone. -/
def contextTable {A : ArchitectureObject U} (d : DependentTable.{u, v} A) :
    IndependentContextPrimitive.Table A := fun q => (d (.context q)).down

/-- The equation table is reconstructed from primitive equation rows alone. -/
def equationTable {A : ArchitectureObject U} (d : DependentTable.{u, v} A) :
    IndependentEquationPrimitive.Table A := fun q => (d (.equation q)).down

/-- Every overlap context is reconstructed from its primitive context-field rows. -/
def overlapTable {A : ArchitectureObject U} (d : DependentTable.{u, v} A) :
    IndependentOverlapCandidate.Table A := fun q => (d (.overlap q)).down

/-- Coverage predicate values retain their original point arguments. -/
def coverageTable {A : ArchitectureObject U} (d : DependentTable.{u, v} A) :
    IndependentCoveragePrimitive.Table A := fun q => (d (.coverage q)).down

/-- Raw rows retain candidate zero and context-pair activation without a site in the query type. -/
def rawTable {A : ArchitectureObject U} (d : DependentTable.{u, v} A) :
    IndependentRawCandidate.Table.{u, v} A := fun q => d (.raw q)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive
