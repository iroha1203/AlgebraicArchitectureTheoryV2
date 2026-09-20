import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInverseRows
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawCandidateReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport
import Formal.Util.AssertStandardAxioms

/-!
# Explicit raw Hom laws on the common primitive declarations

Implementation notes: all raw families and sparse polynomial values are read
from the original object tables. Context, coordinate, local-data, relation,
and coefficient correspondence is expressed by common Boolean points. There
is no native raw map, ring hom, site arrow, or global polynomial equation in
these fields. Bijective coordinate renaming permits the finite exponent and
coefficient point criterion of IndependentPolynomialPointTransport.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site
open IndependentRawCandidate (CoefficientRef coord rel)

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U}

/-- Explicit raw maps are indexed by the primitive inverse context points. -/
def contextPoints (h : Table.{u, v} U .explicit) (W : ArchCtx A) (V : ArchCtx B) : Bool :=
  h (.atObjects A B (.context .backward W V))

/-- The forward coordinate graph cell at any candidate carriers and point pair. -/
def coordinatePoint (h : Table.{u, v} U .explicit) (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (c : C) (d : D) : Bool :=
  h (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d))))

/-- The forward relation-generator graph cell at any candidate index carriers. -/
def relationPoint (h : Table.{u, v} U .explicit) (W : ArchCtx A) (V : ArchCtx B)
    (I J : Type u) (i : I) (j : J) : Bool :=
  h (.atObjects A B (.raw (.relation .forward W V (.edge I J i j))))

/-- Every explicit raw condition is an inverse graph law or a primitive finite point comparison. -/
structure PointLaws (s : IndependentRawCandidate.Table.{u, v} A)
    (t : IndependentRawCandidate.Table.{u, v} B) (h : Table.{u, v} U .explicit) : Prop where
  /-- Inactive inverse context pairs carry no coordinate data. -/
  coordinateInactive : ∀ W V, contextPoints h W V = false → ∀ q, InverseRows.coordinate h A B W V q = false
  /-- Active coordinate rows construct an equivalence of the declared raw carriers. -/
  coordinateRows : ∀ W V, contextPoints h W V = true →
    IndependentInverseGraph.IsLawful (coord s W) (coord t V) (InverseRows.coordinate h A B W V)
  /-- Inactive inverse context pairs carry no relation-generator data. -/
  relationInactive : ∀ W V, contextPoints h W V = false → ∀ q, InverseRows.relation h A B W V q = false
  /-- Active relation rows construct an equivalence of the declared relation carriers. -/
  relationRows : ∀ W V, contextPoints h W V = true →
    IndependentInverseGraph.IsLawful (rel s W) (rel t V) (InverseRows.relation h A B W V)
  /-- Either inactive context or inactive coordinate point makes every local-data cell false. -/
  localDataInactive : ∀ W V C D (c : C) (d : D),
    contextPoints h W V = false ∨ coordinatePoint h W V C D c d = false →
    ∀ q, InverseRows.localData h A B W V C D c d q = false
  /-- Active coordinate and local-data type responses determine the dependent inverse fiber graph. -/
  localDataRows : ∀ W V C D (c : C) (d : D) (L M : Type u),
    contextPoints h W V = true → coordinatePoint h W V C D c d = true →
    (s (.localData W C c)).down = some L → (t (.localData V D d)).down = some M →
    IndependentInverseGraph.IsLawful L M (InverseRows.localData h A B W V C D c d)
  /-- Coordinate labels agree at every active coordinate graph point. -/
  label : ∀ W V C D (c : C) (d : D),
    contextPoints h W V = true → coordinatePoint h W V C D c d = true →
    (s (.label W C c)).down = (t (.label V D d)).down
  /-- Relation preservation reads two sparse polynomial responses and compares their primitive graph points. -/
  polynomial : ∀ W V C D I J (rk rl : CoefficientRef.{v}) (i : I) (j : J) p p',
    contextPoints h W V = true → relationPoint h W V I J i j = true →
    (s (.polynomial W C I rk i)).down = some p → (t (.polynomial V D J rl j)).down = some p' →
    IndependentPolynomialPointTransport.PointLaws (coordinatePoint h W V C D)
      (fun a b => h (.coefficient (.edge rk.1 rl.1 a b))) p p'
  /-- Restriction naturality is tested on sparse images of corresponding variables at inverse context pairs. -/
  image : ∀ W X V Y C D E F (rk rl : CoefficientRef.{v}) (x : E) (y : F) p p',
    contextPoints h W V = true → contextPoints h X Y = true → coordinatePoint h X Y E F x y = true →
    (s (.image W X C E rk x)).down = some p → (t (.image V Y D F rl y)).down = some p' →
    IndependentPolynomialPointTransport.PointLaws (coordinatePoint h W V C D)
      (fun a b => h (.coefficient (.edge rk.1 rl.1 a b))) p p'

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
