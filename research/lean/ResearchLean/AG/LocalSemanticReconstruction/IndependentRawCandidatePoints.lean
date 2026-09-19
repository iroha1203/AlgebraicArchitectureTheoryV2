import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawCandidateReadings
import Formal.Util.AssertStandardAxioms

/-!
# Active primitive points of the native raw reader

Implementation notes: these comparison lemmas expose individual primitive
responses, so downstream Hom constructors need not unfold the candidate
reader or its activation guards. All carriers are those of the displayed
native primitive fields; no completed map is introduced.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentRawCandidate

noncomputable section

universe u v

open Site CategoryTheory LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable (S : AATSite A) (k : Type v) [CommRing k] (R : RawAmbientRestrictionSystem S k)

/-- The coordinate declaration is the raw carrier at that exact context reference. -/
theorem read_coordinate (W : ArchCtx A) :
    (read S k R (.coordinate W)).down = (R.coordFamily ⟨W⟩).Coord := rfl

/-- The relation declaration is the raw relation carrier at that exact context reference. -/
theorem read_relation (W : ArchCtx A) :
    (read S k R (.relation W)).down = (R.relationFamily ⟨W⟩).Relation := rfl

/-- The active label response contains the original native label. -/
theorem read_label (W : ArchCtx A) (c : (R.coordFamily ⟨W⟩).Coord) :
    (read S k R (.label W (R.coordFamily ⟨W⟩).Coord c)).down = some ((R.coordFamily ⟨W⟩).label c) := by
  classical
  simp [read, raise, IndependentRawLocal.read]

/-- The active local-data response contains the original dependent native carrier. -/
theorem read_localData (W : ArchCtx A) (c : (R.coordFamily ⟨W⟩).Coord) :
    (read S k R (.localData W (R.coordFamily ⟨W⟩).Coord c)).down = some ((R.coordFamily ⟨W⟩).LocalData c) := by
  classical
  simp [read, raise, IndependentRawLocal.read]

/-- The active sparse relation response is precisely the original finite native polynomial. -/
theorem read_polynomial (W : ArchCtx A) (i : (R.relationFamily ⟨W⟩).Relation) :
    (read S k R (.polynomial W (R.coordFamily ⟨W⟩).Coord (R.relationFamily ⟨W⟩).Relation
      (coefficientRef k) i)).down = some (IndependentPolynomialExpressions.sparseEquiv ((R.relationFamily ⟨W⟩).polynomial i)) := by
  classical
  simp [read, raise, transportPolynomial, IndependentRawLocal.read]
  rfl

/-- A readable context pair returns the original sparse variable image of its native arrow. -/
theorem read_image {W X : ArchCtx A} (hx : S.contextPreorder.le W X) (c : (R.coordFamily ⟨X⟩).Coord) :
    (read S k R (.image W X (R.coordFamily ⟨W⟩).Coord (R.coordFamily ⟨X⟩).Coord (coefficientRef k) c)).down =
      some (IndependentPolynomialExpressions.sparseEquiv
        ((R.restrictionStable (homOfLE hx : (⟨W⟩ : S.category) ⟶ ⟨X⟩)).restriction.variableImage c)) := by
  classical
  simp [read, raise, transportPolynomial, IndependentRawLocal.read, hx]
  rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentRawCandidate

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentRawCandidate
