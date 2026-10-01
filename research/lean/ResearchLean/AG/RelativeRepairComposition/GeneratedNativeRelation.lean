import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeMatrices
import ResearchLean.AG.RelativeRepairComposition.GeneratedRelationRows
import ResearchLean.AG.RelativeRepairComposition.InterfaceQuotient

/-!
# Generated independent public relations for the full original local matrix

## Implementation notes

The same original differential supplies the public output matrix after private
elimination. Its generated rows are independent, bounded by the original public
dimension, and reused for every consistent right-hand side.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace FiniteNative
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)]
variable [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ U.vertices)]
variable [DecidablePred (· ∈ U.edges)] [DecidablePred (· ∈ U.faces)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)


/-- All private image coordinates are generated from the same original private matrix. -/
def generatedPrivateImageCoordinates :=
  (FiniteElimination.rectangleImageEquivalence (Dmatrix M B U P internalEdges hlinear)).trans
    (FiniteElimination.imageEquivalence (FiniteElimination.squareExtension (Dmatrix M B U P internalEdges hlinear)) (generatedElimination M B U P internalEdges hlinear enumK enumEdges enumFaces))

/-- Each generated private image basis vector lies in the full original face space. -/
def generatedPrivateImageBasisValue
    (i : FiniteElimination.Active (FiniteElimination.squareExtension (Dmatrix M B U P internalEdges hlinear)) (generatedElimination M B U P internalEdges hlinear enumK enumEdges enumFaces)) :=
  (generatedPrivateImageCoordinates M B U P internalEdges hlinear enumK enumEdges enumFaces).symm (Pi.single i 1)

/-- The entire native original cokernel uses the section generated from this same matrix. -/
noncomputable def generatedQuotientEquivalence :=
  LinearInterface.quotientEquivalence (D M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces) (generatedSection_regular M B U P internalEdges hlinear enumK enumEdges enumFaces)

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- The generated kernel projector spans precisely the full original private kernel. -/
theorem generated_kernel_projection_range :
    LinearMap.range (LinearInterface.kernelProjection (D M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces)) = LinearMap.ker (D M B U P internalEdges hlinear) :=
  LinearInterface.kernel_projection_range (D M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces) (generatedSection_regular M B U P internalEdges hlinear enumK enumEdges enumFaces)

/-- Compute the full projected public differential once without a right-hand side. -/
def publicMatrix : Matrix (Index2 M B U P) (ZIndex M B U P internalEdges) k :=
  LinearMap.toMatrix' ((LinearInterface.projection (D M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces)).comp (F M B U P internalEdges hlinear))

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- The computed matrix is exactly the projected original public differential. -/
theorem public_matrix_correct (z : ZIndex M B U P internalEdges → k) :
    Matrix.toLin' (publicMatrix M B U P internalEdges hlinear enumK enumEdges enumFaces) z = LinearInterface.projection (D M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces) ((F M B U P internalEdges hlinear) z) := by
  rw [publicMatrix,Matrix.toLin'_toMatrix']
  rfl

/-- Independent rows are generated from the full projected original public matrix. -/
def generatedPublicRows := FiniteElimination.publicRow (publicMatrix M B U P internalEdges hlinear enumK enumEdges enumFaces) enumK (enum2 M B U P enumFaces) (enumZ M B U P internalEdges enumEdges)

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- The complete generated original public rows are independent. -/
theorem generated_public_rows_independent : LinearIndependent k
    (generatedPublicRows M B U P internalEdges hlinear enumK enumEdges enumFaces) :=
  FiniteElimination.public_rows_independent (publicMatrix M B U P internalEdges hlinear enumK enumEdges enumFaces) enumK (enum2 M B U P enumFaces) (enumZ M B U P internalEdges enumEdges)

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- Generated public equations never exceed the original public-coordinate dimension. -/
theorem generated_public_row_count :
    Fintype.card (FiniteElimination.RectangularActive (publicMatrix M B U P internalEdges hlinear enumK enumEdges enumFaces) enumK (enum2 M B U P enumFaces) (enumZ M B U P internalEdges enumEdges)) ≤
      Fintype.card (ZIndex M B U P internalEdges) :=
  FiniteElimination.public_row_count (publicMatrix M B U P internalEdges hlinear enumK enumEdges enumFaces) enumK (enum2 M B U P enumFaces) (enumZ M B U P internalEdges enumEdges)

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- Every nonempty public relation is expressed by the same independent computed rows. -/
theorem generated_public_affine_relation (r : Index2 M B U P → k)
    (z₀ : ↥(LinearInterface.Relation (D M B U P internalEdges hlinear) (F M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces) r))
    (z : ZIndex M B U P internalEdges → k) :
    z ∈ LinearInterface.Relation (D M B U P internalEdges hlinear) (F M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces) r ↔ ∀ i,
      generatedPublicRows M B U P internalEdges hlinear enumK enumEdges enumFaces i z =
        generatedPublicRows M B U P internalEdges hlinear enumK enumEdges enumFaces i z₀.1 := by
  have hh := FiniteElimination.public_affine_relation (publicMatrix M B U P internalEdges hlinear enumK enumEdges enumFaces) enumK (enum2 M B U P enumFaces) (enumZ M B U P internalEdges enumEdges)
    (LinearInterface.projection (D M B U P internalEdges hlinear) (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces) r) z₀.1
    ((public_matrix_correct M B U P internalEdges hlinear enumK enumEdges enumFaces z₀.1).trans z₀.2) z
  simpa only [public_matrix_correct,generatedPublicRows,LinearInterface.Relation,Set.mem_setOf_eq] using hh

end FiniteNative
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
