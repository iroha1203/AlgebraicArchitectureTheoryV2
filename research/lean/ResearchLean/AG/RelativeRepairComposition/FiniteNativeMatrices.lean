import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeCoordinates
import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinateEnumerations
import ResearchLean.AG.RelativeRepairComposition.FiniteMatrixInterface
import ResearchLean.AG.RelativeRepairComposition.LinearInterfaceAction

/-!
# One finite elimination of the original local differential

## Implementation notes

The original-cell input enumerations generate all full kernel coordinate lists.
Only the private matrix is reduced. Its computed section depends on the same
D, without a right-hand side or candidate-subset argument.
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

/-- Enumerate all original nonfixed vertex coordinates in degree zero. -/
def enum0 [Fintype K.Vertex] [DecidableEq K.Vertex]
    (enumVertices : FiniteElimination.Enumeration K.Vertex) :
    FiniteElimination.Enumeration (Index0 M B U P) :=
  FiniteFamily.indexEnumeration M.A B U.vertices P.vertices enumVertices

/-- Enumerate all original nonfixed triple coordinates in degree three. -/
def enum3 [Fintype K.ThreeCell] [DecidableEq K.ThreeCell]
    [DecidablePred (· ∈ P.triples)] [DecidablePred (· ∈ U.triples)]
    (enumTriples : FiniteElimination.Enumeration K.ThreeCell) :
    FiniteElimination.Enumeration (Index3 M B U P) :=
  FiniteFamily.indexEnumeration (fun t => M.A (K.threeTarget t))
    (B.comap M.A K.threeTarget) U.triples P.triples enumTriples

/-- Enumerate every original nonfixed edge's complete kernel coordinates. -/
def enum1 : FiniteElimination.Enumeration (Index1 M B U P) :=
  FiniteFamily.indexEnumeration (fun e : EdgeName (K := K) => M.A e.2.1)
    (B.comap M.A (fun e : EdgeName (K := K) => e.2.1)) U.edges P.edges enumEdges

/-- Enumerate every original nonfixed face's complete kernel coordinates. -/
def enum2 : FiniteElimination.Enumeration (Index2 M B U P) :=
  FiniteFamily.indexEnumeration (fun f => M.A (K.twoTarget f)) (B.comap M.A K.twoTarget) U.faces P.faces enumFaces

/-- Internal enumeration selects exactly the specified private original coordinates. -/
def enumX : FiniteElimination.Enumeration (XIndex M B U P internalEdges) :=
  (enum1 M B U P enumEdges).subtype (· ∈ privateIndex M B U P internalEdges)

/-- Public enumeration retains the whole complementary original coordinate family. -/
def enumZ : FiniteElimination.Enumeration (ZIndex M B U P internalEdges) :=
  (enum1 M B U P enumEdges).subtype (· ∉ privateIndex M B U P internalEdges)

/-- The internal matrix is obtained by evaluating the actual original private columns. -/
def Dmatrix : Matrix (Index2 M B U P) (XIndex M B U P internalEdges) k :=
  LinearMap.toMatrix' (D M B U P internalEdges hlinear)

/-- The public matrix is obtained by evaluating every remaining original column. -/
def Fmatrix : Matrix (Index2 M B U P) (ZIndex M B U P internalEdges) k :=
  LinearMap.toMatrix' (F M B U P internalEdges hlinear)

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.faces)] [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every internal matrix value is the complete original differential value. -/
theorem Dmatrix_correct (x : XIndex M B U P internalEdges → k) :
    Matrix.toLin' (Dmatrix M B U P internalEdges hlinear) x = D M B U P internalEdges hlinear x := by
  rw [Dmatrix,Matrix.toLin'_toMatrix']

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.faces)] [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every public matrix value is the complete original differential value. -/
theorem Fmatrix_correct (z : ZIndex M B U P internalEdges → k) :
    Matrix.toLin' (Fmatrix M B U P internalEdges hlinear) z = F M B U P internalEdges hlinear z := by
  rw [Fmatrix,Matrix.toLin'_toMatrix']

/-- Generate the private elimination data once, independently of every right-hand side and range. -/
def generatedElimination : FiniteElimination.Reduction
    (FiniteElimination.squareExtension (Dmatrix M B U P internalEdges hlinear)) :=
  FiniteElimination.reduce enumK
    (FiniteElimination.sumEnumeration (enumX M B U P internalEdges enumEdges) (enum2 M B U P enumFaces))
    (FiniteElimination.squareExtension (Dmatrix M B U P internalEdges hlinear))

/-- Generate the image section once, using only D and the complete input coordinate lists. -/
def generatedSection : (Index2 M B U P → k) →ₗ[k] (XIndex M B U P internalEdges → k) :=
  let R := generatedElimination M B U P internalEdges hlinear enumK enumEdges enumFaces
  Matrix.toLin' (Matrix.toBlocks₂₁
    (R.column * Matrix.diagonal (fun i => (R.value i)⁻¹) * R.row))

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- The generated section law is discharged on the same actual original matrix. -/
theorem generatedSection_regular (x : XIndex M B U P internalEdges → k) :
    D M B U P internalEdges hlinear
      (generatedSection M B U P internalEdges hlinear enumK enumEdges enumFaces
        (D M B U P internalEdges hlinear x)) = D M B U P internalEdges hlinear x := by
  have h := FiniteMatrixInterface.section_regular enumK (enum2 M B U P enumFaces)
    (enumX M B U P internalEdges enumEdges) (Dmatrix M B U P internalEdges hlinear) x
  simpa only [Dmatrix_correct] using h

end FiniteNative
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
