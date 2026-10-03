import ResearchLean.AG.RelativeRepairComposition.W1SymbolicPublicMatrices
import ResearchLean.AG.RelativeRepairComposition.W1SymbolicLocalStructure

/-!
# Reusing the independently generated W1 public rows for every input update

The actual private image is zero, so the original projected public matrix is
its complete original F matrix. The same complete coordinate names and lists
therefore generate the same independent rows at every x,y, before any rhs or
candidate permission set is supplied.

## Implementation notes

The actual projected matrices and their actual full face/public lists are
compared before applying the same public-row generator. Finite/equality
instances are compared by uniqueness; the full generated row family is
compared by HEq along its computed active-index type. Comparing only its span
would omit the requested reuse of the generated rows themselves.
-/
namespace AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalInterfaces W1GeneratedRelations W1SymbolicPublicMatrices
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
local notation "M" x y => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- Read the independently projected actual matrix on every original structural coordinate. -/
noncomputable def structuralProjectedMatrix (x y : ZMod 3) (j : Bool) :
    Matrix (W1SymbolicPublicMatrices.faceIndex j) (W1SymbolicPublicMatrices.publicIndex j) (ZMod 3) :=
  FiniteNative.publicMatrix (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))) (bases true x y) (regions j) fixedRegion (priv j)
    (original_linear true x y) enumK enumEdges enumFaces

/-- The complete projected matrix is the entire original F matrix because its actual private image is zero. -/
theorem projected_eq_public (x y : ZMod 3) (j : Bool) :
    structuralProjectedMatrix x y j = structuralPublicMatrix x y j := by
  unfold structuralProjectedMatrix structuralPublicMatrix FiniteNative.publicMatrix W1LocalInterfaces.publicMatrix FiniteNative.Fmatrix
  apply congrArg LinearMap.toMatrix'
  apply LinearMap.ext
  intro z
  exact projection_identity x y j _

/-- The complete independently projected public matrix is the same at every symbolic input pair. -/
theorem projected_matrix_same (x y : ZMod 3) (j : Bool) :
    structuralProjectedMatrix x y j = structuralProjectedMatrix 0 0 j :=
  (projected_eq_public x y j).trans ((public_matrix_same x y j).trans (projected_eq_public 0 0 j).symm)

/-- The full actual original public enumeration, before any candidate range is selected. -/
noncomputable def actualPublic (x y : ZMod 3) (j : Bool) :
    FiniteElimination.Enumeration (W1SymbolicPublicMatrices.publicIndex j) :=
  FiniteNative.enumZ (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y)))
    (bases true x y) (regions j) fixedRegion (priv j) enumEdges

/-- Every complete actual public list retains the same original names and full basis indices. -/
theorem public_enumeration_same (x y : ZMod 3) (j : Bool) : actualPublic x y j = actualPublic 0 0 j := by
  unfold actualPublic FiniteNative.enumZ
  apply W1SymbolicLocalStructure.enumeration_subtype_congr j (fun e => e.1.1 ∉ priv j)
  exact W1SymbolicLocalStructure.edges_same x y j

/-- The original finite public-row generator with all input data and finite/equality instances explicit. -/
noncomputable def rowsFor (j : Bool)
    (f : Fintype (W1SymbolicPublicMatrices.faceIndex j)) (d : DecidableEq (W1SymbolicPublicMatrices.faceIndex j))
    (g : Fintype (W1SymbolicPublicMatrices.publicIndex j)) (e : DecidableEq (W1SymbolicPublicMatrices.publicIndex j))
    (m : Matrix (W1SymbolicPublicMatrices.faceIndex j) (W1SymbolicPublicMatrices.publicIndex j) (ZMod 3))
    (A : FiniteElimination.Enumeration (W1SymbolicPublicMatrices.faceIndex j))
    (B : FiniteElimination.Enumeration (W1SymbolicPublicMatrices.publicIndex j)) := by
  letI : Fintype (W1SymbolicPublicMatrices.faceIndex j) := f
  letI : DecidableEq (W1SymbolicPublicMatrices.faceIndex j) := d
  letI : Fintype (W1SymbolicPublicMatrices.publicIndex j) := g
  letI : DecidableEq (W1SymbolicPublicMatrices.publicIndex j) := e
  exact FiniteElimination.publicRow m enumK A B

/-- Equal full original matrices and lists give exactly the same complete generated row family. -/
theorem rows_congr (j : Bool)
    {f₁ f₂ : Fintype (W1SymbolicPublicMatrices.faceIndex j)}
    {d₁ d₂ : DecidableEq (W1SymbolicPublicMatrices.faceIndex j)}
    {g₁ g₂ : Fintype (W1SymbolicPublicMatrices.publicIndex j)}
    {e₁ e₂ : DecidableEq (W1SymbolicPublicMatrices.publicIndex j)}
    {m n : Matrix (W1SymbolicPublicMatrices.faceIndex j) (W1SymbolicPublicMatrices.publicIndex j) (ZMod 3)}
    {A B : FiniteElimination.Enumeration (W1SymbolicPublicMatrices.faceIndex j)}
    {C D : FiniteElimination.Enumeration (W1SymbolicPublicMatrices.publicIndex j)}
    (hm : m = n) (hA : A = B) (hC : C = D) :
    HEq (rowsFor j f₁ d₁ g₁ e₁ m A C) (rowsFor j f₂ d₂ g₂ e₂ n B D) := by
  cases Subsingleton.elim f₁ f₂
  cases Subsingleton.elim d₁ d₂
  cases Subsingleton.elim g₁ g₂
  cases Subsingleton.elim e₁ e₂
  subst n
  subst B
  subst D
  rfl

/-- The independent original public rows are reused across all x,y, retaining every row and full original basis value. -/
theorem generated_rows_same (x y : ZMod 3) (j : Bool) :
    HEq (FiniteNative.generatedPublicRows (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))) (bases true x y) (regions j) fixedRegion (priv j)
      (original_linear true x y) enumK enumEdges enumFaces)
      (FiniteNative.generatedPublicRows (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true 0 0))) (bases true 0 0) (regions j) fixedRegion (priv j)
        (original_linear true 0 0) enumK enumEdges enumFaces) := by
  unfold FiniteNative.generatedPublicRows
  apply rows_congr j
  · exact projected_matrix_same x y j
  · exact W1SymbolicLocalStructure.faces_same x y j
  · exact public_enumeration_same x y j

end AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SymbolicGeneratedRows
