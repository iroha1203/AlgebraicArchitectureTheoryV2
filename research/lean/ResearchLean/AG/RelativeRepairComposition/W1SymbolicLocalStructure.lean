import ResearchLean.AG.RelativeRepairComposition.W1GeneratedRelations

/-!
# The same private W1 elimination and section across all symbolic x,y inputs

All original coordinate names and dimensions are structural input data. The
actual private D matrices are zero on the same full coordinate spaces for every
x,y. Their generated eliminations and sections therefore coincide with the
single (0,0) generation; only the actual signed reference rhs is updated.

## Implementation notes

The explicit coordinate types retain each original cell and its entire Fin 1
basis. The matrices and enumerations are still the actual native generator's
inputs. Explicit finite/equality instances let congruence compare those inputs
using instance uniqueness, without reducing the finite search merely to compare
instance presentations. Comparing an image or a selected private value would
omit data required for symbolic reuse.
-/
namespace AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalInterfaces W1PrivateMatrixZero
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

/-- Every original complete coordinate index uses the same structural dimension, independently of actual reference values. -/
theorem basis_dimension_same (x y : ZMod 3) (v : geometry.Vertex) :
    (bases true x y).dimension v = (bases true 0 0).dimension v := rfl

/-- Every retained original face keeps its complete one-dimensional basis index. -/
abbrev faceIndex (j : Bool) := Σ _f : {f : Bool // f ∈ (regions j).faces ∧ f ∉ fixedRegion.faces}, Fin 1

/-- Every retained original edge keeps its complete one-dimensional basis index. -/
abbrev edgeIndex (j : Bool) := Σ _e : {e : EdgeName (K := geometry) // e ∈ (regions j).edges ∧ e ∉ fixedRegion.edges}, Fin 1

/-- Private coordinates retain exactly their original nonshared always-edge names. -/
abbrev privateIndex (j : Bool) := {e : edgeIndex j // e.1.1 ∈ ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j}

/-- Public coordinates retain the entire complementary family of original edge names. -/
abbrev publicIndex (j : Bool) := {e : edgeIndex j // e.1.1 ∉ ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j}

/-- Read the actual full private matrix on the same explicit original names and full basis indices. -/
noncomputable def structuralPrivateMatrix (x y : ZMod 3) (j : Bool) :
    Matrix (faceIndex j) (privateIndex j) (ZMod 3) := privateMatrix x y j

/-- Every entry of the actual full original private matrix vanishes. -/
theorem structural_private_matrix_zero (x y : ZMod 3) (j : Bool) :
    structuralPrivateMatrix x y j = 0 := private_matrix_zero x y j

/-- The whole actual original private matrix is the same on its original complete coordinates at every input value. -/
theorem private_matrix_same (x y : ZMod 3) (j : Bool) :
    structuralPrivateMatrix x y j = structuralPrivateMatrix 0 0 j :=
  (structural_private_matrix_zero x y j).trans (structural_private_matrix_zero 0 0 j).symm

local notation "M" x y => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "priv" j => ClosedRegion.privateAlwaysEdges regions fixedRegion candidates j

/-- The actual complete original face enumeration on its structural coordinate type. -/
noncomputable def actualFaces (x y : ZMod 3) (j : Bool) : FiniteElimination.Enumeration (faceIndex j) :=
  FiniteNative.enum2 (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))) (bases true x y) (regions j) fixedRegion enumFaces

/-- The actual complete original edge enumeration on its structural coordinate type. -/
noncomputable def actualEdges (x y : ZMod 3) (j : Bool) : FiniteElimination.Enumeration (edgeIndex j) :=
  FiniteNative.enum1 (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))) (bases true x y) (regions j) fixedRegion enumEdges

/-- The actual complete private enumeration on its original structural coordinate type. -/
noncomputable def actualPrivate (x y : ZMod 3) (j : Bool) : FiniteElimination.Enumeration (privateIndex j) :=
  FiniteNative.enumX (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))) (bases true x y) (regions j) fixedRegion (priv j) enumEdges

/-- All actual face lists retain exactly the same original cells and full basis indices. -/
theorem faces_same (x y : ZMod 3) (j : Bool) : actualFaces x y j = actualFaces 0 0 j := by
  unfold actualFaces FiniteNative.enum2 FiniteFamily.indexEnumeration
  simp only [FiniteFamily.Bases.comap, bases]

/-- All actual edge lists retain exactly the same original cells and full basis indices. -/
theorem edges_same (x y : ZMod 3) (j : Bool) : actualEdges x y j = actualEdges 0 0 j := by
  unfold actualEdges FiniteNative.enum1 FiniteFamily.indexEnumeration
  simp only [FiniteFamily.Bases.comap, bases]

/-- Subset enumeration depends on its actual list and predicate; predicate decisions are unique. -/
theorem enumeration_subtype_congr (j : Bool) (p : edgeIndex j → Prop)
    {E F : FiniteElimination.Enumeration (edgeIndex j)} {d₁ d₂ : DecidablePred p} (h : E = F) :
    @FiniteElimination.Enumeration.subtype _ E p d₁ =
      @FiniteElimination.Enumeration.subtype _ F p d₂ := by
  cases Subsingleton.elim d₁ d₂
  subst F
  rfl

/-- The complete actual private lists agree before any input value or permission changes. -/
theorem private_same (x y : ZMod 3) (j : Bool) : actualPrivate x y j = actualPrivate 0 0 j := by
  unfold actualPrivate FiniteNative.enumX
  apply enumeration_subtype_congr j (fun e => e.1.1 ∈ priv j)
  exact edges_same x y j

/-- Fixed original complete face enumeration for the common generation. -/
noncomputable def structuralFaces (j : Bool) : FiniteElimination.Enumeration (faceIndex j) := actualFaces 0 0 j

/-- Fixed original complete edge enumeration for the common generation. -/
noncomputable def structuralEdges (j : Bool) : FiniteElimination.Enumeration (edgeIndex j) := actualEdges 0 0 j

/-- Combine the same complete actual private and face lists before generation. -/
noncomputable def actualEnum (x y : ZMod 3) (j : Bool) :
    FiniteElimination.Enumeration (faceIndex j ⊕ privateIndex j) :=
  FiniteElimination.sumEnumeration (actualPrivate x y j) (actualFaces x y j)

/-- The entire actual elimination enumeration is unchanged across the symbolic input family. -/
theorem enumeration_same (x y : ZMod 3) (j : Bool) : actualEnum x y j = actualEnum 0 0 j := by
  unfold actualEnum
  rw [private_same x y j, faces_same x y j]

/-- Finite reduction respects its full input data and the unique finite/equality instances. -/
theorem reduction_congr (j : Bool)
    {f₁ f₂ : Fintype (faceIndex j ⊕ privateIndex j)}
    {d₁ d₂ : DecidableEq (faceIndex j ⊕ privateIndex j)}
    {E F : FiniteElimination.Enumeration (faceIndex j ⊕ privateIndex j)}
    {m n : Matrix (faceIndex j) (privateIndex j) (ZMod 3)} (hE : E = F) (hm : m = n) :
    HEq (@FiniteElimination.reduce (ZMod 3) _ _ _ (faceIndex j ⊕ privateIndex j) f₁ d₁
      enumK E (FiniteElimination.squareExtension m))
      (@FiniteElimination.reduce (ZMod 3) _ _ _ (faceIndex j ⊕ privateIndex j) f₂ d₂
        enumK F (FiniteElimination.squareExtension n)) := by
  cases Subsingleton.elim f₁ f₂
  cases Subsingleton.elim d₁ d₂
  subst F
  subst n
  rfl

/-- The complete actual elimination is reused at every symbolic input on its original full names and lists. -/
theorem elimination_same (x y : ZMod 3) (j : Bool) :
    HEq (elimination x y j) (elimination 0 0 j) := by
  unfold elimination FiniteNative.generatedElimination
  apply reduction_congr j
  · exact enumeration_same x y j
  · exact private_matrix_same x y j

/-- Read the actual generated section on every original structural coordinate. -/
noncomputable def structuralSection (x y : ZMod 3) (j : Bool) :
    (faceIndex j → ZMod 3) →ₗ[ZMod 3] (privateIndex j → ZMod 3) := generatedSection x y j

/-- The unchanged finite section generator with all its finite/equality instances explicit. -/
noncomputable def sectionFor (j : Bool)
    (f : Fintype (faceIndex j)) (d : DecidableEq (faceIndex j))
    (g : Fintype (privateIndex j)) (e : DecidableEq (privateIndex j))
    (E : FiniteElimination.Enumeration (faceIndex j ⊕ privateIndex j))
    (m : Matrix (faceIndex j) (privateIndex j) (ZMod 3)) :
    (faceIndex j → ZMod 3) →ₗ[ZMod 3] (privateIndex j → ZMod 3) := by
  letI : Fintype (faceIndex j) := f
  letI : DecidableEq (faceIndex j) := d
  letI : Fintype (privateIndex j) := g
  letI : DecidableEq (privateIndex j) := e
  letI : Fintype (faceIndex j ⊕ privateIndex j) := @instFintypeSum _ _ f g
  letI : DecidableEq (faceIndex j ⊕ privateIndex j) := @instDecidableEqSum _ _ d e
  let R := FiniteElimination.reduce enumK E (FiniteElimination.squareExtension m)
  exact Matrix.toLin' (Matrix.toBlocks₂₁
    (R.column * Matrix.diagonal (fun i => (R.value i)⁻¹) * R.row))

/-- Equal original lists and matrices yield the same whole section, independently of instance presentation. -/
theorem section_congr (j : Bool)
    {f₁ f₂ : Fintype (faceIndex j)} {d₁ d₂ : DecidableEq (faceIndex j)}
    {g₁ g₂ : Fintype (privateIndex j)} {e₁ e₂ : DecidableEq (privateIndex j)}
    {E F : FiniteElimination.Enumeration (faceIndex j ⊕ privateIndex j)}
    {m n : Matrix (faceIndex j) (privateIndex j) (ZMod 3)} (hE : E = F) (hm : m = n) :
    sectionFor j f₁ d₁ g₁ e₁ E m = sectionFor j f₂ d₂ g₂ e₂ F n := by
  cases Subsingleton.elim f₁ f₂
  cases Subsingleton.elim d₁ d₂
  cases Subsingleton.elim g₁ g₂
  cases Subsingleton.elim e₁ e₂
  subst F
  subst n
  rfl

/-- The actual full generated section is reused across every input value before S is chosen. -/
theorem section_same (x y : ZMod 3) (j : Bool) :
    structuralSection x y j = structuralSection 0 0 j := by
  unfold structuralSection generatedSection FiniteNative.generatedSection
  apply section_congr j
  · exact enumeration_same x y j
  · exact private_matrix_same x y j

end AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SymbolicLocalStructure
