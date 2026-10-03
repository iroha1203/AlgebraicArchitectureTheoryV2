import ResearchLean.AG.RelativeRepairComposition.W2ActualRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials
import ResearchLean.AG.RelativeRepairComposition.GeneratedNativeRelation

/-!
# W2's full actual finite coefficients and complete input lists

Every original vertex uses its entire affine projection kernel, identified
with F3. The complete original cell and field lists precede every local
generation and permission choice. The actual face defect has its original
empty face domain.
-/
namespace AAT.AG.RelativeRepairComposition.W2FiniteCoefficients
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs
local notation "T" => originalTower
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)

/-- Every original vertex's full categorical kernel has the entire F3 coordinate space. -/
noncomputable def kernelCoordinate (v : geometry.Vertex) : (M).A v ≃ₗ[ZMod 3] ZMod 3 :=
  NativeAffine.linearCoefficient geometry reference reference comparison linear_faces v

/-- The complete full-kernel basis at every original vertex has its one original coordinate. -/
noncomputable def bases : FiniteFamily.Bases (k := ZMod 3) (M).A where
  dimension _ := 1
  coordinate v := (kernelCoordinate v).trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 3) (ZMod 3)).symm

/-- The sole complete basis index at each original vertex. -/
def basisIndex (v : geometry.Vertex) : Fin (bases.dimension v) := ⟨0, by change 0 < 1; decide⟩

/-- The full basis reads the same entire actual kernel coordinate. -/
theorem basis_value (v : geometry.Vertex) (a : (M).A v) :
    bases.coordinate v a (basisIndex v) = kernelCoordinate v a := rfl

/-- The whole inverse kernel coordinate is the same original actual affine translation. -/
theorem kernel_inverse_value (v : geometry.Vertex) (a : ZMod 3) :
    FiberAut.hom (kernelInclusion
      (GroupExtension.projection (projection (k := ZMod 3) (A := ZMod 3)))
      (GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)) ((T).original.object v)
      (Additive.toMul ((kernelCoordinate v).symm a))) = translation (k := ZMod 3) a :=
  NativeAffine.coefficient_inverse_value geometry reference reference comparison linear_faces v a

/-- Every complete original edge transport is linear on the whole original kernel modules. -/
theorem original_linear {i j : geometry.Vertex} (e : geometry.Edge i j) (t : ZMod 3) (a : (M).A i) :
    (M).edge e (t • a) = t • (M).edge e a :=
  NativeAffine.edge_linear geometry reference reference comparison linear_faces e t a

/-- The original fixed face condition follows from the specified empty face type. -/
theorem fixed_faces (f : geometry.TwoCell) (_hf : f ∈ fixedRegion.faces) :
    (T).toTower.upper.pathLift (geometry.twoLeft f) ≫ FiberAut.hom ((T).comparator f) =
      (T).toTower.upper.pathLift (geometry.twoRight f) := f.elim

/-- The actual relative defect is constructed from the same original full affine input. -/
noncomputable def actualDefect := ActualEquation.defectFamily T fixedRegion fixed_faces

/-- The same actual defect is zero on its whole original empty face family. -/
theorem actual_defect_zero : actualDefect = 0 := by
  apply Subtype.ext
  funext f
  exact f.1.elim

/-- The full arithmetic list is fixed before any local generation or permission choice. -/
def enumK : FiniteElimination.Enumeration (ZMod 3) :=
  ⟨[0,1,2], by intro a; fin_cases a <;> simp⟩

/-- Both original typed edge names occur in the complete original list. -/
def enumEdges : FiniteElimination.Enumeration (EdgeName (K := geometry)) :=
  ⟨[name edgeOne,name edgeTwo], by
    rintro ⟨i,j,e,hs,ht⟩
    cases hs
    cases ht
    fin_cases e <;> simp [geometry, name, edgeOne, edgeTwo, edgeSource, edgeTarget]⟩

/-- The original empty face list is complete for the specified original geometry. -/
def enumFaces : FiniteElimination.Enumeration geometry.TwoCell := ⟨[], fun f => f.elim⟩

/-- The complete original Bool patch list is fixed before permissions are imposed. -/
def enumRegions : FiniteElimination.Enumeration Bool :=
  ⟨[false,true], by intro j; cases j <;> simp⟩

end AAT.AG.RelativeRepairComposition.W2FiniteCoefficients
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2FiniteCoefficients
