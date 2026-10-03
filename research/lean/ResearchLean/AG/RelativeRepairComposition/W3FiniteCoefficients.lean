import ResearchLean.AG.RelativeRepairComposition.W3ActualRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials
import ResearchLean.AG.RelativeRepairComposition.GeneratedNativeRelation

/-! # W3's whole actual finite kernels and complete input lists

Both loop transports use the same full categorical kernel A=F3² at every
original vertex. Full two-coordinate bases and the complete input lists are
fixed before any local generation or later permission S.
-/
namespace AAT.AG.RelativeRepairComposition.W3FiniteCoefficients
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
variable (sheared : Bool)
local notation "T" => originalTower sheared
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)

/-- Every original full categorical kernel has the entire specified A coordinate space. -/
noncomputable def kernelCoordinate (v : geometry.Vertex) : (M).A v ≃ₗ[ZMod 3] A :=
  NativeAffine.linearCoefficient geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) v

/-- The complete basis at each original vertex has both actual F3 coordinates. -/
noncomputable def bases : FiniteFamily.Bases (k := ZMod 3) (M).A where
  dimension _ := 2
  coordinate := kernelCoordinate sheared

/-- Every original coordinate is a basis index, without selecting a proper subspace. -/
def basisIndex (v : geometry.Vertex) (i : Fin 2) : Fin ((bases sheared).dimension v) := i

/-- The complete basis reads each actual full-kernel coordinate. -/
theorem basis_value (v : geometry.Vertex) (a : (M).A v) (i : Fin 2) :
    (bases sheared).coordinate v a (basisIndex sheared v i) = kernelCoordinate sheared v a i := rfl

/-- Inverting the full kernel coordinates restores the original actual vector translation. -/
theorem kernel_inverse_value (v : geometry.Vertex) (a : A) :
    FiberAut.hom (kernelInclusion
      (GroupExtension.projection (projection (k := ZMod 3) (A := A)))
      (GroupExtension.terminal (A ≃ₗ[ZMod 3] A)) ((T).original.object v)
      (Additive.toMul ((kernelCoordinate sheared v).symm a))) = translation (k := ZMod 3) a :=
  NativeAffine.coefficient_inverse_value geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) v a

/-- Every original transport is linear on the entire original kernel vector space. -/
theorem original_linear {i j : geometry.Vertex} (e : geometry.Edge i j) (t : ZMod 3) (a : (M).A i) :
    (M).edge e (t • a) = t • (M).edge e a :=
  NativeAffine.edge_linear geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) e t a

/-- The specified empty face family discharges the original physical fixed-face condition. -/
theorem fixed_faces (f : geometry.TwoCell) (_hf : f ∈ fixedRegion.faces) :
    (T).toTower.upper.pathLift (geometry.twoLeft f) ≫ FiberAut.hom ((T).comparator f) =
      (T).toTower.upper.pathLift (geometry.twoRight f) := f.elim

/-- The actual full relative face defect is generated from the same original affine input. -/
noncomputable def actualDefect := ActualEquation.defectFamily T fixedRegion (fixed_faces sheared)

/-- The defect is zero on its complete original empty face domain. -/
theorem actual_defect_zero : actualDefect sheared = 0 := by
  apply Subtype.ext
  funext f
  exact f.1.elim

/-- The complete original field list precedes every local generation and permission choice. -/
def enumK : FiniteElimination.Enumeration (ZMod 3) :=
  ⟨[0,1,2], by intro a; fin_cases a <;> simp⟩

/-- Both complete original typed edge names occur in the input list. -/
def enumEdges : FiniteElimination.Enumeration (EdgeName (K := geometry)) :=
  ⟨[name edgeE,name edgeF], by
    rintro ⟨i,j,e,hs,ht⟩
    cases hs
    cases ht
    fin_cases e <;> simp [geometry, name, edgeE, edgeF, edgeSource, edgeTarget]⟩

/-- The complete specified original face list is empty. -/
def enumFaces : FiniteElimination.Enumeration geometry.TwoCell := ⟨[], fun f => f.elim⟩

/-- The complete original finite patch list precedes all permissions. -/
def enumRegions : FiniteElimination.Enumeration Bool :=
  ⟨[false,true], by intro j; cases j <;> simp⟩

end AAT.AG.RelativeRepairComposition.W3FiniteCoefficients
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3FiniteCoefficients
