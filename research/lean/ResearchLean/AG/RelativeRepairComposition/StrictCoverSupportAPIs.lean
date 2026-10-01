import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.NativeLocalInterface

/-!
# Evaluation APIs used by strict supported interfaces

## Implementation notes

These laws expose zero restriction and the public component of the existing
full generated inverse, without changing its objects or coordinate values.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA
namespace CoverEquation
variable {K : FiniteTransportPresentation.{uG}}
/-- The original defect restriction sends zero to zero on every closed region. -/
theorem defect_zero (M : LocalCoefficients.{uG,uA} K) (P U : ClosedRegion K) :
    defect M P 0 U = 0 := map_zero (RelativeCover.r2 M P (ClosedRegion.to_all U))
end CoverEquation
namespace ClosedRegion
/-- The original restricted vertex differential reads its original endpoints. -/
theorem d0Hom_edge_value {K : FiniteTransportPresentation.{uG}}
    (M : LocalCoefficients.{uG,uA} K) (U : ClosedRegion K)
    (b : C0 M U) (e : U.edges) :
    d0Hom M U b e = b ⟨e.1.2.1,(U.edge_closed e.1 e.2).2⟩ -
      M.edge e.1.2.2 (b ⟨e.1.1,(U.edge_closed e.1 e.2).1⟩) := by
  change Family.extend M.A U.vertices b e.1.2.1 -
    M.edge e.1.2.2 (Family.extend M.A U.vertices b e.1.1) = _
  rw [Family.extend_on M.A U.vertices b _ (U.edge_closed e.1 e.2).2,
    Family.extend_on M.A U.vertices b _ (U.edge_closed e.1 e.2).1]
end ClosedRegion
namespace RelativeCover
/-- The relative vertex differential reads the same original endpoints. -/
theorem d0_edge_value {K : FiniteTransportPresentation.{uG}}
    (M : LocalCoefficients.{uG,uA} K) (P U : ClosedRegion K)
    (b : C0 M U P) (e : U.edges) :
    (d0 M U P b).1 e = b.1 ⟨e.1.2.1,(U.edge_closed e.1 e.2).2⟩ -
      M.edge e.1.2.2 (b.1 ⟨e.1.1,(U.edge_closed e.1 e.2).1⟩) := by
  rw [d0_val]
  exact ClosedRegion.d0Hom_edge_value M U b.1 e
end RelativeCover
namespace FiniteNative
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)] [DecidablePred (· ∈ U.faces)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
/-- The full generated inverse restores exactly the input public component. -/
theorem generated_solution_inverse_public
    (y : GeneratedObjects M B U P internalEdges hlinear δ enumK enumEdges enumFaces) :
    (edgeSplit M B U P internalEdges
      ((generatedSolutionEquiv M B U P internalEdges hlinear δ enumK enumEdges enumFaces).symm y).1).2 = y.1.1 := by
  change (edgeSplit M B U P internalEdges
    ((edgeSplit M B U P internalEdges).symm _)).2 = y.1.1
  rw [LinearEquiv.apply_symm_apply]
  rfl
end FiniteNative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
