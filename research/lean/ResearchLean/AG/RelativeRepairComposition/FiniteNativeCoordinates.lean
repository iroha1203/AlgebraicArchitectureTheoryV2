import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteCoefficientDifferentials
import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinatePartition
import ResearchLean.AG.RelativeRepairComposition.FiniteElimination
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Full original-coordinate matrices of the local relative complex

## Implementation notes

All cell bases come from the same original vertex kernels. Matrix columns are
computed by evaluating the original differential on those basis vectors. The
internalEdges/public split retains each original edge name, with all shared and
candidate coordinates on the public side.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace FiniteNative
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)]
variable [DecidablePred (· ∈ P.faces)]

/-- Every vertex uses its complete original input basis. -/
abbrev Index0 := FiniteFamily.Index M.A B U.vertices P.vertices
/-- Every original edge uses the complete basis at its original target. -/
abbrev Index1 := FiniteFamily.Index (fun e : EdgeName (K := K) => M.A e.2.1)
  (B.comap M.A (fun e : EdgeName (K := K) => e.2.1)) U.edges P.edges
/-- Every original face uses the complete basis at its authored target. -/
abbrev Index2 := FiniteFamily.Index (fun f => M.A (K.twoTarget f))
  (B.comap M.A K.twoTarget) U.faces P.faces
/-- Every original triple uses the complete basis at its authored target. -/
abbrev Index3 := FiniteFamily.Index (fun t => M.A (K.threeTarget t))
  (B.comap M.A K.threeTarget) U.triples P.triples

/-- Full linear coordinates of the original relative vertices. -/
def coordinate0 : RelativeCover.C0 M U P ≃ₗ[k] (Index0 M B U P → k) :=
  FiniteFamily.equivalence M.A B U.vertices P.vertices
/-- Full linear coordinates of the original relative edges. -/
def coordinate1 : RelativeCover.C1 M U P ≃ₗ[k] (Index1 M B U P → k) :=
  FiniteFamily.equivalence (fun e : EdgeName (K := K) => M.A e.2.1)
    (B.comap M.A (fun e : EdgeName (K := K) => e.2.1)) U.edges P.edges
/-- Full linear coordinates of the original relative faces. -/
def coordinate2 : RelativeCover.C2 M U P ≃ₗ[k] (Index2 M B U P → k) :=
  FiniteFamily.equivalence (fun f => M.A (K.twoTarget f)) (B.comap M.A K.twoTarget) U.faces P.faces

/-- Full linear coordinates retain every original triple and its complete target kernel. -/
def coordinate3 [DecidablePred (· ∈ P.triples)] :
    RelativeCover.C3 M U P ≃ₗ[k] (Index3 M B U P → k) :=
  FiniteFamily.equivalence (fun t => M.A (K.threeTarget t)) (B.comap M.A K.threeTarget) U.triples P.triples

variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]

/-- Private coordinate membership refers to its same original nonfixed edge. -/
def privateIndex : Set (Index1 M B U P) := {j | j.1.1 ∈ internalEdges}

/-- Private coordinate membership is decided by its same original edge membership. -/
instance privateIndexDecidable : DecidablePred (· ∈ privateIndex M B U P internalEdges) :=
  fun j => show Decidable (j.1.1 ∈ internalEdges) from inferInstance

/-- All private coordinates keep their original edge and complete basis index. -/
abbrev XIndex := ↥(privateIndex M B U P internalEdges)
/-- The public complement keeps all other original coordinates. -/
abbrev ZIndex := ↥((privateIndex M B U P internalEdges)ᶜ)

/-- The full edge coordinate map splits into exact private and public families. -/
def edgeSplit : RelativeCover.C1 M U P ≃ₗ[k]
    ((XIndex M B U P internalEdges → k) × (ZIndex M B U P internalEdges → k)) :=
  (coordinate1 M B U P).trans (FinitePartition.equivalence (privateIndex M B U P internalEdges))

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)] in
/-- A retained original edge value depends only on public coordinates, with its full kernel basis. -/
theorem public_edge_value (x : XIndex M B U P internalEdges → k)
    (z : ZIndex M B U P internalEdges → k) (e : U.edges)
    (hp : e.1 ∉ P.edges) (hi : e.1 ∉ internalEdges) :
    ((edgeSplit M B U P internalEdges).symm (x,z)).1 e =
      (B.coordinate e.1.2.1).symm
        (fun j => z ⟨⟨⟨e.1,e.2,hp⟩,j⟩,hi⟩) := by
  rw [edgeSplit,LinearEquiv.trans_symm,LinearEquiv.trans_apply]
  rw [coordinate1,FiniteFamily.restore_value _ _ _ _ _ e hp]
  congr 1
  funext j
  exact FinitePartition.join_public (privateIndex M B U P internalEdges) (x,z)
    ⟨⟨⟨e.1,e.2,hp⟩,j⟩,hi⟩

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)] in
/-- Every public original edge value is independent of every internal kernel choice. -/
theorem public_edge_private_independent (x x' : XIndex M B U P internalEdges → k)
    (z : ZIndex M B U P internalEdges → k) (e : U.edges)
    (hp : e.1 ∉ P.edges) (hi : e.1 ∉ internalEdges) :
    ((edgeSplit M B U P internalEdges).symm (x,z)).1 e =
      ((edgeSplit M B U P internalEdges).symm (x',z)).1 e := by
  rw [public_edge_value M B U P internalEdges x z e hp hi,
    public_edge_value M B U P internalEdges x' z e hp hi]

variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)]

/-- The full original face differential in the split edge coordinates. -/
def faceMap :
    ((XIndex M B U P internalEdges → k) × (ZIndex M B U P internalEdges → k)) →ₗ[k] (Index2 M B U P → k) :=
  (coordinate2 M B U P).toLinearMap.comp
    ((differential1 M hlinear U P).comp (edgeSplit M B U P internalEdges).symm.toLinearMap)

/-- Only the selected private columns form the internal differential. -/
def D : (XIndex M B U P internalEdges → k) →ₗ[k] (Index2 M B U P → k) :=
  (faceMap M B U P internalEdges hlinear).comp (LinearMap.inl k _ _)

/-- All other original columns form the public differential. -/
def F : (ZIndex M B U P internalEdges → k) →ₗ[k] (Index2 M B U P → k) :=
  (faceMap M B U P internalEdges hlinear).comp (LinearMap.inr k _ _)

/-- The original vertex differential determines both full label components. -/
def labelMap : RelativeCover.C0 M U P →ₗ[k]
    ((XIndex M B U P internalEdges → k) × (ZIndex M B U P internalEdges → k)) :=
  (edgeSplit M B U P internalEdges).toLinearMap.comp (differential0 M hlinear U P)

/-- The internal label component uses the original full zero-cochain. -/
def a : RelativeCover.C0 M U P →ₗ[k] (XIndex M B U P internalEdges → k) :=
  (LinearMap.fst k _ _).comp (labelMap M B U P internalEdges hlinear)

/-- The public label component uses the same original full zero-cochain. -/
def c : RelativeCover.C0 M U P →ₗ[k] (ZIndex M B U P internalEdges → k) :=
  (LinearMap.snd k _ _).comp (labelMap M B U P internalEdges hlinear)

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- Private and public columns together are the complete original differential. -/
theorem D_add_F (x : XIndex M B U P internalEdges → k) (z : ZIndex M B U P internalEdges → k) :
    D M B U P internalEdges hlinear x + F M B U P internalEdges hlinear z =
      faceMap M B U P internalEdges hlinear (x,z) := by
  change (faceMap M B U P internalEdges hlinear) (x,0) + (faceMap M B U P internalEdges hlinear) (0,z) = _
  rw [← map_add]
  congr 1
  exact Prod.ext (add_zero x) (zero_add z)

omit [DecidablePred (· ∈ P.vertices)] in
/-- The generated label components satisfy the same original differential-square law. -/
theorem D_a_add_F_c (b : RelativeCover.C0 M U P) :
    D M B U P internalEdges hlinear (a M B U P internalEdges hlinear b) +
      F M B U P internalEdges hlinear (c M B U P internalEdges hlinear b) = 0 := by
  rw [D_add_F]
  change coordinate2 M B U P
    (differential1 M hlinear U P ((edgeSplit M B U P internalEdges).symm
      ((edgeSplit M B U P internalEdges) (differential0 M hlinear U P b)))) = 0
  rw [LinearEquiv.symm_apply_apply,differential1_differential0,map_zero]

end FiniteNative
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
