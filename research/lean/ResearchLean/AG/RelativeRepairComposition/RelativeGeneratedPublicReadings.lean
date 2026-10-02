import ResearchLean.AG.RelativeRepairComposition.FiniteNativeArbitraryEquation

/-!
# Public-only readings of all independently generated arbitrary equations

## Implementation notes

The public value is read from a zero-private coordinate without imposing zero
on any generated object's private kernel. Every restored nonprivate edge,
including prescribed fixed edges, has that same value for every kernel choice.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ U.edges)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]

/-- All physical public values depend only on the complete public coordinate. -/
def publicValue (z : FiniteNative.ZIndex M bases U P internalEdges → k) (e : U.edges) : M.A e.1.2.1 :=
  ((FiniteNative.edgeSplit M bases U P internalEdges).symm (0,z)).1 e

variable [Fintype k] [DecidableEq k]
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.faces)]
variable [DecidablePred (· ∈ P.faces)]
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k) (x : M.A s),
  M.edge e (a • x) = a • M.edge e x)
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)

/-- Arbitrary generated restoration keeps the complete independent public coordinate. -/
theorem restored_public (value : RelativeCover.C2 M U P)
    (y : FiniteNative.GeneratedRelativeObjects M bases U P internalEdges hlinear value ek ee ef) :
    (FiniteNative.edgeSplit M bases U P internalEdges
      ((FiniteNative.generatedRelativeEquiv M bases U P internalEdges hlinear value ek ee ef).symm y).1).2 = y.1.1 :=
  FiniteNative.generatedRelativeEquiv_inverse_public M bases U P internalEdges hlinear value ek ee ef y

/-- Every full restored public value is independent of all private kernel choices. -/
theorem restored_value_public (value : RelativeCover.C2 M U P)
    (y : FiniteNative.GeneratedRelativeObjects M bases U P internalEdges hlinear value ek ee ef)
    (e : U.edges) (he : e.1 ∉ internalEdges) :
    ((FiniteNative.generatedRelativeEquiv M bases U P internalEdges hlinear value ek ee ef).symm y).1.1 e =
      publicValue M bases U P internalEdges y.1.1 e := by
  let h := ((FiniteNative.generatedRelativeEquiv M bases U P internalEdges hlinear value ek ee ef).symm y).1
  have hz := restored_public M bases U P internalEdges hlinear ek ee ef value y
  have hh : h = (FiniteNative.edgeSplit M bases U P internalEdges).symm
      ((FiniteNative.edgeSplit M bases U P internalEdges h).1,y.1.1) := by
    rw [← hz]
    exact (LinearEquiv.symm_apply_apply _ h).symm
  change h.1 e = _
  rw [hh]
  by_cases hp : e.1 ∈ P.edges
  · exact (((FiniteNative.edgeSplit M bases U P internalEdges).symm _).2 e hp).trans
      (((FiniteNative.edgeSplit M bases U P internalEdges).symm (0,y.1.1)).2 e hp).symm
  · exact FiniteNative.public_edge_private_independent M bases U P internalEdges _ 0 y.1.1 e hp he

end AAT.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeGeneratedPublicReadings
