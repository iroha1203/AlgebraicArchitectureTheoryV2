import ResearchLean.AG.RelativeRepairComposition.SubdivisionCandidateColumns
import ResearchLean.AG.RelativeRepairComposition.NamedColumnEquivalence

/-!
# All original quotient duals and all candidate ranges under actual subdivision

Every original whole kernel column and the actual signed obstruction are used.
The entire quotient dual, its full obstruction support family and every named
range are compared using the same previously constructed actual linear maps.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.DualSupports
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)
attribute [local instance] LinearCoefficients.coefficientModules
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)
local notation "M" => T.toTower.localCoefficients
local notation "newP" => oldRegion K chosen P hp
local notation "newCandidates" => oldEdgeSet K chosen candidates
local notation "newLinear" => LinearCoefficients.edge_linear T chosen F hlinear

attribute [local instance] Classical.propDecidable
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
/-- The independent full new candidate image equals the corresponding full original image for every S. -/
theorem range_map (S : Set candidates) :
    (NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) ((CandidateColumns.nameEquiv candidates chosen hc) '' S)).map (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear).toLinearMap = NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) S :=
  NamedColumnEquivalence.range_map (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (CandidateColumns.nameEquiv candidates chosen hc) (CandidateColumns.kernelEquiv (k := k) T candidates chosen F hc) (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (CandidateColumns.quotient_column T P candidates chosen F hp hc hlinear houtside) S

/-- Full quotient range membership is reflected for every independent quotient element and every S. -/
theorem mem_range_iff (S : Set candidates) (o : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)))) :
    o ∈ NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔ (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) o ∈ NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) S :=
  NamedColumnEquivalence.mem_range_iff (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (CandidateColumns.nameEquiv candidates chosen hc) (CandidateColumns.kernelEquiv (k := k) T candidates chosen F hc) (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (CandidateColumns.quotient_column T P candidates chosen F hp hc hlinear houtside) S o

/-- Compare the entire field duals of the independently generated actual always quotients. -/
noncomputable def dualEquiv : Module.Dual k (RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P ⧸ LinearMap.range (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear)) ≃ₗ[k] Module.Dual k (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear))) :=
  (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear).dualMap

/-- Every actual quotient dual value is retained by the same full quotient comparison. -/
theorem dualEquiv_value (phi : Module.Dual k (RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P ⧸ LinearMap.range (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear))) (o : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)))) :
    dualEquiv T P candidates chosen F hp hc hlinear phi o = phi ((RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) o) := rfl

/-- Every full nonzero-column support is exactly the image of its original complete names. -/
theorem support_eq (phi : Module.Dual k (RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P ⧸ LinearMap.range (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear))) :
    NamedDual.support (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (dualEquiv T P candidates chosen F hp hc hlinear phi) =
      (CandidateColumns.nameEquiv candidates chosen hc) '' NamedDual.support (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) phi :=
  NamedColumnEquivalence.support_eq (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (CandidateColumns.nameEquiv candidates chosen hc) (CandidateColumns.kernelEquiv (k := k) T candidates chosen F hc) (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (CandidateColumns.quotient_column T P candidates chosen F hp hc hlinear houtside) phi

/-- The entire nonzero-obstruction support family is preserved, without selecting a dual basis. -/
theorem obstruction_support_family (o : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)))) :
    {U : Set (oldEdgeSet K chosen candidates) | ∃ psi : Module.Dual k (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear))), psi o ≠ 0 ∧ U = NamedDual.support (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) psi} =
      {U : Set (oldEdgeSet K chosen candidates) | ∃ phi : Module.Dual k (RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P ⧸ LinearMap.range (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear)), phi ((RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) o) ≠ 0 ∧
        U = (CandidateColumns.nameEquiv candidates chosen hc) '' NamedDual.support (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) phi} :=
  NamedColumnEquivalence.obstruction_support_family (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (CandidateColumns.nameEquiv candidates chosen hc) (CandidateColumns.kernelEquiv (k := k) T candidates chosen F hc) (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (CandidateColumns.quotient_column T P candidates chosen F hp hc hlinear houtside) o

/-- Every permission range hits all full obstruction supports exactly when its original range does. -/
theorem hits_iff (o : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)))) (S : Set candidates) :
    NamedDual.Hits (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) o ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔ NamedDual.Hits (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) ((RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) o) S :=
  NamedColumnEquivalence.hits_iff (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (CandidateColumns.nameEquiv candidates chosen hc) (CandidateColumns.kernelEquiv (k := k) T candidates chosen F hc) (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (CandidateColumns.quotient_column T P candidates chosen F hp hc hlinear houtside) o S

/-- Inclusion-minimal full quotient ranges correspond at every complete candidate subset. -/
theorem minimal_range_iff (o : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)))) (S : Set candidates) :
    Minimal (fun V => o ∈ NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) V) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔
      Minimal (fun V => (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) o ∈ NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) V) S :=
  NamedColumnEquivalence.minimal_range_iff (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (CandidateColumns.nameEquiv candidates chosen hc) (CandidateColumns.kernelEquiv (k := k) T candidates chosen F hc) (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (CandidateColumns.quotient_column T P candidates chosen F hp hc hlinear houtside) o S

/-- All minimal transversals of the entire actual quotient dual family correspond. -/
theorem minimal_hits_iff (o : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)))) (S : Set candidates) :
    Minimal (NamedDual.Hits (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) o) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔
      Minimal (NamedDual.Hits (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) ((RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) o)) S :=
  NamedColumnEquivalence.minimal_hits_iff (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (CandidateColumns.nameEquiv candidates chosen hc) (CandidateColumns.kernelEquiv (k := k) T candidates chosen F hc) (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (CandidateColumns.quotient_column T P candidates chosen F hp hc hlinear houtside) o S

end AAT.AG.RelativeRepairComposition.Subdivision.DualSupports
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.DualSupports
