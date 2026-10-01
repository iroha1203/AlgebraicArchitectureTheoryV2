import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverRestoration
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification

/-!
# The same global cokernel condition and independently generated finite public relations

The bridge passes through the original actual repair equivalence and retains
all local kernel freedom. Full native vertex labels are those of the accepted
GeneratedCoverRestoration equivalence; no label-effect quotient is introduced.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace OriginalPublicRanges
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (T : OriginalTowerPresentation K p q)
local notation "M" => T.toTower.localCoefficients
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (bases : FiniteFamily.Bases (k := k) (T.toTower.localCoefficients).A)
variable (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "δ" => ActualEquation.defectFamily T P hfixed
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (S : Set candidates)
local notation "allowed" => OriginalRanges.allowed candidates S
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed

include enumI hc in
/-- Every independent finite public relation exists exactly at the same original global range condition. -/
theorem public_nonempty_iff_range :
    Nonempty (GeneratedPublicRelations.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed) ↔
      LinearInterface.q (OriginalColumns.D (k := k) M P candidates hlinear) (-δ) ∈
        NamedDual.ranges (OriginalRanges.column (k := k) M P candidates houtside hlinear) S :=
  (GeneratedCoverRestoration.repair_nonempty_iff_public T bases P U candidates hlinear hfixed
    enumK enumEdges enumFaces enumI hc allowed).symm.trans
      (OriginalRangeClassification.repair_nonempty_iff_range (k := k) T P candidates houtside hlinear hfixed S)

/-- All original actual repairs are all feasible public families times every full local internal kernel. -/
noncomputable def publicKernelEquiv : SupportedRepair T fixed ≃
    (GeneratedPublicRelations.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed ×
      (∀ i, LinearMap.ker (FiniteNative.D M bases (U i) P
        (ClosedRegion.privateAlwaysEdges U P candidates i) hlinear))) :=
  (GeneratedCoverRestoration.objectEquiv T bases P U candidates hlinear hfixed
    enumK enumEdges enumFaces enumI hc allowed).trans
      (GeneratedPublicRelations.publicKernelEquiv M bases P U candidates hlinear δ
        enumK enumEdges enumFaces allowed)

/-- Every public value and every private freedom restore the same actual original edge correction. -/
theorem restore_edge_value
    (z : GeneratedPublicRelations.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed)
    (n : ∀ i, LinearMap.ker (FiniteNative.D M bases (U i) P
      (ClosedRegion.privateAlwaysEdges U P candidates i) hlinear)) (i : I) (e : (U i).edges) :
    T.solutionCorrection ((publicKernelEquiv T bases P U candidates hlinear hfixed
      enumK enumEdges enumFaces enumI hc S).symm (z,n)).1 e.1 =
        ((GeneratedStrictCover.restore M bases P U candidates hlinear δ enumK enumEdges enumFaces allowed
          (GeneratedPublicRelations.assemble M bases P U candidates hlinear δ
            enumK enumEdges enumFaces allowed z n)).1 i).1.1.1 e :=
  GeneratedCoverRestoration.inverse_edge_value T bases P U candidates hlinear hfixed
    enumK enumEdges enumFaces enumI hc allowed
      (GeneratedPublicRelations.assemble M bases P U candidates hlinear δ
        enumK enumEdges enumFaces allowed z n) i e

end OriginalPublicRanges
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
