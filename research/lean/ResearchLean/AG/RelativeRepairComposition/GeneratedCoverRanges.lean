import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverRestoration
import ResearchLean.AG.RelativeRepairComposition.GeneratedRangeInclusion
import ResearchLean.AG.RelativeRepairComposition.RangeMaps

/-!
# Full actual coordinate and reconstruction functors commute with every range inclusion

## Implementation notes

The allowed set changes only support proofs. The generated matrices, sections,
public values, private vectors and full vertex labels remain identical.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace GeneratedCoverRanges
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

variable {S V : Set (EdgeName (K := K))}
local notation "actualInc" h => repairInclusion T (fixedEdgesForRange_antitone P.edges candidates h)
local notation "genInc" h => GeneratedRangeInclusion.objectsInclusion M bases P U candidates hlinear δ enumK enumEdges enumFaces h
local notation "coord" S => GeneratedCoverRestoration.objectEquiv T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc S
local notation "eqv" S => GeneratedCoverRestoration.equivalence T bases P U candidates hlinear hfixed enumK enumEdges enumFaces enumI hc S

/-- The same coordinate construction commutes with every inclusion of allowed ranges. -/
theorem coordinate_inclusion (h : S ⊆ V)
    (R : SupportedRepair T (fixedEdgesForRange P.edges candidates S)) :
    (coord V) ((actualInc h) R) = (genInc h) ((coord S) R) := rfl

/-- Reconstruction returns the same full actual repair under every range relaxation. -/
theorem reconstruction_inclusion (h : S ⊆ V)
    (y : GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces S) :
    (coord V).symm ((genInc h) y) = (actualInc h) ((coord S).symm y) := rfl

omit [Fintype I] [DecidableEq I] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Forward label coordinates commute with range relaxation at every original vertex. -/
theorem label_inclusion (h : S ⊆ V)
    (b : supportedC0 T P.vertices (fixedEdgesForRange P.edges candidates S)) :
    GeneratedCoverRestoration.labelEquiv T P U candidates enumI hc V
      (gaugeInclusion T P.vertices (fixedEdgesForRange_antitone P.edges candidates h) b) =
    GeneratedRangeInclusion.labelsInclusion M P U candidates h
      (GeneratedCoverRestoration.labelEquiv T P U candidates enumI hc S b) := rfl

omit [Fintype I] [DecidableEq I] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Inverse full labels commute with range relaxation without replacing labels by effects. -/
theorem label_reconstruction_inclusion (h : S ⊆ V)
    (b : StrictSupportedCover.Labels M P U candidates S) :
    (GeneratedCoverRestoration.labelEquiv T P U candidates enumI hc V).symm
      (GeneratedRangeInclusion.labelsInclusion M P U candidates h b) =
    gaugeInclusion T P.vertices (fixedEdgesForRange_antitone P.edges candidates h)
      ((GeneratedCoverRestoration.labelEquiv T P U candidates enumI hc S).symm b) := rfl

/-- The full coordinate functors commute with the independent original actual inclusion functors. -/
theorem coordinate_functor_inclusion (h : S ⊆ V) :
    ActualRelative.rangeFunctor T P candidates h ⋙ (eqv V).functor =
      (eqv S).functor ⋙ GeneratedRangeInclusion.functor M bases P U candidates hlinear δ enumK enumEdges enumFaces h := rfl

/-- The full reconstruction functors commute with inclusion on every original object and every arrow. -/
theorem reconstruction_functor_inclusion (h : S ⊆ V) :
    GeneratedRangeInclusion.functor M bases P U candidates hlinear δ enumK enumEdges enumFaces h ⋙ (eqv V).inverse =
      (eqv S).inverse ⋙ ActualRelative.rangeFunctor T P candidates h := rfl

end GeneratedCoverRanges
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
