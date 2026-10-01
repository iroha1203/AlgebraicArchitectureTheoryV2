import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses
import ResearchLean.AG.RelativeRepairComposition.GeneratedNativeRelation
import ResearchLean.AG.RelativeRepairComposition.InterfaceQuotient

/-!
# Original local generators with only private always-allowed edges eliminated

## Implementation notes

Each region selects its private columns from the same original cover and named
candidate set. All candidate and shared coordinates remain public. The local
actual-repair equivalence and public restriction use that exact selection.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD uCover
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace FiniteCoverInterfaces
variable (T : OriginalTowerPresentation K p q)
local notation "M" => T.toTower.localCoefficients
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (bases : FiniteFamily.Bases (k := k) (T.toTower.localCoefficients).A) {I : Type uCover} [Fintype I] [DecidableEq I]
variable (regions : I → ClosedRegion K) (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (regions i).vertices)]
variable [∀ i, DecidablePred (· ∈ (regions i).edges)]
variable [∀ i, DecidablePred (· ∈ (regions i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
local notation "δ" => ActualEquation.defectFamily T P hfixed


/-- The actual cover region uses exactly the generated nonshared always-allowed private set. -/
noncomputable def localEquivalence (i : I) := NativeRepairInterface.equivalence T bases (regions i) P (ClosedRegion.privateAlwaysEdges regions P candidates i) hlinear hfixed enumK enumEdges enumFaces

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.faces)]
  [∀ i, DecidablePred (· ∈ (regions i).vertices)] [∀ i, DecidablePred (· ∈ (regions i).faces)]
  [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every shared original overlap value is read solely from the local public coordinates. -/
theorem shared_restriction_public_only (i j : I) (hij : j ≠ i)
    (x : FiniteNative.XIndex M bases (regions i) P (ClosedRegion.privateAlwaysEdges regions P candidates i) → k)
    (z : FiniteNative.ZIndex M bases (regions i) P (ClosedRegion.privateAlwaysEdges regions P candidates i) → k) :
    (fun e : (ClosedRegion.inter (regions i) (regions j)).edges =>
      ((FiniteNative.edgeSplit M bases (regions i) P (ClosedRegion.privateAlwaysEdges regions P candidates i)).symm (x,z)).1
        ⟨e.1,(ClosedRegion.inter_left (regions i) (regions j)).edges e.2⟩) =
      FiniteNative.publicRestriction M bases (regions i) P (ClosedRegion.privateAlwaysEdges regions P candidates i)
        (ClosedRegion.inter (regions i) (regions j)) (ClosedRegion.inter_left (regions i) (regions j)) z :=
  FiniteNative.restriction_public_only M bases (regions i) P
    (ClosedRegion.privateAlwaysEdges regions P candidates i) _ _
    (fun e he => ClosedRegion.overlap_not_private regions P candidates i j hij e he) x z

omit [Fintype I] [DecidableEq I] [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)]
  [DecidablePred (· ∈ P.faces)] [∀ i, DecidablePred (· ∈ (regions i).vertices)]
  [∀ i, DecidablePred (· ∈ (regions i).edges)] [∀ i, DecidablePred (· ∈ (regions i).faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every original named candidate remains on the public side of this exact elimination. -/
theorem candidate_retained (i : I) (e : EdgeName (K := K)) (he : e ∈ candidates) :
    e ∉ ClosedRegion.privateAlwaysEdges regions P candidates i :=
  ClosedRegion.candidate_not_private regions P candidates i e he

end FiniteCoverInterfaces
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
