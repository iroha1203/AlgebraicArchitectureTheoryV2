import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification
import ResearchLean.AG.RelativeRepairComposition.OriginalNativeRangeCohomology
import ResearchLean.AG.RelativeRepairComposition.NativeCoverObstruction

/-! # The same actual obstruction through the original all-range quotient and H2 -/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uk uG uE uB uD vE vB vD
namespace OriginalRangeObstruction
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
/-- Decide membership in the full original edge region by its universal predicate. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original vertex region by its universal predicate. -/
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original face region by its universal predicate. -/
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k ((T.toTower.localCoefficients).A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.toTower.localCoefficients).A i),
  (T.toTower.localCoefficients).edge e (t • x) = t • (T.toTower.localCoefficients).edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
  (K.threeLeft s) (K.threeRight s))
local notation "M" => T.toTower.localCoefficients
local notation "D0" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "Bcol" => OriginalRanges.column (k := k) M P candidates houtside hlinear
local notation "delta" => ActualEquation.defectFamily T P hfixed
local notation "obs" => OriginalRangeClassification.obstruction (k := k) T P candidates hlinear hfixed

/-- The original always obstruction modulo every candidate range is the same negative actual H2 class. -/
theorem obstruction_H2 :
    OriginalRangeQuotient.equivalence (k := k) M P candidates houtside hlinear
      ((NamedDual.ranges Bcol Set.univ).mkQ obs) =
        (OriginalNativeRangeCohomology.classMap (k := k) M P hlinear
          (-ActualRelative.obstructionClass T P ∅ ∅ hfixed hsyzygy)).1 := by
  change OriginalRangeQuotient.equivalence (k := k) M P candidates houtside hlinear
    ((NamedDual.ranges (CokernelNamed.column D0
      (OriginalColumns.column (k := k) M P candidates houtside hlinear)) Set.univ).mkQ
        (LinearInterface.q D0 (-delta))) = _
  refine (OriginalRangeQuotient.equivalence_value (k := k) M P candidates houtside hlinear (-delta)).trans ?_
  simp only [map_neg]
  change -(LinearMap.range (FiniteCoefficients.differential1 M hlinear ClosedRegion.all P)).mkQ
    delta = -(OriginalNativeRangeCohomology.classMap (k := k) M P hlinear
      (QuotientAddGroup.mk (ActualRelative.obstructionCocycle T P hfixed hsyzygy))).1
  rw [OriginalNativeRangeCohomology.classMap_value]
  rfl

include hsyzygy in
/-- The same actual obstruction quotient image lies in the induced original typed d2 kernel. -/
theorem obstruction_image_cycle :
    OriginalRangeQuotient.equivalence (k := k) M P candidates houtside hlinear
      ((NamedDual.ranges Bcol Set.univ).mkQ obs) ∈
        LinearMap.ker (OriginalRangeQuotient.inducedD2 (k := k) M P hlinear) := by
  rw [obstruction_H2 (k := k) T P candidates houtside hlinear hfixed hsyzygy]
  exact (OriginalNativeRangeCohomology.classMap (k := k) M P hlinear
    (-ActualRelative.obstructionClass T P ∅ ∅ hfixed hsyzygy)).2

end OriginalRangeObstruction
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
