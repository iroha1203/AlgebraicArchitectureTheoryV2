import ResearchLean.AG.RelativeRepairComposition.SubdivisionAlwaysDifferential
import ResearchLean.AG.RelativeRepairComposition.SubdivisionActualDefect
import ResearchLean.AG.RelativeRepairComposition.NativeEquationBridge
import ResearchLean.AG.RelativeRepairComposition.LinearInterface

/-!
# The same actual always quotient and obstruction after subdivision

The full quotient comparison comes from equality of the independently defined
always images. It preserves every original representative and the negative
actual defect, with the original fixed laws generating the new ones.

## Implementation notes

Equality of the independently generated always images permits a quotient
comparison that reads every unchanged face representative. Comparing only
vanishing or repair existence would not preserve the actual quotient point
and every whole candidate column, so those weaker comparisons were rejected.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.RangeQuotient
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

local notation "oldD" => OriginalColumns.D (k := k) M P candidates hlinear
include hc in
/-- The full independent new always cokernel is equivalent to the full original cokernel. -/
noncomputable def equivalence :
    (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all newP ⧸
      LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear)) ≃ₗ[k]
    (RelativeCover.C2 M ClosedRegion.all P ⧸ LinearMap.range oldD) :=
  Submodule.quotEquivOfEq _ _ (AlwaysDifferential.range_D T P candidates chosen F hp hc hlinear)

/-- Every same complete face representative descends through the actual quotient comparison. -/
theorem equivalence_q (c : RelativeCover.C2 M ClosedRegion.all P) :
    equivalence T P candidates chosen F hp hc hlinear (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear) c) =
      LinearInterface.q oldD c := rfl

/-- Inverse comparison also retains every full original representative. -/
theorem inverse_q (c : RelativeCover.C2 M ClosedRegion.all P) :
    (equivalence T P candidates chosen F hp hc hlinear).symm (LinearInterface.q oldD c) =
      LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear) c := by
  apply (equivalence T P candidates chosen F hp hc hlinear).injective
  rw [LinearEquiv.apply_symm_apply,equivalence_q]

include hc in
/-- The original always obstruction vanishes exactly when the independent new one vanishes. -/
theorem q_zero_iff (c : RelativeCover.C2 M ClosedRegion.all P) :
    LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear) c = 0 ↔ LinearInterface.q oldD c = 0 := by
  rw [← equivalence_q T P candidates chosen F hp hc hlinear c]
  exact ((equivalence T P candidates chosen F hp hc hlinear).map_eq_zero_iff).symm

variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))

/-- Independently generated actual defect families keep every full original face coordinate. -/
theorem defectFamily_eq :
    ActualEquation.defectFamily (originalTower T chosen F) newP
      (fixed_face_laws T chosen F P hp hfixed) =
      ActualEquation.defectFamily T P hfixed := by
  apply Subtype.ext
  funext f
  change (originalTower T chosen F).toTower.defect f.1 = T.toTower.defect f.1
  exact congrFun (defect_substitute T chosen F) f.1

/-- The entire signed actual obstruction o=q(-delta) is preserved by the same quotient map. -/
theorem obstruction_eq :
    equivalence T P candidates chosen F hp hc hlinear
      (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear) (-(ActualEquation.defectFamily (originalTower T chosen F) newP
        (fixed_face_laws T chosen F P hp hfixed)))) =
      LinearInterface.q oldD (-ActualEquation.defectFamily T P hfixed) := by
  rw [defectFamily_eq,equivalence_q]

end AAT.AG.RelativeRepairComposition.Subdivision.RangeQuotient
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.RangeQuotient
