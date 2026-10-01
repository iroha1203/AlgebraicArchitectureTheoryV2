import ResearchLean.AG.RelativeRepairComposition.CoverObstructionKernel

/-!
# The sign of the integration connecting class

The cover difference is first-minus-second, while the actual plan difference is
second-minus-first. The full lift is therefore (-hU,-hV); its differential is
precisely the global defect, with a positive sign.
## Implementation notes

G-130 B fixes the difference map and plan cycle with opposite orders.
The actual negative plan pair and its differential compute the native
connecting class. Assuming a connecting-value certificate would omit
this sign and original-defect obligation.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace CoverPlanConnecting
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P U V : ClosedRegion K)
variable (c : RelativeComplex.Z2 M P)
/-- The complete global defect family retains every original face value. -/
noncomputable def defectFamily : RelativeCover.C2 M ClosedRegion.all P :=
  (RelativeCover.original2 M P).symm c.1
/-- The full negative pair of plans lifts their second-minus-first overlap cycle. -/
theorem negative_plan_lift
    (hU : CoverEquation.Solution M P (defectFamily M P c) U)
    (hV : CoverEquation.Solution M P (defectFamily M P c) V) :
    (RelativeCover.originalCoverShortComplex M P U V).g.f 1 (-hU.1,-hV.1) =
      (CoverObstruction.differenceCycle M P (defectFamily M P c) U V hU hV).1 := by
  change RelativeCover.r1 M P (ClosedRegion.inter_left U V) (-hU.1) -
    RelativeCover.r1 M P (ClosedRegion.inter_right U V) (-hV.1) = _
  rw [map_neg,map_neg]
  change -RelativeCover.r1 M P (ClosedRegion.inter_left U V) hU.1 -
    -RelativeCover.r1 M P (ClosedRegion.inter_right U V) hV.1 =
      RelativeCover.r1 M P (ClosedRegion.inter_right U V) hV.1 -
        RelativeCover.r1 M P (ClosedRegion.inter_left U V) hU.1
  abel
/-- The differential of the complete negative plan pair is the original global defect. -/
theorem negative_plan_differential
    (hU : CoverEquation.Solution M P (defectFamily M P c) U)
    (hV : CoverEquation.Solution M P (defectFamily M P c) V) :
    (RelativeCover.originalCoverShortComplex M P U V).f.f 2 c.1 =
      (RelativeCover.pairComplex M P U V).d 1 2 (-hU.1,-hV.1) := by
  have hu := hU.2
  have hv := hV.2
  change RelativeCover.d1 M U P hU.1 =
    -RelativeCover.r2 M P (ClosedRegion.to_all U) (defectFamily M P c) at hu
  change RelativeCover.d1 M V P hV.1 =
    -RelativeCover.r2 M P (ClosedRegion.to_all V) (defectFamily M P c) at hv
  change (RelativeCover.r2 M P (ClosedRegion.to_all U) (defectFamily M P c),
    RelativeCover.r2 M P (ClosedRegion.to_all V) (defectFamily M P c)) =
      (RelativeCover.d1 M U P (-hU.1),RelativeCover.d1 M V P (-hV.1))
  rw [map_neg,map_neg,hu,hv,neg_neg,neg_neg]
/-- The native connecting class of the specified plans is the positive original defect class. -/
theorem connecting_plan_class (hc : ClosedRegion.Cover U V)
    (hU : CoverEquation.Solution M P (defectFamily M P c) U)
    (hV : CoverEquation.Solution M P (defectFamily M P c) V) :
    CoverObstructionKernel.connecting M P U V hc
      (QuotientAddGroup.mk (CoverObstruction.differenceCycle M P
        (defectFamily M P c) U V hU hV)) =
      (QuotientAddGroup.mk c : RelativeComplex.H2 M P ∅ ∅) := by
  have hh := CoverConnecting.connecting_class
    (RelativeCover.original_cover_short_exact M P U V hc) 1 2 (by simp)
    (CoverCohomology.nativeCycle1 M P (ClosedRegion.inter U V)
      (CoverObstruction.differenceCycle M P (defectFamily M P c) U V hU hV))
    (-hU.1,-hV.1) (negative_plan_lift M P U V c hU hV)
    (OriginalCohomology.nativeCycle2 M P c)
    (negative_plan_differential M P U V c hU hV)
  change (OriginalCohomology.secondHomologyIso M P).hom
    ((RelativeCover.original_cover_short_exact M P U V hc).δ 1 2 (by simp)
      ((CoverCohomology.firstHomologyIso M P (ClosedRegion.inter U V)).inv
        (QuotientAddGroup.mk (CoverObstruction.differenceCycle M P
          (defectFamily M P c) U V hU hV)))) = _
  rw [CoverCohomology.native_h1_inverse_class]
  exact (congrArg (fun x => (OriginalCohomology.secondHomologyIso M P).hom x) hh).trans
    (OriginalCohomology.native_h2_class M P c)
end CoverPlanConnecting
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
