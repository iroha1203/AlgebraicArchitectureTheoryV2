import ResearchLean.AG.RelativeRepairComposition.CoverPlanConnecting
import ResearchLean.AG.RelativeRepairComposition.NativeDescent

/-!
# Integration obstruction for independent actual native repairs

The local plans are independent repairs of the actual restricted towers. All
original overlap gauge arrows remain, and the global source is the original K.
The defect cocycle comes from its own authored three-cell conditions.
## Implementation notes

G-130 B uses independent actual repairs of each native restricted tower.
The full arrow equivalence restores every original vertex label. The
authored original three-cell conditions generate the actual defect
cocycle; its vanishing or a global repair is never supplied as input.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace NativeCoverObstruction
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "M" => T.toTower.localCoefficients
local notation "δ" => ActualEquation.defectFamily T P hfixed
/-- Coordinates of each independent actual local repair retain its complete correction. -/
noncomputable def localCoordinate (U : ClosedRegion K) (R : NativeDescent.LocalGroupoid T P U) :
    CoverEquation.Solution M P δ U := ActualEquation.nativeRepairEquiv T P hfixed U R.back
/-- The full specified overlap cycle is generated from the actual local plans. -/
noncomputable def differenceCycle (U V : ClosedRegion K)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    CoverCohomology.Z1 M P (ClosedRegion.inter U V) :=
  CoverObstruction.differenceCycle M P δ U V
    (localCoordinate T P hfixed U R) (localCoordinate T P hfixed V Q)
/-- The entire native H1 class of the actual plan difference. -/
noncomputable def differenceClass (U V : ClosedRegion K)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    CoverCohomology.H1 M P (ClosedRegion.inter U V) :=
  QuotientAddGroup.mk (differenceCycle T P hfixed U V R Q)
/-- The same exact-sum integration quotient for actual native repairs. -/
noncomputable def omega (U V : ClosedRegion K)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    CoverObstruction.Omega M P U V := QuotientAddGroup.mk (differenceClass T P hfixed U V R Q)
/-- Every actual overlap gauge corresponds to the entire original equation gauge arrow. -/
noncomputable def overlapArrowEquiv (U V : ClosedRegion K)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    ((NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_left U V)).obj R ⟶
      (NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_right U V)).obj Q) ≃
    ((CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_left U V)).obj
        ((ActualEquation.nativeRepairEquationEquivalence T P hfixed U).functor.obj R) ⟶
      (CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_right U V)).obj
        ((ActualEquation.nativeRepairEquationEquivalence T P hfixed V).functor.obj Q)) :=
  ((ActualEquation.nativeRepairEquationEquivalence T P hfixed
    (ClosedRegion.inter U V)).symm.fullyFaithfulFunctor.homEquiv).symm
/-- Restoring every overlap gauge keeps every original vertex label. -/
theorem overlap_arrow_inverse_value (U V : ClosedRegion K)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V)
    (b : (CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_left U V)).obj
        ((ActualEquation.nativeRepairEquationEquivalence T P hfixed U).functor.obj R) ⟶
      (CoverEquation.restrictionFunctor M P δ (ClosedRegion.inter_right U V)).obj
        ((ActualEquation.nativeRepairEquationEquivalence T P hfixed V).functor.obj Q))
    (v : (ClosedRegion.inter U V).vertices) :
    ((overlapArrowEquiv T P hfixed U V R Q).symm b).1.toAdd.1 v = b.1.toAdd.1 v := rfl
/-- Reading every actual overlap gauge keeps every original vertex label. -/
theorem overlap_arrow_value (U V : ClosedRegion K)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V)
    (b : (NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_left U V)).obj R ⟶
      (NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_right U V)).obj Q)
    (v : (ClosedRegion.inter U V).vertices) :
    (overlapArrowEquiv T P hfixed U V R Q b).1.toAdd.1 v = b.1.toAdd.1 v := by
  have hh := overlap_arrow_inverse_value T P hfixed U V R Q
    (overlapArrowEquiv T P hfixed U V R Q b) v
  rw [Equiv.symm_apply_apply] at hh
  exact hh.symm
/-- The specified independent actual plans glue exactly when their H1 difference vanishes. -/
theorem specified_plans_glue_iff (U V : ClosedRegion K)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    Nonempty ((NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_left U V)).obj R ⟶
      (NativeDescent.restrictionFunctor T P hfixed (ClosedRegion.inter_right U V)).obj Q) ↔
      differenceClass T P hfixed U V R Q = 0 := by
  rw [show differenceClass T P hfixed U V R Q =
    (QuotientAddGroup.mk (CoverObstruction.differenceCycle M P δ U V
      (localCoordinate T P hfixed U R) (localCoordinate T P hfixed V Q)) :
      CoverCohomology.H1 M P (ClosedRegion.inter U V)) from rfl,
    ← CoverObstruction.seam_exists_iff]
  constructor
  · rintro ⟨b⟩
    let c := overlapArrowEquiv T P hfixed U V R Q b
    exact ⟨c.1.toAdd,Equation.hom_condition _ _ _ _ c⟩
  · rintro ⟨b,hb⟩
    exact ⟨(overlapArrowEquiv T P hfixed U V R Q).symm
      (Equation.homOfLabel _ _ _ _ b hb)⟩
/-- The integration class does not depend on either independent actual local plan. -/
theorem omega_independent (U V : ClosedRegion K)
    (R R' : NativeDescent.LocalGroupoid T P U) (Q Q' : NativeDescent.LocalGroupoid T P V) :
    omega T P hfixed U V R Q = omega T P hfixed U V R' Q' :=
  (CoverObstruction.omega_independent M P δ U V
    (localCoordinate T P hfixed U R) (localCoordinate T P hfixed U R')
    (localCoordinate T P hfixed V Q) (localCoordinate T P hfixed V Q')).symm
/-- The integration class vanishes exactly when a full actual repair on original K exists. -/
theorem omega_eq_zero_iff_original_repair (U V : ClosedRegion K)
    (hc : ClosedRegion.Cover U V)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    omega T P hfixed U V R Q = 0 ↔ Nonempty (SupportedRepair T P.edges) := by
  have hh := CoverObstruction.omega_eq_zero_iff_global M P δ U V hc
    (localCoordinate T P hfixed U R) (localCoordinate T P hfixed V Q)
  exact hh.trans (ActualEquation.originalRepairEquiv T P hfixed).symm.nonempty_congr
variable (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
  (K.threeLeft s) (K.threeRight s))
/-- The actual full defect family is generated from the original authored cocycle. -/
theorem authored_defect_family :
    CoverPlanConnecting.defectFamily M P (ActualRelative.obstructionCocycle T P hfixed hsyzygy) = δ := rfl
/-- The native original-K connecting map has the required positive actual-defect sign. -/
theorem connecting_actual_difference (U V : ClosedRegion K) (hc : ClosedRegion.Cover U V)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    CoverObstructionKernel.connecting M P U V hc (differenceClass T P hfixed U V R Q) =
      ActualRelative.obstructionClass T P ∅ ∅ hfixed hsyzygy :=
  CoverPlanConnecting.connecting_plan_class M P U V
    (ActualRelative.obstructionCocycle T P hfixed hsyzygy) hc
    (localCoordinate T P hfixed U R) (localCoordinate T P hfixed V Q)
/-- The full integration-kernel equivalence sends the actual class to its original defect class. -/
theorem omega_kernel_actual_class (U V : ClosedRegion K) (hc : ClosedRegion.Cover U V)
    (R : NativeDescent.LocalGroupoid T P U) (Q : NativeDescent.LocalGroupoid T P V) :
    (CoverObstructionKernel.omegaKernelEquiv M P U V hc (omega T P hfixed U V R Q)).1 =
      ActualRelative.obstructionClass T P ∅ ∅ hfixed hsyzygy := by
  change (CoverObstructionKernel.omegaKernelEquiv M P U V hc
    (QuotientAddGroup.mk (differenceClass T P hfixed U V R Q))).1 = _
  rw [CoverObstructionKernel.omega_kernel_value]
  exact connecting_actual_difference T P hfixed hsyzygy U V hc R Q
end NativeCoverObstruction
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
