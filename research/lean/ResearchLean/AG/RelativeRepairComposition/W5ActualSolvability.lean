import ResearchLean.AG.RelativeRepairComposition.W5IntegrationObstruction
import ResearchLean.AG.RelativeRepairComposition.W5AbsoluteCohomology

/-! # W5's all-input actual solvability and four original witnesses

Every original pair has both independent actual local plans. A whole original
repair exists precisely when its same two inputs agree, precisely when the
original relative class or the actual integration class vanishes. All four
specified inputs keep their original repair values and actual class readings.
-/
namespace AAT.AG.RelativeRepairComposition.W5ActualSolvability
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput W5Regions W5AuthoredOperations W5ActualRepairs W5LocalRepairs
open W5RelativeCoefficients W5RelativeObstruction W5NativeDescent W5OverlapCohomology W5IntegrationObstruction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
/-- Every original input pair has both independent full actual local repairs. -/
theorem local_always (b₁ b₂ : ZMod 2) (side : Bool) : Nonempty (LocalRepairs b₁ b₂ (region side)) :=
  ⟨localPlan b₁ b₂ side⟩
/-- Every original whole actual repair exists exactly when its same two physically fixed inputs agree. -/
theorem global_iff (b₁ b₂ : ZMod 2) : Nonempty (RealRepairs b₁ b₂) ↔ b₁ = b₂ := by
  constructor
  · rintro ⟨R⟩
    exact (value_inputs R).1.symm.trans (value_inputs R).2
  · intro h
    exact ⟨fromValue b₁ b₂ b₁ rfl h⟩
/-- The same whole original native repairs have precisely the independent actual solvability condition. -/
theorem native_global_iff (b₁ b₂ : ZMod 2) :
    Nonempty (SupportedRepair (originalTower b₁ b₂) fixedRegion.edges) ↔ b₁ = b₂ :=
  (NativeAffine.repairEquivalence geometry (reference b₁ b₂) (reference b₁ b₂)
    comparison (linear_faces b₁ b₂) fixedRegion.edges).nonempty_congr.trans (global_iff b₁ b₂)
/-- The relative obstruction is the same original actual defect class. -/
noncomputable def relativeObstruction (b₁ b₂ : ZMod 2) :=
  ActualRelative.obstructionClass (originalTower b₁ b₂) fixedRegion ∅ ∅
    (fixed_faces b₁ b₂) (original_syzygy b₁ b₂)
/-- The actual integration class uses independently constructed local native plans on both original patches. -/
noncomputable def integrationObstruction (b₁ b₂ : ZMod 2) :=
  NativeCoverObstruction.omega (originalTower b₁ b₂) fixedRegion (fixed_faces b₁ b₂)
    leftRegion rightRegion (nativeLocalPlan b₁ b₂ false) (nativeLocalPlan b₁ b₂ true)
/-- The relative actual class vanishes exactly when the original physical inputs agree. -/
theorem relative_zero_iff (b₁ b₂ : ZMod 2) : relativeObstruction b₁ b₂ = 0 ↔ b₁ = b₂ := by
  rw [← (originalH2Coordinate b₁ b₂).map_eq_zero_iff]
  change originalH2Coordinate b₁ b₂
    (ActualRelative.obstructionClass (originalTower b₁ b₂) fixedRegion ∅ ∅
      (fixed_faces b₁ b₂) (original_syzygy b₁ b₂)) = 0 ↔ b₁ = b₂
  rw [actual_obstruction_value,sub_eq_zero,eq_comm]
/-- The same original whole actual repair condition is exactly generic A's relative obstruction criterion. -/
theorem general_a (b₁ b₂ : ZMod 2) :
    Nonempty (SupportedRepair (originalTower b₁ b₂) fixedRegion.edges) ↔ relativeObstruction b₁ b₂ = 0 := by
  simpa [fixedEdgesForRange] using ActualRelative.repair_nonempty_iff_obstruction_zero
    (originalTower b₁ b₂) fixedRegion ∅ ∅ (fixed_faces b₁ b₂) (original_syzygy b₁ b₂)
/-- Every independent actual pair's Omega class vanishes precisely for equal original inputs. -/
theorem omega_zero_iff (b₁ b₂ : ZMod 2)
    (R : NativeDescent.LocalGroupoid (originalTower b₁ b₂) fixedRegion leftRegion)
    (Q : NativeDescent.LocalGroupoid (originalTower b₁ b₂) fixedRegion rightRegion) :
    NativeCoverObstruction.omega (originalTower b₁ b₂) fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q = 0 ↔ b₁ = b₂ := by
  constructor
  · intro h
    have hv := omega_value b₁ b₂ R Q
    rw [h,map_zero] at hv
    exact (sub_eq_zero.mp hv.symm).symm
  · intro h
    apply (omegaCoordinate b₁ b₂).injective
    rw [omega_value,map_zero,h,sub_self]
/-- Generic B retains the same original physical whole repair predicate for every independent actual local pair. -/
theorem general_b (b₁ b₂ : ZMod 2)
    (R : NativeDescent.LocalGroupoid (originalTower b₁ b₂) fixedRegion leftRegion)
    (Q : NativeDescent.LocalGroupoid (originalTower b₁ b₂) fixedRegion rightRegion) :
    NativeCoverObstruction.omega (originalTower b₁ b₂) fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q = 0 ↔
      Nonempty (SupportedRepair (originalTower b₁ b₂) fixedRegion.edges) :=
  NativeCoverObstruction.omega_eq_zero_iff_original_repair (originalTower b₁ b₂) fixedRegion (fixed_faces b₁ b₂)
    leftRegion rightRegion regions_cover R Q
/-- The zero diagonal input has its complete original shared-zero repair. -/
noncomputable def repair00 : RealRepairs 0 0 := fromValue 0 0 0 rfl rfl
/-- The one diagonal input has its complete original shared-one repair. -/
noncomputable def repair11 : RealRepairs 1 1 := fromValue 1 1 1 rfl rfl
/-- Both diagonal actual repair witnesses retain their specified original shared values. -/
theorem diagonal_values : value repair00 = 0 ∧ value repair11 = 1 :=
  ⟨value_from 0 0 0 rfl rfl,value_from 1 1 1 rfl rfl⟩
/-- The first off-diagonal input has both original local plans and no complete original repair. -/
theorem off_diagonal01 : Nonempty (LocalRepairs 0 1 leftRegion) ∧ Nonempty (LocalRepairs 0 1 rightRegion) ∧
    ¬ Nonempty (RealRepairs 0 1) :=
  ⟨local_always 0 1 false,local_always 0 1 true,by rw [global_iff]; exact zero_ne_one⟩
/-- The second off-diagonal input has both original local plans and no complete original repair. -/
theorem off_diagonal10 : Nonempty (LocalRepairs 1 0 leftRegion) ∧ Nonempty (LocalRepairs 1 0 rightRegion) ∧
    ¬ Nonempty (RealRepairs 1 0) :=
  ⟨local_always 1 0 false,local_always 1 0 true,by rw [global_iff]; exact one_ne_zero⟩
/-- Both actual relative off-diagonal original obstruction classes are nonzero. -/
theorem relative_off_diagonal : relativeObstruction 0 1 ≠ 0 ∧ relativeObstruction 1 0 ≠ 0 := by
  constructor
  · exact (relative_zero_iff 0 1).not.mpr zero_ne_one
  · exact (relative_zero_iff 1 0).not.mpr one_ne_zero
/-- The same prescribed whole Omega classes on the two off-diagonal inputs are nonzero. -/
theorem integration_off_diagonal : integrationObstruction 0 1 ≠ 0 ∧ integrationObstruction 1 0 ≠ 0 := by
  constructor
  · exact (omega_zero_iff 0 1 _ _).not.mpr zero_ne_one
  · exact (omega_zero_iff 1 0 _ _).not.mpr one_ne_zero
/-- All four original input pairs have the specified exact whole relative class readings. -/
theorem four_relative_values :
    originalH2Coordinate 0 0 (relativeObstruction 0 0) = 0 ∧
    originalH2Coordinate 1 1 (relativeObstruction 1 1) = 0 ∧
    originalH2Coordinate 0 1 (relativeObstruction 0 1) = 1 ∧
    originalH2Coordinate 1 0 (relativeObstruction 1 0) = 1 := by
  simp only [relativeObstruction,actual_obstruction_value]
  norm_num
  exact ZMod.neg_eq_self_mod_two 1
/-- All four original actual local-pair classes have the specified entire Omega readings. -/
theorem four_integration_values :
    omegaCoordinate 0 0 (integrationObstruction 0 0) = 0 ∧
    omegaCoordinate 1 1 (integrationObstruction 1 1) = 0 ∧
    omegaCoordinate 0 1 (integrationObstruction 0 1) = 1 ∧
    omegaCoordinate 1 0 (integrationObstruction 1 0) = 1 := by
  simp only [integrationObstruction,omega_value]
  norm_num
  exact ZMod.neg_eq_self_mod_two 1
/-- The same original absolute cohomology vanishes while both physical-relative off-diagonal classes survive. -/
theorem absolute_relative_comparison :
    (∀ b₁ b₂ : ZMod 2, ∀ h : RelativeComplex.H2 (originalTower b₁ b₂).toTower.localCoefficients ClosedRegion.empty ∅ ∅, h = 0) ∧
      relativeObstruction 0 1 ≠ 0 ∧ relativeObstruction 1 0 ≠ 0 :=
  ⟨W5AbsoluteCohomology.absolute_h2_zero,relative_off_diagonal⟩

end AAT.AG.RelativeRepairComposition.W5ActualSolvability
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5ActualSolvability
