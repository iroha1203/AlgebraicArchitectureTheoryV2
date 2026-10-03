import ResearchLean.AG.RepairObservationDuality.W1SubdivisionQueries

/-!
# G-131 E: independent actual split repairs and every full numerical coordinate

## Implementation notes

The five coordinates are read from arbitrary independently defined supported
split repairs, rather than from the image of restoration. Actual collapse
proves their validator. Conversely, restoration has exactly all five supplied
coordinates. This identifies the full numeric validator with actual repairs
and discharges the none output using the same original support conditions.
-/
namespace AAT.AG.RepairObservationDuality.W1SubdivisionValues
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open RelativeRepairComposition W1AffineInput W1Regions W1ActualRepairs W1FiniteCoefficients W1ActualCorrections
open W1SubdivisionInput W1PhysicalInputs W1NumericalEquation W1SubdivisionQueries
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

/-- The entire old numerical vector is read from every independent native original repair. -/
noncomputable def oldValues (p : Permissions) (v : Values)
    (R : SupportedRepair (originalTower true (v false) (v true)) (fixedEdges (allowed p))) : Corrections :=
  ![kernelCoordinate true (v false) (v true) () ((originalTower true (v false) (v true)).solutionCorrection R.1 (name edgeE)),
    kernelCoordinate true (v false) (v true) () ((originalTower true (v false) (v true)).solutionCorrection R.1 (name edgeA)),
    kernelCoordinate true (v false) (v true) () ((originalTower true (v false) (v true)).solutionCorrection R.1 (name edgeB)),
    kernelCoordinate true (v false) (v true) () ((originalTower true (v false) (v true)).solutionCorrection R.1 (name edgeC))]

/-- Every full old native coordinate vector reads the actual original authored parameters. -/
theorem old_parameters (p : Permissions) (v : Values)
    (R : SupportedRepair (originalTower true (v false) (v true)) (fixedEdges (allowed p))) :
    W1NumericalEquation.parameters (oldValues p v R) =
      ((nativeParametersEquiv true (v false) (v true) (allowed p)) R).1 := by
  have he := native_correction_parameters true (v false) (v true) (allowed p) R (name edgeE)
  have ha := native_correction_parameters true (v false) (v true) (allowed p) R (name edgeA)
  have hb := native_correction_parameters true (v false) (v true) (allowed p) R (name edgeB)
  have hc := native_correction_parameters true (v false) (v true) (allowed p) R (name edgeC)
  change oldValues p v R 0 = ((nativeParametersEquiv true (v false) (v true) (allowed p)) R).1.u at he
  change oldValues p v R 1 = ((nativeParametersEquiv true (v false) (v true) (allowed p)) R).1.h at ha
  change oldValues p v R 2 = ((nativeParametersEquiv true (v false) (v true) (allowed p)) R).1.z at hb
  change oldValues p v R 3 = ((nativeParametersEquiv true (v false) (v true) (allowed p)) R).1.v at hc
  cases hq : ((nativeParametersEquiv true (v false) (v true) (allowed p)) R).1 with
  | mk u h z c =>
    simp only [hq] at he ha hb hc
    change W1ActualRepairs.Parameters.mk _ _ _ _ = _
    congr 1

/-- Every independent old repair satisfies the same complete constrained numerical equation. -/
theorem old_valid (p : Permissions) (v : Values)
    (R : SupportedRepair (originalTower true (v false) (v true)) (fixedEdges (allowed p))) :
    differential p (oldValues p v R) = affineRhs rhsLinear 0 v := by
  rw [equation_iff,old_parameters]
  exact ((nativeParametersEquiv true (v false) (v true) (allowed p)) R).2

/-- The full five numerical coordinates read each surviving original kernel and both complete factor kernels. -/
noncomputable def splitValues (p : Permissions) (v : Values)
    (R : W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p)) : SplitCorrections :=
  ![kernelCoordinate true (v false) (v true) () ((splitTower (v false) (v true)).solutionCorrection R.1
       (Subdivision.oldEdgeName geometry chosen (name edgeE) (by simp [chosen,name,edgeE,edgeA,geometry]))),
    kernelCoordinate true (v false) (v true) () ((splitTower (v false) (v true)).solutionCorrection R.1
       (Subdivision.oldEdgeName geometry chosen (name edgeB) (by simp [chosen,name,edgeB,edgeA,geometry]))),
    kernelCoordinate true (v false) (v true) () ((splitTower (v false) (v true)).solutionCorrection R.1
       (Subdivision.oldEdgeName geometry chosen (name edgeC) (by simp [chosen,name,edgeC,edgeA,geometry]))),
    W1SubdivisionRepairs.middleCoefficient (v false) (v true) ((splitTower (v false) (v true)).solutionCorrection R.1
       (Subdivision.firstEdgeName geometry chosen)),
    W1SubdivisionRepairs.middleCoefficient (v false) (v true) ((splitTower (v false) (v true)).solutionCorrection R.1
       (Subdivision.secondEdgeName geometry chosen))]

/-- Numeric collapse of every independent split repair reads exactly all four old actual correction values. -/
theorem collapse_values (p : Permissions) (v : Values)
    (R : W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p)) :
    collapse (splitValues p v R) = oldValues p v
      (Subdivision.collapseSupported (originalTower true (v false) (v true)) chosen
        (factors (v false) (v true)) (fixedEdges (allowed p)) (chosen_not_fixed _) R) := by
  ext i
  fin_cases i
  · exact (congrArg (kernelCoordinate true (v false) (v true) ())
      (Subdivision.collapseSupported_old _ _ _ _ _ R (name edgeE) (by simp [chosen,name,edgeE,edgeA,geometry]))).symm
  · have h := W1SubdivisionCoordinates.collapse_coordinate (v false) (v true)
      ((splitTower (v false) (v true)).solutionCorrection R.1)
    have hc := Subdivision.collapseSupported_correction (originalTower true (v false) (v true)) chosen
      (factors (v false) (v true)) (fixedEdges (allowed p)) (chosen_not_fixed _) R
    change _ = kernelCoordinate true (v false) (v true) ()
      ((originalTower true (v false) (v true)).solutionCorrection _ (name edgeA))
    rw [hc]
    exact h.symm
  · exact (congrArg (kernelCoordinate true (v false) (v true) ())
      (Subdivision.collapseSupported_old _ _ _ _ _ R (name edgeB) (by simp [chosen,name,edgeB,edgeA,geometry]))).symm
  · exact (congrArg (kernelCoordinate true (v false) (v true) ())
      (Subdivision.collapseSupported_old _ _ _ _ _ R (name edgeC) (by simp [chosen,name,edgeC,edgeA,geometry]))).symm

/-- Every independent full split repair has a valid fully acquired numerical output. -/
theorem split_valid (p : Permissions) (v : Values)
    (R : W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p)) :
    ValidSplit p v (some (splitValues p v R)) := by
  rw [validSplit_iff,Option.map_some,validOutput_some_iff,collapse_values]
  exact old_valid p v _

/-- Restoration returns every one of the complete five specified split correction values. -/
theorem restore_values (p : Permissions) (v : Values) (b : SplitCorrections)
    (hb : ValidSplit p v (some b)) : splitValues p v (W1SubdivisionQueries.restore p v b hb) = b := by
  have hf := restore_factors p v b hb
  have he := restore_old p v b hb (name edgeE) (by simp [chosen,name,edgeE,edgeA,geometry])
  have hz := restore_old p v b hb (name edgeB) (by simp [chosen,name,edgeB,edgeA,geometry])
  have hv := restore_old p v b hb (name edgeC) (by simp [chosen,name,edgeC,edgeA,geometry])
  ext i
  fin_cases i
  · change kernelCoordinate true (v false) (v true) () _ = b 0
    rw [he]
    have h := native_inverse_correction true (v false) (v true) (allowed p)
      ⟨W1NumericalEquation.parameters (collapse b),(equation_iff p v (collapse b)).mp ((validOutput_some_iff _ _ _ _).mp hb)⟩ (name edgeE)
    simpa [parameters_u,collapse_zero,W1AuthoredOperations.correctionValue,name,edgeE,geometry] using h
  · change kernelCoordinate true (v false) (v true) () _ = b 1
    rw [hz]
    have h := native_inverse_correction true (v false) (v true) (allowed p)
      ⟨W1NumericalEquation.parameters (collapse b),(equation_iff p v (collapse b)).mp ((validOutput_some_iff _ _ _ _).mp hb)⟩ (name edgeB)
    simpa [parameters_z,collapse_two,W1AuthoredOperations.correctionValue,name,edgeE,edgeA,edgeB,geometry] using h
  · change kernelCoordinate true (v false) (v true) () _ = b 2
    rw [hv]
    have h := native_inverse_correction true (v false) (v true) (allowed p)
      ⟨W1NumericalEquation.parameters (collapse b),(equation_iff p v (collapse b)).mp ((validOutput_some_iff _ _ _ _).mp hb)⟩ (name edgeC)
    simpa [parameters_v,collapse_three,W1AuthoredOperations.correctionValue,name,edgeE,edgeA,edgeB,edgeC,geometry] using h
  · exact hf.1
  · exact hf.2

/-- Full split numerical validity is exactly existence of an independent actual repair with every supplied coordinate. -/
theorem actual_some_iff (p : Permissions) (v : Values) (b : SplitCorrections) :
    ValidSplit p v (some b) ↔ ∃ R : W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p),
      splitValues p v R = b := by
  constructor
  · intro hb
    exact ⟨W1SubdivisionQueries.restore p v b hb,restore_values p v b hb⟩
  · rintro ⟨R,rfl⟩
    exact split_valid p v R

/-- The none answer excludes every independent actual supported split repair. -/
theorem actual_none_iff (p : Permissions) (v : Values) :
    ValidSplit p v none ↔ ¬ Nonempty (W1SubdivisionRepairs.NewRepairs (v false) (v true) (allowed p)) := by
  rw [validSplit_iff,Option.map_none,validOutput_none_iff]
  constructor
  · intro hn ⟨R⟩
    exact hn ⟨collapse (splitValues p v R),(validOutput_some_iff _ _ _ _).mp (split_valid p v R)⟩
  · intro hn ⟨a,ha⟩
    have hb : ValidSplit p v (some (extend 0 a)) :=
      (valid_extend_iff p v 0 (some a)).mpr ((validOutput_some_iff _ _ _ _).mpr ha)
    exact hn ⟨W1SubdivisionQueries.restore p v (extend 0 a) hb⟩

end AAT.AG.RepairObservationDuality.W1SubdivisionValues
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1SubdivisionValues
