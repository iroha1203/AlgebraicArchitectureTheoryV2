import ResearchLean.AG.RelativeRepairComposition.W1RelativeCoefficients

/-!
# Original W1 actual operations and whole native correction values

## Implementation notes

Corrections are evaluated as actual operation times inverse of the same
original reference. The already proved whole repair equivalence then reads
the same value in the entire native categorical kernel. This comparison
prevents replacing real affine operations with an assumed scalar equation.
-/
namespace AAT.AG.RelativeRepairComposition.W1ActualCorrections
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs W1FiniteCoefficients

/-- Every independent actual repair's correction is evaluated on the same original full operation and inverse reference. -/
theorem parameters_real_correction {negative : Bool} {x y : ZMod 3}
    {S : Set (EdgeName (K := geometry))} (R : RealRepairs negative x y S)
    (e : EdgeName (K := geometry)) :
    NativeAffine.realCorrection geometry (reference negative x y) comparison (fixedEdges S) R e =
      correctionValue (parameters R).u (parameters R).h (parameters R).z (parameters R).v e.2.2 := by
  rw [NativeAffine.real_correction_value]
  have he := congrFun (congrFun (congrFun (parameters_operations R) e.1) e.2.1) e.2.2
  rw [← he]
  change ((translation (k := ZMod 3)
      (correctionValue (parameters R).u (parameters R).h (parameters R).z (parameters R).v e.2.2) *
        reference negative x y e.2.2) * (reference negative x y e.2.2)⁻¹) 0 = _
  rw [mul_assoc, mul_inv_cancel, mul_one, translation_apply, add_zero]

/-- The whole native actual correction equals the same original independent u,h,z,v value at every original edge name. -/
theorem native_correction_parameters (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry)))
    (R : SupportedRepair (originalTower negative x y) (fixedEdges S)) (e : EdgeName (K := geometry)) :
    kernelCoordinate negative x y e.2.1 ((originalTower negative x y).solutionCorrection R.1 e) =
      correctionValue
        (parameters (NativeAffine.repairEquivalence geometry (reference negative x y) (reference negative x y)
          comparison (linear_faces negative x y) (fixedEdges S) R)).u
        (parameters (NativeAffine.repairEquivalence geometry (reference negative x y) (reference negative x y)
          comparison (linear_faces negative x y) (fixedEdges S) R)).h
        (parameters (NativeAffine.repairEquivalence geometry (reference negative x y) (reference negative x y)
          comparison (linear_faces negative x y) (fixedEdges S) R)).z
        (parameters (NativeAffine.repairEquivalence geometry (reference negative x y) (reference negative x y)
          comparison (linear_faces negative x y) (fixedEdges S) R)).v e.2.2 :=
  (NativeAffine.real_correction_native geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) (fixedEdges S) R e).symm.trans
      (parameters_real_correction _ e)

/-- Reconstructing actual operations from derived parameters evaluates their entire actual original correction family. -/
theorem actualRepair_real_correction (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) (p : Parameters)
    (he : Equations negative x y p) (ha : Allowed S p) (e : EdgeName (K := geometry)) :
    NativeAffine.realCorrection geometry (reference negative x y) comparison (fixedEdges S)
        (actualRepair negative x y S p he ha) e = correctionValue p.u p.h p.z p.v e.2.2 := by
  rw [parameters_real_correction, actualRepair_parameters]

/-- The inverse whole native correspondence restores the exact original correction family on every original full kernel. -/
theorem native_inverse_correction (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) (p : {p : Parameters // Equations negative x y p ∧ Allowed S p})
    (e : EdgeName (K := geometry)) :
    kernelCoordinate negative x y e.2.1
        ((originalTower negative x y).solutionCorrection
          ((nativeParametersEquiv negative x y S).symm p).1 e) =
      correctionValue p.1.u p.1.h p.1.z p.1.v e.2.2 := by
  have hv := native_correction_parameters negative x y S ((nativeParametersEquiv negative x y S).symm p) e
  change kernelCoordinate negative x y e.2.1
      ((originalTower negative x y).solutionCorrection ((nativeParametersEquiv negative x y S).symm p).1 e) =
    correctionValue
      ((nativeParametersEquiv negative x y S) ((nativeParametersEquiv negative x y S).symm p)).1.u
      ((nativeParametersEquiv negative x y S) ((nativeParametersEquiv negative x y S).symm p)).1.h
      ((nativeParametersEquiv negative x y S) ((nativeParametersEquiv negative x y S).symm p)).1.z
      ((nativeParametersEquiv negative x y S) ((nativeParametersEquiv negative x y S).symm p)).1.v e.2.2 at hv
  rw [Equiv.apply_symm_apply] at hv
  exact hv

end AAT.AG.RelativeRepairComposition.W1ActualCorrections
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1ActualCorrections
