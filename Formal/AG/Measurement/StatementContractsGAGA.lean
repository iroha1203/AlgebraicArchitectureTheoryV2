import Formal.AG.Measurement.Examples

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
The fixed Lean acceptance signature for VIII.Theorem 12.3.  This module is a
machine-checked contract: it repeats the required conjuncts without adding a
certificate field or a second theorem surface.
-/

example {M : MeasurementProfile.{u, v}} [Field M.Coeff]
    {C : AATGAGACommonFiniteData M} (F : AATGAGACertifiedFields C) :
    F.finiteHodgeTheoremPackage.hodgeData.harmonicKernelIdentifiesCohomology ∧
      Nonempty
        (C.finiteCechSource.geometry.CechHn 0 ≃
          F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.degreeZeroComplex.laplacian.ker) ∧
        (∀ n, Nonempty
          (C.finiteCechSource.geometry.CechHn (n + 1) ≃
            (AATGAGAAllDegreeRealCechHodgeInput.successorComplex
              F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput n).laplacian.ker)) ∧
        F.finiteHodgeTheoremPackage.hodgeData.allDegreeDecomposition ∧
          (∀ (n : Nat) (c : C.finiteCechSource.geometry.CechCochain n),
            F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.realD n
              (F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.sourceToReal n c) =
                F.finiteHodgeTheoremPackage.hodgeData.allDegreeInput.sourceToReal (n + 1)
                  (C.finiteCechSource.geometry.differentialLinear n c)) ∧
            F.periodStokesTheoremPackage.periodStokesStatement ∧
              F.topologicalDebtTheoremPackage.topologicalCapacityStatement ∧
                Nonempty
                  (C.lawConflict ≃ₗ[
                    Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
                    Derived.Intersection.mathlibTor
                      (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
                      C.ambientLeftIdeal C.ambientRightIdeal 1) ∧
                C.hilbertSeriesConflictStatement :=
  aatGAGACertifiedComparisonStatement_holds F

example : AATGAGAFiniteMeasurementComparison gagaComparisonExampleData :=
  gagaComparisonExamplePackage

end Measurement
end AAT.AG
