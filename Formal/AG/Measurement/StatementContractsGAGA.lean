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
      F.finiteHodgeTheoremPackage.hodgeData.finiteHodgeDecomposition ∧
        (∀ omega gamma,
          Cohomology.IntervalBasisStokes.pair1
              (Cohomology.IntervalBasisStokes.d0 omega) gamma =
            Cohomology.IntervalBasisStokes.pair0 omega
              (Cohomology.IntervalBasisStokes.boundary0 gamma)) ∧
          (∀ x y,
            F.periodStokesTheoremPackage.extensionAccounting.kappa_U (x + y) =
              F.periodStokesTheoremPackage.extensionAccounting.kappa_U x +
                F.periodStokesTheoremPackage.extensionAccounting.kappa_U y) ∧
            (Module.finrank M.Coeff C.finiteCechSource.nerveComplex.C1 <=
              Module.finrank M.Coeff C.finiteCechSource.nerveComplex.H1 +
                Module.finrank M.Coeff C.finiteCechSource.nerveComplex.C0 +
                  Module.finrank M.Coeff C.finiteCechSource.nerveComplex.C2) ∧
              Nonempty
                (F.derivedConflictTheoremPackage.lawConflict ≃ₗ[
                    Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff]
                  Derived.Intersection.mathlibTor
                    (Derived.Counterexample.SharedWitnessCoord.ChartRing M.Coeff)
                    F.derivedConflictTheoremPackage.leftIdeal
                    F.derivedConflictTheoremPackage.rightIdeal 1) :=
  aatGAGACertifiedComparisonStatement_holds F

example : AATGAGAFiniteMeasurementComparison gagaComparisonExampleData :=
  gagaComparisonExamplePackage

end Measurement
end AAT.AG
