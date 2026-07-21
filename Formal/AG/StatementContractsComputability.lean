import Formal.AG.Measurement.Computability
import Formal.AG.Measurement.Examples

noncomputable section

namespace AAT.AG

universe u v

/-!
Fixed statement contracts for Part VIII, theorem 4.2.

The generic contract accepts the generated finite regime plus selected
square-free and finite-resolution data.  The selected coefficient branch,
Čech reduction, and verdicts are conclusions of
`Measurement.finiteAATComputability`.
-/

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M)
    (D : Measurement.FiniteAATComputationData M R) :
    Nonempty (Measurement.FiniteAATComputability R D) :=
  Measurement.finiteAATComputability R D

example :
    Nonempty
      (Measurement.FiniteAATComputability
        Measurement.computabilityFiniteMeasurementRegime
        Measurement.finiteComputabilityExampleData) :=
  Measurement.finiteComputabilityExample_verified

example :
    Measurement.finiteComputabilityExamplePackage.coefficientComputation.route =
      Measurement.CoefficientComputationRoute.effectiveFinitelyPresented :=
  Measurement.finiteComputabilityExample_effectiveRouteSelected

example :
    (Measurement.CechComputationProcedure.finiteDimensional
      Measurement.finiteDimensionalRationalCechProcedure).route =
        Measurement.CoefficientComputationRoute.finiteDimensionalLinearAlgebra :=
  Measurement.finiteDimensionalRationalRoute_fires

example : Infinite Measurement.finiteDimensionalRationalProfile.Coeff :=
  Measurement.finiteDimensionalRationalCoeff_infinite

example (n : Nat) :
    letI : Field Measurement.finiteDimensionalRationalProfile.Coeff :=
      Measurement.finiteDimensionalRationalCoeffField
    Module.Finite Measurement.finiteDimensionalRationalProfile.Coeff
      (Measurement.finiteDimensionalRationalCechModel.Cohomology n) :=
  Measurement.finiteDimensionalRationalCohomology_moduleFinite n

example :
    Measurement.finiteComputabilityZeroCochain ≠
      Measurement.finiteComputabilityOneCochain :=
  Measurement.finiteComputabilityCochain_nondegenerate

example :
    ∀ n (h : Measurement.computabilityFiniteMeasurementRegime.geometry.CechHn n),
      Measurement.computabilityFiniteMeasurementRegime.geometry.classOfCocycle n
        (Measurement.finiteComputabilityEffectiveCechProcedure.quotientRepresentative
          n h) = h :=
  Measurement.finiteComputabilityExample_effectiveProcedureRoute.2.2

example :
    Measurement.finiteComputabilityExampleData.conflictSupport =
      Measurement.forbiddenSupportPQFinset :=
  Measurement.finiteComputabilityExample_combinatoricsRoute

end AAT.AG
