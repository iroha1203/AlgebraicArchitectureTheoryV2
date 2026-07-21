import Formal.AG.Measurement.Computability
import Formal.AG.Measurement.Examples

noncomputable section

namespace AAT.AG

universe u v

/-!
Fixed statement contracts for Part VIII, theorem 4.2.

The generic contract accepts the generated finite regime plus selected
square-free and finite-resolution data.  The Čech objects, all-degree finite
reductions, and verdicts are conclusions of
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
    ∀ n,
      Finite
        (Measurement.computabilityFiniteMeasurementRegime.geometry.CechHn n) :=
  Measurement.finiteComputabilityExample_linearAlgebraRoute

example :
    Measurement.finiteComputabilityZeroCochain ≠
      Measurement.finiteComputabilityOneCochain :=
  Measurement.finiteComputabilityCochain_nondegenerate

example :
    ∀ n
      (h : Measurement.computabilityFiniteMeasurementRegime.geometry.CechHn n),
      h ∈ Measurement.finiteComputabilityExamplePackage.cohomologyClasses n :=
  Measurement.finiteComputabilityExample_effectiveProcedureRoute.2.2

example :
    Measurement.finiteComputabilityExampleData.conflictSupport =
      Measurement.forbiddenSupportPQFinset :=
  Measurement.finiteComputabilityExample_combinatoricsRoute

end AAT.AG
