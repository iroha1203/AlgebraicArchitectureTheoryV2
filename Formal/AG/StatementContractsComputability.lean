import Formal.AG.Measurement.Computability
import Formal.AG.Measurement.Examples

noncomputable section

namespace AAT.AG

universe u v

/-!
Fixed statement contracts for Part VIII, theorem 4.2.

The generic contract accepts only the finite regime and the selected primitive
Čech, square-free, and finite-resolution data.  The finite reductions are the
conclusion of `Measurement.finiteAATComputability`.
-/

example {M : Measurement.MeasurementProfile.{u, v}}
    (R : Measurement.FiniteMeasurementRegime M) [CommRing M.Coeff]
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
    Finite Measurement.finiteComputabilityExampleData.cech.complex.H1 :=
  Measurement.finiteComputabilityExample_linearAlgebraRoute

example :
    Function.Bijective
      Measurement.finiteComputabilityExamplePackage.quotientComparison :=
  Measurement.finiteComputabilityExample_effectiveProcedureRoute.2.2

example :
    Measurement.finiteComputabilityExampleData.conflictSupport =
      {Measurement.SquareFreeSupportVertex.p,
        Measurement.SquareFreeSupportVertex.q,
        Measurement.SquareFreeSupportVertex.r} :=
  Measurement.finiteComputabilityExample_combinatoricsRoute

end AAT.AG
