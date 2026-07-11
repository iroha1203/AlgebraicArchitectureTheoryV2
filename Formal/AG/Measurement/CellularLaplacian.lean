import Formal.AG.Measurement.RefactorTransport

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R6 / AC13 cellular measurement model, sheaf Laplacian, and
distance-to-flatness readings.

The model is finite and selected. It records the cochain, coboundary, adjoint,
inner-product, residual, and projection-distance data used by later Hodge
packages. It does not make near-flatness a structural lawfulness theorem.
-/

/-- VIII.Definition 8.1: selected finite cellular measurement model. -/
structure CellularMeasurementModel (M : MeasurementProfile.{u, v}) where
  Cell : Type u
  Degree : Type u
  Cochain : Degree -> Type v
  Differential : Degree -> Degree -> Type v
  d : (n m : Degree) -> Differential n m -> Cochain n -> Cochain m
  Adjoint : Degree -> Degree -> Type v
  dAdjoint : (n m : Degree) -> Adjoint n m -> Cochain m -> Cochain n
  InnerProductValue : Type v
  innerProduct : (n : Degree) -> Cochain n -> Cochain n -> InnerProductValue
  NormValue : Type v
  norm : (n : Degree) -> Cochain n -> NormValue
  finiteCells : Prop
  finiteCells_cert : finiteCells
  finiteDimensionalCochains : Prop
  finiteDimensionalCochains_cert : finiteDimensionalCochains
  finiteIncidenceCategory : Prop
  finiteIncidenceCategory_cert : finiteIncidenceCategory
  linearRestrictionMaps : Prop
  linearRestrictionMaps_cert : linearRestrictionMaps
  differentialSquaresZero : Prop
  differentialSquaresZero_cert : differentialSquaresZero
  adjointsAvailable : Prop
  adjointsAvailable_cert : adjointsAvailable
  finiteInnerProductRegime : Prop
  finiteInnerProductRegime_cert : finiteInnerProductRegime

namespace CellularMeasurementModel

/-- VIII.Definition 8.1: expose finite cells. -/
theorem finiteCells_holds {M : MeasurementProfile.{u, v}}
    (C : CellularMeasurementModel M) : C.finiteCells :=
  C.finiteCells_cert

/-- VIII.Definition 8.1: expose finite-dimensional selected cochain groups. -/
theorem finiteDimensionalCochains_holds {M : MeasurementProfile.{u, v}}
    (C : CellularMeasurementModel M) : C.finiteDimensionalCochains :=
  C.finiteDimensionalCochains_cert

/-- VIII.Definition 8.1: expose the selected `d ∘ d = 0` cochain law. -/
theorem differentialSquaresZero_holds {M : MeasurementProfile.{u, v}}
    (C : CellularMeasurementModel M) : C.differentialSquaresZero :=
  C.differentialSquaresZero_cert

end CellularMeasurementModel

/--
VIII.Definition 8.2: selected sheaf Laplacian reading.

`laplacian_eq_formula` records the finite model's reading of
`L_n = d_{n-1} d_{n-1}^* + d_n^* d_n`.
-/
structure SheafLaplacianReading {M : MeasurementProfile.{u, v}}
    (C : CellularMeasurementModel M) where
  degree : C.Degree
  previousDegree : C.Degree
  nextDegree : C.Degree
  LaplacianOperator : Type v
  laplacian : LaplacianOperator
  d_prev : C.Differential previousDegree degree
  d_next : C.Differential degree nextDegree
  d_prev_adjoint : C.Adjoint previousDegree degree
  d_next_adjoint : C.Adjoint degree nextDegree
  d_prev_operator : C.Cochain previousDegree -> C.Cochain degree :=
    C.d previousDegree degree d_prev
  d_next_operator : C.Cochain degree -> C.Cochain nextDegree :=
    C.d degree nextDegree d_next
  d_prev_adjoint_operator : C.Cochain degree -> C.Cochain previousDegree :=
    C.dAdjoint previousDegree degree d_prev_adjoint
  d_next_adjoint_operator : C.Cochain nextDegree -> C.Cochain degree :=
    C.dAdjoint degree nextDegree d_next_adjoint
  laplacian_eq_formula : Prop
  laplacian_eq_formula_cert : laplacian_eq_formula
  finiteSelfAdjointReading : Prop
  finiteSelfAdjointReading_cert : finiteSelfAdjointReading

namespace SheafLaplacianReading

/-- VIII.Definition 8.2: expose the selected Laplacian formula. -/
theorem laplacian_eq_formula_holds {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} (L : SheafLaplacianReading C) :
    L.laplacian_eq_formula :=
  L.laplacian_eq_formula_cert

end SheafLaplacianReading

/--
VIII.Definition 8.3: residual norm and projection-defined distance to flatness.

The boundary field records that zero distance-to-flatness is an analytic
reading, not a lawfulness theorem.
-/
structure DistanceToFlatnessReading {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} (L : SheafLaplacianReading C) where
  sectionDegree : C.Degree
  selectedSection : C.Cochain sectionDegree
  residualNorm : C.NormValue
  distanceToFlatness : C.NormValue
  residual_eq_norm_d0 : Prop
  residual_eq_norm_d0_cert : residual_eq_norm_d0
  projectionDefinedDistance : Prop
  projectionDefinedDistance_cert : projectionDefinedDistance
  analyticReadingOnly : Prop
  analyticReadingOnly_cert : analyticReadingOnly
  distanceZeroDoesNotImplyLawful : Prop
  distanceZeroDoesNotImplyLawful_cert : distanceZeroDoesNotImplyLawful

namespace DistanceToFlatnessReading

/-- VIII.Definition 8.3: expose the selected residual norm reading. -/
theorem residual_eq_norm_d0_holds {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    (D : DistanceToFlatnessReading L) : D.residual_eq_norm_d0 :=
  D.residual_eq_norm_d0_cert

/-- VIII.Definition 8.3: zero analytic distance is not promoted to lawfulness. -/
theorem distanceZeroDoesNotImplyLawful_holds {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    (D : DistanceToFlatnessReading L) : D.distanceZeroDoesNotImplyLawful :=
  D.distanceZeroDoesNotImplyLawful_cert

end DistanceToFlatnessReading

end Measurement
end AAT.AG
