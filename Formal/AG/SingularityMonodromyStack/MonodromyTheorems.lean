import Formal.AG.SingularityMonodromyStack.Monodromy

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v y z

/--
VI.定理10.5: selected transport descent problem.

The detecting-axis condition is explicit data: all selected square monodromy
defects vanish exactly when the selected free transport kills the relators of
the R5 presentation. The theorem below then applies the R5 quotient universal
property.
-/
structure TransportDescentProblem {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
    {M : MonodromyAction.{u, v, y, z} Pi}
    {K : PresentationTwoComplex.{u, v, y, z} H}
    (T : Pi.FreeTransport) where
  Square : Type z
  [squareFintype : Fintype Square]
  measured : Square -> MeasuredSquareMonodromy M K
  relationBoundaryZero : Prop :=
    ∀ square : Square, ∀ axis : (measured square).Axis,
      (measured square).mu axis = 0
  relationBoundaryZero_iff_sendsRelators :
    relationBoundaryZero ↔ Pi.SendsRelatorsToIdentity T

attribute [instance] TransportDescentProblem.squareFintype

namespace TransportDescentProblem

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
variable {M : MonodromyAction.{u, v, y, z} Pi}
variable {K : PresentationTwoComplex.{u, v, y, z} H}
variable {T : Pi.FreeTransport}

/--
VI.定理10.5: transport descends to the presented quotient exactly when all
selected generator-boundary monodromy defects vanish.
-/
theorem transport_descent_criterion
    (D : TransportDescentProblem.{u, v, y, z} (Pi := Pi) (M := M) (K := K) T) :
    D.relationBoundaryZero ↔
      ∃ Q : Pi.QuotientTransport, Pi.FactorsThroughQuotient T Q :=
  D.relationBoundaryZero_iff_sendsRelators.trans (Pi.quotientUniversalProperty T)

/-- VI.定理10.5: zero selected boundary defects imply quotient factorization. -/
theorem factorsThroughQuotient_of_relationBoundaryZero
    (D : TransportDescentProblem.{u, v, y, z} (Pi := Pi) (M := M) (K := K) T)
    (hzero : D.relationBoundaryZero) :
    ∃ Q : Pi.QuotientTransport, Pi.FactorsThroughQuotient T Q :=
  (D.transport_descent_criterion).mp hzero

/-- VI.定理10.5: quotient factorization forces zero selected boundary defects. -/
theorem relationBoundaryZero_of_factorsThroughQuotient
    (D : TransportDescentProblem.{u, v, y, z} (Pi := Pi) (M := M) (K := K) T)
    (hdescends : ∃ Q : Pi.QuotientTransport, Pi.FactorsThroughQuotient T Q) :
    D.relationBoundaryZero :=
  (D.transport_descent_criterion).mpr hdescends

end TransportDescentProblem

/--
VI.定理10.7: selected square filling predicate for one measured square.

This package records the selected axis exactness assumption used by the theorem:
any selected filling must make the measured monodromy defect zero on the chosen
axis.
-/
structure SquareMonodromyFillingProblem {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
    {M : MonodromyAction.{u, v, y, z} Pi}
    {K : PresentationTwoComplex.{u, v, y, z} H}
    (Q : MeasuredSquareMonodromy.{u, v, y, z} M K) where
  axis : Q.Axis
  SelectedAxisFilling : Prop
  filling_implies_mu_zero : SelectedAxisFilling -> Q.mu axis = 0

namespace SquareMonodromyFillingProblem

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
variable {M : MonodromyAction.{u, v, y, z} Pi}
variable {K : PresentationTwoComplex.{u, v, y, z} H}
variable {Q : MeasuredSquareMonodromy.{u, v, y, z} M K}

/--
VI.定理10.7: nonzero selected square monodromy refutes selected axis filling.
-/
theorem squareMonodromy_nonfillability
    (F : SquareMonodromyFillingProblem.{u, v, y, z} Q)
    (hmu : Q.mu F.axis ≠ 0) :
    ¬ F.SelectedAxisFilling := by
  intro hfill
  exact hmu (F.filling_implies_mu_zero hfill)

end SquareMonodromyFillingProblem

/--
VI.定理11.1: selected hidden architecture debt reading.

Endpoint equivalence alone does not create debt. The bridge below records the
bounded reading used by the theorem: endpoint-equivalent loops with nonidentity
obstruction monodromy are read as hidden architecture debt.
-/
structure HiddenArchitectureDebtReading {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
    (M : MonodromyAction.{u, v, y, z} Pi)
    (gamma : Pi.Pi1) where
  EndpointEquivalentLoop : Prop
  HiddenArchitectureDebt : Prop
  debt_of_endpoint_nonidentity :
    EndpointEquivalentLoop -> M.MonodromyDebt gamma -> HiddenArchitectureDebt

namespace HiddenArchitectureDebtReading

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
variable {M : MonodromyAction.{u, v, y, z} Pi}
variable {gamma : Pi.Pi1}

/--
VI.定理11.1: endpoint-equivalent loop plus nonidentity obstruction monodromy
gives selected hidden architecture debt.
-/
theorem monodromy_debt_theorem
    (D : HiddenArchitectureDebtReading.{u, v, y, z} M gamma)
    (hendpoint : D.EndpointEquivalentLoop)
    (hdebt : M.MonodromyDebt gamma) :
    D.HiddenArchitectureDebt :=
  D.debt_of_endpoint_nonidentity hendpoint hdebt

/-- VI.定理11.1: nonidentity obstruction monodromy is the debt condition used. -/
theorem hiddenDebt_of_nonidentity_obstructionMonodromy
    (D : HiddenArchitectureDebtReading.{u, v, y, z} M gamma)
    (hendpoint : D.EndpointEquivalentLoop)
    (hmon :
      M.obstructionMonodromy gamma ≠
        (CoefficientAutomorphism.id M.coefficient).obAut) :
    D.HiddenArchitectureDebt :=
  D.monodromy_debt_theorem hendpoint hmon

end HiddenArchitectureDebtReading

end SingularityMonodromyStack
end AAT.AG
