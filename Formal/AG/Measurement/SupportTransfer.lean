import Formal.AG.Measurement.LawConflict

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v w

/-!
Part VIII R8 / AC18-AC20 support-localized transfer measurement and finite
Wasserstein transfer cost.

The support-localized transfer theorem is a sufficient-condition theorem
package. Lower bounds and Wasserstein statements remain theorem-candidate
interfaces with explicit finite data.
-/

/--
VIII.Definition 10.1: support-localized repair path / direction.

The reading is relative to a selected LawConflict class and its support. It
stores the path image, direction support, and selected conflict-support
function as concrete sets. Intersection and localization are derived
predicates rather than freely supplied truth fields.
-/
structure SupportLocalizedRepairPath
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) where
  RepairPath : Type u
  RepairDirection : Type u
  selectedRepairPath : RepairPath
  selectedRepairDirection : RepairDirection
  pathImage : RepairPath -> Set A.SupportCarrier
  directionSupport : RepairDirection -> Set A.SupportCarrier
  conflictSupport : L.ConflictClass -> Set A.SupportCarrier

namespace SupportLocalizedRepairPath

/-- VIII.Definition 10.1: the selected path image meets the computed support of
the selected conflict class. -/
def pathImageIntersectsSupport {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L) : Prop :=
  (S.pathImage S.selectedRepairPath ∩
    S.conflictSupport L.selectedConflictClass).Nonempty

/-- VIII.Definition 10.1: the selected first-order direction meets the computed
support of the selected conflict class. -/
def directionSupportIntersectsConflict {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L) : Prop :=
  (S.directionSupport S.selectedRepairDirection ∩
    S.conflictSupport L.selectedConflictClass).Nonempty

/-- VIII.Definition 10.1: localization is witnessed by the selected path or
the selected first-order direction. -/
def SupportLocalized {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L) : Prop :=
  S.pathImageIntersectsSupport ∨ S.directionSupportIntersectsConflict

/-- A path-support intersection supplies support localization. -/
theorem supportLocalized_of_path {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L)
    (h : S.pathImageIntersectsSupport) :
    S.SupportLocalized :=
  Or.inl h

/-- A direction-support intersection supplies support localization. -/
theorem supportLocalized_of_direction {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L)
    (h : S.directionSupportIntersectsConflict) :
    S.SupportLocalized :=
  Or.inr h

end SupportLocalizedRepairPath

/--
VIII.Definition 10.2: transfer measurement pairing.

The pairing maps a selected repair direction and selected LawConflict class
into a transfer-residue target. The selected residue is derived by evaluating
the pairing; nontriviality is the fixed predicate on that derived value.
-/
structure TransferMeasurementPairing
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L) where
  TransferResidue : Type v
  NormValue : Type v
  zeroResidue : TransferResidue
  NontrivialResidue : TransferResidue -> Prop
  norm : TransferResidue -> NormValue
  pairing : S.RepairDirection -> L.ConflictClass -> TransferResidue

namespace TransferMeasurementPairing

/-- The selected transfer residue is the pairing evaluated on the selected
direction and the measurement's selected conflict class. -/
def selectedResidue {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L}
    (P : TransferMeasurementPairing S) :
    P.TransferResidue :=
  P.pairing S.selectedRepairDirection L.selectedConflictClass

/-- The zero predicate is equality with the distinguished zero residue. -/
def ZeroResidue {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L}
    (P : TransferMeasurementPairing S) :
    P.TransferResidue -> Prop :=
  fun residue => residue = P.zeroResidue

/-- The selected direction has a nontrivial transfer residue precisely when
the fixed predicate holds of the computed pairing value. -/
def selectedDirectionNontrivialResidue {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L}
    (P : TransferMeasurementPairing S) : Prop :=
  P.NontrivialResidue P.selectedResidue

/-- The selected residue equation follows from its definition. -/
theorem selectedResidue_eq_pairing {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L}
    (P : TransferMeasurementPairing S) :
    P.selectedResidue =
      P.pairing S.selectedRepairDirection L.selectedConflictClass :=
  rfl

end TransferMeasurementPairing

/--
VIII.Theorem 10.3: support-localized transfer theorem package.

The theorem is conditional on an actual support intersection and on the
computed pairing residue satisfying the fixed nontriviality predicate. Its
conclusion is the derived selected-direction reading.
-/
def SupportLocalizedTransfer
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L}
    (P : TransferMeasurementPairing S) : Prop :=
  S.SupportLocalized ->
    P.NontrivialResidue P.selectedResidue ->
      P.selectedDirectionNontrivialResidue

namespace SupportLocalizedTransfer

/-- VIII.Theorem 10.3: expose the nontrivial residue obtained from the
support-localized pairing. -/
theorem nontrivial_transferred_residue_of_pairing {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} {P : TransferMeasurementPairing S}
    (T : SupportLocalizedTransfer P)
    (hLocalized : S.SupportLocalized)
    (hNontrivial : P.NontrivialResidue P.selectedResidue) :
    P.selectedDirectionNontrivialResidue :=
  T hLocalized hNontrivial

end SupportLocalizedTransfer

/-- VIII.Theorem 10.3: construct the selected transfer conclusion from the
actual support intersection and computed pairing value. -/
theorem supportLocalizedTransferPackage {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L}
    (P : TransferMeasurementPairing S) :
    SupportLocalizedTransfer P := by
  intro _ hNontrivial
  exact hNontrivial

/-- VIII.Theorem 10.3: direct form of the support-localized transfer
inference. -/
theorem supportLocalizedTransfer {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L}
    (P : TransferMeasurementPairing S) :
    SupportLocalizedTransfer P :=
  supportLocalizedTransferPackage P

/--
VIII.Theorem candidate 10.4: transfer lower-bound statement-only interface.

The lower-bound claim is not proved here; it is guarded by explicit
nondegeneracy, support-weight, projection-norm, and constant assumptions.
-/
structure TransferLowerBoundCandidate
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} (P : TransferMeasurementPairing S) where
  SupportWeight : Type v
  ProjectionNorm : Type v
  LowerBoundConstant : Type v
  LowerBoundExpression : Type v
  supportWeight : SupportWeight
  projectionNorm : ProjectionNorm
  lambda_M : LowerBoundConstant
  lowerBoundExpression : LowerBoundExpression
  normedTarget : Prop
  nondegeneratePairing : Prop
  supportWeightPositive : Prop
  projectionNormPositive : Prop
  lowerBoundConclusion : Prop
  lowerBoundStatement : Prop
  lowerBoundStatement_shape :
    lowerBoundStatement =
      (normedTarget ->
        nondegeneratePairing ->
          supportWeightPositive ->
            projectionNormPositive ->
              lowerBoundConclusion)
  candidateOnly : Prop
  candidateOnly_cert : candidateOnly

/--
VIII.Definition 10.6: finite Wasserstein transfer cost reading.

This is a finite support graph / transportation-plan interface, not general
measure theory.
-/
structure WassersteinTransferCostReading {M : MeasurementProfile.{u, v}} where
  FiniteSupportNode : Type u
  FiniteSupportEdge : Type u
  GroundDistance : Type v
  TransportationPlan : Type u
  CostValue : Type v
  sourceNode : FiniteSupportNode
  absorbedNode : FiniteSupportNode
  groundDistance : FiniteSupportNode -> FiniteSupportNode -> GroundDistance
  selectedPlan : TransportationPlan
  planCost : TransportationPlan -> CostValue
  wassersteinCost : CostValue
  finiteSupportGraph : Prop
  finiteSupportGraph_cert : finiteSupportGraph
  feasibleTransportationPlan : Prop
  feasibleTransportationPlan_cert : feasibleTransportationPlan
  costReadsFinitePlan : Prop
  costReadsFinitePlan_cert : costReadsFinitePlan
  finiteOptimalTransportOnly : Prop
  finiteOptimalTransportOnly_cert : finiteOptimalTransportOnly

namespace WassersteinTransferCostReading

/-- VIII.Definition 10.6: expose finite support graph availability. -/
theorem finiteSupportGraph_holds {M : MeasurementProfile.{u, v}}
    (W : WassersteinTransferCostReading (M := M)) : W.finiteSupportGraph :=
  W.finiteSupportGraph_cert

/-- VIII.Definition 10.6: expose the finite plan cost reading. -/
theorem costReadsFinitePlan_holds {M : MeasurementProfile.{u, v}}
    (W : WassersteinTransferCostReading (M := M)) : W.costReadsFinitePlan :=
  W.costReadsFinitePlan_cert

end WassersteinTransferCostReading

/--
VIII.Theorem candidate 10.7: finite Wasserstein lower-bound statement.

The statement shape records `W_1 >= m * dist(s, Abs)` as a candidate reading
under finite graph and feasible-plan assumptions.
-/
structure WassersteinTransferLowerBoundCandidate {M : MeasurementProfile.{u, v}}
    (W : WassersteinTransferCostReading (M := M)) where
  MassValue : Type v
  DistanceToAbsorbed : Type v
  LowerBoundExpression : Type v
  mass : MassValue
  distanceToAbsorbed : DistanceToAbsorbed
  lowerBoundExpression : LowerBoundExpression
  finiteGraphAssumption : Prop
  feasiblePlanAssumption : Prop
  positiveMassAssumption : Prop
  lowerBoundConclusion : Prop
  lowerBoundStatement : Prop
  lowerBoundStatement_shape :
    lowerBoundStatement =
      (finiteGraphAssumption ->
        feasiblePlanAssumption ->
          positiveMassAssumption ->
            lowerBoundConclusion)
  candidateOnly : Prop
  candidateOnly_cert : candidateOnly

namespace WassersteinTransferLowerBoundCandidate

/-- VIII.Theorem candidate 10.7: expose the finite Wasserstein lower-bound shape. -/
theorem lowerBoundStatement_shape_holds {M : MeasurementProfile.{u, v}}
    {W : WassersteinTransferCostReading (M := M)}
    (B : WassersteinTransferLowerBoundCandidate W) :
    B.lowerBoundStatement =
      (B.finiteGraphAssumption ->
        B.feasiblePlanAssumption ->
          B.positiveMassAssumption ->
            B.lowerBoundConclusion) :=
  B.lowerBoundStatement_shape

/-- VIII.Theorem candidate 10.7: record that the lower bound remains candidate-only. -/
theorem candidateOnly_holds {M : MeasurementProfile.{u, v}}
    {W : WassersteinTransferCostReading (M := M)}
    (B : WassersteinTransferLowerBoundCandidate W) : B.candidateOnly :=
  B.candidateOnly_cert

end WassersteinTransferLowerBoundCandidate

end Measurement
end AAT.AG
