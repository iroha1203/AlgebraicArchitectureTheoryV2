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
records intersection with the selected conflict support, not global repair
coverage.
-/
structure SupportLocalizedRepairPath
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) where
  RepairPath : Type u
  RepairDirection : Type u
  DirectionSupport : Type u
  selectedRepairPath : RepairPath
  selectedRepairDirection : RepairDirection
  directionSupport : RepairDirection -> DirectionSupport
  directionHitsConflictSupport : RepairDirection -> L.ConflictClass -> Prop
  selectedConflictClass : L.ConflictClass
  selectedClass_eq_lawConflictClass :
    selectedConflictClass = L.selectedConflictClass
  pathImageIntersectsSupport : Prop
  pathImageIntersectsSupport_cert : pathImageIntersectsSupport
  directionSupportIntersectsConflict : Prop
  directionSupportIntersectsConflict_cert : directionSupportIntersectsConflict
  supportLocalizedOnly : Prop
  supportLocalizedOnly_cert : supportLocalizedOnly

namespace SupportLocalizedRepairPath

/-- VIII.Definition 10.1: expose selected path / support intersection. -/
theorem pathImageIntersectsSupport_holds {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L) : S.pathImageIntersectsSupport :=
  S.pathImageIntersectsSupport_cert

/-- VIII.Definition 10.1: expose selected direction / conflict-support intersection. -/
theorem directionSupportIntersectsConflict_holds {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (S : SupportLocalizedRepairPath L) : S.directionSupportIntersectsConflict :=
  S.directionSupportIntersectsConflict_cert

end SupportLocalizedRepairPath

/--
VIII.Definition 10.2: transfer measurement pairing.

The pairing maps a selected repair direction and selected LawConflict class
into a transfer-residue target with explicit zero / nontrivial predicates.
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
  ZeroResidue : TransferResidue -> Prop
  NontrivialResidue : TransferResidue -> Prop
  norm : TransferResidue -> NormValue
  pairing : S.RepairDirection -> L.ConflictClass -> TransferResidue
  selectedResidue : TransferResidue
  selectedResidue_eq_pairing :
    selectedResidue = pairing S.selectedRepairDirection S.selectedConflictClass
  selectedDirectionNontrivialResidue : Prop
  selectedDirectionNontrivialResidue_cert :
    selectedDirectionNontrivialResidue
  nontrivialPairingSufficient : Prop
  nontrivialPairingSufficient_shape :
    nontrivialPairingSufficient =
      (NontrivialResidue (pairing S.selectedRepairDirection S.selectedConflictClass) ->
        selectedDirectionNontrivialResidue)
  nontrivialPairingSufficient_cert : nontrivialPairingSufficient
  detectingPairingRequiredForNecessity : Prop
  detectingPairingRequiredForNecessity_cert : detectingPairingRequiredForNecessity

namespace TransferMeasurementPairing

/-- VIII.Definition 10.2: expose the selected pairing residue equation. -/
theorem selectedResidue_eq_pairing_holds {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} (P : TransferMeasurementPairing S) :
    P.selectedResidue = P.pairing S.selectedRepairDirection S.selectedConflictClass :=
  P.selectedResidue_eq_pairing

/-- VIII.Definition 10.2: record that necessity requires an extra detecting assumption. -/
theorem detectingPairingRequiredForNecessity_holds {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} (P : TransferMeasurementPairing S) :
    P.detectingPairingRequiredForNecessity :=
  P.detectingPairingRequiredForNecessity_cert

end TransferMeasurementPairing

/--
VIII.Theorem 10.3: support-localized transfer theorem package.

The theorem is one-way: a nontrivial selected pairing residue is sufficient to
mark the selected repair direction as having a nontrivial transferred residue.
-/
structure SupportLocalizedTransfer
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} (P : TransferMeasurementPairing S) where
  nontrivial_pairing_implies_transferred_residue :
    P.NontrivialResidue (P.pairing S.selectedRepairDirection S.selectedConflictClass) ->
      P.selectedDirectionNontrivialResidue

namespace SupportLocalizedTransfer

/-- VIII.Theorem 10.3: expose the sufficient-condition transfer implication. -/
theorem nontrivial_transferred_residue_of_pairing {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} {P : TransferMeasurementPairing S}
    (T : SupportLocalizedTransfer P)
    (h : P.NontrivialResidue (P.pairing S.selectedRepairDirection S.selectedConflictClass)) :
    P.selectedDirectionNontrivialResidue :=
  T.nontrivial_pairing_implies_transferred_residue h

end SupportLocalizedTransfer

/-- VIII.Theorem 10.3: construct the selected transfer theorem package. -/
def supportLocalizedTransferPackage {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} (P : TransferMeasurementPairing S) :
    SupportLocalizedTransfer P where
  nontrivial_pairing_implies_transferred_residue :=
    P.nontrivialPairingSufficient_shape.mp P.nontrivialPairingSufficient_cert

/-- VIII.Theorem 10.3: selected support-localized transfer exists under explicit data. -/
theorem supportLocalizedTransfer {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R] {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    {S : SupportLocalizedRepairPath L} (P : TransferMeasurementPairing S) :
    Nonempty (SupportLocalizedTransfer P) :=
  ⟨supportLocalizedTransferPackage P⟩

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
