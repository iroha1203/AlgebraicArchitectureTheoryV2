import Formal.Arch.Evolution.ArchitecturePath

/-!
Reverse-import theorem packages from ArchSig structural readings.

These declarations abstract review patterns that are visible in ArchSig output
back into bounded AAT theorem surfaces.  They are intentionally assumption
relative: each theorem exposes the exact witness, trajectory, or boundary
evidence needed before a tooling reading may be treated as reflective.
-/

namespace Formal.Arch

universe u v w

namespace ReverseImportTheorems

/--
Boundary for a projection that forgets selected Atom axes.

The projection may preserve a coarse reading, but reflection back to structural
zero or obstruction absence is allowed only through explicit axis preservation
and witness-completeness assumptions.
-/
structure AxisForgettingProjectionBoundary where
  coarseReadingPreserved : Prop
  selectedAxisPreservation : Prop
  witnessCompleteness : Prop
  reflectsStructuralZero : Prop
  reflectsObstructionAbsence : Prop
  nonConclusions : Prop
  zeroReflectionRequiresAxisWitness :
    reflectsStructuralZero -> selectedAxisPreservation ∧ witnessCompleteness
  obstructionReflectionRequiresAxisWitness :
    reflectsObstructionAbsence -> selectedAxisPreservation ∧ witnessCompleteness

namespace AxisForgettingProjectionBoundary

/-- The projection has the assumptions needed for reflection only when both selected facts hold. -/
def HasReflectionWitnesses (boundary : AxisForgettingProjectionBoundary) : Prop :=
  boundary.selectedAxisPreservation ∧ boundary.witnessCompleteness

/--
If the required axis-preservation / witness-completeness package is missing,
structural-zero reflection is blocked.
-/
theorem not_zeroReflecting_of_missingAxisWitness
    (boundary : AxisForgettingProjectionBoundary)
    (hMissing : ¬ boundary.HasReflectionWitnesses) :
    ¬ boundary.reflectsStructuralZero := by
  intro hReflects
  exact hMissing (boundary.zeroReflectionRequiresAxisWitness hReflects)

/--
If the required axis-preservation / witness-completeness package is missing,
obstruction-absence reflection is blocked.
-/
theorem not_obstructionReflecting_of_missingAxisWitness
    (boundary : AxisForgettingProjectionBoundary)
    (hMissing : ¬ boundary.HasReflectionWitnesses) :
    ¬ boundary.reflectsObstructionAbsence := by
  intro hReflects
  exact hMissing (boundary.obstructionReflectionRequiresAxisWitness hReflects)

/-- The non-conclusion clause remains part of the projection boundary. -/
theorem records_nonConclusions
    (boundary : AxisForgettingProjectionBoundary) :
    boundary.nonConclusions -> boundary.nonConclusions :=
  id

end AxisForgettingProjectionBoundary

/--
A selected signature trajectory is any path observation used as a signature
coordinate.  If generated homotopy preserves that observation, trajectory
disagreement refutes selected homotopy.
-/
theorem selectedSignatureTrajectory_refutesPathHomotopy
    {State : Type u} {Step : State -> State -> Type v} {α : Type w}
    {IndependentSquare :
      (W X Y Z : State) ->
        Step W X -> Step X Z -> Step W Y -> Step Y Z -> Prop}
    {SameExternalContract :
      (X Y : State) -> Step X Y -> Step X Y -> Prop}
    {RepairFill :
      (X Y : State) -> ArchitecturePath Step X Y ->
        ArchitecturePath Step X Y -> Prop}
    {Obs : {X Y : State} -> ArchitecturePath Step X Y -> α}
    (hIndependentSquare :
      ∀ {W X Y Z T : State}
        (a : Step W X) (b : Step X Z) (c : Step W Y) (d : Step Y Z)
        (rest : ArchitecturePath Step Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : State} (s t : Step X Y)
        (rest : ArchitecturePath Step Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : State} {p q : ArchitecturePath Step X Y},
        RepairFill X Y p q ->
          (suffix : ArchitecturePath Step Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : State} (step : Step X Y)
        {p q : ArchitecturePath Step Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {X Y : State} {p q : ArchitecturePath Step X Y}
    (hTrajectoryDiff : Obs p ≠ Obs q) :
    ¬ ArchitecturePath.PathHomotopy (Step := Step)
        IndependentSquare SameExternalContract RepairFill p q := by
  intro hHomotopy
  exact hTrajectoryDiff
    (ArchitecturePath.PathHomotopy.observation_eq
      (Step := Step) (Obs := Obs)
      hIndependentSquare hSameExternalContract hRepairFill hConsContext
      hHomotopy)

/--
Boundary for reading a bridge edge across a candidate split.

The theorem package does not claim that every bridge transfers an obstruction.
It says that when a bridge carries shared support and the selected obstruction
is supported on that bridge, split readiness must be backed by filler, lifting,
or boundary-operation evidence.
-/
structure BridgeEdgeSplitObstructionBoundary where
  bridgeCarriesSharedAtomSupport : Prop
  selectedObstructionSupportedOnBridge : Prop
  fillerEvidence : Prop
  liftingEvidence : Prop
  boundaryOperationEvidence : Prop
  splitReadyWithoutTransfer : Prop
  nonConclusions : Prop
  splitReadinessRequiresBoundaryEvidence :
    bridgeCarriesSharedAtomSupport ->
      selectedObstructionSupportedOnBridge ->
        splitReadyWithoutTransfer ->
          fillerEvidence ∨ liftingEvidence ∨ boundaryOperationEvidence

namespace BridgeEdgeSplitObstructionBoundary

/-- Evidence that can block transfer across the selected split boundary. -/
def HasBoundaryEvidence
    (boundary : BridgeEdgeSplitObstructionBoundary) : Prop :=
  boundary.fillerEvidence ∨ boundary.liftingEvidence ∨
    boundary.boundaryOperationEvidence

/--
Without filler, lifting, or boundary-operation evidence, the selected split is
not ready under the bridge-support assumptions.
-/
theorem not_splitReadyWithoutTransfer_of_missingBoundaryEvidence
    (boundary : BridgeEdgeSplitObstructionBoundary)
    (hBridge : boundary.bridgeCarriesSharedAtomSupport)
    (hSupported : boundary.selectedObstructionSupportedOnBridge)
    (hMissing : ¬ boundary.HasBoundaryEvidence) :
    ¬ boundary.splitReadyWithoutTransfer := by
  intro hReady
  exact hMissing
    (boundary.splitReadinessRequiresBoundaryEvidence hBridge hSupported hReady)

/-- Transfer-risk reports keep both bridge assumptions and the missing-evidence boundary explicit. -/
def RecordsTransferRisk
    (boundary : BridgeEdgeSplitObstructionBoundary) : Prop :=
  boundary.bridgeCarriesSharedAtomSupport ∧
    boundary.selectedObstructionSupportedOnBridge ∧
      ¬ boundary.HasBoundaryEvidence ∧
        boundary.nonConclusions

/-- The transfer-risk package is exactly the conjunction of the recorded fields. -/
theorem recordsTransferRisk_of_missingBoundaryEvidence
    (boundary : BridgeEdgeSplitObstructionBoundary)
    (hBridge : boundary.bridgeCarriesSharedAtomSupport)
    (hSupported : boundary.selectedObstructionSupportedOnBridge)
    (hMissing : ¬ boundary.HasBoundaryEvidence)
    (hNonConclusion : boundary.nonConclusions) :
    boundary.RecordsTransferRisk := by
  exact ⟨hBridge, hSupported, hMissing, hNonConclusion⟩

end BridgeEdgeSplitObstructionBoundary

end ReverseImportTheorems

end Formal.Arch
