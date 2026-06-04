import Formal.Arch.Evolution.SFTField
import Formal.Arch.AAT.Operation
import Formal.Arch.Signature.SignatureLawfulness

namespace Formal.Arch

universe u v w q r s t m

/--
A selected AAT theorem-status package as it is exposed to SFT.

The record keeps theorem evidence, measured-zero evidence, unmeasured-axis
boundaries, tooling/report boundaries, and non-conclusions separate. SFT may
read this package as a local premise, but the package is not itself a forecast
correctness certificate.
-/
structure AATTheoremStatus where
  theoremPackage : Prop
  measuredZeroEvidence : Prop
  theoremBoundary : Prop
  unmeasuredAxisBoundary : Prop
  toolingBoundary : Prop
  nonConclusions : Prop

namespace AATTheoremStatus

/-- The selected AAT theorem package is available as theorem-status evidence. -/
def RecordsTheoremPackage (status : AATTheoremStatus) : Prop :=
  status.theoremPackage

/-- Selected measured-zero evidence remains explicit. -/
def RecordsMeasuredZeroEvidence (status : AATTheoremStatus) : Prop :=
  status.measuredZeroEvidence

/-- The AAT theorem boundary remains explicit. -/
def RecordsTheoremBoundary (status : AATTheoremStatus) : Prop :=
  status.theoremBoundary

/-- Unmeasured axes remain explicit rather than silently safe. -/
def RecordsUnmeasuredAxisBoundary (status : AATTheoremStatus) : Prop :=
  status.unmeasuredAxisBoundary

/-- Tooling/report assumptions remain boundary data, not stronger theorem status. -/
def RecordsToolingBoundary (status : AATTheoremStatus) : Prop :=
  status.toolingBoundary

/-- AAT-level non-conclusions remain explicit. -/
def RecordsNonConclusions (status : AATTheoremStatus) : Prop :=
  status.nonConclusions

/--
Read the existing Signature-integrated zero-curvature theorem package as an
AAT theorem-status item for SFT interface purposes.
-/
noncomputable def ofArchitectureZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (measuredZeroEvidence theoremBoundary unmeasuredAxisBoundary
      toolingBoundary nonConclusions : Prop) :
    AATTheoremStatus where
  theoremPackage := ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X
  measuredZeroEvidence := measuredZeroEvidence
  theoremBoundary := theoremBoundary
  unmeasuredAxisBoundary := unmeasuredAxisBoundary
  toolingBoundary := toolingBoundary
  nonConclusions := nonConclusions

/-- The zero-curvature constructor exposes the stored theorem package. -/
theorem records_theoremPackage_of_architectureZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    {measuredZeroEvidence theoremBoundary unmeasuredAxisBoundary
      toolingBoundary nonConclusions : Prop}
    (hPackage : ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X) :
    (ofArchitectureZeroCurvatureTheoremPackage X measuredZeroEvidence
      theoremBoundary unmeasuredAxisBoundary toolingBoundary
      nonConclusions).RecordsTheoremPackage :=
  hPackage

end AATTheoremStatus

/--
SFT reads an Atom-axiomatized `AATCore` as local algebra.

This is the new Atom-rooted boundary.  It starts from an `AtomAxiomSystem` and
an `AATCore system`, not from an observation or presentation wrapper.
-/
structure AATCoreLocalAlgebraForSFT
    {system : AtomAxiomSystem.{u, v}}
    (core : AAT.AATCore system) where
  usedAsLocalAlgebra : Prop
  usedAsLocalAlgebraEvidence : usedAsLocalAlgebra
  sftDoesNotRedefineAtoms : Prop
  sftDoesNotRedefineAtomsEvidence : sftDoesNotRedefineAtoms
  sftDoesNotRedefineAAT : Prop
  sftDoesNotRedefineAATEvidence : sftDoesNotRedefineAAT
  noForecastCorrectnessFromAATAlone : Prop
  noForecastCorrectnessFromAATAloneEvidence :
    noForecastCorrectnessFromAATAlone
  sftEventDoesNotCreateAtomsEvidence : system.noSFTEventCreatesAtoms
  nonConclusions : Prop

namespace AATCoreLocalAlgebraForSFT

variable {system : AtomAxiomSystem.{u, v}}
variable {core : AAT.AATCore system}

/-- SFT uses the selected `AATCore` as local algebra. -/
theorem reads_aatcore_as_local_algebra
    (boundary : AATCoreLocalAlgebraForSFT core) :
    boundary.usedAsLocalAlgebra :=
  boundary.usedAsLocalAlgebraEvidence

/-- SFT does not redefine Atom when consuming `AATCore`. -/
theorem sft_does_not_redefine_atoms
    (boundary : AATCoreLocalAlgebraForSFT core) :
    boundary.sftDoesNotRedefineAtoms :=
  boundary.sftDoesNotRedefineAtomsEvidence

/-- SFT does not redefine AAT when consuming `AATCore`. -/
theorem sft_does_not_redefine_aat
    (boundary : AATCoreLocalAlgebraForSFT core) :
    boundary.sftDoesNotRedefineAAT :=
  boundary.sftDoesNotRedefineAATEvidence

/-- The `AATCore` premise alone does not prove forecast correctness. -/
theorem aatcore_alone_does_not_prove_forecast_correctness
    (boundary : AATCoreLocalAlgebraForSFT core) :
    boundary.noForecastCorrectnessFromAATAlone :=
  boundary.noForecastCorrectnessFromAATAloneEvidence

/-- The consumed `AATCore` remains observation-independent. -/
theorem core_independent_of_observation
    (_boundary : AATCoreLocalAlgebraForSFT core) :
    core.noObservationDependency :=
  core.independent_of_observation

/-- SFT events do not create atoms in the root axiom system. -/
theorem sft_event_does_not_create_atoms
    (boundary : AATCoreLocalAlgebraForSFT core) :
    system.noSFTEventCreatesAtoms :=
  boundary.sftEventDoesNotCreateAtomsEvidence

end AATCoreLocalAlgebraForSFT

/--
Atom-level delta between two selected Atom-axiomatized AAT cores.

The delta records source/target/preserved atom readings.  It does not create
atoms; all atoms still come from the root axiom system.
-/
structure AATCoreAtomDelta
    {system : AtomAxiomSystem.{u, v}}
    (source target : AAT.AATCore system) where
  sourceAtom : system.Atom -> Prop
  targetAtom : system.Atom -> Prop
  preservedAtom : system.Atom -> Prop
  transformedAtom : system.Atom -> system.Atom -> Prop
  sourceAtomPrimitive :
    ∀ atom, sourceAtom atom -> system.Primitive atom
  targetAtomPrimitive :
    ∀ atom, targetAtom atom -> system.Primitive atom
  preservedAtomOnSource :
    ∀ atom, preservedAtom atom -> sourceAtom atom
  preservedAtomOnTarget :
    ∀ atom, preservedAtom atom -> targetAtom atom
  transitionBoundary : Prop
  doesNotCreateAtomsEvidence : system.noSFTEventCreatesAtoms
  nonConclusions : Prop

namespace AATCoreAtomDelta

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}

/-- Source-side atoms in the delta are primitive root atoms. -/
theorem source_atom_primitive
    (delta : AATCoreAtomDelta source target)
    {atom : system.Atom}
    (hAtom : delta.sourceAtom atom) :
    system.Primitive atom :=
  delta.sourceAtomPrimitive atom hAtom

/-- Target-side atoms in the delta are primitive root atoms. -/
theorem target_atom_primitive
    (delta : AATCoreAtomDelta source target)
    {atom : system.Atom}
    (hAtom : delta.targetAtom atom) :
    system.Primitive atom :=
  delta.targetAtomPrimitive atom hAtom

/-- Preserved atoms are present on both source and target readings. -/
theorem preserved_atom_on_source_and_target
    (delta : AATCoreAtomDelta source target)
    {atom : system.Atom}
    (hPreserved : delta.preservedAtom atom) :
    delta.sourceAtom atom ∧ delta.targetAtom atom :=
  ⟨delta.preservedAtomOnSource atom hPreserved,
    delta.preservedAtomOnTarget atom hPreserved⟩

/-- Atom deltas do not create atom existence. -/
theorem delta_does_not_create_atoms
    (delta : AATCoreAtomDelta source target) :
    system.noSFTEventCreatesAtoms :=
  delta.doesNotCreateAtomsEvidence

end AATCoreAtomDelta

/--
Semantic delta over an `AATCoreAtomDelta`.

The semantic predicate is an SFT-side reading over existing atoms.  It is not a
new atom constructor.
-/
structure AATCoreSemanticDelta
    {system : AtomAxiomSystem.{u, v}}
    {source target : AAT.AATCore system}
    (delta : AATCoreAtomDelta source target) where
  semanticAtom : system.Atom -> Prop
  sourceSemanticAtomsPrimitive :
    ∀ atom, delta.sourceAtom atom -> semanticAtom atom ->
      system.Primitive atom
  targetSemanticAtomsPrimitive :
    ∀ atom, delta.targetAtom atom -> semanticAtom atom ->
      system.Primitive atom
  semanticBoundary : Prop
  doesNotCreateAtomsEvidence : system.noSFTEventCreatesAtoms
  nonConclusions : Prop

namespace AATCoreSemanticDelta

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}
variable {delta : AATCoreAtomDelta source target}

/-- Source-side semantic atoms are still primitive root atoms. -/
theorem source_semantic_atom_primitive
    (semanticDelta : AATCoreSemanticDelta delta)
    {atom : system.Atom}
    (hSource : delta.sourceAtom atom)
    (hSemantic : semanticDelta.semanticAtom atom) :
    system.Primitive atom :=
  semanticDelta.sourceSemanticAtomsPrimitive atom hSource hSemantic

/-- Target-side semantic atoms are still primitive root atoms. -/
theorem target_semantic_atom_primitive
    (semanticDelta : AATCoreSemanticDelta delta)
    {atom : system.Atom}
    (hTarget : delta.targetAtom atom)
    (hSemantic : semanticDelta.semanticAtom atom) :
    system.Primitive atom :=
  semanticDelta.targetSemanticAtomsPrimitive atom hTarget hSemantic

/-- Semantic deltas do not create atom existence. -/
theorem semantic_delta_does_not_create_atoms
    (semanticDelta : AATCoreSemanticDelta delta) :
    system.noSFTEventCreatesAtoms :=
  semanticDelta.doesNotCreateAtomsEvidence

end AATCoreSemanticDelta

/--
Law-relative circuit delta between two selected `AATCore` readings.

Circuits remain law-relative obstruction witnesses over selected molecules.
The delta connects them to source/target cores without turning SFT transition
data into an atom constructor.
-/
structure AATCoreCircuitDelta
    {system : AtomAxiomSystem.{u, v}}
    (source target : AAT.AATCore system) where
  law : AAT.DesignLaw system
  molecule : AAT.Molecule system
  lawOnSource : source.laws law
  lawOnTarget : target.laws law
  moleculeOnSource : source.molecules molecule
  moleculeOnTarget : target.molecules molecule
  createdCircuit : AAT.ObstructionCircuit law molecule -> Prop
  removedCircuit : AAT.ObstructionCircuit law molecule -> Prop
  preservedCircuit : AAT.ObstructionCircuit law molecule -> Prop
  circuitBoundary : Prop
  doesNotCreateAtomsEvidence : system.noSFTEventCreatesAtoms
  nonConclusions : Prop

namespace AATCoreCircuitDelta

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}

/-- Source-side circuit molecules contain primitive root atoms. -/
theorem source_molecule_atom_primitive
    (delta : AATCoreCircuitDelta source target)
    {atom : system.Atom}
    (hAtom : delta.molecule.atoms atom) :
    system.Primitive atom :=
  source.atom_of_selected_molecule delta.moleculeOnSource hAtom

/-- Target-side circuit molecules contain primitive root atoms. -/
theorem target_molecule_atom_primitive
    (delta : AATCoreCircuitDelta source target)
    {atom : system.Atom}
    (hAtom : delta.molecule.atoms atom) :
    system.Primitive atom :=
  target.atom_of_selected_molecule delta.moleculeOnTarget hAtom

/-- The selected circuit law does not create atom existence. -/
theorem law_does_not_create_atoms
    (delta : AATCoreCircuitDelta source target) :
    system.noLawCreatesAtoms :=
  delta.law.does_not_create_atoms

/-- Circuit deltas do not create atom existence. -/
theorem circuit_delta_does_not_create_atoms
    (delta : AATCoreCircuitDelta source target) :
    system.noSFTEventCreatesAtoms :=
  delta.doesNotCreateAtomsEvidence

end AATCoreCircuitDelta

/--
Law-relative circuit delta for transport transitions.

Unlike `AATCoreCircuitDelta`, this record does not require one law and one
molecule to be selected by both cores. Generated operations can move the
selected source molecule/law to a selected target molecule/law, so the circuit
surface keeps source and target selections separate.
-/
structure AATCoreTransportCircuitDelta
    {system : AtomAxiomSystem.{u, v}}
    (source target : AAT.AATCore system) where
  sourceLaw : AAT.DesignLaw system
  targetLaw : AAT.DesignLaw system
  sourceMolecule : AAT.Molecule system
  targetMolecule : AAT.Molecule system
  sourceLawOnSource : source.laws sourceLaw
  targetLawOnTarget : target.laws targetLaw
  sourceMoleculeOnSource : source.molecules sourceMolecule
  targetMoleculeOnTarget : target.molecules targetMolecule
  sourceCircuit : AAT.ObstructionCircuit sourceLaw sourceMolecule -> Prop
  targetCircuit : AAT.ObstructionCircuit targetLaw targetMolecule -> Prop
  transportedCircuit :
    AAT.ObstructionCircuit sourceLaw sourceMolecule ->
      AAT.ObstructionCircuit targetLaw targetMolecule -> Prop
  circuitBoundary : Prop
  doesNotCreateAtomsEvidence : system.noSFTEventCreatesAtoms
  nonConclusions : Prop

namespace AATCoreTransportCircuitDelta

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}

/-- Source-side transport-circuit molecules contain primitive root atoms. -/
theorem source_molecule_atom_primitive
    (delta : AATCoreTransportCircuitDelta source target)
    {atom : system.Atom}
    (hAtom : delta.sourceMolecule.atoms atom) :
    system.Primitive atom :=
  source.atom_of_selected_molecule delta.sourceMoleculeOnSource hAtom

/-- Target-side transport-circuit molecules contain primitive root atoms. -/
theorem target_molecule_atom_primitive
    (delta : AATCoreTransportCircuitDelta source target)
    {atom : system.Atom}
    (hAtom : delta.targetMolecule.atoms atom) :
    system.Primitive atom :=
  target.atom_of_selected_molecule delta.targetMoleculeOnTarget hAtom

/-- Source-side selected law does not create atom existence. -/
theorem source_law_does_not_create_atoms
    (delta : AATCoreTransportCircuitDelta source target) :
    system.noLawCreatesAtoms :=
  delta.sourceLaw.does_not_create_atoms

/-- Target-side selected law does not create atom existence. -/
theorem target_law_does_not_create_atoms
    (delta : AATCoreTransportCircuitDelta source target) :
    system.noLawCreatesAtoms :=
  delta.targetLaw.does_not_create_atoms

/-- Transport circuit deltas do not create atom existence. -/
theorem transport_circuit_delta_does_not_create_atoms
    (delta : AATCoreTransportCircuitDelta source target) :
    system.noSFTEventCreatesAtoms :=
  delta.doesNotCreateAtomsEvidence

end AATCoreTransportCircuitDelta

/--
SFT-visible transition between two Atom-axiomatized AAT cores.

The transition consumes an AAT operation package and records atom, semantic,
and circuit deltas as SFT analysis inputs.  It does not define AAT and does not
create atom existence.
-/
structure AATCoreTransition
    {system : AtomAxiomSystem.{u, v}}
    (source target : AAT.AATCore system) where
  operationPackage : AAT.OperationPreservationPackage source target
  atomDelta : AATCoreAtomDelta source target
  semanticDelta : AATCoreSemanticDelta atomDelta
  circuitDelta : AATCoreCircuitDelta source target
  transitionBoundary : Prop
  fieldSigBoundary : Prop
  nonConclusions : Prop

namespace AATCoreTransition

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}

/-- The selected transition boundary remains explicit. -/
def RecordsTransitionBoundary
    (transition : AATCoreTransition source target) : Prop :=
  transition.transitionBoundary

/-- FieldSig-related transition data remains an analysis boundary. -/
def RecordsFieldSigBoundary
    (transition : AATCoreTransition source target) : Prop :=
  transition.fieldSigBoundary

/-- The underlying AAT operation package does not create atom existence. -/
theorem operation_does_not_create_atoms
    (transition : AATCoreTransition source target) :
    system.noToolOutputCreatesAtoms :=
  transition.operationPackage.operation_does_not_create_atoms

/-- The atom delta does not create atom existence. -/
theorem atom_delta_does_not_create_atoms
    (transition : AATCoreTransition source target) :
    system.noSFTEventCreatesAtoms :=
  transition.atomDelta.delta_does_not_create_atoms

/-- The semantic delta does not create atom existence. -/
theorem semantic_delta_does_not_create_atoms
    (transition : AATCoreTransition source target) :
    system.noSFTEventCreatesAtoms :=
  transition.semanticDelta.semantic_delta_does_not_create_atoms

/-- The circuit delta does not create atom existence. -/
theorem circuit_delta_does_not_create_atoms
    (transition : AATCoreTransition source target) :
    system.noSFTEventCreatesAtoms :=
  transition.circuitDelta.circuit_delta_does_not_create_atoms

end AATCoreTransition

/--
SFT-visible transport transition between two Atom-axiomatized AAT cores.

This is the transition shape used by generated operations whose selected
source molecule/law is transported to a selected target molecule/law.  It keeps
the same atom, semantic, and circuit delta surfaces as `AATCoreTransition`,
but consumes an `OperationTransportPackage` rather than forcing preservation of
the same molecule and law.
-/
structure AATCoreTransportTransition
    {system : AtomAxiomSystem.{u, v}}
    (source target : AAT.AATCore system) where
  transportPackage : AAT.OperationTransportPackage source target
  atomDelta : AATCoreAtomDelta source target
  semanticDelta : AATCoreSemanticDelta atomDelta
  circuitDelta : AATCoreTransportCircuitDelta source target
  transitionBoundary : Prop
  fieldSigBoundary : Prop
  nonConclusions : Prop

namespace AATCoreTransportTransition

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}

/-- The selected transport-transition boundary remains explicit. -/
def RecordsTransitionBoundary
    (transition : AATCoreTransportTransition source target) : Prop :=
  transition.transitionBoundary

/-- FieldSig-related transport data remains an analysis boundary. -/
def RecordsFieldSigBoundary
    (transition : AATCoreTransportTransition source target) : Prop :=
  transition.fieldSigBoundary

/-- The underlying AAT transport package does not create atom existence. -/
theorem operation_does_not_create_atoms
    (transition : AATCoreTransportTransition source target) :
    system.noToolOutputCreatesAtoms :=
  transition.transportPackage.operation_does_not_create_atoms

/-- The atom delta does not create atom existence. -/
theorem atom_delta_does_not_create_atoms
    (transition : AATCoreTransportTransition source target) :
    system.noSFTEventCreatesAtoms :=
  transition.atomDelta.delta_does_not_create_atoms

/-- The semantic delta does not create atom existence. -/
theorem semantic_delta_does_not_create_atoms
    (transition : AATCoreTransportTransition source target) :
    system.noSFTEventCreatesAtoms :=
  transition.semanticDelta.semantic_delta_does_not_create_atoms

/-- The circuit delta does not create atom existence. -/
theorem circuit_delta_does_not_create_atoms
    (transition : AATCoreTransportTransition source target) :
    system.noSFTEventCreatesAtoms :=
  transition.circuitDelta.transport_circuit_delta_does_not_create_atoms

end AATCoreTransportTransition

/--
SFT-side forecast status exposed at the AAT/SFT interface.

The fields are intentionally proposition-valued. They track what an SFT
forecast package still owes: local premises, support/model boundaries,
trajectory safety, unmeasured-axis safety, theorem boundaries, tooling
boundaries, forecast boundaries, and non-conclusions.
-/
structure SFTForecastStatus where
  localPremise : Prop
  supportBoundary : Prop
  trajectorySafetyBoundary : Prop
  measuredAxisBoundary : Prop
  unmeasuredAxisBoundary : Prop
  theoremBoundary : Prop
  toolingBoundary : Prop
  forecastBoundary : Prop
  nonConclusions : Prop

namespace SFTForecastStatus

/-- The SFT forecast status records a local premise supplied by AAT. -/
def RecordsLocalPremise (status : SFTForecastStatus) : Prop :=
  status.localPremise

/-- Support/model assumptions remain explicit. -/
def RecordsSupportBoundary (status : SFTForecastStatus) : Prop :=
  status.supportBoundary

/-- Future trajectory safety remains an explicit boundary obligation. -/
def RecordsTrajectorySafetyBoundary (status : SFTForecastStatus) : Prop :=
  status.trajectorySafetyBoundary

/-- Measured-axis assumptions remain explicit. -/
def RecordsMeasuredAxisBoundary (status : SFTForecastStatus) : Prop :=
  status.measuredAxisBoundary

/-- Unmeasured-axis safety remains an explicit boundary obligation. -/
def RecordsUnmeasuredAxisBoundary (status : SFTForecastStatus) : Prop :=
  status.unmeasuredAxisBoundary

/-- The theorem/modeling boundary remains explicit on the SFT side. -/
def RecordsTheoremBoundary (status : SFTForecastStatus) : Prop :=
  status.theoremBoundary

/-- Tooling/report assumptions remain explicit on the SFT side. -/
def RecordsToolingBoundary (status : SFTForecastStatus) : Prop :=
  status.toolingBoundary

/-- Forecast correctness/calibration remains an explicit boundary obligation. -/
def RecordsForecastBoundary (status : SFTForecastStatus) : Prop :=
  status.forecastBoundary

/-- SFT forecast non-conclusions remain explicit. -/
def RecordsNonConclusions (status : SFTForecastStatus) : Prop :=
  status.nonConclusions

end SFTForecastStatus

/--
Boundary relation for reading AAT theorem status as an SFT local premise.

The relation preserves the one-way reading used by the SFT documents: AAT
theorem evidence can serve as a local premise, while trajectory safety,
unmeasured-axis safety, tooling boundaries, forecast boundaries, and
non-conclusions remain live obligations.
-/
structure AATToSFTInterfaceBoundary
    (aat : AATTheoremStatus) (forecast : SFTForecastStatus) : Prop where
  readsAATAsLocalPremise :
    aat.RecordsTheoremPackage -> forecast.RecordsLocalPremise
  preservesAATTheoremBoundary :
    aat.RecordsTheoremBoundary -> forecast.RecordsTheoremBoundary
  preservesMeasuredAxisBoundary :
    aat.RecordsMeasuredZeroEvidence -> forecast.RecordsMeasuredAxisBoundary
  preservesUnmeasuredAxisBoundary :
    aat.RecordsUnmeasuredAxisBoundary -> forecast.RecordsUnmeasuredAxisBoundary
  preservesToolingBoundary :
    aat.RecordsToolingBoundary -> forecast.RecordsToolingBoundary
  recordsSupportBoundary :
    forecast.RecordsSupportBoundary
  recordsTrajectorySafetyBoundary :
    forecast.RecordsTrajectorySafetyBoundary
  recordsForecastBoundary :
    forecast.RecordsForecastBoundary
  recordsNonConclusions :
    aat.RecordsNonConclusions -> forecast.RecordsNonConclusions

namespace AATToSFTInterfaceBoundary

variable {aat : AATTheoremStatus} {forecast : SFTForecastStatus}

/-- AAT theorem status is read as an SFT local premise, not as the full forecast. -/
theorem aat_theorem_status_as_local_premise
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hAAT : aat.RecordsTheoremPackage) :
    forecast.RecordsLocalPremise :=
  hBoundary.readsAATAsLocalPremise hAAT

/--
AAT lawfulness/theorem status alone does not discharge SFT trajectory safety:
the trajectory-safety boundary is still recorded by the interface package.
-/
theorem aat_lawfulness_alone_does_not_discharge_trajectory_safety_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast) :
    forecast.RecordsTrajectorySafetyBoundary :=
  hBoundary.recordsTrajectorySafetyBoundary

/--
Measured-zero AAT evidence does not discharge unmeasured-axis safety: the
unmeasured-axis boundary is preserved explicitly.
-/
theorem measured_zero_does_not_discharge_unmeasured_axis_safety_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hUnmeasured : aat.RecordsUnmeasuredAxisBoundary) :
    forecast.RecordsUnmeasuredAxisBoundary :=
  hBoundary.preservesUnmeasuredAxisBoundary hUnmeasured

/--
Tool/report output crossing the interface remains tooling-boundary data on the
SFT side, not stronger AAT theorem status.
-/
theorem tool_report_output_does_not_strengthen_aat_theorem_status
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hTooling : aat.RecordsToolingBoundary) :
    forecast.RecordsToolingBoundary :=
  hBoundary.preservesToolingBoundary hTooling

/-- AAT theorem-boundary records stay visible as SFT theorem-boundary records. -/
theorem preserves_theorem_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hTheoremBoundary : aat.RecordsTheoremBoundary) :
    forecast.RecordsTheoremBoundary :=
  hBoundary.preservesAATTheoremBoundary hTheoremBoundary

/-- Measured-axis evidence can be preserved without becoming unmeasured-axis safety. -/
theorem preserves_measured_axis_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hMeasured : aat.RecordsMeasuredZeroEvidence) :
    forecast.RecordsMeasuredAxisBoundary :=
  hBoundary.preservesMeasuredAxisBoundary hMeasured

/-- Forecast correctness/calibration remains an explicit SFT boundary. -/
theorem forecast_status_records_forecast_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast) :
    forecast.RecordsForecastBoundary :=
  hBoundary.recordsForecastBoundary

/-- Interface non-conclusions are preserved into SFT forecast status. -/
theorem interface_preserves_nonConclusions
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hNonConclusions : aat.RecordsNonConclusions) :
    forecast.RecordsNonConclusions :=
  hBoundary.recordsNonConclusions hNonConclusions

end AATToSFTInterfaceBoundary

end Formal.Arch
