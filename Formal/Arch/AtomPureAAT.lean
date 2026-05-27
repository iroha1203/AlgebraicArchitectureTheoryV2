import Formal.Arch.AtomCoreAAT
import Formal.Arch.Operation.AtomPureOperation
import Formal.Arch.Repair.AtomPureRepair
import Formal.Arch.Repair.AtomPureSynthesis

namespace Formal.Arch

universe u v w r s t

/--
Signature-free Atom-axiomatized AAT theorem suite.

This is the pure central theorem surface: one atom core, one atom-level
zero-curvature package, and operation/repair/synthesis packages are all read
from Atom Core facts before any ArchitectureSignature or ArchSig observation
layer is attached.
-/
structure AtomAxiomatizedPureTheoremSuite
    (C : Type u) (E : Type v) (D : Type w)
    (RepairState : Type r) (RepairRule : Type s)
    (SynthesisState : Type t)
    (repairSource repairTarget : RepairState) where
  core : AtomAxiomatizedPureAAT C E D
  zeroCurvature : AtomZeroCurvatureTheoremPackage core
  operation : AtomAxiomatizedPureOperationPackage C E D
  operationSurfaceMatches : operation.surface = core.surface
  repair :
    AtomFiniteRepairPackage
      zeroCurvature.law
      zeroCurvature.requiredMolecule
      RepairState RepairRule repairSource repairTarget
  synthesisSpec :
    AtomAATSynthesisSpec
      core.surface
      zeroCurvature.law
      zeroCurvature.requiredMolecule
      SynthesisState
  synthesisCandidate : SynthesisState
  synthesisCandidateAtoms :
    ∀ atom,
      core.surface.atoms atom ->
        synthesisSpec.stateHasAtom synthesisCandidate atom
  synthesisCandidateMolecules :
    ∀ molecule,
      core.surface.molecules molecule ->
        synthesisSpec.stateHasMolecule synthesisCandidate molecule
  synthesisCandidateLaws :
    ∀ law,
      core.surface.laws law ->
        synthesisSpec.stateHasLaw synthesisCandidate law
  synthesisCandidateNoRequiredObstructionCircuit :
    synthesisSpec.stateNoRequiredObstructionCircuit synthesisCandidate
  noArchitectureSignatureDependency : Prop
  noArchitectureSignatureDependencyEvidence :
    noArchitectureSignatureDependency
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  suiteBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedPureTheoremSuite

/-- The pure suite is independent of observation tooling. -/
theorem independent_of_observation
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.core.surface.noObservationDependency :=
  AtomAxiomatizedPureAAT.independent_of_observation suite.core

/-- The pure suite is independent of SFT forecasting. -/
theorem independent_of_sft
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.core.surface.noSFTDependency :=
  AtomAxiomatizedPureAAT.independent_of_sft suite.core

/-- The pure suite has no ArchitectureSignature dependency. -/
theorem independent_of_architecture_signature
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.noArchitectureSignatureDependency :=
  suite.noArchitectureSignatureDependencyEvidence

/-- The operation package is over the same selected atom surface as the core. -/
theorem operation_surface_matches
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.operation.surface = suite.core.surface :=
  suite.operationSurfaceMatches

/-- The selected zero-curvature law does not create primitive atom existence. -/
theorem zeroCurvature_law_does_not_create_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).lawDoesNotCreateAtoms :=
  AtomZeroCurvatureTheoremPackage.law_does_not_create_atoms
    suite.zeroCurvature

/-- The selected zero-curvature law does not change primitive atom existence. -/
theorem zeroCurvature_law_does_not_change_atom_existence
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).lawDoesNotChangeAtomExistence :=
  AtomZeroCurvatureTheoremPackage.law_does_not_change_atom_existence
    suite.zeroCurvature

/-- The selected zero-curvature law evaluates atoms that already exist. -/
theorem zeroCurvature_law_atoms_exist_before_law
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).atomsExistBeforeLaw :=
  AtomZeroCurvatureTheoremPackage.law_atoms_exist_before_law
    suite.zeroCurvature

/-- The pure suite exposes atom-level zero curvature. -/
theorem atomZeroCurvature
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvature
      suite.zeroCurvature.law
      suite.zeroCurvature.requiredMolecule :=
  suite.zeroCurvature.atomZeroCurvature

/-- Atom-level zero curvature gives atom-configuration lawfulness. -/
theorem atomLawful_from_atomZeroCurvature
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    LawfulWithinAtomConfiguration
      suite.zeroCurvature.law
      suite.zeroCurvature.requiredMolecule :=
  AtomZeroCurvatureTheoremPackage.atomLawful suite.zeroCurvature

/-- Required molecules in the pure theorem suite are selected by the pure surface. -/
theorem requiredMolecule_on_surface
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    {molecule : AtomMolecule C E D}
    (hRequired : suite.zeroCurvature.requiredMolecule molecule) :
    suite.core.surface.molecules molecule :=
  suite.zeroCurvature.requiredMolecule_on_surface hRequired

/--
Atoms in required suite molecules are selected by the same pure Atom-AAT
surface.
-/
theorem atom_of_requiredMolecule
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    {molecule : AtomMolecule C E D}
    (hRequired : suite.zeroCurvature.requiredMolecule molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    suite.core.surface.atoms atom :=
  suite.zeroCurvature.atom_of_requiredMolecule hRequired hAtom

/-- Required suite molecules are supported by the pure surface atoms. -/
theorem requiredMolecule_supportedBy_surface_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    {molecule : AtomMolecule C E D}
    (hRequired : suite.zeroCurvature.requiredMolecule molecule) :
    AtomMoleculeSupportedBy
      suite.core.surface.selectedAtomUniverse molecule :=
  suite.zeroCurvature.requiredMolecule_supportedBy_surface_atoms hRequired

/-- Atoms in required suite molecules remain primitive Atom Core facts. -/
theorem requiredMolecule_atom_is_primitive
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    {molecule : AtomMolecule C E D}
    (hRequired : suite.zeroCurvature.requiredMolecule molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    PrimitiveArchitectureAtom atom :=
  suite.zeroCurvature.requiredMolecule_atom_is_primitive
    hRequired hAtom

/-- The suite operation preserves its selected atom surface. -/
theorem operation_preservesSurfaceInvariant
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    PreservesInvariant
      (AtomPresentationOperation.source
        (surface := suite.operation.surface))
      (AtomPresentationOperation.target
        (surface := suite.operation.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        suite.operation.surface)
      suite.operation.operation () :=
  AtomAxiomatizedPureOperationPackage.preservesSurfaceInvariant
    suite.operation

/-- The suite operation belongs to the atom-surface operation family. -/
theorem operation_ops_mem_surfaceInvariant
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    Ops
      (AtomPresentationOperation.source
        (surface := suite.operation.surface))
      (AtomPresentationOperation.target
        (surface := suite.operation.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        suite.operation.surface)
      (fun I : Unit => I = ())
      suite.operation.operation :=
  AtomAxiomatizedPureOperationPackage.ops_mem_surfaceInvariant
    suite.operation

/-- The suite repair component as a pure Atom-AAT repair package. -/
def repairPackage
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedPureRepairPackage
      suite.core RepairState RepairRule repairSource repairTarget where
  law := suite.zeroCurvature.law
  requiredMolecule := suite.zeroCurvature.requiredMolecule
  lawOnSurface := suite.zeroCurvature.lawOnSurface
  requiredMoleculesOnSurface :=
    suite.zeroCurvature.requiredMoleculesOnSurface
  repair := suite.repair
  lawfulnessBridge := suite.zeroCurvature.lawfulnessBridge
  noArchitectureSignatureDependency :=
    suite.noArchitectureSignatureDependency
  noArchitectureSignatureDependencyEvidence :=
    suite.noArchitectureSignatureDependencyEvidence
  repairAxiomBoundary := suite.suiteBoundary
  theoremPackageBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The repair component clears every required atom obstruction circuit. -/
theorem repair_target_noRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    NoRequiredObstructionCircuit
      suite.zeroCurvature.law
      suite.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureRepairPackage.target_noRequiredObstructionCircuit
    suite.repairPackage

/-- Repair clearing is atom-level zero curvature. -/
theorem repair_target_atomZeroCurvature
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvature
      suite.zeroCurvature.law
      suite.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureRepairPackage.target_atomZeroCurvature
    suite.repairPackage

/-- Repair clearing and the atom lawfulness bridge give atom lawfulness. -/
theorem repair_target_atomLawful
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    LawfulWithinAtomConfiguration
      suite.zeroCurvature.law
      suite.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureRepairPackage.target_atomLawful
    suite.repairPackage

/-- Repair-derived zero curvature uses a law that does not create atoms. -/
theorem repair_law_does_not_create_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).lawDoesNotCreateAtoms :=
  AtomAxiomatizedPureRepairPackage.law_does_not_create_atoms
    suite.repairPackage

/--
Repair-derived zero curvature uses a law that does not change primitive atom
existence.
-/
theorem repair_law_does_not_change_atom_existence
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).lawDoesNotChangeAtomExistence :=
  AtomAxiomatizedPureRepairPackage.law_does_not_change_atom_existence
    suite.repairPackage

/-- Repair-derived zero curvature uses a law that evaluates pre-existing atoms. -/
theorem repair_law_atoms_exist_before_law
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).atomsExistBeforeLaw :=
  AtomAxiomatizedPureRepairPackage.law_atoms_exist_before_law
    suite.repairPackage

/-- The suite synthesis component as a pure Atom-AAT synthesis package. -/
def synthesisPackage
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedPureSynthesisPackage suite.core SynthesisState where
  law := suite.zeroCurvature.law
  requiredMolecule := suite.zeroCurvature.requiredMolecule
  lawOnSurface := suite.zeroCurvature.lawOnSurface
  requiredMoleculesOnSurface :=
    suite.zeroCurvature.requiredMoleculesOnSurface
  spec := suite.synthesisSpec
  candidate := suite.synthesisCandidate
  candidateAtoms := suite.synthesisCandidateAtoms
  candidateMolecules := suite.synthesisCandidateMolecules
  candidateLaws := suite.synthesisCandidateLaws
  candidateNoRequiredObstructionCircuit :=
    suite.synthesisCandidateNoRequiredObstructionCircuit
  lawfulnessBridge := suite.zeroCurvature.lawfulnessBridge
  noArchitectureSignatureDependency :=
    suite.noArchitectureSignatureDependency
  noArchitectureSignatureDependencyEvidence :=
    suite.noArchitectureSignatureDependencyEvidence
  coverageAssumptions := suite.coverageAssumptions
  exactnessAssumptions := suite.exactnessAssumptions
  synthesisBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The synthesized candidate satisfies every atom-generated constraint. -/
theorem synthesis_candidate_satisfies
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSatisfies
      suite.synthesisPackage.system
      suite.synthesisCandidate :=
  AtomAxiomatizedPureSynthesisPackage.candidate_satisfies
    suite.synthesisPackage

/-- Candidate no-circuit soundness is atom-level zero curvature. -/
theorem synthesis_candidate_atomZeroCurvature
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvature
      suite.zeroCurvature.law
      suite.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureSynthesisPackage.candidate_atomZeroCurvature
    suite.synthesisPackage

/-- Candidate no-circuit soundness gives atom-configuration lawfulness. -/
theorem synthesis_candidate_atomLawful
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    LawfulWithinAtomConfiguration
      suite.zeroCurvature.law
      suite.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureSynthesisPackage.candidate_atomLawful
    suite.synthesisPackage

/-- Synthesis-derived zero curvature uses a law that does not create atoms. -/
theorem synthesis_law_does_not_create_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).lawDoesNotCreateAtoms :=
  AtomAxiomatizedPureSynthesisPackage.law_does_not_create_atoms
    suite.synthesisPackage

/--
Synthesis-derived zero curvature uses a law that does not change primitive atom
existence.
-/
theorem synthesis_law_does_not_change_atom_existence
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).lawDoesNotChangeAtomExistence :=
  AtomAxiomatizedPureSynthesisPackage.law_does_not_change_atom_existence
    suite.synthesisPackage

/-- Synthesis-derived zero curvature uses a law that evaluates pre-existing atoms. -/
theorem synthesis_law_atoms_exist_before_law
    {C : Type u} {E : Type v} {D : Type w}
    {RepairState : Type r} {RepairRule : Type s}
    {SynthesisState : Type t}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.core.lawSeparation
      suite.zeroCurvature.law
      suite.zeroCurvature.lawOnSurface).atomsExistBeforeLaw :=
  AtomAxiomatizedPureSynthesisPackage.law_atoms_exist_before_law
    suite.synthesisPackage

end AtomAxiomatizedPureTheoremSuite

end Formal.Arch
