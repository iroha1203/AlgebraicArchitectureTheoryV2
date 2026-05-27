import Formal.Arch.AtomPureAAT
import Formal.Arch.Operation.AtomOperation
import Formal.Arch.Repair.AtomRepair
import Formal.Arch.Repair.AtomSynthesis

namespace Formal.Arch

universe u v w q r s t m

/--
Unified Atom-axiomatized AAT theorem suite.

The suite fixes one pure atom surface and one selected atom-derived
zero-curvature package, then reads operation preservation, finite repair
clearing, and synthesis soundness from that same atom foundation.
-/
structure AtomAxiomatizedTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    (E : Type q) (D : Type r)
    (RepairState : Type s) (RepairRule : Type t)
    (SynthesisState : Type m)
    (repairSource repairTarget : RepairState) where
  pureCore : AtomAxiomatizedPureAAT C E D
  aat : ArchitectureSignature.AtomAxiomatizedAAT X E D
  pureCoreSurfaceMatches : pureCore.surface = aat.surface
  pureCoreLawOnSurface :
    pureCore.surface.laws aat.zeroCurvature.law
  operation : AtomPresentationOperation aat.surface
  repair :
    AtomFiniteRepairPackage
      aat.zeroCurvature.law
      aat.zeroCurvature.requiredMolecule
      RepairState RepairRule repairSource repairTarget
  synthesisSpec :
    AtomAATSynthesisSpec
      aat.surface
      aat.zeroCurvature.law
      aat.zeroCurvature.requiredMolecule
      SynthesisState
  synthesisCandidate : SynthesisState
  synthesisCandidateAtoms :
    ∀ atom,
      aat.surface.atoms atom ->
        synthesisSpec.stateHasAtom synthesisCandidate atom
  synthesisCandidateMolecules :
    ∀ molecule,
      aat.surface.molecules molecule ->
        synthesisSpec.stateHasMolecule synthesisCandidate molecule
  synthesisCandidateLaws :
    ∀ law,
      aat.surface.laws law ->
        synthesisSpec.stateHasLaw synthesisCandidate law
  synthesisCandidateNoRequiredObstructionCircuit :
    synthesisSpec.stateNoRequiredObstructionCircuit synthesisCandidate
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  suiteBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedTheoremSuite

/-- The unified suite carries the pure Atom-AAT core before Signature reading. -/
theorem pure_core_surface_matches
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.pureCore.surface = suite.aat.surface :=
  suite.pureCoreSurfaceMatches

/-- The pure core carried by the suite is independent of ArchitectureSignature. -/
theorem independent_of_architecture_signature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.pureCore.noArchitectureSignatureDependency :=
  AtomAxiomatizedPureAAT.independent_of_architecture_signature
    suite.pureCore

/-- The zero-curvature law is a selected pure-core law and does not create atoms. -/
theorem zeroCurvature_law_does_not_create_atoms
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.pureCore.lawSeparation
      suite.aat.zeroCurvature.law
      suite.pureCoreLawOnSurface).lawDoesNotCreateAtoms :=
  AtomAxiomatizedPureAAT.selected_law_does_not_create_atoms
    suite.pureCore suite.pureCoreLawOnSurface

/-- The unified suite exposes the atom-only zero-curvature theorem package. -/
def atomZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvatureTheoremPackage suite.pureCore where
  law := suite.aat.zeroCurvature.law
  requiredMolecule := suite.aat.zeroCurvature.requiredMolecule
  lawOnSurface := suite.pureCoreLawOnSurface
  requiredMoleculesOnSurface := by
    intro molecule hRequired
    have hMolecule :
        suite.aat.surface.molecules molecule :=
      suite.aat.requiredMoleculesOnSurface molecule hRequired
    simpa [suite.pureCoreSurfaceMatches] using hMolecule
  requiredCircuitsOnSurface := by
    intro molecule hRequired hCircuit
    exact
      suite.pureCore.circuitClosure
        suite.pureCoreLawOnSurface
        (by
          have hMolecule :
              suite.aat.surface.molecules molecule :=
            suite.aat.requiredMoleculesOnSurface molecule hRequired
          simpa [suite.pureCoreSurfaceMatches] using hMolecule)
        hCircuit
  lawfulnessBridge := suite.aat.zeroCurvature.lawfulnessBridge
  atomZeroCurvature := suite.aat.zeroCurvature.noRequiredObstructionCircuit
  atomZeroCurvatureBoundary := suite.suiteBoundary
  theoremPackageBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The central suite records atom-level zero curvature before Signature reading. -/
theorem atomZeroCurvature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvature
      suite.aat.zeroCurvature.law
      suite.aat.zeroCurvature.requiredMolecule :=
  (suite.atomZeroCurvatureTheoremPackage).atomZeroCurvature

/--
The atom-only zero-curvature theorem package gives atom-configuration
lawfulness.
-/
theorem atomLawful_from_atomZeroCurvature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    LawfulWithinAtomConfiguration
      suite.aat.zeroCurvature.law
      suite.aat.zeroCurvature.requiredMolecule :=
  AtomZeroCurvatureTheoremPackage.atomLawful
    suite.atomZeroCurvatureTheoremPackage

/-- The unified suite exposes the Signature-free atom operation package. -/
def pureOperationPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedPureOperationPackage C E D where
  surface := suite.aat.surface
  operation := suite.operation
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  operationAxiomBoundary := suite.suiteBoundary
  theoremPackageBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/--
The central suite's operation preservation is already a pure atom operation
theorem before Signature reading.
-/
theorem pure_operation_preservesSurfaceInvariant
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    PreservesInvariant
      (AtomPresentationOperation.source (surface := suite.aat.surface))
      (AtomPresentationOperation.target (surface := suite.aat.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds suite.aat.surface)
      suite.operation () :=
  AtomAxiomatizedPureOperationPackage.preservesSurfaceInvariant
    suite.pureOperationPackage

/-- The unified suite exposes the Signature-free atom repair package. -/
def pureRepairPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedPureRepairPackage
      suite.pureCore RepairState RepairRule repairSource repairTarget where
  law := suite.aat.zeroCurvature.law
  requiredMolecule := suite.aat.zeroCurvature.requiredMolecule
  lawOnSurface := suite.pureCoreLawOnSurface
  requiredMoleculesOnSurface := by
    intro molecule hRequired
    have hMolecule :
        suite.aat.surface.molecules molecule :=
      suite.aat.requiredMoleculesOnSurface molecule hRequired
    simpa [suite.pureCoreSurfaceMatches] using hMolecule
  repair := suite.repair
  lawfulnessBridge := suite.aat.zeroCurvature.lawfulnessBridge
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  repairAxiomBoundary := suite.suiteBoundary
  theoremPackageBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The pure repair component is independent of ArchitectureSignature. -/
theorem pure_repair_independent_of_architecture_signature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.pureRepairPackage.noArchitectureSignatureDependency :=
  AtomAxiomatizedPureRepairPackage.independent_of_architecture_signature
    suite.pureRepairPackage

/--
The central suite's repair clearing is already a pure atom repair theorem
before Signature reading.
-/
theorem pure_repair_target_noRequiredObstructionCircuit
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    NoRequiredObstructionCircuit
      suite.aat.zeroCurvature.law
      suite.aat.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureRepairPackage.target_noRequiredObstructionCircuit
    suite.pureRepairPackage

/-- The central suite's repair clearing is atom-level zero curvature. -/
theorem pure_repair_target_atomZeroCurvature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvature
      suite.aat.zeroCurvature.law
      suite.aat.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureRepairPackage.target_atomZeroCurvature
    suite.pureRepairPackage

/-- Repair-derived zero curvature is available as an atom-only theorem package. -/
def pureRepairZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvatureTheoremPackage suite.pureCore :=
  AtomAxiomatizedPureRepairPackage.atomZeroCurvatureTheoremPackage
    suite.pureRepairPackage

/--
Repair-derived zero curvature uses the same selected law that does not create
atom existence.
-/
theorem pure_repair_law_does_not_create_atoms
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.pureCore.lawSeparation
      suite.aat.zeroCurvature.law
      suite.pureCoreLawOnSurface).lawDoesNotCreateAtoms :=
  AtomAxiomatizedPureRepairPackage.law_does_not_create_atoms
    suite.pureRepairPackage

/-- The unified suite exposes the Signature-free atom synthesis package. -/
def pureSynthesisPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedPureSynthesisPackage suite.pureCore SynthesisState where
  law := suite.aat.zeroCurvature.law
  requiredMolecule := suite.aat.zeroCurvature.requiredMolecule
  lawOnSurface := suite.pureCoreLawOnSurface
  requiredMoleculesOnSurface := by
    intro molecule hRequired
    have hMolecule :
        suite.aat.surface.molecules molecule :=
      suite.aat.requiredMoleculesOnSurface molecule hRequired
    simpa [suite.pureCoreSurfaceMatches] using hMolecule
  spec := {
    stateHasAtom := suite.synthesisSpec.stateHasAtom
    stateHasMolecule := suite.synthesisSpec.stateHasMolecule
    stateHasLaw := suite.synthesisSpec.stateHasLaw
    stateNoRequiredObstructionCircuit :=
      suite.synthesisSpec.stateNoRequiredObstructionCircuit
    stateNoRequiredObstructionCircuitSound :=
      suite.synthesisSpec.stateNoRequiredObstructionCircuitSound
    interpretationBoundary := suite.synthesisSpec.interpretationBoundary
    nonConclusions := suite.synthesisSpec.nonConclusions }
  candidate := suite.synthesisCandidate
  candidateAtoms := by
    intro atom hAtom
    have hAtomAAT :
        suite.aat.surface.atoms atom := by
      simpa [suite.pureCoreSurfaceMatches] using hAtom
    exact suite.synthesisCandidateAtoms atom hAtomAAT
  candidateMolecules := by
    intro molecule hMolecule
    have hMoleculeAAT :
        suite.aat.surface.molecules molecule := by
      simpa [suite.pureCoreSurfaceMatches] using hMolecule
    exact suite.synthesisCandidateMolecules molecule hMoleculeAAT
  candidateLaws := by
    intro law hLaw
    have hLawAAT :
        suite.aat.surface.laws law := by
      simpa [suite.pureCoreSurfaceMatches] using hLaw
    exact suite.synthesisCandidateLaws law hLawAAT
  candidateNoRequiredObstructionCircuit :=
    suite.synthesisCandidateNoRequiredObstructionCircuit
  lawfulnessBridge := suite.aat.zeroCurvature.lawfulnessBridge
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  coverageAssumptions := suite.coverageAssumptions
  exactnessAssumptions := suite.exactnessAssumptions
  synthesisBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The pure synthesis component is independent of ArchitectureSignature. -/
theorem pure_synthesis_independent_of_architecture_signature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.pureSynthesisPackage.noArchitectureSignatureDependency :=
  AtomAxiomatizedPureSynthesisPackage.independent_of_architecture_signature
    suite.pureSynthesisPackage

/--
The central suite's synthesis candidate satisfies atom-generated constraints
before Signature reading.
-/
theorem pure_synthesis_candidate_satisfies
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSatisfies
      suite.pureSynthesisPackage.system
      suite.synthesisCandidate :=
  AtomAxiomatizedPureSynthesisPackage.candidate_satisfies
    suite.pureSynthesisPackage

/-- The central suite's synthesis candidate gives atom-level zero curvature. -/
theorem pure_synthesis_candidate_atomZeroCurvature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvature
      suite.aat.zeroCurvature.law
      suite.aat.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedPureSynthesisPackage.candidate_atomZeroCurvature
    suite.pureSynthesisPackage

/-- Synthesis-derived zero curvature is available as an atom-only theorem package. -/
def pureSynthesisZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomZeroCurvatureTheoremPackage suite.pureCore :=
  AtomAxiomatizedPureSynthesisPackage.atomZeroCurvatureTheoremPackage
    suite.pureSynthesisPackage

/--
Synthesis-derived zero curvature uses the same selected law that does not
create atom existence.
-/
theorem pure_synthesis_law_does_not_create_atoms
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    (suite.pureCore.lawSeparation
      suite.aat.zeroCurvature.law
      suite.pureCoreLawOnSurface).lawDoesNotCreateAtoms :=
  AtomAxiomatizedPureSynthesisPackage.law_does_not_create_atoms
    suite.pureSynthesisPackage

/--
Forget the Signature-connected central suite back to the pure Atom-AAT theorem
suite.
-/
def pureTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedPureTheoremSuite
      C E D RepairState RepairRule SynthesisState
      repairSource repairTarget where
  core := suite.pureCore
  zeroCurvature := suite.atomZeroCurvatureTheoremPackage
  operation := suite.pureOperationPackage
  operationSurfaceMatches := by
    simpa [AtomAxiomatizedTheoremSuite.pureOperationPackage]
      using suite.pureCoreSurfaceMatches.symm
  repair := suite.repair
  synthesisSpec := suite.pureSynthesisPackage.spec
  synthesisCandidate := suite.synthesisCandidate
  synthesisCandidateAtoms :=
    suite.pureSynthesisPackage.candidateAtoms
  synthesisCandidateMolecules :=
    suite.pureSynthesisPackage.candidateMolecules
  synthesisCandidateLaws :=
    suite.pureSynthesisPackage.candidateLaws
  synthesisCandidateNoRequiredObstructionCircuit :=
    suite.pureSynthesisPackage.candidateNoRequiredObstructionCircuit
  noArchitectureSignatureDependency :=
    suite.pureCore.noArchitectureSignatureDependency
  noArchitectureSignatureDependencyEvidence :=
    suite.pureCore.noArchitectureSignatureDependencyEvidence
  coverageAssumptions := suite.coverageAssumptions
  exactnessAssumptions := suite.exactnessAssumptions
  suiteBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The operation component as the existing operation package. -/
def operationPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedOperationPackage X E D where
  aat := suite.aat
  operation := suite.operation
  operationAxiomBoundary := suite.suiteBoundary
  theoremPackageBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The repair component as the existing repair package. -/
def repairPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedRepairPackage
      X E D RepairState RepairRule repairSource repairTarget where
  aat := suite.aat
  repair := suite.repair
  repairAxiomBoundary := suite.suiteBoundary
  theoremPackageBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The synthesis component as the existing synthesis package. -/
def synthesisPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    AtomAxiomatizedSynthesisPackage X E D SynthesisState where
  aat := suite.aat
  spec := suite.synthesisSpec
  candidate := suite.synthesisCandidate
  candidateAtoms := suite.synthesisCandidateAtoms
  candidateMolecules := suite.synthesisCandidateMolecules
  candidateLaws := suite.synthesisCandidateLaws
  candidateNoRequiredObstructionCircuit :=
    suite.synthesisCandidateNoRequiredObstructionCircuit
  coverageAssumptions := suite.coverageAssumptions
  exactnessAssumptions := suite.exactnessAssumptions
  synthesisBoundary := suite.suiteBoundary
  nonConclusions := suite.nonConclusions

/-- The unified suite remains independent of observation tooling. -/
theorem independent_of_observation
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.aat.surface.noObservationDependency :=
  ArchitectureSignature.AtomAxiomatizedAAT.independent_of_observation
    suite.aat

/-- The unified suite remains independent of SFT forecasting. -/
theorem independent_of_sft
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    suite.aat.surface.noSFTDependency :=
  ArchitectureSignature.AtomAxiomatizedAAT.independent_of_sft
    suite.aat

/-- Operation preservation is read from the same atom surface. -/
theorem operation_preservesSurfaceInvariant
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    PreservesInvariant
      (AtomPresentationOperation.source (surface := suite.aat.surface))
      (AtomPresentationOperation.target (surface := suite.aat.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds suite.aat.surface)
      suite.operation () :=
  AtomAxiomatizedOperationPackage.preservesSurfaceInvariant
    suite.operationPackage

/-- Operation preservation also belongs to the selected `Ops` family. -/
theorem operation_ops_mem_surfaceInvariant
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    Ops
      (AtomPresentationOperation.source (surface := suite.aat.surface))
      (AtomPresentationOperation.target (surface := suite.aat.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds suite.aat.surface)
      (fun I : Unit => I = ())
      suite.operation :=
  AtomAxiomatizedOperationPackage.ops_mem_surfaceInvariant
    suite.operationPackage

/-- Finite atom repair clearing gives no required obstruction circuit. -/
theorem repair_target_noRequiredObstructionCircuit
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    NoRequiredObstructionCircuit
      suite.aat.zeroCurvature.law
      suite.aat.zeroCurvature.requiredMolecule :=
  AtomAxiomatizedRepairPackage.target_noRequiredObstructionCircuit
    suite.repairPackage

/-- Finite atom repair clearing gives architecture lawfulness. -/
theorem architectureLawful_of_repair
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSignature.ArchitectureLawful X :=
  AtomAxiomatizedRepairPackage.architectureLawful_of_repair
    suite.repairPackage

/-- The synthesis candidate satisfies every atom-generated constraint. -/
theorem synthesis_candidate_satisfies
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSatisfies
      suite.synthesisPackage.system
      suite.synthesisCandidate :=
  AtomAxiomatizedSynthesisPackage.candidate_satisfies
    suite.synthesisPackage

/-- Atom synthesis gives architecture lawfulness. -/
theorem architectureLawful_of_synthesis
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSignature.ArchitectureLawful X :=
  AtomAxiomatizedSynthesisPackage.architectureLawful_of_synthesis
    suite.synthesisPackage

/-- The base atom theorem package gives zero curvature. -/
theorem zeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X :=
  ArchitectureSignature.AtomAxiomatizedAAT.architectureZeroCurvatureTheoremPackage
    suite.aat

/-- Repair clearing gives zero curvature through the same atom suite. -/
theorem zeroCurvatureTheoremPackage_of_repair
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X :=
  AtomAxiomatizedRepairPackage.architectureZeroCurvatureTheoremPackage_of_repair
    suite.repairPackage

/-- Synthesis soundness gives zero curvature through the same atom suite. -/
theorem zeroCurvatureTheoremPackage_of_synthesis
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (suite :
      AtomAxiomatizedTheoremSuite
        X E D RepairState RepairRule SynthesisState
        repairSource repairTarget) :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X :=
  AtomAxiomatizedSynthesisPackage.architectureZeroCurvatureTheoremPackage_of_synthesis
    suite.synthesisPackage

end AtomAxiomatizedTheoremSuite

end Formal.Arch
