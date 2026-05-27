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
  aat : ArchitectureSignature.AtomAxiomatizedAAT X E D
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
