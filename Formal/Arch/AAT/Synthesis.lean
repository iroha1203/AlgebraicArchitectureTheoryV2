import Formal.Arch.AAT.ZeroCurvature

namespace Formal.Arch
namespace AAT

universe u v s

/--
Synthesis soundness package over an Atom-generated AAT core.

The package records a candidate whose interpretation satisfies the selected
no-required-circuit obligation.  It does not claim solver completeness or
global synthesis completeness.
-/
structure SynthesisSoundnessPackage {system : AtomAxiomSystem.{u, v}}
    (core : AATCore system)
    (State : Type s) where
  law : DesignLaw system
  requiredMolecule : Molecule system -> Prop
  lawOnCore : core.laws law
  requiredMoleculesOnCore :
    ∀ molecule, requiredMolecule molecule -> core.molecules molecule
  requiredCircuitsOnCore :
    ∀ {molecule},
      (hRequired : requiredMolecule molecule) ->
      (hCircuit : ObstructionCircuit law molecule) ->
        core.circuits lawOnCore
          (requiredMoleculesOnCore molecule hRequired) hCircuit
  lawfulnessBridge : LawfulnessBridge law requiredMolecule
  candidate : State
  candidateNoRequiredObstructionCircuit :
    NoRequiredObstructionCircuit law requiredMolecule
  synthesisDoesNotCreateAtomsEvidence :
    system.noToolOutputCreatesAtoms
  coverageBoundary : Prop
  exactnessBoundary : Prop
  synthesisBoundary : Prop
  nonConclusions : Prop

namespace SynthesisSoundnessPackage

/-- Candidate soundness produces the pure zero-curvature theorem package. -/
def zeroCurvaturePackage {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s}
    (pkg : SynthesisSoundnessPackage core State) :
    ZeroCurvaturePackage core where
  law := pkg.law
  requiredMolecule := pkg.requiredMolecule
  lawOnCore := pkg.lawOnCore
  requiredMoleculesOnCore := pkg.requiredMoleculesOnCore
  requiredCircuitsOnCore := pkg.requiredCircuitsOnCore
  lawfulnessBridge := pkg.lawfulnessBridge
  zeroCurvature :=
    zeroCurvature_iff_noRequiredObstructionCircuit.mpr
      pkg.candidateNoRequiredObstructionCircuit
  coverageBoundary := pkg.coverageBoundary
  exactnessBoundary := pkg.exactnessBoundary
  theoremPackageBoundary := pkg.synthesisBoundary
  nonConclusions := pkg.nonConclusions

/-- The synthesized candidate discharges the selected no-required-circuit claim. -/
theorem candidate_noRequiredObstructionCircuit
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s}
    (pkg : SynthesisSoundnessPackage core State) :
    NoRequiredObstructionCircuit pkg.law pkg.requiredMolecule :=
  pkg.candidateNoRequiredObstructionCircuit

/-- Candidate soundness gives selected molecule-family lawfulness. -/
theorem candidate_lawfulWithinMoleculeConfiguration
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s}
    (pkg : SynthesisSoundnessPackage core State) :
    LawfulWithinMoleculeConfiguration pkg.law pkg.requiredMolecule :=
  (pkg.zeroCurvaturePackage).lawfulWithinMoleculeConfiguration

/-- Pure AAT synthesis packages do not create atom existence. -/
theorem synthesis_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s}
    (pkg : SynthesisSoundnessPackage core State) :
    system.noToolOutputCreatesAtoms :=
  pkg.synthesisDoesNotCreateAtomsEvidence

end SynthesisSoundnessPackage

end AAT
end Formal.Arch
