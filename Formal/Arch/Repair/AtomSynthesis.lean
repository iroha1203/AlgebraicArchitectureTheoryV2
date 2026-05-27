import Formal.Arch.Repair.AtomPureSynthesis
import Formal.Arch.Signature.AtomZeroCurvature

namespace Formal.Arch

universe u v w s q r

/--
Synthesis soundness package generated from atom axioms.

The candidate satisfies the atom-generated constraint system.  If the candidate
also satisfies the no-required-circuit constraint, the same atom arrangement
bridges recover the existing zero-curvature theorem package.
-/
structure AtomAxiomatizedSynthesisPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    (E : Type q) (D : Type r)
    (State : Type s) where
  aat : ArchitectureSignature.AtomAxiomatizedAAT X E D
  spec :
    AtomAATSynthesisSpec
      aat.surface
      aat.zeroCurvature.law
      aat.zeroCurvature.requiredMolecule
      State
  candidate : State
  candidateAtoms :
    ∀ atom, aat.surface.atoms atom -> spec.stateHasAtom candidate atom
  candidateMolecules :
    ∀ molecule,
      aat.surface.molecules molecule ->
        spec.stateHasMolecule candidate molecule
  candidateLaws :
    ∀ law, aat.surface.laws law -> spec.stateHasLaw candidate law
  candidateNoRequiredObstructionCircuit :
    spec.stateNoRequiredObstructionCircuit candidate
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  synthesisBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedSynthesisPackage

/-- The atom-generated synthesis constraint system for this package. -/
def system
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    SynthesisConstraintSystem State
      (AtomAATSynthesisConstraint C E D) :=
  pkg.spec.constraintSystem

/-- The synthesized candidate satisfies every atom-generated constraint. -/
theorem candidate_satisfies
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    ArchitectureSatisfies pkg.system pkg.candidate := by
  intro constraint hRequired
  cases constraint with
  | atom atom =>
      exact pkg.candidateAtoms atom hRequired
  | molecule molecule =>
      exact pkg.candidateMolecules molecule hRequired
  | law law =>
      exact pkg.candidateLaws law hRequired
  | noRequiredObstructionCircuits =>
      exact pkg.candidateNoRequiredObstructionCircuit

/-- Atom synthesis soundness as the ordinary `SynthesisSoundnessPackage`. -/
def synthesisSoundnessPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    SynthesisSoundnessPackage pkg.system where
  candidate := pkg.candidate
  sound := pkg.candidate_satisfies
  coverageAssumptions := pkg.coverageAssumptions
  exactnessAssumptions := pkg.exactnessAssumptions
  nonConclusions := pkg.nonConclusions

/-- Candidate soundness can also be read through the ordinary synthesis package. -/
theorem candidate_satisfies_via_synthesisPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    ArchitectureSatisfies
      pkg.system
      (pkg.synthesisSoundnessPackage).candidate :=
  SynthesisSoundnessPackage.candidate_satisfies
    pkg.synthesisSoundnessPackage

/-- The synthesized candidate discharges the selected no-required-circuit claim. -/
theorem candidate_noRequiredObstructionCircuit
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    NoRequiredObstructionCircuit
      pkg.aat.zeroCurvature.law
      pkg.aat.zeroCurvature.requiredMolecule :=
  pkg.spec.noRequiredObstructionCircuit_of_state
    pkg.candidateNoRequiredObstructionCircuit

/-- Candidate no-circuit soundness gives atom-configuration lawfulness. -/
theorem candidate_atomLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    LawfulWithinAtomConfiguration
      pkg.aat.zeroCurvature.law
      pkg.aat.zeroCurvature.requiredMolecule := by
  exact
    pkg.aat.zeroCurvature.lawfulnessBridge.lawful_iff_no_obstructionCircuit.mpr
      pkg.candidate_noRequiredObstructionCircuit

/-- Atom synthesis soundness yields the existing architecture lawfulness package. -/
theorem architectureLawful_of_synthesis
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    ArchitectureSignature.ArchitectureLawful X := by
  have hAtomLawful :
      LawfulWithinAtomConfiguration
        pkg.aat.zeroCurvature.law
        pkg.aat.zeroCurvature.requiredMolecule :=
    pkg.candidate_atomLawful
  have hAcyclic : Acyclic X.G :=
    pkg.aat.zeroCurvature.layering.acyclic_of_lawful hAtomLawful
  exact
    ⟨walkAcyclic_of_acyclic hAcyclic,
      pkg.aat.zeroCurvature.projection.projectionSound_of_lawful
        hAtomLawful,
      pkg.aat.zeroCurvature.lspCompatibleFromLawful hAtomLawful,
      pkg.aat.zeroCurvature.boundaryPolicySoundFromLawful hAtomLawful,
      pkg.aat.zeroCurvature.abstractionPolicySoundFromLawful hAtomLawful⟩

/-- Atom synthesis soundness yields selected required Signature axes zero. -/
theorem requiredSignatureAxesZero_of_synthesis
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    ArchitectureSignature.RequiredSignatureAxesZero
      (ArchitectureSignature.ArchitectureLawModel.signatureOf X) := by
  exact
    (ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero X).mp
      pkg.architectureLawful_of_synthesis

/-- Atom synthesis soundness yields the existing zero-curvature theorem package. -/
theorem architectureZeroCurvatureTheoremPackage_of_synthesis
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r} {State : Type s}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg : AtomAxiomatizedSynthesisPackage X E D State) :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X := by
  exact
    ArchitectureSignature.architectureZeroCurvatureTheoremPackage_of_architectureLawful
      X pkg.architectureLawful_of_synthesis

end AtomAxiomatizedSynthesisPackage

end Formal.Arch
