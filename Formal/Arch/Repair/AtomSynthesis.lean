import Formal.Arch.Repair.RepairSynthesis
import Formal.Arch.Signature.AtomZeroCurvature

namespace Formal.Arch

universe u v w s q r c

/--
Atom-facing synthesis constraints.

The constraints are generated from a pure atom surface: selected atoms,
selected molecules, selected laws, and absence of required atom obstruction
circuits.  They are theorem-facing constraints, not solver output.
-/
inductive AtomAATSynthesisConstraint (C : Type u) (E : Type v) (D : Type w) where
  | atom : ArchitectureAtom C E D -> AtomAATSynthesisConstraint C E D
  | molecule : AtomMolecule C E D -> AtomAATSynthesisConstraint C E D
  | law : DesignLaw C E D -> AtomAATSynthesisConstraint C E D
  | noRequiredObstructionCircuits : AtomAATSynthesisConstraint C E D

/--
A state interpretation for atom-derived synthesis constraints.

This is the boundary that says what it means for a synthesized state to contain
the selected atoms/molecules/laws and to expose no required obstruction circuit.
-/
structure AtomAATSynthesisSpec
    {C : Type u} {E : Type v} {D : Type w}
    (surface : AATPureTheorySurface C E D)
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop)
    (State : Type s) where
  stateHasAtom : State -> ArchitectureAtom C E D -> Prop
  stateHasMolecule : State -> AtomMolecule C E D -> Prop
  stateHasLaw : State -> DesignLaw C E D -> Prop
  stateNoRequiredObstructionCircuit : State -> Prop
  stateNoRequiredObstructionCircuitSound :
    ∀ state,
      stateNoRequiredObstructionCircuit state ->
        NoRequiredObstructionCircuit law requiredMolecule
  interpretationBoundary : Prop
  nonConclusions : Prop

namespace AtomAATSynthesisSpec

/-- The ordinary synthesis constraint system induced by an atom synthesis spec. -/
def constraintSystem
    {C : Type u} {E : Type v} {D : Type w}
    {surface : AATPureTheorySurface C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {State : Type s}
    (spec : AtomAATSynthesisSpec surface law requiredMolecule State) :
    SynthesisConstraintSystem State
      (AtomAATSynthesisConstraint C E D) where
  required := fun
    | AtomAATSynthesisConstraint.atom atom => surface.atoms atom
    | AtomAATSynthesisConstraint.molecule molecule =>
        surface.molecules molecule
    | AtomAATSynthesisConstraint.law selectedLaw =>
        surface.laws selectedLaw
    | AtomAATSynthesisConstraint.noRequiredObstructionCircuits => True
  satisfies := fun state constraint =>
    match constraint with
    | AtomAATSynthesisConstraint.atom atom =>
        spec.stateHasAtom state atom
    | AtomAATSynthesisConstraint.molecule molecule =>
        spec.stateHasMolecule state molecule
    | AtomAATSynthesisConstraint.law selectedLaw =>
        spec.stateHasLaw state selectedLaw
    | AtomAATSynthesisConstraint.noRequiredObstructionCircuits =>
        spec.stateNoRequiredObstructionCircuit state

/-- A state satisfying the no-circuit atom constraint gives no required circuit. -/
theorem noRequiredObstructionCircuit_of_state
    {C : Type u} {E : Type v} {D : Type w}
    {surface : AATPureTheorySurface C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {State : Type s}
    (spec : AtomAATSynthesisSpec surface law requiredMolecule State)
    {state : State}
    (hState : spec.stateNoRequiredObstructionCircuit state) :
    NoRequiredObstructionCircuit law requiredMolecule :=
  spec.stateNoRequiredObstructionCircuitSound state hState

end AtomAATSynthesisSpec

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

/--
Contradictory atom constraints give a proof-carrying no-solution certificate.

The contradiction is atom-level: one required constraint entails a selected
atom, while another required constraint entails its negation.
-/
structure AtomConstraintContradiction
    {State : Type s} {Constraint : Type c}
    {C : Type u} {E : Type v} {D : Type w}
    (system : SynthesisConstraintSystem State Constraint)
    (stateHasAtom : State -> ArchitectureAtom C E D -> Prop) where
  atom : ArchitectureAtom C E D
  requiresAtom : Constraint
  forbidsAtom : Constraint
  requiresAtomRequired : system.required requiresAtom
  forbidsAtomRequired : system.required forbidsAtom
  requiresAtomSound :
    ∀ state, system.satisfies state requiresAtom ->
      stateHasAtom state atom
  forbidsAtomSound :
    ∀ state, system.satisfies state forbidsAtom ->
      ¬ stateHasAtom state atom
  contradictionBoundary : Prop
  nonConclusions : Prop

namespace AtomConstraintContradiction

/-- Atom contradiction implies no architecture satisfies the constraint system. -/
theorem noArchitectureSatisfies
    {State : Type s} {Constraint : Type c}
    {C : Type u} {E : Type v} {D : Type w}
    {system : SynthesisConstraintSystem State Constraint}
    {stateHasAtom : State -> ArchitectureAtom C E D -> Prop}
    (contradiction :
      AtomConstraintContradiction system stateHasAtom) :
    NoArchitectureSatisfies system := by
  intro state hSatisfies
  exact
    (contradiction.forbidsAtomSound state
      (hSatisfies contradiction.forbidsAtom
        contradiction.forbidsAtomRequired))
      (contradiction.requiresAtomSound state
        (hSatisfies contradiction.requiresAtom
          contradiction.requiresAtomRequired))

/-- Package an atom contradiction as an ordinary valid no-solution certificate. -/
def noSolutionCertificate
    {State : Type s} {Constraint : Type c}
    {C : Type u} {E : Type v} {D : Type w}
    {system : SynthesisConstraintSystem State Constraint}
    {stateHasAtom : State -> ArchitectureAtom C E D -> Prop}
    (contradiction :
      AtomConstraintContradiction system stateHasAtom)
    (Certificate : Type r) (cert : Certificate) :
    NoSolutionCertificate Certificate system cert where
  valid := True
  sound := by
    intro _hValid
    exact contradiction.noArchitectureSatisfies
  coverageAssumptions := contradiction.contradictionBoundary
  exactnessAssumptions := contradiction.contradictionBoundary
  nonConclusions := contradiction.nonConclusions

/-- A valid atom contradiction certificate yields no-solution soundness. -/
theorem noArchitectureSatisfies_of_valid_certificate
    {State : Type s} {Constraint : Type c}
    {C : Type u} {E : Type v} {D : Type w}
    {system : SynthesisConstraintSystem State Constraint}
    {stateHasAtom : State -> ArchitectureAtom C E D -> Prop}
    (contradiction :
      AtomConstraintContradiction system stateHasAtom)
    (Certificate : Type r) (cert : Certificate)
    (hValid :
      ValidNoSolutionCertificate
        (contradiction.noSolutionCertificate Certificate cert)) :
    NoArchitectureSatisfies system :=
  NoSolutionCertificate.sound_of_valid
    (contradiction.noSolutionCertificate Certificate cert)
    hValid

end AtomConstraintContradiction

end Formal.Arch
