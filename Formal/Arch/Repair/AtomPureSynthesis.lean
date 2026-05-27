import Formal.Arch.AtomCoreAAT
import Formal.Arch.Repair.RepairSynthesis

namespace Formal.Arch

universe u v w s r c

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
Pure Atom-AAT synthesis package generated from atom axioms.

The candidate satisfies an atom-generated constraint system over a pure
Atom-AAT core.  If it also satisfies the no-required-circuit constraint, the
package yields atom-level zero curvature before any Signature reading.
-/
structure AtomAxiomatizedPureSynthesisPackage
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    (State : Type s) where
  law : DesignLaw C E D
  requiredMolecule : AtomMolecule C E D -> Prop
  lawOnSurface : core.surface.laws law
  requiredMoleculesOnSurface :
    ∀ molecule, requiredMolecule molecule ->
      core.surface.molecules molecule
  spec :
    AtomAATSynthesisSpec
      core.surface
      law
      requiredMolecule
      State
  candidate : State
  candidateAtoms :
    ∀ atom, core.surface.atoms atom -> spec.stateHasAtom candidate atom
  candidateMolecules :
    ∀ molecule,
      core.surface.molecules molecule ->
        spec.stateHasMolecule candidate molecule
  candidateLaws :
    ∀ selectedLaw,
      core.surface.laws selectedLaw ->
        spec.stateHasLaw candidate selectedLaw
  candidateNoRequiredObstructionCircuit :
    spec.stateNoRequiredObstructionCircuit candidate
  lawfulnessBridge : AtomLawfulnessBridge law requiredMolecule
  noArchitectureSignatureDependency : Prop
  noArchitectureSignatureDependencyEvidence :
    noArchitectureSignatureDependency
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  synthesisBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedPureSynthesisPackage

/-- The atom-generated synthesis constraint system for this package. -/
def system
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    SynthesisConstraintSystem State
      (AtomAATSynthesisConstraint C E D) :=
  pkg.spec.constraintSystem

/-- The synthesized candidate satisfies every atom-generated constraint. -/
theorem candidate_satisfies
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
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
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    SynthesisSoundnessPackage pkg.system where
  candidate := pkg.candidate
  sound := pkg.candidate_satisfies
  coverageAssumptions := pkg.coverageAssumptions
  exactnessAssumptions := pkg.exactnessAssumptions
  nonConclusions := pkg.nonConclusions

/-- Candidate soundness can also be read through the ordinary synthesis package. -/
theorem candidate_satisfies_via_synthesisPackage
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    ArchitectureSatisfies
      pkg.system
      (pkg.synthesisSoundnessPackage).candidate :=
  SynthesisSoundnessPackage.candidate_satisfies
    pkg.synthesisSoundnessPackage

/-- The synthesized candidate discharges the selected no-required-circuit claim. -/
theorem candidate_noRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    NoRequiredObstructionCircuit pkg.law pkg.requiredMolecule :=
  pkg.spec.noRequiredObstructionCircuit_of_state
    pkg.candidateNoRequiredObstructionCircuit

/-- Candidate no-circuit soundness is atom-level zero curvature. -/
theorem candidate_atomZeroCurvature
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    AtomZeroCurvature pkg.law pkg.requiredMolecule :=
  atomZeroCurvature_iff_noRequiredObstructionCircuit.mpr
    pkg.candidate_noRequiredObstructionCircuit

/-- Candidate no-circuit soundness gives atom-configuration lawfulness. -/
theorem candidate_atomLawful
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule :=
  pkg.lawfulnessBridge.lawful_iff_no_obstructionCircuit.mpr
    pkg.candidate_noRequiredObstructionCircuit

/-- The synthesis-derived atom zero curvature as an atom-only theorem package. -/
def atomZeroCurvatureTheoremPackage
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    AtomZeroCurvatureTheoremPackage core where
  law := pkg.law
  requiredMolecule := pkg.requiredMolecule
  lawOnSurface := pkg.lawOnSurface
  requiredMoleculesOnSurface := by
    intro molecule hRequired
    exact pkg.requiredMoleculesOnSurface molecule hRequired
  requiredCircuitsOnSurface := by
    intro molecule hRequired hCircuit
    exact
      core.circuitClosure
        pkg.lawOnSurface
        (pkg.requiredMoleculesOnSurface molecule hRequired)
        hCircuit
  lawfulnessBridge := pkg.lawfulnessBridge
  atomZeroCurvature := pkg.candidate_atomZeroCurvature
  atomZeroCurvatureBoundary := pkg.synthesisBoundary
  theoremPackageBoundary := pkg.synthesisBoundary
  nonConclusions := pkg.nonConclusions

/-- Synthesis-derived zero curvature uses a law that does not create atoms. -/
theorem law_does_not_create_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    (core.lawSeparation pkg.law pkg.lawOnSurface).lawDoesNotCreateAtoms :=
  AtomZeroCurvatureTheoremPackage.law_does_not_create_atoms
    pkg.atomZeroCurvatureTheoremPackage

/-- Synthesis-derived zero curvature uses a law that does not change atom existence. -/
theorem law_does_not_change_atom_existence
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    (core.lawSeparation pkg.law pkg.lawOnSurface).lawDoesNotChangeAtomExistence :=
  AtomZeroCurvatureTheoremPackage.law_does_not_change_atom_existence
    pkg.atomZeroCurvatureTheoremPackage

/-- The pure synthesis package remains independent of observation tooling. -/
theorem independent_of_observation
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (_pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    core.surface.noObservationDependency :=
  AtomAxiomatizedPureAAT.independent_of_observation core

/-- The pure synthesis package remains independent of SFT forecasting. -/
theorem independent_of_sft
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (_pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    core.surface.noSFTDependency :=
  AtomAxiomatizedPureAAT.independent_of_sft core

/-- The pure synthesis package remains independent of Signature packages. -/
theorem independent_of_architecture_signature
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s}
    (pkg : AtomAxiomatizedPureSynthesisPackage core State) :
    pkg.noArchitectureSignatureDependency :=
  pkg.noArchitectureSignatureDependencyEvidence

end AtomAxiomatizedPureSynthesisPackage

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
