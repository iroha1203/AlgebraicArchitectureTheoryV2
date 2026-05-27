import Formal.Arch.AtomCoreAAT
import Formal.Arch.Repair.RepairSynthesis

namespace Formal.Arch

universe u v w s r

/--
Repair witness obtained from Atom Core.

The witness is not a primitive atom.  It is a selected law-relative
obstruction circuit, i.e. a minimal bad atom molecule for a selected design law.
-/
structure AtomRepairWitness
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  molecule : AtomMolecule C E D
  required : requiredMolecule molecule
  circuit : ObstructionCircuit law molecule
  nonConclusions : Prop

namespace AtomRepairWitness

/-- An atom repair witness exposes its required selected molecule. -/
theorem selected
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (witness : AtomRepairWitness law requiredMolecule) :
    requiredMolecule witness.molecule :=
  witness.required

/-- An atom repair witness exposes its law-relative obstruction circuit. -/
theorem obstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (witness : AtomRepairWitness law requiredMolecule) :
    ObstructionCircuit law witness.molecule :=
  witness.circuit

/-- Obstruction-circuit repair witnesses are bad for the selected law. -/
theorem bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (witness : AtomRepairWitness law requiredMolecule) :
    law.Bad witness.molecule :=
  obstructionCircuit_bad witness.circuit

end AtomRepairWitness

/--
Repair universe whose witnesses are selected atom obstruction circuits.

The state and measure remain external and bounded: this package does not claim
that every source-code repair or every semantic repair is represented.
-/
structure AtomRepairUniverse
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop)
    (State : Type s) where
  witnessAt : State -> AtomRepairWitness law requiredMolecule -> Prop
  measure : State -> Nat
  stateBoundary : Prop
  witnessBoundary : Prop
  measureBoundary : Prop
  nonConclusions : Prop

namespace AtomRepairUniverse

/-- Read an atom repair universe as the ordinary selected obstruction universe. -/
def selectedObstructionUniverse
    {C : Type u} {E : Type v} {D : Type w} {State : Type s}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (U : AtomRepairUniverse law requiredMolecule State) :
    SelectedObstructionUniverse State
      (AtomRepairWitness law requiredMolecule) where
  selected := fun _ => True
  witnessAt := U.witnessAt
  measure := U.measure

/-- Every atom repair witness is selected in the derived repair universe. -/
theorem selected
    {C : Type u} {E : Type v} {D : Type w} {State : Type s}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (U : AtomRepairUniverse law requiredMolecule State)
    (witness : AtomRepairWitness law requiredMolecule) :
    (U.selectedObstructionUniverse).selected witness := by
  trivial

/-- A state-local atom repair witness is a non-split extension witness. -/
theorem nonSplitWitness_of_witnessAt
    {C : Type u} {E : Type v} {D : Type w} {State : Type s}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (U : AtomRepairUniverse law requiredMolecule State)
    {state : State}
    {witness : AtomRepairWitness law requiredMolecule}
    (hAt : U.witnessAt state witness) :
    NonSplitExtensionWitness U.selectedObstructionUniverse state witness := by
  exact ⟨trivial, hAt⟩

/--
An admissible repair rule for an atom obstruction circuit yields the ordinary
selected repair-measure decrease theorem.
-/
theorem repairStepDecreases_of_admissible
    {C : Type u} {E : Type v} {D : Type w}
    {State : Type s} {Rule : Type r}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (U : AtomRepairUniverse law requiredMolecule State)
    {source target : State} {rule : Rule}
    {witness : AtomRepairWitness law requiredMolecule}
    (hAt : U.witnessAt source witness)
    (hRule :
      AdmissibleRepairRule U.selectedObstructionUniverse rule witness)
    (hStep : RepairStep State Rule source rule target) :
    RepairStepDecreases U.selectedObstructionUniverse source target :=
  Formal.Arch.repairStepDecreases_of_admissible
    (U.nonSplitWitness_of_witnessAt hAt) hRule hStep

end AtomRepairUniverse

/--
Finite repair package whose selected obstructions are atom obstruction circuits.

`targetCircuitWitnessComplete` is the exactness bridge from a required target
obstruction circuit to a repair witness at the target state.  Together with
`FiniteRepairPackage.selectedObstructionsCleared`, it turns finite repair into
`NoRequiredObstructionCircuit`.
-/
structure AtomFiniteRepairPackage
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop)
    (State : Type s) (Rule : Type r)
    (source target : State) where
  repairUniverse : AtomRepairUniverse law requiredMolecule State
  repair :
    FiniteRepairPackage (Rule := Rule)
      repairUniverse.selectedObstructionUniverse source target
  targetCircuitWitnessComplete :
    ∀ molecule,
      requiredMolecule molecule ->
      ObstructionCircuit law molecule ->
        ∃ witness : AtomRepairWitness law requiredMolecule,
          witness.molecule = molecule ∧ repairUniverse.witnessAt target witness
  repairBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace AtomFiniteRepairPackage

/-- The finite atom repair package clears its selected repair witnesses. -/
theorem selectedObstructionsCleared
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomFiniteRepairPackage
        law requiredMolecule State Rule source target) :
    SelectedObstructionsCleared
      pkg.repairUniverse.selectedObstructionUniverse target :=
  FiniteRepairPackage.selectedObstructionsCleared pkg.repair

/-- Finite atom repair gives no required obstruction circuit at the target. -/
theorem target_noRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomFiniteRepairPackage
        law requiredMolecule State Rule source target) :
    NoRequiredObstructionCircuit law requiredMolecule := by
  intro molecule hRequired hCircuit
  rcases pkg.targetCircuitWitnessComplete molecule hRequired hCircuit with
    ⟨witness, _hMolecule, hAt⟩
  exact pkg.selectedObstructionsCleared witness trivial hAt

/-- With the atom lawfulness bridge, finite atom repair gives target lawfulness. -/
theorem target_lawful_of_bridge
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomFiniteRepairPackage
        law requiredMolecule State Rule source target)
    (bridge : AtomLawfulnessBridge law requiredMolecule) :
    LawfulWithinAtomConfiguration law requiredMolecule := by
  exact bridge.lawful_iff_no_obstructionCircuit.mpr
    pkg.target_noRequiredObstructionCircuit

end AtomFiniteRepairPackage

/--
Atom-level repair transition from a source circuit family to a repaired target
circuit family.

This package records that the source has a selected atom obstruction circuit,
while the finite repair package proves that the target selected atom circuit
family is cleared.  It does not claim that every possible obstruction was
removed.
-/
structure AtomRepairTransitionPackage
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (sourceRequired targetRequired : AtomMolecule C E D -> Prop)
    (State : Type s) (Rule : Type r)
    (source target : State) where
  sourceCircuitExists :
    ∃ molecule, sourceRequired molecule ∧ ObstructionCircuit law molecule
  repair :
    AtomFiniteRepairPackage law targetRequired State Rule source target
  transitionBoundary : Prop
  nonConclusions : Prop

namespace AtomRepairTransitionPackage

/-- The source side of the transition exposes a selected atom obstruction circuit. -/
theorem source_has_obstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {sourceRequired targetRequired : AtomMolecule C E D -> Prop}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomRepairTransitionPackage
        law sourceRequired targetRequired State Rule source target) :
    ∃ molecule, sourceRequired molecule ∧ ObstructionCircuit law molecule :=
  pkg.sourceCircuitExists

/-- If source circuits are law-bad, the source selected family is not lawful. -/
theorem source_not_lawful_of_circuitBad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {sourceRequired targetRequired : AtomMolecule C E D -> Prop}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomRepairTransitionPackage
        law sourceRequired targetRequired State Rule source target)
    (circuitBad :
      ∀ molecule,
        sourceRequired molecule ->
        ObstructionCircuit law molecule ->
          law.Bad molecule) :
    ¬ LawfulWithinAtomConfiguration law sourceRequired := by
  intro hLawful
  rcases pkg.sourceCircuitExists with ⟨molecule, hRequired, hCircuit⟩
  exact hLawful molecule hRequired
    (circuitBad molecule hRequired hCircuit)

/-- The target side of the transition has no required atom obstruction circuit. -/
theorem target_noRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {sourceRequired targetRequired : AtomMolecule C E D -> Prop}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomRepairTransitionPackage
        law sourceRequired targetRequired State Rule source target) :
    NoRequiredObstructionCircuit law targetRequired :=
  pkg.repair.target_noRequiredObstructionCircuit

/-- With a target lawfulness bridge, atom repair transition gives target lawfulness. -/
theorem target_lawful_of_bridge
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {sourceRequired targetRequired : AtomMolecule C E D -> Prop}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomRepairTransitionPackage
        law sourceRequired targetRequired State Rule source target)
    (bridge : AtomLawfulnessBridge law targetRequired) :
    LawfulWithinAtomConfiguration law targetRequired :=
  pkg.repair.target_lawful_of_bridge bridge

end AtomRepairTransitionPackage

/--
Pure Atom-AAT together with a finite atom repair package.

This is the Signature-free repair theorem package.  It reads finite repair
clearing as atom-level zero curvature and then builds the atom-only
zero-curvature theorem package over the selected pure Atom-AAT core.
-/
structure AtomAxiomatizedPureRepairPackage
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    (State : Type s) (Rule : Type r)
    (source target : State) where
  law : DesignLaw C E D
  requiredMolecule : AtomMolecule C E D -> Prop
  lawOnSurface : core.surface.laws law
  requiredMoleculesOnSurface :
    ∀ molecule, requiredMolecule molecule ->
      core.surface.molecules molecule
  repair :
    AtomFiniteRepairPackage
      law requiredMolecule State Rule source target
  lawfulnessBridge : AtomLawfulnessBridge law requiredMolecule
  noArchitectureSignatureDependency : Prop
  noArchitectureSignatureDependencyEvidence :
    noArchitectureSignatureDependency
  repairAxiomBoundary : Prop
  theoremPackageBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedPureRepairPackage

/-- Finite atom repair clearing gives no required obstruction circuit. -/
theorem target_noRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    NoRequiredObstructionCircuit pkg.law pkg.requiredMolecule :=
  pkg.repair.target_noRequiredObstructionCircuit

/-- Finite atom repair clearing is atom-level zero curvature. -/
theorem target_atomZeroCurvature
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    AtomZeroCurvature pkg.law pkg.requiredMolecule :=
  atomZeroCurvature_iff_noRequiredObstructionCircuit.mpr
    pkg.target_noRequiredObstructionCircuit

/-- Finite atom repair clearing and the selected bridge give atom lawfulness. -/
theorem target_atomLawful
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule :=
  pkg.repair.target_lawful_of_bridge pkg.lawfulnessBridge

/-- The repair-derived atom zero curvature as an atom-only theorem package. -/
def atomZeroCurvatureTheoremPackage
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    AtomZeroCurvatureTheoremPackage core where
  law := pkg.law
  requiredMolecule := pkg.requiredMolecule
  lawOnSurface := pkg.lawOnSurface
  requiredMoleculesOnSurface := pkg.requiredMoleculesOnSurface
  requiredCircuitsOnSurface := by
    intro molecule hRequired hCircuit
    exact
      core.circuitClosure
        pkg.lawOnSurface
        (pkg.requiredMoleculesOnSurface molecule hRequired)
        hCircuit
  lawfulnessBridge := pkg.lawfulnessBridge
  atomZeroCurvature := pkg.target_atomZeroCurvature
  atomZeroCurvatureBoundary := pkg.theoremPackageBoundary
  theoremPackageBoundary := pkg.theoremPackageBoundary
  nonConclusions := pkg.nonConclusions

/-- Repair-derived zero curvature still uses a law that does not create atoms. -/
theorem law_does_not_create_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    (core.lawSeparation pkg.law pkg.lawOnSurface).lawDoesNotCreateAtoms :=
  AtomZeroCurvatureTheoremPackage.law_does_not_create_atoms
    pkg.atomZeroCurvatureTheoremPackage

/-- Repair-derived zero curvature uses a law that does not change atom existence. -/
theorem law_does_not_change_atom_existence
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    (core.lawSeparation pkg.law pkg.lawOnSurface).lawDoesNotChangeAtomExistence :=
  AtomZeroCurvatureTheoremPackage.law_does_not_change_atom_existence
    pkg.atomZeroCurvatureTheoremPackage

/-- The pure repair package remains independent of observation tooling. -/
theorem independent_of_observation
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (_pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    core.surface.noObservationDependency :=
  AtomAxiomatizedPureAAT.independent_of_observation core

/-- The pure repair package remains independent of SFT forecasting. -/
theorem independent_of_sft
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (_pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    core.surface.noSFTDependency :=
  AtomAxiomatizedPureAAT.independent_of_sft core

/-- The pure repair package remains independent of Signature packages. -/
theorem independent_of_architecture_signature
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg :
      AtomAxiomatizedPureRepairPackage
        core State Rule source target) :
    pkg.noArchitectureSignatureDependency :=
  pkg.noArchitectureSignatureDependencyEvidence

end AtomAxiomatizedPureRepairPackage

end Formal.Arch
