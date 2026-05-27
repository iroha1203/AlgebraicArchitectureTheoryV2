import Formal.Arch.Repair.RepairSynthesis
import Formal.Arch.Signature.AtomZeroCurvature

namespace Formal.Arch

universe u v w s r q t

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
Atom-axiomatized AAT together with a finite atom repair package.

This reads selected repair clearing as an atom-derived route to the existing
architecture lawfulness and zero-curvature theorem package.
-/
structure AtomAxiomatizedRepairPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    (E : Type q) (D : Type r)
    (State : Type s) (Rule : Type t)
    (source target : State) where
  aat : ArchitectureSignature.AtomAxiomatizedAAT X E D
  repair :
    AtomFiniteRepairPackage
      aat.zeroCurvature.law
      aat.zeroCurvature.requiredMolecule
      State Rule source target
  repairAxiomBoundary : Prop
  theoremPackageBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedRepairPackage

/-- The repair package clears required atom obstruction circuits. -/
theorem target_noRequiredObstructionCircuit
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    NoRequiredObstructionCircuit
      pkg.aat.zeroCurvature.law
      pkg.aat.zeroCurvature.requiredMolecule :=
  pkg.repair.target_noRequiredObstructionCircuit

/-- Atom repair clearing and the selected bridge give atom-configuration lawfulness. -/
theorem target_atomLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    LawfulWithinAtomConfiguration
      pkg.aat.zeroCurvature.law
      pkg.aat.zeroCurvature.requiredMolecule := by
  exact
    pkg.aat.zeroCurvature.lawfulnessBridge.lawful_iff_no_obstructionCircuit.mpr
      pkg.target_noRequiredObstructionCircuit

/-- Atom repair clearing yields the existing architecture lawfulness package. -/
theorem architectureLawful_of_repair
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    ArchitectureSignature.ArchitectureLawful X := by
  have hAtomLawful :
      LawfulWithinAtomConfiguration
        pkg.aat.zeroCurvature.law
        pkg.aat.zeroCurvature.requiredMolecule :=
    pkg.target_atomLawful
  have hAcyclic : Acyclic X.G :=
    pkg.aat.zeroCurvature.layering.acyclic_of_lawful hAtomLawful
  exact
    ⟨walkAcyclic_of_acyclic hAcyclic,
      pkg.aat.zeroCurvature.projection.projectionSound_of_lawful
        hAtomLawful,
      pkg.aat.zeroCurvature.lspCompatibleFromLawful hAtomLawful,
      pkg.aat.zeroCurvature.boundaryPolicySoundFromLawful hAtomLawful,
      pkg.aat.zeroCurvature.abstractionPolicySoundFromLawful hAtomLawful⟩

/-- Atom repair clearing yields selected required Signature axes zero. -/
theorem requiredSignatureAxesZero_of_repair
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    ArchitectureSignature.RequiredSignatureAxesZero
      (ArchitectureSignature.ArchitectureLawModel.signatureOf X) := by
  exact
    (ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero X).mp
      pkg.architectureLawful_of_repair

/-- Atom repair clearing yields the existing zero-curvature theorem package. -/
theorem architectureZeroCurvatureTheoremPackage_of_repair
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X := by
  exact
    ArchitectureSignature.architectureZeroCurvatureTheoremPackage_of_architectureLawful
      X pkg.architectureLawful_of_repair

end AtomAxiomatizedRepairPackage

end Formal.Arch
