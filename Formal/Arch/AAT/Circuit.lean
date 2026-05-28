import Formal.Arch.AAT.Law

namespace Formal.Arch
namespace AAT

universe u v

/-- Minimal molecule for a law-relative badness predicate. -/
def MinimalBadMolecule {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system) (M : Molecule system) : Prop :=
  law.Bad M ∧ ∀ N, ProperSubmolecule N M -> ¬ law.Bad N

/-- A pure AAT obstruction circuit is a law-relative minimal bad molecule. -/
def ObstructionCircuit {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system) (M : Molecule system) : Prop :=
  MinimalBadMolecule law M

theorem obstructionCircuit_bad {system : AtomAxiomSystem.{u, v}}
    {law : DesignLaw system} {M : Molecule system}
    (h : ObstructionCircuit law M) :
    law.Bad M :=
  h.1

theorem obstructionCircuit_minimal {system : AtomAxiomSystem.{u, v}}
    {law : DesignLaw system} {M N : Molecule system}
    (h : ObstructionCircuit law M)
    (hProper : ProperSubmolecule N M) :
    ¬ law.Bad N :=
  h.2 N hProper

/-- Upward-closed selected badness for molecule search. -/
def BadUpwardClosed {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system) : Prop :=
  ∀ {M N}, MoleculeSubset M N -> law.Bad M -> law.Bad N

/--
Selected finite molecule universe for finding law-relative minimal bad
configurations.
-/
structure FiniteMoleculeUniverse {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system) where
  selected : Molecule system -> Prop
  minimalOf :
    ∀ M, selected M -> law.Bad M ->
      { N // selected N ∧ ObstructionCircuit law N ∧ MoleculeSubset N M }
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace FiniteMoleculeUniverse

theorem contains_minimal_bad {system : AtomAxiomSystem.{u, v}}
    {law : DesignLaw system}
    (U : FiniteMoleculeUniverse law)
    {M : Molecule system}
    (hSel : U.selected M) (hBad : law.Bad M) :
    ∃ N, U.selected N ∧ ObstructionCircuit law N ∧ MoleculeSubset N M := by
  rcases U.minimalOf M hSel hBad with ⟨N, hN⟩
  exact ⟨N, hN⟩

theorem bad_iff_contains_obstruction_circuit {system : AtomAxiomSystem.{u, v}}
    {law : DesignLaw system}
    (U : FiniteMoleculeUniverse law)
    (hUp : BadUpwardClosed law)
    {M : Molecule system}
    (hSel : U.selected M) :
    law.Bad M ↔
      ∃ N, U.selected N ∧ ObstructionCircuit law N ∧ MoleculeSubset N M := by
  constructor
  · intro hBad
    exact U.contains_minimal_bad hSel hBad
  · intro h
    rcases h with ⟨N, _hSelN, hCircuit, hSub⟩
    exact hUp hSub hCircuit.1

end FiniteMoleculeUniverse

/-- Lawfulness over a selected family of pure AAT molecules. -/
def LawfulWithinMoleculeConfiguration {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system)
    (requiredMolecule : Molecule system -> Prop) : Prop :=
  ∀ M, requiredMolecule M -> ¬ law.Bad M

/-- No required obstruction circuit remains in the selected molecule boundary. -/
def NoRequiredObstructionCircuit {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system)
    (requiredMolecule : Molecule system -> Prop) : Prop :=
  ∀ M, requiredMolecule M -> ¬ ObstructionCircuit law M

/--
Bridge assumptions connecting selected lawfulness to obstruction-circuit
absence.
-/
structure LawfulnessBridge {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system)
    (requiredMolecule : Molecule system -> Prop) where
  badWitnessComplete :
    ∀ M, requiredMolecule M -> law.Bad M ->
      ∃ Ckt, requiredMolecule Ckt ∧ ObstructionCircuit law Ckt
  circuitBad :
    ∀ M, requiredMolecule M -> ObstructionCircuit law M -> law.Bad M
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace LawfulnessBridge

theorem lawful_iff_no_obstructionCircuit {system : AtomAxiomSystem.{u, v}}
    {law : DesignLaw system}
    {requiredMolecule : Molecule system -> Prop}
    (bridge : LawfulnessBridge law requiredMolecule) :
    LawfulWithinMoleculeConfiguration law requiredMolecule ↔
      NoRequiredObstructionCircuit law requiredMolecule := by
  constructor
  · intro hLawful M hRequired hCircuit
    exact hLawful M hRequired (bridge.circuitBad M hRequired hCircuit)
  · intro hNoCircuit M hRequired hBad
    rcases bridge.badWitnessComplete M hRequired hBad with
      ⟨Ckt, hRequiredCkt, hCircuit⟩
    exact hNoCircuit Ckt hRequiredCkt hCircuit

end LawfulnessBridge

end AAT
end Formal.Arch
