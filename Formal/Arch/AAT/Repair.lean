import Formal.Arch.AAT.ZeroCurvature

namespace Formal.Arch
namespace AAT

universe u v s r

/--
Repair clearing package over an Atom-generated AAT core.

The repair package records that a bounded target state has no required
obstruction circuit for a selected law.  It reuses the pure zero-curvature
package as its formal conclusion.
-/
structure RepairClearingPackage {system : AtomAxiomSystem.{u, v}}
    (core : AATCore system)
    (State : Type s) (Rule : Type r)
    (source target : State) where
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
  targetNoRequiredObstructionCircuit :
    NoRequiredObstructionCircuit law requiredMolecule
  repairDoesNotCreateAtomsEvidence :
    system.noToolOutputCreatesAtoms
  repairBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace RepairClearingPackage

/-- Repair clearing produces the pure zero-curvature theorem package. -/
def zeroCurvaturePackage {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg : RepairClearingPackage core State Rule source target) :
    ZeroCurvaturePackage core where
  law := pkg.law
  requiredMolecule := pkg.requiredMolecule
  lawOnCore := pkg.lawOnCore
  requiredMoleculesOnCore := pkg.requiredMoleculesOnCore
  requiredCircuitsOnCore := pkg.requiredCircuitsOnCore
  lawfulnessBridge := pkg.lawfulnessBridge
  zeroCurvature :=
    zeroCurvature_iff_noRequiredObstructionCircuit.mpr
      pkg.targetNoRequiredObstructionCircuit
  coverageBoundary := pkg.repairBoundary
  exactnessBoundary := pkg.exactnessBoundary
  theoremPackageBoundary := pkg.repairBoundary
  nonConclusions := pkg.nonConclusions

/-- Repair clearing gives no required obstruction circuit at the target. -/
theorem target_noRequiredObstructionCircuit
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg : RepairClearingPackage core State Rule source target) :
    NoRequiredObstructionCircuit pkg.law pkg.requiredMolecule :=
  pkg.targetNoRequiredObstructionCircuit

/-- Repair clearing gives lawfulness over the selected molecule family. -/
theorem target_lawfulWithinMoleculeConfiguration
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg : RepairClearingPackage core State Rule source target) :
    LawfulWithinMoleculeConfiguration pkg.law pkg.requiredMolecule :=
  (pkg.zeroCurvaturePackage).lawfulWithinMoleculeConfiguration

/-- Pure AAT repair packages do not create atom existence. -/
theorem repair_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    {State : Type s} {Rule : Type r}
    {source target : State}
    (pkg : RepairClearingPackage core State Rule source target) :
    system.noToolOutputCreatesAtoms :=
  pkg.repairDoesNotCreateAtomsEvidence

end RepairClearingPackage

end AAT
end Formal.Arch
