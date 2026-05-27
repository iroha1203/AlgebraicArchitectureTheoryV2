import Formal.Arch.Repair.AtomPureRepair
import Formal.Arch.Signature.AtomZeroCurvature

namespace Formal.Arch

universe u v w s r q t

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
