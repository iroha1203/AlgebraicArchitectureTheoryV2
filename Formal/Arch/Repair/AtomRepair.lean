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

/-- Atom repair clearing recovers strict layering. -/
theorem target_strictLayered
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    StrictLayered X.G :=
  pkg.aat.zeroCurvature.layering.strictLayered_of_lawful
    pkg.target_atomLawful

/-- Atom repair clearing recovers walk acyclicity. -/
theorem target_walkAcyclic
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    WalkAcyclic X.G :=
  walkAcyclic_of_acyclic
    (pkg.aat.zeroCurvature.layering.acyclic_of_lawful
      pkg.target_atomLawful)

/-- Atom repair clearing recovers projection soundness. -/
theorem target_projectionSound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    ProjectionSound X.G X.π X.GA :=
  pkg.aat.zeroCurvature.projection.projectionSound_of_lawful
    pkg.target_atomLawful

/-- Atom repair clearing rules out selected projection obstruction witnesses. -/
theorem target_noProjectionObstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    NoProjectionObstruction X.G X.π X.GA :=
  pkg.aat.zeroCurvature.projection.noProjectionObstruction_of_lawful
    pkg.target_atomLawful

/-- Atom repair clearing recovers LSP compatibility. -/
theorem target_lspCompatible
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    LSPCompatible X.π X.O :=
  pkg.aat.zeroCurvature.lspCompatibleFromLawful
    pkg.target_atomLawful

/-- Atom repair clearing recovers boundary-policy soundness. -/
theorem target_boundaryPolicySound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    ArchitectureSignature.BoundaryPolicySound X.G X.boundaryAllowed :=
  pkg.aat.zeroCurvature.boundaryPolicySoundFromLawful
    pkg.target_atomLawful

/-- Atom repair clearing recovers abstraction-policy soundness. -/
theorem target_abstractionPolicySound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    {State : Type s} {Rule : Type t}
    {source target : State}
    (pkg :
      AtomAxiomatizedRepairPackage
        X E D State Rule source target) :
    ArchitectureSignature.AbstractionPolicySound X.G X.abstractionAllowed :=
  pkg.aat.zeroCurvature.abstractionPolicySoundFromLawful
    pkg.target_atomLawful

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
  exact
    ⟨pkg.target_walkAcyclic,
      pkg.target_projectionSound,
      pkg.target_lspCompatible,
      pkg.target_boundaryPolicySound,
      pkg.target_abstractionPolicySound⟩

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
