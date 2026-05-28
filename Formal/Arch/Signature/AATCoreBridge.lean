import Formal.Arch.AAT.ZeroCurvature
import Formal.Arch.Signature.SignatureLawfulness

namespace Formal.Arch
namespace ArchitectureSignature

universe u v w q r

/--
Signature / ArchSig bridge as an analysis layer over an Atom-generated AAT core.

The bridge consumes an `AAT.ZeroCurvaturePackage`; it does not define AAT,
create atoms, or promote validation artifacts to Lean theorem discharge.
-/
structure AATCoreSignatureLawfulnessBridge
    {system : AtomAxiomSystem.{q, r}}
    (core : AAT.AATCore system)
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) where
  zeroCurvaturePackage : AAT.ZeroCurvaturePackage core
  architectureLawfulFromAAT :
    AAT.LawfulWithinMoleculeConfiguration
      zeroCurvaturePackage.law
      zeroCurvaturePackage.requiredMolecule ->
        ArchitectureLawful X
  analyzesUsingAAT : Prop
  analyzesUsingAATEvidence : analyzesUsingAAT
  archSigDoesNotDefineAAT : Prop
  archSigDoesNotDefineAATEvidence : archSigDoesNotDefineAAT
  archSigDoesNotCreateAtomsEvidence :
    system.noToolOutputCreatesAtoms
  unknownRejectedUnmeasuredSeparated : Prop
  unknownRejectedUnmeasuredSeparatedEvidence :
    unknownRejectedUnmeasuredSeparated
  measuredZeroBoundary : Prop
  validationIsNotTheoremDischarge : Prop
  nonConclusions : Prop

namespace AATCoreSignatureLawfulnessBridge

/-- The bridge derives Signature lawfulness from pure AAT zero curvature. -/
theorem architectureLawful
    {system : AtomAxiomSystem.{q, r}}
    {core : AAT.AATCore system}
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs}
    (bridge : AATCoreSignatureLawfulnessBridge core X) :
    ArchitectureLawful X :=
  bridge.architectureLawfulFromAAT
    bridge.zeroCurvaturePackage.lawfulWithinMoleculeConfiguration

/--
The Signature zero reading is a consequence of Signature lawfulness, not the
definition of AAT core.
-/
theorem requiredSignatureAxesZero
    {system : AtomAxiomSystem.{q, r}}
    {core : AAT.AATCore system}
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (bridge : AATCoreSignatureLawfulnessBridge core X) :
    RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X) :=
  (architectureLawful_iff_requiredSignatureAxesZero X).mp
    bridge.architectureLawful

/-- ArchSig analyzes using AAT; it does not define the AAT core. -/
theorem archsig_does_not_define_aat
    {system : AtomAxiomSystem.{q, r}}
    {core : AAT.AATCore system}
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs}
    (bridge : AATCoreSignatureLawfulnessBridge core X) :
    bridge.archSigDoesNotDefineAAT :=
  bridge.archSigDoesNotDefineAATEvidence

/-- ArchSig analysis does not create atom existence. -/
theorem archsig_does_not_create_atoms
    {system : AtomAxiomSystem.{q, r}}
    {core : AAT.AATCore system}
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs}
    (bridge : AATCoreSignatureLawfulnessBridge core X) :
    system.noToolOutputCreatesAtoms :=
  bridge.archSigDoesNotCreateAtomsEvidence

/-- Unknown / rejected / unmeasured observations are not measured zero. -/
theorem unknown_rejected_unmeasured_separated
    {system : AtomAxiomSystem.{q, r}}
    {core : AAT.AATCore system}
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs}
    (bridge : AATCoreSignatureLawfulnessBridge core X) :
    bridge.unknownRejectedUnmeasuredSeparated :=
  bridge.unknownRejectedUnmeasuredSeparatedEvidence

/-- The bridge consumes the pure zero-curvature package carried by the core. -/
theorem noRequiredObstructionCircuit
    {system : AtomAxiomSystem.{q, r}}
    {core : AAT.AATCore system}
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs}
    (bridge : AATCoreSignatureLawfulnessBridge core X) :
    AAT.NoRequiredObstructionCircuit
      bridge.zeroCurvaturePackage.law
      bridge.zeroCurvaturePackage.requiredMolecule :=
  bridge.zeroCurvaturePackage.noRequiredObstructionCircuit

end AATCoreSignatureLawfulnessBridge

end ArchitectureSignature
end Formal.Arch
