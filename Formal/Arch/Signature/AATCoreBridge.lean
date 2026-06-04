import Formal.Arch.AAT.ZeroCurvature
import Formal.Arch.AAT.GeneratedLawModel
import Formal.Arch.Signature.SignatureLawfulness

namespace Formal.Arch
namespace ArchitectureSignature

universe u v w q r

/--
Signature / ArchSig bridge as an analysis layer over an Atom-generated AAT core.

The bridge consumes an `AAT.ZeroCurvaturePackage`; it does not define AAT,
create atoms, or promote validation artifacts to Lean theorem discharge.
LLM-native `LawPolicy` artifacts select a tooling policy for reading observations;
they do not replace the pure AAT law carried by the core.
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

/--
Construct the Signature bridge from an Atom-generated law model.

Callers still provide the analysis / tooling boundary propositions, but they do
not provide an `architectureLawfulFromAAT` proof.  The bridge consumes the
generated zero-curvature package and derives Signature lawfulness from the
generated law model itself.
-/
noncomputable def ofGeneratedLawModel
    {system : AtomAxiomSystem.{q, r}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (model : AAT.GeneratedArchitectureLawModel object)
    (analyzesUsingAAT archSigDoesNotDefineAAT
      unknownRejectedUnmeasuredSeparated measuredZeroBoundary
      validationIsNotTheoremDischarge nonConclusions : Prop)
    (hAnalyzesUsingAAT : analyzesUsingAAT)
    (hArchSigDoesNotDefineAAT : archSigDoesNotDefineAAT)
    (hUnknownRejectedUnmeasuredSeparated :
      unknownRejectedUnmeasuredSeparated) :
    AATCoreSignatureLawfulnessBridge
      model.generatedAATCore model.toArchitectureLawModel where
  zeroCurvaturePackage := model.generatedZeroCurvaturePackage
  architectureLawfulFromAAT := by
    intro _hGeneratedLawfulWithin
    exact model.generatedArchitectureLawful
  analyzesUsingAAT := analyzesUsingAAT
  analyzesUsingAATEvidence := hAnalyzesUsingAAT
  archSigDoesNotDefineAAT := archSigDoesNotDefineAAT
  archSigDoesNotDefineAATEvidence := hArchSigDoesNotDefineAAT
  archSigDoesNotCreateAtomsEvidence :=
    system.tool_output_does_not_create_atoms
  unknownRejectedUnmeasuredSeparated :=
    unknownRejectedUnmeasuredSeparated
  unknownRejectedUnmeasuredSeparatedEvidence :=
    hUnknownRejectedUnmeasuredSeparated
  measuredZeroBoundary := measuredZeroBoundary
  validationIsNotTheoremDischarge := validationIsNotTheoremDischarge
  nonConclusions := nonConclusions

/-- Generated constructor stores the generated zero-curvature package. -/
theorem ofGeneratedLawModel_zeroCurvaturePackage_eq_generated
    {system : AtomAxiomSystem.{q, r}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (model : AAT.GeneratedArchitectureLawModel object)
    (analyzesUsingAAT archSigDoesNotDefineAAT
      unknownRejectedUnmeasuredSeparated measuredZeroBoundary
      validationIsNotTheoremDischarge nonConclusions : Prop)
    (hAnalyzesUsingAAT : analyzesUsingAAT)
    (hArchSigDoesNotDefineAAT : archSigDoesNotDefineAAT)
    (hUnknownRejectedUnmeasuredSeparated :
      unknownRejectedUnmeasuredSeparated) :
    (ofGeneratedLawModel model analyzesUsingAAT archSigDoesNotDefineAAT
      unknownRejectedUnmeasuredSeparated measuredZeroBoundary
      validationIsNotTheoremDischarge nonConclusions
      hAnalyzesUsingAAT hArchSigDoesNotDefineAAT
      hUnknownRejectedUnmeasuredSeparated).zeroCurvaturePackage =
        model.generatedZeroCurvaturePackage := by
  rfl

/-- Generated constructor derives Signature lawfulness from the generated model. -/
theorem ofGeneratedLawModel_architectureLawful
    {system : AtomAxiomSystem.{q, r}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (model : AAT.GeneratedArchitectureLawModel object) :
    ArchitectureLawful model.toArchitectureLawModel :=
  model.generatedArchitectureLawful

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
