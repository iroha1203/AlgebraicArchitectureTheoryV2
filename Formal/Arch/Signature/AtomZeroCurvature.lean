import Formal.Arch.Atomization
import Formal.Arch.Signature.SignatureLawfulness

namespace Formal.Arch

universe u v w q r

namespace ArchitectureSignature

/--
Atom-derived bridge to the current static zero-curvature theorem package.

The package records the selected atom law, the required atom molecules, the
obstruction-circuit bridge that turns absence of required atom circuits into
atom lawfulness, and the arrangement-law readings needed by the existing
`ArchitectureLawModel`.
-/
structure AtomDerivedZeroCurvaturePackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) (E : Type q) (D : Type r) where
  law : DesignLaw C E D
  requiredMolecule : AtomMolecule C E D -> Prop
  lawfulnessBridge : AtomLawfulnessBridge law requiredMolecule
  noRequiredObstructionCircuit :
    NoRequiredObstructionCircuit law requiredMolecule
  layering : LayeringAtomArrangementLaw X.G law requiredMolecule
  projection : ProjectionAtomArrangementLaw X.G X.π X.GA law requiredMolecule
  lspCompatibleFromLawful :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      LSPCompatible X.π X.O
  boundaryPolicySoundFromLawful :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      BoundaryPolicySound X.G X.boundaryAllowed
  abstractionPolicySoundFromLawful :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      AbstractionPolicySound X.G X.abstractionAllowed
  atomBoundary : Prop
  moleculeBoundary : Prop
  obstructionCircuitBoundary : Prop
  zeroCurvatureBoundary : Prop
  nonConclusions : Prop

namespace AtomDerivedZeroCurvaturePackage

/--
Absence of required atom obstruction circuits gives atom-configuration
lawfulness via the selected atom lawfulness bridge.
-/
theorem atomLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule := by
  exact
    (AtomLawfulnessBridge.lawful_iff_no_obstructionCircuit
      pkg.lawfulnessBridge).mpr
      pkg.noRequiredObstructionCircuit

/--
The selected atom package entails the existing Signature-level architecture
lawfulness predicate.
-/
theorem architectureLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    ArchitectureLawful X := by
  have hAtomLawful :
      LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule :=
    pkg.atomLawful
  have hAcyclic : Acyclic X.G :=
    pkg.layering.acyclic_of_lawful hAtomLawful
  exact
    ⟨walkAcyclic_of_acyclic hAcyclic,
      pkg.projection.projectionSound_of_lawful hAtomLawful,
      pkg.lspCompatibleFromLawful hAtomLawful,
      pkg.boundaryPolicySoundFromLawful hAtomLawful,
      pkg.abstractionPolicySoundFromLawful hAtomLawful⟩

/--
Atom-derived lawfulness gives selected required Signature axes zero.
-/
theorem requiredSignatureAxesZero
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X) := by
  exact
    (architectureLawful_iff_requiredSignatureAxesZero X).mp
      pkg.architectureLawful

/--
Atom-derived lawfulness gives the current proved zero-curvature theorem
package.
-/
theorem architectureZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    ArchitectureZeroCurvatureTheoremPackage X := by
  exact
    architectureZeroCurvatureTheoremPackage_of_architectureLawful X
      pkg.architectureLawful

end AtomDerivedZeroCurvaturePackage

end ArchitectureSignature

end Formal.Arch
