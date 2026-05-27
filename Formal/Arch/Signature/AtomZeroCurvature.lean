import Formal.Arch.AtomPureAAT
import Formal.Arch.Signature.SignatureLawfulness

namespace Formal.Arch

universe u v w q r s t m

namespace ArchitectureSignature

/--
Atom arrangement laws for the current required static ArchitectureLawModel
components.

This package groups the five arrangement readings that recover the existing
static lawfulness surface from atom-configuration lawfulness.
-/
structure StaticAtomArrangementLawPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) {E : Type q} {D : Type r}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  layering : LayeringAtomArrangementLaw X.G law requiredMolecule
  projection : ProjectionAtomArrangementLaw X.G X.π X.GA law requiredMolecule
  lsp : LSPAtomArrangementLaw X.π X.O law requiredMolecule
  boundaryPolicy :
    EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed law requiredMolecule
  abstractionPolicy :
    EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed law requiredMolecule
  arrangementBoundary : Prop
  nonConclusions : Prop

namespace StaticAtomArrangementLawPackage

theorem strictLayered_of_lawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : StaticAtomArrangementLawPackage X law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    StrictLayered X.G :=
  pkg.layering.strictLayered_of_lawful hLawful

theorem projectionSound_of_lawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : StaticAtomArrangementLawPackage X law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    ProjectionSound X.G X.π X.GA :=
  pkg.projection.projectionSound_of_lawful hLawful

theorem lspCompatible_of_lawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : StaticAtomArrangementLawPackage X law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    LSPCompatible X.π X.O :=
  pkg.lsp.lspCompatible_of_lawful hLawful

theorem boundaryPolicySound_of_lawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : StaticAtomArrangementLawPackage X law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    BoundaryPolicySound X.G X.boundaryAllowed :=
  pkg.boundaryPolicy.policySound_of_lawful hLawful

theorem abstractionPolicySound_of_lawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : StaticAtomArrangementLawPackage X law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    AbstractionPolicySound X.G X.abstractionAllowed :=
  pkg.abstractionPolicy.policySound_of_lawful hLawful

theorem architectureLawful_of_lawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : StaticAtomArrangementLawPackage X law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    ArchitectureLawful X :=
  ⟨walkAcyclic_of_acyclic
      (pkg.layering.acyclic_of_lawful hLawful),
    pkg.projectionSound_of_lawful hLawful,
    pkg.lspCompatible_of_lawful hLawful,
    pkg.boundaryPolicySound_of_lawful hLawful,
    pkg.abstractionPolicySound_of_lawful hLawful⟩

end StaticAtomArrangementLawPackage

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
  staticArrangements :
    StaticAtomArrangementLawPackage X law requiredMolecule
  atomBoundary : Prop
  moleculeBoundary : Prop
  obstructionCircuitBoundary : Prop
  zeroCurvatureBoundary : Prop
  nonConclusions : Prop

namespace AtomDerivedZeroCurvaturePackage

/--
Build the Signature-level atom-derived zero-curvature bridge from the pure
Atom-AAT zero-curvature theorem package plus a Signature static arrangement
package.
-/
def ofAtomZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (arrangements :
      StaticAtomArrangementLawPackage X
        atomPkg.law atomPkg.requiredMolecule)
    (atomBoundary : Prop)
    (moleculeBoundary : Prop)
    (obstructionCircuitBoundary : Prop)
    (zeroCurvatureBoundary : Prop)
    (nonConclusions : Prop) :
    AtomDerivedZeroCurvaturePackage X E D where
  law := atomPkg.law
  requiredMolecule := atomPkg.requiredMolecule
  lawfulnessBridge := atomPkg.lawfulnessBridge
  noRequiredObstructionCircuit := atomPkg.noRequiredObstructionCircuit
  staticArrangements := arrangements
  atomBoundary := atomBoundary
  moleculeBoundary := moleculeBoundary
  obstructionCircuitBoundary := obstructionCircuitBoundary
  zeroCurvatureBoundary := zeroCurvatureBoundary
  nonConclusions := nonConclusions

/--
Build the Signature-level atom-derived bridge from explicit atom arrangement
laws for all current required static law components.
-/
def ofAtomArrangementLaws
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (layering :
      LayeringAtomArrangementLaw X.G
        atomPkg.law atomPkg.requiredMolecule)
    (projection :
      ProjectionAtomArrangementLaw X.G X.π X.GA
        atomPkg.law atomPkg.requiredMolecule)
    (lsp :
      LSPAtomArrangementLaw X.π X.O
        atomPkg.law atomPkg.requiredMolecule)
    (boundaryPolicy :
      EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed
        atomPkg.law atomPkg.requiredMolecule)
    (abstractionPolicy :
      EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed
        atomPkg.law atomPkg.requiredMolecule)
    (atomBoundary : Prop)
    (moleculeBoundary : Prop)
    (obstructionCircuitBoundary : Prop)
    (zeroCurvatureBoundary : Prop)
    (nonConclusions : Prop) :
    AtomDerivedZeroCurvaturePackage X E D :=
  ofAtomZeroCurvatureTheoremPackage
    (X := X)
    atomPkg
    { layering := layering
      projection := projection
      lsp := lsp
      boundaryPolicy := boundaryPolicy
      abstractionPolicy := abstractionPolicy
      arrangementBoundary := atomBoundary
      nonConclusions := nonConclusions }
    atomBoundary
    moleculeBoundary
    obstructionCircuitBoundary
    zeroCurvatureBoundary
    nonConclusions

/--
Build the Signature-level atom-derived bridge from a grouped static atom
arrangement-law package.
-/
def ofStaticAtomArrangementPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (arrangements :
      StaticAtomArrangementLawPackage X
        atomPkg.law atomPkg.requiredMolecule)
    (atomBoundary : Prop)
    (moleculeBoundary : Prop)
    (obstructionCircuitBoundary : Prop)
    (zeroCurvatureBoundary : Prop)
    (nonConclusions : Prop) :
    AtomDerivedZeroCurvaturePackage X E D :=
  ofAtomZeroCurvatureTheoremPackage
    (X := X)
    atomPkg
    arrangements
    atomBoundary
    moleculeBoundary
    obstructionCircuitBoundary
    zeroCurvatureBoundary
    nonConclusions

/--
The Signature-level atom-derived package still carries atom-level zero
curvature as its primitive theorem source.
-/
theorem atomZeroCurvature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    AtomZeroCurvature pkg.law pkg.requiredMolecule :=
  pkg.noRequiredObstructionCircuit

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

/-- The grouped static arrangement laws carried by the atom-derived package. -/
def staticArrangementLawPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    StaticAtomArrangementLawPackage X pkg.law pkg.requiredMolecule :=
  pkg.staticArrangements

/-- Layering arrangement law carried by the grouped static arrangement package. -/
def layering
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    LayeringAtomArrangementLaw X.G pkg.law pkg.requiredMolecule :=
  pkg.staticArrangements.layering

/-- Projection arrangement law carried by the grouped static arrangement package. -/
def projection
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    ProjectionAtomArrangementLaw X.G X.π X.GA pkg.law pkg.requiredMolecule :=
  pkg.staticArrangements.projection

/-- LSP arrangement law carried by the grouped static arrangement package. -/
def lsp
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    LSPAtomArrangementLaw X.π X.O pkg.law pkg.requiredMolecule :=
  pkg.staticArrangements.lsp

/-- Boundary-policy arrangement law carried by the grouped static package. -/
def boundaryPolicy
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed
      pkg.law pkg.requiredMolecule :=
  pkg.staticArrangements.boundaryPolicy

/-- Abstraction-policy arrangement law carried by the grouped static package. -/
def abstractionPolicy
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed
      pkg.law pkg.requiredMolecule :=
  pkg.staticArrangements.abstractionPolicy

/-- Compatibility accessor retained for callers that read LSP from lawfulness. -/
theorem lspCompatibleFromLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D)
    (hLawful : LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule) :
    LSPCompatible X.π X.O :=
  pkg.staticArrangements.lspCompatible_of_lawful hLawful

/-- Compatibility accessor retained for callers that read boundary policy from lawfulness. -/
theorem boundaryPolicySoundFromLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D)
    (hLawful : LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule) :
    BoundaryPolicySound X.G X.boundaryAllowed :=
  pkg.staticArrangements.boundaryPolicySound_of_lawful hLawful

/-- Compatibility accessor retained for callers that read abstraction policy from lawfulness. -/
theorem abstractionPolicySoundFromLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D)
    (hLawful : LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule) :
    AbstractionPolicySound X.G X.abstractionAllowed :=
  pkg.staticArrangements.abstractionPolicySound_of_lawful hLawful

/--
Atom-derived lawfulness recovers the selected strict layering invariant.
-/
theorem strictLayered
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    StrictLayered X.G :=
  pkg.layering.strictLayered_of_lawful pkg.atomLawful

/-- Atom-derived lawfulness recovers graph acyclicity. -/
theorem acyclic
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    Acyclic X.G :=
  pkg.layering.acyclic_of_lawful pkg.atomLawful

/-- Atom-derived lawfulness recovers walk acyclicity. -/
theorem walkAcyclic
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    WalkAcyclic X.G :=
  walkAcyclic_of_acyclic pkg.acyclic

/-- Atom-derived lawfulness recovers projection soundness. -/
theorem projectionSound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    ProjectionSound X.G X.π X.GA :=
  pkg.projection.projectionSound_of_lawful pkg.atomLawful

/-- Atom-derived lawfulness rules out selected projection obstruction witnesses. -/
theorem noProjectionObstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    NoProjectionObstruction X.G X.π X.GA :=
  pkg.projection.noProjectionObstruction_of_lawful pkg.atomLawful

/-- Atom-derived lawfulness recovers LSP compatibility. -/
theorem lspCompatible
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    LSPCompatible X.π X.O :=
  pkg.lspCompatibleFromLawful pkg.atomLawful

/-- Atom-derived lawfulness recovers boundary-policy soundness. -/
theorem boundaryPolicySound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    BoundaryPolicySound X.G X.boundaryAllowed :=
  pkg.boundaryPolicySoundFromLawful pkg.atomLawful

/-- Atom-derived lawfulness recovers abstraction-policy soundness. -/
theorem abstractionPolicySound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    AbstractionPolicySound X.G X.abstractionAllowed :=
  pkg.abstractionPolicySoundFromLawful pkg.atomLawful

/--
The selected atom package entails the existing Signature-level architecture
lawfulness predicate.
-/
theorem architectureLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    ArchitectureLawful X := by
  exact
    ⟨pkg.walkAcyclic,
      pkg.projectionSound,
      pkg.lspCompatible,
      pkg.boundaryPolicySound,
      pkg.abstractionPolicySound⟩

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

/--
Atom-derived lawfulness also gives the matrix diagnostics carried by the
zero-curvature theorem package.
-/
theorem matrixDiagnosticCorollaries
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    [DecidableEq C] [DecidableRel X.G.edge]
    (pkg : AtomDerivedZeroCurvaturePackage X E D) :
    MatrixDiagnosticCorollaries X :=
  matrixDiagnosticCorollaries_of_architectureLawful X
    pkg.architectureLawful

/--
Pure Atom-AAT zero curvature, interpreted through Signature arrangement
readings, gives the existing Signature-level zero-curvature theorem package.
-/
theorem architectureZeroCurvatureTheoremPackage_of_atomZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (arrangements :
      StaticAtomArrangementLawPackage X
        atomPkg.law atomPkg.requiredMolecule) :
    ArchitectureZeroCurvatureTheoremPackage X := by
  exact
    (ofStaticAtomArrangementPackage
      (X := X)
      atomPkg
      arrangements
      True True True True True).architectureZeroCurvatureTheoremPackage

/--
Pure Atom-AAT zero curvature plus atom arrangement laws for all current required
static law components gives the existing Signature-level zero-curvature theorem
package.
-/
theorem architectureZeroCurvatureTheoremPackage_of_atomArrangementLaws
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (layering :
      LayeringAtomArrangementLaw X.G
        atomPkg.law atomPkg.requiredMolecule)
    (projection :
      ProjectionAtomArrangementLaw X.G X.π X.GA
        atomPkg.law atomPkg.requiredMolecule)
    (lsp :
      LSPAtomArrangementLaw X.π X.O
        atomPkg.law atomPkg.requiredMolecule)
    (boundaryPolicy :
      EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed
        atomPkg.law atomPkg.requiredMolecule)
    (abstractionPolicy :
      EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed
        atomPkg.law atomPkg.requiredMolecule) :
    ArchitectureZeroCurvatureTheoremPackage X := by
  exact
    (ofAtomArrangementLaws
      (X := X)
      atomPkg
      layering
      projection
      lsp
      boundaryPolicy
      abstractionPolicy
      True True True True True).architectureZeroCurvatureTheoremPackage

/--
Pure Atom-AAT zero curvature plus a grouped static atom arrangement-law package
gives the existing Signature-level zero-curvature theorem package.
-/
theorem architectureZeroCurvatureTheoremPackage_of_staticAtomArrangementPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (arrangements :
      StaticAtomArrangementLawPackage X
        atomPkg.law atomPkg.requiredMolecule) :
    ArchitectureZeroCurvatureTheoremPackage X :=
  (ofStaticAtomArrangementPackage
      (X := X)
      atomPkg
      arrangements
      True True True True True).architectureZeroCurvatureTheoremPackage

/--
Build the Signature-level atom-derived bridge from the pure Atom-AAT theorem
suite plus a grouped static atom arrangement-law package.
-/
def ofPureTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (atomBoundary : Prop)
    (moleculeBoundary : Prop)
    (obstructionCircuitBoundary : Prop)
    (zeroCurvatureBoundary : Prop)
    (nonConclusions : Prop) :
    AtomDerivedZeroCurvaturePackage X E D :=
  ofStaticAtomArrangementPackage
    (X := X)
    suite.zeroCurvature
    arrangements
    atomBoundary
    moleculeBoundary
    obstructionCircuitBoundary
    zeroCurvatureBoundary
    nonConclusions

/--
Build the Signature-level atom-derived bridge from a pure theorem suite and
explicit atom arrangement laws for all current required static components.
-/
def ofPureTheoremSuiteArrangementLaws
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (layering :
      LayeringAtomArrangementLaw X.G
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (projection :
      ProjectionAtomArrangementLaw X.G X.π X.GA
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (lsp :
      LSPAtomArrangementLaw X.π X.O
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (boundaryPolicy :
      EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (abstractionPolicy :
      EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (atomBoundary : Prop)
    (moleculeBoundary : Prop)
    (obstructionCircuitBoundary : Prop)
    (zeroCurvatureBoundary : Prop)
    (nonConclusions : Prop) :
    AtomDerivedZeroCurvaturePackage X E D :=
  ofAtomArrangementLaws
    (X := X)
    suite.zeroCurvature
    layering
    projection
    lsp
    boundaryPolicy
    abstractionPolicy
    atomBoundary
    moleculeBoundary
    obstructionCircuitBoundary
    zeroCurvatureBoundary
    nonConclusions

/--
Build the Signature-level atom-derived bridge from a pure theorem suite and a
grouped static atom arrangement-law package.
-/
def ofPureTheoremSuiteStaticArrangementPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (atomBoundary : Prop)
    (moleculeBoundary : Prop)
    (obstructionCircuitBoundary : Prop)
    (zeroCurvatureBoundary : Prop)
    (nonConclusions : Prop) :
    AtomDerivedZeroCurvaturePackage X E D :=
  ofPureTheoremSuite
    (X := X)
    suite
    arrangements
    atomBoundary
    moleculeBoundary
    obstructionCircuitBoundary
    zeroCurvatureBoundary
    nonConclusions

/--
A pure Atom-AAT theorem suite, interpreted by a grouped static atom arrangement
law package, gives lawfulness.
-/
theorem architectureLawful_of_pureTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule) :
    ArchitectureLawful X :=
  (ofPureTheoremSuite
      (X := X)
      suite
      arrangements
      True True True True True).architectureLawful

/--
Pure Atom-AAT theorem suite zero curvature, interpreted through Signature
static arrangement readings, gives selected required Signature axes zero.
-/
theorem requiredSignatureAxesZero_of_pureTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule) :
    RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X) :=
  (ofPureTheoremSuite
      (X := X)
      suite
      arrangements
      True True True True True).requiredSignatureAxesZero

/--
Pure Atom-AAT theorem suite zero curvature, interpreted through Signature
static arrangement readings, gives the existing Signature-level
zero-curvature theorem package.
-/
theorem architectureZeroCurvatureTheoremPackage_of_pureTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule) :
    ArchitectureZeroCurvatureTheoremPackage X :=
  (ofPureTheoremSuite
      (X := X)
      suite
      arrangements
      True True True True True).architectureZeroCurvatureTheoremPackage

/--
Pure Atom-AAT theorem suite plus atom arrangement laws for all current required
static law components gives the existing Signature-level zero-curvature theorem
package.
-/
theorem architectureZeroCurvatureTheoremPackage_of_pureTheoremSuiteArrangementLaws
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (layering :
      LayeringAtomArrangementLaw X.G
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (projection :
      ProjectionAtomArrangementLaw X.G X.π X.GA
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (lsp :
      LSPAtomArrangementLaw X.π X.O
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (boundaryPolicy :
      EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (abstractionPolicy :
      EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule) :
    ArchitectureZeroCurvatureTheoremPackage X :=
  (ofPureTheoremSuiteArrangementLaws
      (X := X)
      suite
      layering
      projection
      lsp
      boundaryPolicy
      abstractionPolicy
      True True True True True).architectureZeroCurvatureTheoremPackage

/--
Pure Atom-AAT theorem suite plus a grouped static atom arrangement-law package
gives the existing Signature-level zero-curvature theorem package.
-/
theorem architectureZeroCurvatureTheoremPackage_of_pureTheoremSuiteStaticArrangementPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule) :
    ArchitectureZeroCurvatureTheoremPackage X :=
  (ofPureTheoremSuiteStaticArrangementPackage
      (X := X)
      suite
      arrangements
      True True True True True).architectureZeroCurvatureTheoremPackage

/--
Pure Atom-AAT theorem suite zero curvature, interpreted through Signature
static arrangement readings, gives the matrix diagnostic corollaries carried by the
zero-curvature theorem package.
-/
theorem matrixDiagnosticCorollaries_of_pureTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    [DecidableEq C] [DecidableRel X.G.edge]
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule) :
    MatrixDiagnosticCorollaries X :=
  matrixDiagnosticCorollaries_of_architectureLawful X
    (architectureLawful_of_pureTheoremSuite
      (X := X)
      suite
      arrangements)

end AtomDerivedZeroCurvaturePackage

/--
AAT read as an atom-axiomatized pure theory surface.

This package connects the pure atom surface to the selected zero-curvature
bridge: laws, required molecules, and required obstruction circuits are read
from the atom surface, while the current static theorem package is recovered
through `AtomDerivedZeroCurvaturePackage`.
-/
structure AtomAxiomatizedAAT
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureLawModel C A Obs) (E : Type q) (D : Type r) where
  surface : AATPureTheorySurface C E D
  zeroCurvature : AtomDerivedZeroCurvaturePackage X E D
  lawOnSurface : surface.laws zeroCurvature.law
  requiredMoleculesOnSurface :
    ∀ molecule, zeroCurvature.requiredMolecule molecule ->
      surface.molecules molecule
  requiredCircuitsOnSurface :
    ∀ {molecule},
      (hRequired : zeroCurvature.requiredMolecule molecule) ->
      (hCircuit : ObstructionCircuit zeroCurvature.law molecule) ->
        surface.circuits lawOnSurface
          (requiredMoleculesOnSurface molecule hRequired) hCircuit
  atomAxiomBoundary : Prop
  theoremPackageBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedAAT

/--
Build an atom-axiomatized AAT package from a pure Atom-AAT core, its
atom-only zero-curvature theorem package, and a grouped static atom
arrangement-law package.
-/
def ofPureAtomZeroCurvature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (arrangements :
      StaticAtomArrangementLawPackage X
        atomPkg.law atomPkg.requiredMolecule)
    (atomAxiomBoundary : Prop)
    (theoremPackageBoundary : Prop)
    (nonConclusions : Prop) :
    AtomAxiomatizedAAT X E D where
  surface := core.surface
  zeroCurvature :=
    AtomDerivedZeroCurvaturePackage.ofAtomZeroCurvatureTheoremPackage
      (X := X)
      atomPkg
      arrangements
      atomAxiomBoundary
      atomAxiomBoundary
      theoremPackageBoundary
      theoremPackageBoundary
      nonConclusions
  lawOnSurface := atomPkg.lawOnSurface
  requiredMoleculesOnSurface := atomPkg.requiredMoleculesOnSurface
  requiredCircuitsOnSurface := by
    intro molecule hRequired hCircuit
    exact atomPkg.requiredCircuit_on_surface hRequired hCircuit
  atomAxiomBoundary := atomAxiomBoundary
  theoremPackageBoundary := theoremPackageBoundary
  nonConclusions := nonConclusions

/--
Build an atom-axiomatized AAT package from a pure Atom-AAT zero-curvature
package and explicit atom arrangement laws for all current required static
components.
-/
def ofPureAtomArrangementLaws
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (layering :
      LayeringAtomArrangementLaw X.G
        atomPkg.law atomPkg.requiredMolecule)
    (projection :
      ProjectionAtomArrangementLaw X.G X.π X.GA
        atomPkg.law atomPkg.requiredMolecule)
    (lsp :
      LSPAtomArrangementLaw X.π X.O
        atomPkg.law atomPkg.requiredMolecule)
    (boundaryPolicy :
      EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed
        atomPkg.law atomPkg.requiredMolecule)
    (abstractionPolicy :
      EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed
        atomPkg.law atomPkg.requiredMolecule)
    (atomAxiomBoundary : Prop)
    (theoremPackageBoundary : Prop)
    (nonConclusions : Prop) :
    AtomAxiomatizedAAT X E D :=
  ofPureAtomZeroCurvature
    (X := X)
    atomPkg
    { layering := layering
      projection := projection
      lsp := lsp
      boundaryPolicy := boundaryPolicy
      abstractionPolicy := abstractionPolicy
      arrangementBoundary := atomAxiomBoundary
      nonConclusions := nonConclusions }
    atomAxiomBoundary
    theoremPackageBoundary
    nonConclusions

/--
Build an atom-axiomatized AAT package from a pure Atom-AAT zero-curvature
package and a grouped static atom arrangement-law package.
-/
def ofPureAtomStaticArrangementPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {core : AtomAxiomatizedPureAAT C E D}
    (atomPkg : AtomZeroCurvatureTheoremPackage core)
    (arrangements :
      StaticAtomArrangementLawPackage X
        atomPkg.law atomPkg.requiredMolecule)
    (atomAxiomBoundary : Prop)
    (theoremPackageBoundary : Prop)
    (nonConclusions : Prop) :
    AtomAxiomatizedAAT X E D :=
  ofPureAtomZeroCurvature
    (X := X)
    atomPkg
    arrangements
    atomAxiomBoundary
    theoremPackageBoundary
    nonConclusions

/--
Build an atom-axiomatized AAT package from the pure Atom-AAT theorem suite and
a grouped static atom arrangement-law package.
-/
def ofPureTheoremSuite
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (atomAxiomBoundary : Prop)
    (theoremPackageBoundary : Prop)
    (nonConclusions : Prop) :
    AtomAxiomatizedAAT X E D :=
  ofPureAtomZeroCurvature
    (X := X)
    suite.zeroCurvature
    arrangements
    atomAxiomBoundary
    theoremPackageBoundary
    nonConclusions

/--
Build an atom-axiomatized AAT package from a pure theorem suite and explicit
atom arrangement laws for all current required static components.
-/
def ofPureTheoremSuiteArrangementLaws
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (layering :
      LayeringAtomArrangementLaw X.G
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (projection :
      ProjectionAtomArrangementLaw X.G X.π X.GA
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (lsp :
      LSPAtomArrangementLaw X.π X.O
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (boundaryPolicy :
      EdgePolicyAtomArrangementLaw X.G X.boundaryAllowed
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (abstractionPolicy :
      EdgePolicyAtomArrangementLaw X.G X.abstractionAllowed
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (atomAxiomBoundary : Prop)
    (theoremPackageBoundary : Prop)
    (nonConclusions : Prop) :
    AtomAxiomatizedAAT X E D :=
  ofPureAtomArrangementLaws
    (X := X)
    suite.zeroCurvature
    layering
    projection
    lsp
    boundaryPolicy
    abstractionPolicy
    atomAxiomBoundary
    theoremPackageBoundary
    nonConclusions

/--
Build an atom-axiomatized AAT package from a pure theorem suite and a grouped
static atom arrangement-law package.
-/
def ofPureTheoremSuiteStaticArrangementPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    {RepairState : Type s} {RepairRule : Type t}
    {SynthesisState : Type m}
    {repairSource repairTarget : RepairState}
    (suite :
      AtomAxiomatizedPureTheoremSuite
        C E D RepairState RepairRule SynthesisState
        repairSource repairTarget)
    (arrangements :
      StaticAtomArrangementLawPackage X
        suite.zeroCurvature.law
        suite.zeroCurvature.requiredMolecule)
    (atomAxiomBoundary : Prop)
    (theoremPackageBoundary : Prop)
    (nonConclusions : Prop) :
    AtomAxiomatizedAAT X E D :=
  ofPureTheoremSuite
    (X := X)
    suite
    arrangements
    atomAxiomBoundary
    theoremPackageBoundary
    nonConclusions

/-- The atom-axiomatized AAT surface is independent of observation tooling. -/
theorem independent_of_observation
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    pkg.surface.noObservationDependency :=
  pkg.surface.independent_of_observation

/-- The atom-axiomatized AAT surface is independent of SFT forecasting. -/
theorem independent_of_sft
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    pkg.surface.noSFTDependency :=
  pkg.surface.independent_of_sft

/-- Required molecules selected by the atom-axiomatized package are on its pure surface. -/
theorem requiredMolecule_on_surface
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.zeroCurvature.requiredMolecule molecule) :
    pkg.surface.molecules molecule :=
  pkg.requiredMoleculesOnSurface molecule hRequired

/--
Atoms occurring in required molecules remain selected by the same pure atom
surface.
-/
theorem atom_of_requiredMolecule
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.zeroCurvature.requiredMolecule molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    pkg.surface.atoms atom :=
  pkg.surface.atom_of_selected_molecule
    (pkg.requiredMolecule_on_surface hRequired) hAtom

/-- Required molecules are supported by the package's selected atom universe. -/
theorem requiredMolecule_supportedBy_surface_atoms
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.zeroCurvature.requiredMolecule molecule) :
    AtomMoleculeSupportedBy pkg.surface.selectedAtomUniverse molecule :=
  pkg.surface.selected_molecule_supportedBy_selected_atoms
    (pkg.requiredMolecule_on_surface hRequired)

/-- Atoms in required molecules are primitive Atom Core facts. -/
theorem requiredMolecule_atom_is_primitive
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.zeroCurvature.requiredMolecule molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    PrimitiveArchitectureAtom atom :=
  have _hSelected : pkg.surface.atoms atom :=
    pkg.atom_of_requiredMolecule hRequired hAtom
  primitiveArchitectureAtom_constructive atom

/-- Required atom obstruction circuits are selected by the pure atom surface. -/
theorem requiredCircuit_on_surface
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.zeroCurvature.requiredMolecule molecule)
    (hCircuit : ObstructionCircuit pkg.zeroCurvature.law molecule) :
    pkg.surface.circuits pkg.lawOnSurface
      (pkg.requiredMoleculesOnSurface molecule hRequired) hCircuit :=
  pkg.requiredCircuitsOnSurface hRequired hCircuit

/-- The atom-axiomatized package exposes atom-level zero curvature. -/
theorem atomZeroCurvature
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    AtomZeroCurvature
      pkg.zeroCurvature.law pkg.zeroCurvature.requiredMolecule :=
  pkg.zeroCurvature.atomZeroCurvature

/-- The atom-axiomatized package gives atom-configuration lawfulness. -/
theorem atomLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    LawfulWithinAtomConfiguration
      pkg.zeroCurvature.law pkg.zeroCurvature.requiredMolecule :=
  pkg.zeroCurvature.atomLawful

/-- The atom-axiomatized package recovers the selected strict layering invariant. -/
theorem strictLayered
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    StrictLayered X.G :=
  pkg.zeroCurvature.strictLayered

/-- The atom-axiomatized package recovers graph acyclicity. -/
theorem acyclic
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    Acyclic X.G :=
  pkg.zeroCurvature.acyclic

/-- The atom-axiomatized package recovers walk acyclicity. -/
theorem walkAcyclic
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    WalkAcyclic X.G :=
  pkg.zeroCurvature.walkAcyclic

/-- The atom-axiomatized package recovers projection soundness. -/
theorem projectionSound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    ProjectionSound X.G X.π X.GA :=
  pkg.zeroCurvature.projectionSound

/--
The atom-axiomatized package rules out selected projection obstruction
witnesses.
-/
theorem noProjectionObstruction
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    NoProjectionObstruction X.G X.π X.GA :=
  pkg.zeroCurvature.noProjectionObstruction

/-- The atom-axiomatized package recovers LSP compatibility. -/
theorem lspCompatible
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    LSPCompatible X.π X.O :=
  pkg.zeroCurvature.lspCompatible

/-- The atom-axiomatized package recovers boundary-policy soundness. -/
theorem boundaryPolicySound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    BoundaryPolicySound X.G X.boundaryAllowed :=
  pkg.zeroCurvature.boundaryPolicySound

/-- The atom-axiomatized package recovers abstraction-policy soundness. -/
theorem abstractionPolicySound
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    AbstractionPolicySound X.G X.abstractionAllowed :=
  pkg.zeroCurvature.abstractionPolicySound

/-- The atom-axiomatized package gives existing Signature-level lawfulness. -/
theorem architectureLawful
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedAAT X E D) :
    ArchitectureLawful X :=
  pkg.zeroCurvature.architectureLawful

/-- The atom-axiomatized package gives selected required Signature axes zero. -/
theorem requiredSignatureAxesZero
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg : AtomAxiomatizedAAT X E D) :
    RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X) :=
  pkg.zeroCurvature.requiredSignatureAxesZero

/-- The atom-axiomatized package gives the current zero-curvature theorem package. -/
theorem architectureZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg : AtomAxiomatizedAAT X E D) :
    ArchitectureZeroCurvatureTheoremPackage X :=
  pkg.zeroCurvature.architectureZeroCurvatureTheoremPackage

/-- The atom-axiomatized package gives the matrix diagnostic corollaries. -/
theorem matrixDiagnosticCorollaries
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureLawModel C A Obs} {E : Type q} {D : Type r}
    [DecidableEq C] [DecidableRel X.G.edge]
    (pkg : AtomAxiomatizedAAT X E D) :
    MatrixDiagnosticCorollaries X :=
  pkg.zeroCurvature.matrixDiagnosticCorollaries

end AtomAxiomatizedAAT

end ArchitectureSignature

end Formal.Arch
