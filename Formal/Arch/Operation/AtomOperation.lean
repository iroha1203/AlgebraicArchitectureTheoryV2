import Formal.Arch.Operation.OperationInvariant
import Formal.Arch.Signature.AtomZeroCurvature

namespace Formal.Arch

universe u v w q r

/--
An atom presentation covers the selected pure AAT surface when every selected
atom is observed with a measurement-carrying status.
-/
def AtomSurfacePresented
    {C : Type u} {E : Type v} {D : Type w}
    (surface : AATPureTheorySurface C E D)
    (presentation : AtomPresentation C E D) : Prop :=
  ∀ atom, surface.atoms atom ->
    ∃ observed,
      presentation.observed observed ∧
      observed.atom = atom ∧
      observed.measurementStatus.SupportsMeasurement

/--
An atom delta preserves a pure AAT surface when every atom selected by the
surface is selected as preserved by the delta.
-/
def AtomDeltaPreservesSurface
    {C : Type u} {E : Type v} {D : Type w}
    (surface : AATPureTheorySurface C E D)
    (delta : AtomDelta C E D) : Prop :=
  ∀ atom, surface.atoms atom -> delta.preserved atom

/--
An operation over atom presentations, relative to a pure AAT atom surface.

The package is deliberately presentation-level: it says that a selected atom
surface is preserved across a validated atom delta, and then exposes that fact
as the ordinary AAT `PreservesInvariant` relation.
-/
structure AtomPresentationOperation
    {C : Type u} {E : Type v} {D : Type w}
    (surface : AATPureTheorySurface C E D) where
  delta : PresentedAtomDelta C E D
  preservesSurface :
    AtomSurfacePresented surface delta.before ->
      AtomDeltaPreservesSurface surface delta.delta
  preservedSurfaceObservedAfter :
    ∀ atom, surface.atoms atom ->
      AtomSurfacePresented surface delta.before ->
      delta.delta.preserved atom ->
        ∃ observed,
          delta.after.observed observed ∧
          observed.atom = atom ∧
          observed.measurementStatus.SupportsMeasurement
  operationBoundary : Prop
  nonConclusions : Prop

namespace AtomPresentationOperation

/-- Source presentation of an atom presentation operation. -/
def source
    {C : Type u} {E : Type v} {D : Type w}
    {surface : AATPureTheorySurface C E D}
    (op : AtomPresentationOperation surface) :
    AtomPresentation C E D :=
  op.delta.before

/-- Target presentation of an atom presentation operation. -/
def target
    {C : Type u} {E : Type v} {D : Type w}
    {surface : AATPureTheorySurface C E D}
    (op : AtomPresentationOperation surface) :
    AtomPresentation C E D :=
  op.delta.after

/-- The selected invariant: this presentation covers the pure atom surface. -/
def atomSurfacePresentedHolds
    {C : Type u} {E : Type v} {D : Type w}
    (surface : AATPureTheorySurface C E D)
    (_ : Unit) (presentation : AtomPresentation C E D) : Prop :=
  AtomSurfacePresented surface presentation

/--
If the source presentation covers the pure surface, a surface-preserving atom
operation gives a target presentation that also covers the same surface.
-/
theorem target_presented_of_source
    {C : Type u} {E : Type v} {D : Type w}
    {surface : AATPureTheorySurface C E D}
    (op : AtomPresentationOperation surface)
    (hSource : AtomSurfacePresented surface (source op)) :
    AtomSurfacePresented surface (target op) := by
  intro atom hAtom
  exact
    op.preservedSurfaceObservedAfter atom hAtom hSource
      (op.preservesSurface hSource atom hAtom)

/--
The atom-surface preservation package is an ordinary operation/invariant
preservation theorem.
-/
theorem preservesSurfaceInvariant
    {C : Type u} {E : Type v} {D : Type w}
    {surface : AATPureTheorySurface C E D}
    (op : AtomPresentationOperation surface) :
    PreservesInvariant
      (source (surface := surface))
      (target (surface := surface))
      (atomSurfacePresentedHolds surface)
      op () := by
  intro hSource
  exact target_presented_of_source op hSource

/--
The same preservation can be read through the `Ops` closure API for the
singleton selected atom-surface invariant family.
-/
theorem ops_mem_surfaceInvariant
    {C : Type u} {E : Type v} {D : Type w}
    {surface : AATPureTheorySurface C E D}
    (op : AtomPresentationOperation surface) :
    Ops
      (source (surface := surface))
      (target (surface := surface))
      (atomSurfacePresentedHolds surface)
      (fun I : Unit => I = ())
      op := by
  intro I hI
  subst I
  exact preservesSurfaceInvariant op

end AtomPresentationOperation

/--
Atom-axiomatized AAT together with a surface-preserving atom presentation
operation.

This combines the pure atom surface, atom-derived zero-curvature theorem
package, and ordinary operation/invariant preservation bridge.  It does not
classify every operation or prove extractor completeness.
-/
structure AtomAxiomatizedOperationPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    (E : Type q) (D : Type r) where
  aat : ArchitectureSignature.AtomAxiomatizedAAT X E D
  operation : AtomPresentationOperation aat.surface
  operationAxiomBoundary : Prop
  theoremPackageBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedOperationPackage

/-- The packaged atom operation preserves the selected pure atom surface. -/
theorem preservesSurfaceInvariant
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedOperationPackage X E D) :
    PreservesInvariant
      (AtomPresentationOperation.source (surface := pkg.aat.surface))
      (AtomPresentationOperation.target (surface := pkg.aat.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds pkg.aat.surface)
      pkg.operation () := by
  exact AtomPresentationOperation.preservesSurfaceInvariant pkg.operation

/-- The packaged atom operation belongs to the singleton atom-surface `Ops` family. -/
theorem ops_mem_surfaceInvariant
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedOperationPackage X E D) :
    Ops
      (AtomPresentationOperation.source (surface := pkg.aat.surface))
      (AtomPresentationOperation.target (surface := pkg.aat.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds pkg.aat.surface)
      (fun I : Unit => I = ())
      pkg.operation := by
  exact AtomPresentationOperation.ops_mem_surfaceInvariant pkg.operation

/-- The atom-axiomatized package still recovers the zero-curvature theorem package. -/
theorem architectureZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (pkg : AtomAxiomatizedOperationPackage X E D) :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.architectureZeroCurvatureTheoremPackage
      pkg.aat

end AtomAxiomatizedOperationPackage

end Formal.Arch
