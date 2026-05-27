import Formal.Arch.Operation.AtomPureOperation
import Formal.Arch.Signature.AtomZeroCurvature

namespace Formal.Arch

universe u v w q r

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

/-- Forget the Signature interpretation and recover the pure atom operation package. -/
def pureOperationPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    {X : ArchitectureSignature.ArchitectureLawModel C A Obs}
    {E : Type q} {D : Type r}
    (pkg : AtomAxiomatizedOperationPackage X E D) :
    AtomAxiomatizedPureOperationPackage C E D where
  surface := pkg.aat.surface
  operation := pkg.operation
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  operationAxiomBoundary := pkg.operationAxiomBoundary
  theoremPackageBoundary := pkg.theoremPackageBoundary
  nonConclusions := pkg.nonConclusions

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
