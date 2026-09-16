import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardCoverage
import Formal.Util.AssertStandardAxioms

/-!
# Structural forward coverage for the concrete CS readings

The full-family context rebase retains the source context's minimal support
data exactly, and its functor maps every selected boundary restriction.  These
facts give support and boundary preservation for arbitrary lens and protocol
forward morphisms without an inverse coordinate map.

Signature-axis visibility is deliberately not claimed here.  Its predicate
requires a restriction into the target reading, including a contravariant map
from every target observable.  A non-surjective forward coordinate map does
not supply that reverse observable map, and the coordinate-local auxiliary
maps of the preceding cycle are not a single global observable action.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Lens support and boundary -/

/-- Exact Atom support visible in a source context remains visible after the
full-family endpoint rebase. -/
theorem lensAATForwardSupportVisible
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    {W : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (atom : LensAATAtom input)
    (hvisible : (lensAATGeometryCoverageRequirements input X).supportVisibleOn
      W atom) :
    (lensAATGeometryCoverageRequirements input Y).supportVisibleOn
      ((f.lawContextFunctor).obj ⟨W⟩).ctx atom :=
  hvisible

/-- Every selected source boundary restriction is mapped to the corresponding
boundary restriction between the rebased target contexts. -/
theorem lensAATForwardBoundaryVisible
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    {W base : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (hvisible : (lensAATGeometryCoverageRequirements input X).boundaryVisibleOn
      W base) :
    (lensAATGeometryCoverageRequirements input Y).boundaryVisibleOn
      ((f.lawContextFunctor).obj ⟨W⟩).ctx
      ((f.lawContextFunctor).obj ⟨base⟩).ctx :=
  leOfHom (f.lawContextFunctor.map (homOfLE hvisible))

/-! ## Protocol support and boundary -/

/-- Exact protocol Atom support is unchanged by the endpoint rebase. -/
theorem protocolAATForwardSupportVisible
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (atom : ProtocolAATAtom input)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).supportVisibleOn
      W atom) :
    (protocolAATGeometryCoverageRequirements input Y).supportVisibleOn
      ((f.lawContextFunctor).obj ⟨W⟩).ctx atom :=
  hvisible

/-- Every selected protocol boundary restriction is mapped by the same
endpoint rebase functor. -/
theorem protocolAATForwardBoundaryVisible
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    {W base : Site.ArchCtx
      (protocolLawObject input X.State X.toLawStructure)}
    (hvisible :
      (protocolAATGeometryCoverageRequirements input X).boundaryVisibleOn
        W base) :
    (protocolAATGeometryCoverageRequirements input Y).boundaryVisibleOn
      ((f.lawContextFunctor).obj ⟨W⟩).ctx
      ((f.lawContextFunctor).obj ⟨base⟩).ctx :=
  leOfHom (f.lawContextFunctor.map (homOfLE hvisible))

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
