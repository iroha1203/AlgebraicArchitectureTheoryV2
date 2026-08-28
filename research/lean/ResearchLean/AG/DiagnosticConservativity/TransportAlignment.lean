import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticCovariance
import ResearchLean.AG.DoctrineFiberProduct.ExactBottomGlobalLiftCoherence

/-!
# G-113 revision 2 transport alignment

This module fixes the F0 type surface for the indexed diagnostic transport
equivalence.  At each vertex of one `IndexedBaseDiagramHom`, the G-111
covariant action and the G-112 contravariant semantic-global reindexing are
formed from the same authored base arrow.

## Implementation notes

The G-111 `vertexIndex` is reused rather than introducing a second validated
arrow syntax.  The revision-2 names expose the two opposite-variance functors
and their agreement with the existing diagnostic action.  No equivalence,
fullness, faithfulness, essential surjectivity, unit, or counit is stored in a
field or accepted as an argument; those remain producer obligations after F0.
The rejected alternative was a comparison structure whose fields could carry
the later conclusion before it had been constructed.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/--
The revision-2 covariant push at one indexed vertex, using exactly the G-111
validated vertex term.
-/
noncomputable def indexedDiagnosticTransportPush
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    CoreFiber (D.vertex vertex) ⥤ CoreFiber (E.vertex vertex) :=
  indexedFiberAction (hom.vertexIndex vertex)

/--
The revision-2 contravariant reindexing at the same indexed vertex, generated
by the G-112 semantic-global cleavage.
-/
noncomputable def indexedDiagnosticTransportReindex
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    CoreFiber (E.vertex vertex) ⥤ CoreFiber (D.vertex vertex) :=
  exact_bottom_semantic_global_reindex_functor (hom.app vertex)

/-- The G-111 validated vertex term decodes to the authored diagram hom component. -/
@[simp]
theorem indexedDiagnosticTransport_vertexIndex_decode
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (hom.vertexIndex vertex).decode = hom.app vertex :=
  rfl

/-- The revision-2 push is definitionally the reviewed G-111 indexed action. -/
theorem indexedDiagnosticTransportPush_eq_indexedFiberAction
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    indexedDiagnosticTransportPush hom vertex =
      indexedFiberAction (hom.vertexIndex vertex) :=
  rfl

/-- The revision-2 push uses the canonical core transport over the same base arrow. -/
theorem indexedDiagnosticTransportPush_eq_coreFiberTransportFunctor
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    indexedDiagnosticTransportPush hom vertex =
      coreFiberTransportFunctor (hom.app vertex) :=
  rfl

/-- The revision-2 inverse candidate is exactly the reviewed G-112 reindexing. -/
theorem indexedDiagnosticTransportReindex_eq_semanticGlobal
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    indexedDiagnosticTransportReindex hom vertex =
      exact_bottom_semantic_global_reindex_functor (hom.app vertex) :=
  rfl

/--
On every generated diagnostic interpretation, the revision-2 push object is
the G-111 transported vertex package.
-/
theorem indexedDiagnosticTransportPush_obj_fiberPackage
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    (indexedDiagnosticTransportPush hom vertex).obj
        (source.fiberPackage vertex) =
      (hom.transportedInterpretation source).fiberPackage vertex :=
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
