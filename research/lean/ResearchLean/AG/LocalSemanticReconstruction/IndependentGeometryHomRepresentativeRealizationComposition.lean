import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeReader
import Formal.Util.AssertStandardAxioms

/-!
# Directed representative realization composition on common queries

Implementation notes: support, axis, and observable maps follow a middle
context point and then a middle value point. Their directed character is
retained. Native realization supplies are used only to compare the complete
point table, including every inactive context candidate.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}

/-- Compose all three representative realization roles directly from common primitive context and value points. -/
def composeRealization (s : IndependentContextPrimitive.Table A) (t : IndependentContextPrimitive.Table B)
    (h : Table.{u, v} U .representative) (hp : PointLaws s t h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .representative) : RealizationQuery A C .representative → Bool
  | .representativeSupport W Z x z => IndependentFixedIndexedPointGraph.compose (contextPoints h) hctx
      (support h) hp.supportRows (support k) W Z x z
  | .representativeAxis W Z x z => IndependentFixedIndexedPointGraph.compose (contextPoints h) hctx
      (axis h) hp.axisRows (axis k) W Z x z
  | .representativeObservable W Z x z => IndependentFixedIndexedPointGraph.compose (contextPoints h) hctx
      (observable h) hp.observableRows (observable k) W Z x z

variable {G H K : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (g : PackageTotalHom H.core K.core)
variable (h : Table.{u, v} U .representative) (hm : Maps f h) (hp : NativePoints G.core H.core h)
variable (hctx : ∀ W : ArchCtx G.core.object, ∃! V : ArchCtx H.core.object, contextPoints h W V = true)
variable (k : Table.{u, v} U .representative) (km : Maps g k) (kp : NativePoints H.core K.core k)

/-- Direct composition of every representative query reads the original native realization composite. -/
theorem composeRealization_eq_native :
    composeRealization (IndependentContextPrimitive.read G.core.contextPreorder)
      (IndependentContextPrimitive.read H.core.contextPreorder) h hp hctx k =
      NativeReader.representativeRealizationRead (G := G) (H := K) (PackageTotalHom.comp f g)
        (RealizationTransportSupply.exactComp (G := G) (H := H) (K := K)
          (assemble f h hm hp) (assemble g k km kp)) := by
  funext a
  cases a with
  | representativeSupport W Z x z =>
    exact congrArg (fun t => t W Z x z)
      (IndependentFixedIndexedPointGraph.compose_eq_read (contextPoints h) hctx (support h) hp.supportRows
        (support k) (contextPoints k) kp.supportRows (forward f) hm.context (forward g) km.context)
  | representativeAxis W Z x z =>
    exact congrArg (fun t => t W Z x z)
      (IndependentFixedIndexedPointGraph.compose_eq_read (contextPoints h) hctx (axis h) hp.axisRows
        (axis k) (contextPoints k) kp.axisRows (forward f) hm.context (forward g) km.context)
  | representativeObservable W Z x z =>
    exact congrArg (fun t => t W Z x z)
      (IndependentFixedIndexedPointGraph.compose_eq_read (contextPoints h) hctx (observable h) hp.observableRows
        (observable k) (contextPoints k) kp.observableRows (forward f) hm.context (forward g) km.context)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization
