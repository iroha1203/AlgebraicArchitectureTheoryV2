import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedInverseComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationPoints
import Formal.Util.AssertStandardAxioms

/-!
# Primitive composition of explicit realization fibers

Implementation notes: each forward direction follows two forward value rows.
Each backward direction follows the second inverse value before the first.
All three roles retain their original context references and inverse laws.
Native supplies occur only in the all-candidate comparison theorems.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}}

section Primitive

variable {A B C : ArchitectureObject U}
variable (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
variable (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
variable (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)

/-- Compose both support directions directly on their original context and value points. -/
def composeSupport : Direction → IndependentFixedIndexedPointGraph.Table
    (fun W : ArchCtx A => W.Support) (fun Z : ArchCtx C => Z.Support)
  | .forward => IndependentFixedIndexedPointGraph.compose (contextPoints h) hctx
      (support h .forward) hp.supportRows.forward (support k .forward)
  | .backward => IndependentFixedIndexedPointGraph.composeBackward (contextPoints h) hctx
      (support h .backward) (contextPoints k) (support k .forward) (support k .backward) kp.supportRows

/-- Direct support composition preserves every dependent inverse-row law. -/
theorem composeSupport_inverseLaws :
    IndependentFixedIndexedPointGraph.InverseLaws
      (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
      (composeSupport h hp hctx k kp .forward) (composeSupport h hp hctx k kp .backward) :=
  IndependentFixedIndexedPointGraph.compose_inverseLaws (contextPoints h) hctx
    (support h .forward) (support h .backward) hp.supportRows
    (contextPoints k) (support k .forward) (support k .backward) kp.supportRows

/-- Compose both axis directions directly on their original context and value points. -/
def composeAxis : Direction → IndependentFixedIndexedPointGraph.Table
    (fun W : ArchCtx A => W.Axis) (fun Z : ArchCtx C => Z.Axis)
  | .forward => IndependentFixedIndexedPointGraph.compose (contextPoints h) hctx
      (axis h .forward) hp.axisRows.forward (axis k .forward)
  | .backward => IndependentFixedIndexedPointGraph.composeBackward (contextPoints h) hctx
      (axis h .backward) (contextPoints k) (axis k .forward) (axis k .backward) kp.axisRows

/-- Direct axis composition preserves every dependent inverse-row law. -/
theorem composeAxis_inverseLaws :
    IndependentFixedIndexedPointGraph.InverseLaws
      (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
      (composeAxis h hp hctx k kp .forward) (composeAxis h hp hctx k kp .backward) :=
  IndependentFixedIndexedPointGraph.compose_inverseLaws (contextPoints h) hctx
    (axis h .forward) (axis h .backward) hp.axisRows
    (contextPoints k) (axis k .forward) (axis k .backward) kp.axisRows

/-- Compose both observable directions directly on their original context and value points. -/
def composeObservable : Direction → IndependentFixedIndexedPointGraph.Table
    (fun W : ArchCtx A => W.Observable) (fun Z : ArchCtx C => Z.Observable)
  | .forward => IndependentFixedIndexedPointGraph.compose (contextPoints h) hctx
      (observable h .forward) hp.observableRows.forward (observable k .forward)
  | .backward => IndependentFixedIndexedPointGraph.composeBackward (contextPoints h) hctx
      (observable h .backward) (contextPoints k) (observable k .forward) (observable k .backward) kp.observableRows

/-- Direct observable composition preserves every dependent inverse-row law. -/
theorem composeObservable_inverseLaws :
    IndependentFixedIndexedPointGraph.InverseLaws
      (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
      (composeObservable h hp hctx k kp .forward) (composeObservable h hp hctx k kp .backward) :=
  IndependentFixedIndexedPointGraph.compose_inverseLaws (contextPoints h) hctx
    (observable h .forward) (observable h .backward) hp.observableRows
    (contextPoints k) (observable k .forward) (observable k .backward) kp.observableRows

end Primitive

section Native

variable {P Q R : AATCorePackage U}
variable (f : PackageTotalHom P Q) (g : PackageTotalHom Q R)
variable (h : Table.{u, v} U .explicit) (hm : Maps f h) (hp : PointLaws P.object Q.object h)
variable (hctx : ∀ W : ArchCtx P.object, ∃! V : ArchCtx Q.object, contextPoints h W V = true)
variable (k : Table.{u, v} U .explicit) (km : Maps g k) (kp : PointLaws Q.object R.object k)

/-- Both composed support directions read the original native composite at every candidate context pair. -/
theorem composeSupport_eq_native (d : Direction) :
    composeSupport h hp hctx k kp d =
      IndependentFixedIndexedPointGraph.read (forward (PackageTotalHom.comp f g))
        (fun W => (ExplicitRealizationTransportSupply.comp (assemble f h hm hp) (assemble g k km kp)).supportEquiv ⟨W⟩) := by
  have he := IndependentFixedIndexedPointGraph.compose_eq_read (contextPoints h) hctx
    (support h .forward) hp.supportRows.forward (support k .forward) (contextPoints k) kp.supportRows.forward
    (forward f) hm.context (forward g) km.context
  cases d with
  | forward => exact he
  | backward =>
    exact (IndependentFixedIndexedPointGraph.composeBackward_eq_forward (contextPoints h) hctx
      (support h .forward) (support h .backward) hp.supportRows
      (contextPoints k) (support k .forward) (support k .backward) kp.supportRows).trans he

/-- Both composed axis directions read the original native composite at every candidate context pair. -/
theorem composeAxis_eq_native (d : Direction) :
    composeAxis h hp hctx k kp d =
      IndependentFixedIndexedPointGraph.read (forward (PackageTotalHom.comp f g))
        (fun W => (ExplicitRealizationTransportSupply.comp (assemble f h hm hp) (assemble g k km kp)).axisEquiv ⟨W⟩) := by
  have he := IndependentFixedIndexedPointGraph.compose_eq_read (contextPoints h) hctx
    (axis h .forward) hp.axisRows.forward (axis k .forward) (contextPoints k) kp.axisRows.forward
    (forward f) hm.context (forward g) km.context
  cases d with
  | forward => exact he
  | backward =>
    exact (IndependentFixedIndexedPointGraph.composeBackward_eq_forward (contextPoints h) hctx
      (axis h .forward) (axis h .backward) hp.axisRows
      (contextPoints k) (axis k .forward) (axis k .backward) kp.axisRows).trans he

/-- Both composed observable directions read the original native composite at every candidate context pair. -/
theorem composeObservable_eq_native (d : Direction) :
    composeObservable h hp hctx k kp d =
      IndependentFixedIndexedPointGraph.read (forward (PackageTotalHom.comp f g))
        (fun W => (ExplicitRealizationTransportSupply.comp (assemble f h hm hp) (assemble g k km kp)).observableEquiv ⟨W⟩) := by
  have he := IndependentFixedIndexedPointGraph.compose_eq_read (contextPoints h) hctx
    (observable h .forward) hp.observableRows.forward (observable k .forward) (contextPoints k) kp.observableRows.forward
    (forward f) hm.context (forward g) km.context
  cases d with
  | forward => exact he
  | backward =>
    exact (IndependentFixedIndexedPointGraph.composeBackward_eq_forward (contextPoints h) hctx
      (observable h .forward) (observable h .backward) hp.observableRows
      (contextPoints k) (observable k .forward) (observable k .backward) kp.observableRows).trans he

end Native

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization
