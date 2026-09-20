import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationCompositionFibers
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointAction
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeReader
import Formal.Util.AssertStandardAxioms

/-!
# Complete primitive explicit realization composition

Implementation notes: the composed inverse fiber points determine the actual
context action through the existing primitive action equation. Each action
reads one backward composite value, applies the original context operation at
that value, and reads one forward composite point. Naturality of the original
native composite proves the comparison, including both kinds of inactive
context pair. No completed context action is a new local value.
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

/-- Compose all inverse fibers and actual-action queries using only their original primitive points. -/
def composeRealization : RealizationQuery A C .explicit → Bool
  | .explicitSupport d W Z x z => composeSupport h hp hctx k kp d W Z x z
  | .explicitAxis d W Z x z => composeAxis h hp hctx k kp d W Z x z
  | .explicitObservable d W Z x z => composeObservable h hp hctx k kp d W Z x z
  | .actualSupport W X V Y g y z => IndependentFixedIndexedPointGraph.action
      (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
      (composeSupport h hp hctx k kp .forward) (composeSupport h hp hctx k kp .backward)
      (composeSupport_inverseLaws h hp hctx k kp) W X V Y g.supportMap y z
  | .actualAxis W X V Y g y z => IndependentFixedIndexedPointGraph.action
      (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
      (composeAxis h hp hctx k kp .forward) (composeAxis h hp hctx k kp .backward)
      (composeAxis_inverseLaws h hp hctx k kp) W X V Y g.axisMap y z
  | .actualObservable W X V Y g y z => IndependentFixedIndexedPointGraph.action
      (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
      (composeObservable h hp hctx k kp .forward) (composeObservable h hp hctx k kp .backward)
      (composeObservable_inverseLaws h hp hctx k kp) X W Y V g.observableRestrict y z

end Primitive

section NativeInactive

variable {P Q : AATCorePackage U}
variable (f : PackageTotalHom P Q) (R : ExplicitRealizationTransportSupply P Q f)

/-- Either inactive context pair makes every native actual support point false. -/
theorem readActualSupport_inactive (W X : ArchCtx P.object) (V Y : ArchCtx Q.object)
    (g : ContextMorphism W X) (y : V.Support) (z : Y.Support)
    (hn : forward f W ≠ V ∨ forward f X ≠ Y) :
    readActualSupport f R W X V Y g y z = false := by
  classical
  rcases hn with hw | hx
  · simp [readActualSupport, hw]
  · simp [readActualSupport, hx]

/-- Either inactive context pair makes every native actual axis point false. -/
theorem readActualAxis_inactive (W X : ArchCtx P.object) (V Y : ArchCtx Q.object)
    (g : ContextMorphism W X) (y : V.Axis) (z : Y.Axis)
    (hn : forward f W ≠ V ∨ forward f X ≠ Y) :
    readActualAxis f R W X V Y g y z = false := by
  classical
  rcases hn with hw | hx
  · simp [readActualAxis, hw]
  · simp [readActualAxis, hx]

/-- Either inactive context pair makes every native actual observable point false. -/
theorem readActualObservable_inactive (W X : ArchCtx P.object) (V Y : ArchCtx Q.object)
    (g : ContextMorphism W X) (y : Y.Observable) (z : V.Observable)
    (hn : forward f W ≠ V ∨ forward f X ≠ Y) :
    readActualObservable f R W X V Y g y z = false := by
  classical
  rcases hn with hw | hx
  · simp [readActualObservable, hw]
  · simp [readActualObservable, hx]

end NativeInactive

section Native

variable {G H K : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (g : PackageTotalHom H.core K.core)
variable (h : Table.{u, v} U .explicit) (hm : Maps f h) (hp : PointLaws G.core.object H.core.object h)
variable (hctx : ∀ W : ArchCtx G.core.object, ∃! V : ArchCtx H.core.object, contextPoints h W V = true)
variable (k : Table.{u, v} U .explicit) (km : Maps g k) (kp : PointLaws H.core.object K.core.object k)

/-- Every primitive fiber and actual-action query reads the original native explicit realization composite. -/
theorem composeRealization_eq_native : composeRealization h hp hctx k kp =
    NativeReader.explicitRealizationRead (G := G) (H := K) (PackageTotalHom.comp f g)
      (ExplicitRealizationTransportSupply.comp (assemble f h hm hp) (assemble g k km kp)) := by
  classical
  let Rcmp := ExplicitRealizationTransportSupply.comp (assemble f h hm hp) (assemble g k km kp)
  have hc : ∀ W Z, IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) W Z = true ↔
      forward (PackageTotalHom.comp f g) W = Z :=
    IndependentFixedIndexedPointGraph.compose_index_iff (contextPoints h) hctx (contextPoints k)
      (forward f) hm.context (forward g) km.context
  funext a
  cases a with
  | explicitSupport d W Z x z =>
    exact congrArg (fun t => t W Z x z) (composeSupport_eq_native f g h hm hp hctx k km kp d)
  | explicitAxis d W Z x z =>
    exact congrArg (fun t => t W Z x z) (composeAxis_eq_native f g h hm hp hctx k km kp d)
  | explicitObservable d W Z x z =>
    exact congrArg (fun t => t W Z x z) (composeObservable_eq_native f g h hm hp hctx k km kp d)
  | actualSupport W X V Y a y z =>
    by_cases hw : forward (PackageTotalHom.comp f g) W = V
    · subst V
      by_cases hx : forward (PackageTotalHom.comp f g) X = Y
      · subst Y
        apply Bool.eq_iff_iff.mpr
        exact (IndependentFixedIndexedPointGraph.action_point_iff
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeSupport h hp hctx k kp .forward) (composeSupport h hp hctx k kp .backward)
            (composeSupport_inverseLaws h hp hctx k kp)
          (forward (PackageTotalHom.comp f g)) hc (fun W => Rcmp.supportEquiv ⟨W⟩)
          (composeSupport_eq_native f g h hm hp hctx k km kp .forward).symm
          W X a.supportMap (Rcmp.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) a).supportMap
          (fun x => (Rcmp.support_naturality (W := ⟨W⟩) (V := ⟨X⟩) a x).symm) y z).trans
          (readActualSupport_point_iff (PackageTotalHom.comp f g) Rcmp W X a y z).symm
      · have hx0 : IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) X Y = false :=
          Bool.eq_false_iff.mpr (fun ht => hx ((hc X Y).1 ht))
        exact (IndependentFixedIndexedPointGraph.action_inactive
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeSupport h hp hctx k kp .forward) (composeSupport h hp hctx k kp .backward)
            (composeSupport_inverseLaws h hp hctx k kp)
          W X (forward (PackageTotalHom.comp f g) W) Y
          a.supportMap y z (Or.inr hx0)).trans
          (readActualSupport_inactive (PackageTotalHom.comp f g) Rcmp W X _ Y a y z (Or.inr hx)).symm
    · have hw0 : IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) W V = false :=
        Bool.eq_false_iff.mpr (fun ht => hw ((hc W V).1 ht))
      exact (IndependentFixedIndexedPointGraph.action_inactive
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeSupport h hp hctx k kp .forward) (composeSupport h hp hctx k kp .backward)
            (composeSupport_inverseLaws h hp hctx k kp)
          W X V Y a.supportMap y z (Or.inl hw0)).trans
        (readActualSupport_inactive (PackageTotalHom.comp f g) Rcmp W X V Y a y z (Or.inl hw)).symm
  | actualAxis W X V Y a y z =>
    by_cases hw : forward (PackageTotalHom.comp f g) W = V
    · subst V
      by_cases hx : forward (PackageTotalHom.comp f g) X = Y
      · subst Y
        apply Bool.eq_iff_iff.mpr
        exact (IndependentFixedIndexedPointGraph.action_point_iff
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeAxis h hp hctx k kp .forward) (composeAxis h hp hctx k kp .backward)
            (composeAxis_inverseLaws h hp hctx k kp)
          (forward (PackageTotalHom.comp f g)) hc (fun W => Rcmp.axisEquiv ⟨W⟩)
          (composeAxis_eq_native f g h hm hp hctx k km kp .forward).symm
          W X a.axisMap (Rcmp.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) a).axisMap
          (fun x => (Rcmp.axis_naturality (W := ⟨W⟩) (V := ⟨X⟩) a x).symm) y z).trans
          (readActualAxis_point_iff (PackageTotalHom.comp f g) Rcmp W X a y z).symm
      · have hx0 : IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) X Y = false :=
          Bool.eq_false_iff.mpr (fun ht => hx ((hc X Y).1 ht))
        exact (IndependentFixedIndexedPointGraph.action_inactive
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeAxis h hp hctx k kp .forward) (composeAxis h hp hctx k kp .backward)
            (composeAxis_inverseLaws h hp hctx k kp)
          W X (forward (PackageTotalHom.comp f g) W) Y
          a.axisMap y z (Or.inr hx0)).trans
          (readActualAxis_inactive (PackageTotalHom.comp f g) Rcmp W X _ Y a y z (Or.inr hx)).symm
    · have hw0 : IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) W V = false :=
        Bool.eq_false_iff.mpr (fun ht => hw ((hc W V).1 ht))
      exact (IndependentFixedIndexedPointGraph.action_inactive
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeAxis h hp hctx k kp .forward) (composeAxis h hp hctx k kp .backward)
            (composeAxis_inverseLaws h hp hctx k kp)
          W X V Y a.axisMap y z (Or.inl hw0)).trans
        (readActualAxis_inactive (PackageTotalHom.comp f g) Rcmp W X V Y a y z (Or.inl hw)).symm
  | actualObservable W X V Y a y z =>
    by_cases hw : forward (PackageTotalHom.comp f g) W = V
    · subst V
      by_cases hx : forward (PackageTotalHom.comp f g) X = Y
      · subst Y
        apply Bool.eq_iff_iff.mpr
        exact (IndependentFixedIndexedPointGraph.action_point_iff
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeObservable h hp hctx k kp .forward) (composeObservable h hp hctx k kp .backward)
            (composeObservable_inverseLaws h hp hctx k kp)
          (forward (PackageTotalHom.comp f g)) hc (fun W => Rcmp.observableEquiv ⟨W⟩)
          (composeObservable_eq_native f g h hm hp hctx k km kp .forward).symm
          X W a.observableRestrict (Rcmp.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) a).observableRestrict
          (fun x => (Rcmp.observable_naturality (W := ⟨W⟩) (V := ⟨X⟩) a x).symm) y z).trans
          (readActualObservable_point_iff (PackageTotalHom.comp f g) Rcmp W X a y z).symm
      · have hx0 : IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) X Y = false :=
          Bool.eq_false_iff.mpr (fun ht => hx ((hc X Y).1 ht))
        exact (IndependentFixedIndexedPointGraph.action_inactive
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeObservable h hp hctx k kp .forward) (composeObservable h hp hctx k kp .backward)
            (composeObservable_inverseLaws h hp hctx k kp)
          X W Y (forward (PackageTotalHom.comp f g) W)
          a.observableRestrict y z (Or.inl hx0)).trans
          (readActualObservable_inactive (PackageTotalHom.comp f g) Rcmp W X _ Y a y z (Or.inr hx)).symm
    · have hw0 : IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) W V = false :=
        Bool.eq_false_iff.mpr (fun ht => hw ((hc W V).1 ht))
      exact (IndependentFixedIndexedPointGraph.action_inactive
          (IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k))
            (composeObservable h hp hctx k kp .forward) (composeObservable h hp hctx k kp .backward)
            (composeObservable_inverseLaws h hp hctx k kp)
          X W Y V a.observableRestrict y z (Or.inr hw0)).trans
        (readActualObservable_inactive (PackageTotalHom.comp f g) Rcmp W X V Y a y z (Or.inl hw)).symm

end Native

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization
