import ResearchLean.AG.GeometryTransport.Opcartesian

/-!
# Geometry-factor laws

The deconjugated realization comparisons inherit all three naturality laws
from the supplied composite hom.  This file then packages the componentwise
factor into a geometry hom over the arbitrary core tail.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

set_option maxHeartbeats 2000000

/-- The factor axis comparison is natural in the intermediate context. -/
theorem geometryFactor_axis_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (axis : W.ctx.Axis) :
    (targetContextMorphism (f := tail) w).axisMap
        (geometryFactorAxisComp G sigma tail H W axis) =
      geometryFactorAxisComp G sigma tail H V
        ((sourceContextMorphism w).axisMap axis) := by
  let canonical := transportAlongHom G.core sigma
  let inverseArrow := (contextInverse canonical).map w
  let sourceAxis := (canonicalSectionAxisEquiv G sigma W).symm axis
  calc
    _ = axisEquivOfContextEq
        (compositeTailContextSection_eq G sigma tail V)
        ((K.core.contextPreorder.morphism
          (leOfHom ((contextFunctor (PackageTotalHom.comp canonical tail)).map
            inverseArrow))).axisMap
          (H.axisComp (contextBackward canonical W) sourceAxis)) :=
      axisEquivOfContextEq_naturality
        (compositeTailContextSection_eq G sigma tail W)
        (compositeTailContextSection_eq G sigma tail V)
        ((contextFunctor (PackageTotalHom.comp canonical tail)).map inverseArrow)
        ((contextFunctor tail).map w)
        (H.axisComp (contextBackward canonical W) sourceAxis)
    _ = axisEquivOfContextEq
        (compositeTailContextSection_eq G sigma tail V)
        (H.axisComp (contextBackward canonical V)
          ((G.core.contextPreorder.morphism
            (leOfHom inverseArrow)).axisMap sourceAxis)) := by
      exact congrArg
        (axisEquivOfContextEq
          (compositeTailContextSection_eq G sigma tail V))
        (H.axis_naturality inverseArrow sourceAxis)
    _ = _ := by
      simp only [geometryFactorAxisComp, sourceAxis, canonical,
        sourceContextMorphism]
      rw [canonicalSectionAxisEquiv_symm_naturality G sigma w axis]

/-- The factor observable comparison is natural in the intermediate context. -/
theorem geometryFactor_observable_naturality {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail))
    {W V : (geomTransportAlong G sigma).site.category} (w : W ⟶ V)
    (observable : V.ctx.Observable) :
    (targetContextMorphism (f := tail) w).observableRestrict
        (geometryFactorObservableComp G sigma tail H V observable) =
      geometryFactorObservableComp G sigma tail H W
        ((sourceContextMorphism w).observableRestrict observable) := by
  let canonical := transportAlongHom G.core sigma
  let inverseArrow := (contextInverse canonical).map w
  let sourceObservable :=
    (canonicalSectionObservableEquiv G sigma V).symm observable
  calc
    _ = observableEquivOfContextEq
        (compositeTailContextSection_eq G sigma tail W)
        ((K.core.contextPreorder.morphism
          (leOfHom ((contextFunctor (PackageTotalHom.comp canonical tail)).map
            inverseArrow))).observableRestrict
          (H.observableComp (contextBackward canonical V) sourceObservable)) :=
      observableEquivOfContextEq_naturality
        (compositeTailContextSection_eq G sigma tail W)
        (compositeTailContextSection_eq G sigma tail V)
        ((contextFunctor (PackageTotalHom.comp canonical tail)).map inverseArrow)
        ((contextFunctor tail).map w)
        (H.observableComp (contextBackward canonical V) sourceObservable)
    _ = observableEquivOfContextEq
        (compositeTailContextSection_eq G sigma tail W)
        (H.observableComp (contextBackward canonical W)
          ((G.core.contextPreorder.morphism
            (leOfHom inverseArrow)).observableRestrict sourceObservable)) := by
      exact congrArg
        (observableEquivOfContextEq
          (compositeTailContextSection_eq G sigma tail W))
        (H.observable_naturality inverseArrow sourceObservable)
    _ = _ := by
      simp only [geometryFactorObservableComp, sourceObservable, canonical,
        sourceContextMorphism]
      rw [canonicalSectionObservableEquiv_symm_naturality
        G sigma w observable]

/-- The componentwise deconjugation is a geometry hom over the supplied tail. -/
noncomputable def geometryFactorGeometryHom {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    GeomReadHom (geomTransportAlong G sigma) K tail where
  coverage := geometryFactorCoverage G sigma tail H
  overlap := geometryFactorOverlap G sigma tail H
  coefficientHom := H.coefficientHom
  raw_eq := geometryFactor_raw_eq G sigma tail H
  supportComp := geometryFactorSupportComp G sigma tail H
  axisComp := geometryFactorAxisComp G sigma tail H
  observableComp := geometryFactorObservableComp G sigma tail H
  supportReads := geometryFactor_supportReads G sigma tail H
  axisReads := geometryFactor_axisReads G sigma tail H
  observableReads := geometryFactor_observableReads G sigma tail H
  support_naturality := geometryFactor_support_naturality G sigma tail H
  axis_naturality := geometryFactor_axis_naturality G sigma tail H
  observable_naturality := geometryFactor_observable_naturality G sigma tail H

/-- The total geometry factor over an arbitrary core-package tail. -/
noncomputable def geometryTotalFactor {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (h : GeometryTotalHom G K)
    (hbase : h.base = PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail) :
    GeometryTotalHom (geomTransportAlong G sigma) K where
  base := tail
  geometry := geometryFactorGeometryHom G sigma tail
    (GeomReadHom.castBase hbase h.geometry)

/-- The total geometry factor projects to the supplied arbitrary core tail. -/
@[simp] theorem geometryTotalFactor_base {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (h : GeometryTotalHom G K)
    (hbase : h.base = PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail) :
    (geometryTotalFactor G sigma tail h hbase).base = tail :=
  rfl

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
