import ResearchLean.AG.GeometryTransport.FactorLaws

/-!
# Factorization and uniqueness

The componentwise factor is inverse to composition with the canonical
geometry transport.  These equalities supply the explicit unique-factor form
of the strong cocartesian universal property.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

set_option maxHeartbeats 2000000

/-- Reindexing a geometry hom along base equality changes only its dependent
type, not its data. -/
private theorem castBase_heq {U : AtomCarrier.{u}}
    {G K : GeometryPackage.{u, v} U}
    {f g : PackageTotalHom G.core K.core} (hfg : f = g)
    (F : GeomReadHom G K f) : HEq (GeomReadHom.castBase hfg F) F := by
  cases hfg
  rfl

/-- Composition respects dependent reindexing of the tail geometry hom. -/
private theorem comp_castBase_heq {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    {g g' : PackageTotalHom H.core K.core} (hgg' : g = g')
    (F : GeomReadHom G H f) (T : GeomReadHom H K g) :
    HEq (GeomReadHom.comp F (GeomReadHom.castBase hgg' T))
      (GeomReadHom.comp F T) := by
  cases hgg'
  rfl

/-- Equality of total geometry homs identifies their dependent geometry data. -/
private theorem geometry_heq_of_eq {U : AtomCarrier.{u}}
    {G K : GeometryPackage.{u, v} U}
    {F T : GeometryTotalHom G K} (h : F = T) : HEq F.geometry T.geometry := by
  cases h
  rfl

/-- Coefficient composition with the canonical identity map is unchanged. -/
theorem geometryFactor_coefficient_fac {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma)
      (geometryFactorGeometryHom G sigma tail H)).coefficientHom =
      H.coefficientHom := by
  rfl

/-- Support comparison deconjugation cancels canonical composition. -/
theorem geometryFactor_support_fac {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    HEq
      (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma)
        (geometryFactorGeometryHom G sigma tail H)).supportComp
      H.supportComp := by
  apply heq_of_eq
  funext W support
  let canonical : PackageTotalHom G.core (geomTransportAlong G sigma).core :=
    transportAlongHom G.core sigma
  let hback := canonicalContextRetraction_eq G sigma W
  let sourceSupport :
      (contextBackward canonical (contextForward canonical W)).ctx.Support :=
    (canonicalSectionSupportEquiv G sigma (contextForward canonical W)).symm
      (geomTransportSupportComp G sigma W support)
  change supportEquivOfContextEq
      (compositeTailContextSection_eq G sigma tail (contextForward canonical W))
      (H.supportComp (contextBackward canonical (contextForward canonical W))
        sourceSupport) = H.supportComp W support
  have htarget :
      compositeTailContextSection_eq G sigma tail (contextForward canonical W) =
        congrArg
          (fun X => contextForward
            (PackageTotalHom.comp canonical tail) X) hback :=
    Subsingleton.elim _ _
  rw [htarget]
  calc
    _ = H.supportComp W (supportEquivOfContextEq hback sourceSupport) := by
      simpa [canonical] using
        (supportEquivOfContextEq_family
          (fun X => contextForward (PackageTotalHom.comp canonical tail) X)
          H.supportComp hback sourceSupport)
    _ = H.supportComp W support := congrArg (H.supportComp W)
      (canonicalSectionSupportEquiv_triangle G sigma W support)

/-- Axis comparison deconjugation cancels canonical composition. -/
theorem geometryFactor_axis_fac {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    HEq
      (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma)
        (geometryFactorGeometryHom G sigma tail H)).axisComp
      H.axisComp := by
  apply heq_of_eq
  funext W axis
  let canonical : PackageTotalHom G.core (geomTransportAlong G sigma).core :=
    transportAlongHom G.core sigma
  let hback := canonicalContextRetraction_eq G sigma W
  let sourceAxis :
      (contextBackward canonical (contextForward canonical W)).ctx.Axis :=
    (canonicalSectionAxisEquiv G sigma (contextForward canonical W)).symm
      (geomTransportAxisComp G sigma W axis)
  change axisEquivOfContextEq
      (compositeTailContextSection_eq G sigma tail (contextForward canonical W))
      (H.axisComp (contextBackward canonical (contextForward canonical W))
        sourceAxis) = H.axisComp W axis
  have htarget :
      compositeTailContextSection_eq G sigma tail (contextForward canonical W) =
        congrArg
          (fun X => contextForward
            (PackageTotalHom.comp canonical tail) X) hback :=
    Subsingleton.elim _ _
  rw [htarget]
  calc
    _ = H.axisComp W (axisEquivOfContextEq hback sourceAxis) := by
      simpa [canonical] using
        (axisEquivOfContextEq_family
          (fun X => contextForward (PackageTotalHom.comp canonical tail) X)
          H.axisComp hback sourceAxis)
    _ = H.axisComp W axis := congrArg (H.axisComp W)
      (canonicalSectionAxisEquiv_triangle G sigma W axis)

/-- Observable comparison deconjugation cancels canonical composition. -/
theorem geometryFactor_observable_fac {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    HEq
      (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma)
        (geometryFactorGeometryHom G sigma tail H)).observableComp
      H.observableComp := by
  apply heq_of_eq
  funext W observable
  let canonical : PackageTotalHom G.core (geomTransportAlong G sigma).core :=
    transportAlongHom G.core sigma
  let hback := canonicalContextRetraction_eq G sigma W
  let sourceObservable :
      (contextBackward canonical (contextForward canonical W)).ctx.Observable :=
    (canonicalSectionObservableEquiv G sigma (contextForward canonical W)).symm
      (geomTransportObservableComp G sigma W observable)
  change observableEquivOfContextEq
      (compositeTailContextSection_eq G sigma tail (contextForward canonical W))
      (H.observableComp (contextBackward canonical (contextForward canonical W))
        sourceObservable) = H.observableComp W observable
  have htarget :
      compositeTailContextSection_eq G sigma tail (contextForward canonical W) =
        congrArg
          (fun X => contextForward
            (PackageTotalHom.comp canonical tail) X) hback :=
    Subsingleton.elim _ _
  rw [htarget]
  calc
    _ = H.observableComp W
        (observableEquivOfContextEq hback sourceObservable) := by
      simpa [canonical] using
        (observableEquivOfContextEq_family
          (fun X => contextForward (PackageTotalHom.comp canonical tail) X)
          H.observableComp hback sourceObservable)
    _ = H.observableComp W observable := congrArg (H.observableComp W)
      (canonicalSectionObservableEquiv_triangle G sigma W observable)

/-- The componentwise factor reconstructs the supplied composite geometry hom. -/
theorem geometryFactor_fac {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (H : GeomReadHom G K (PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)) :
    GeomReadHom.comp (geomTransportAlongGeometryHom G sigma)
      (geometryFactorGeometryHom G sigma tail H) = H := by
  apply GeomReadHom.ext
  · exact geometryFactor_coefficient_fac G sigma tail H
  · exact geometryFactor_support_fac G sigma tail H
  · exact geometryFactor_axis_fac G sigma tail H
  · exact geometryFactor_observable_fac G sigma tail H

/-- Factoring the composite of the canonical hom with an arbitrary tail
recovers the tail support comparison. -/
theorem geometryFactor_support_of_composite {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (T : GeomReadHom (geomTransportAlong G sigma) K tail) :
    HEq
      (geometryFactorGeometryHom G sigma tail
        (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma) T)).supportComp
      T.supportComp := by
  apply heq_of_eq
  funext W support
  let canonical : PackageTotalHom G.core (geomTransportAlong G sigma).core :=
    transportAlongHom G.core sigma
  let hsection := canonicalContextSection_eq G sigma W
  let sourceSupport := (canonicalSectionSupportEquiv G sigma W).symm support
  let transportedSupport := geomTransportSupportComp G sigma
    (contextBackward canonical W) sourceSupport
  change supportEquivOfContextEq
      (compositeTailContextSection_eq G sigma tail W)
      (T.supportComp (contextForward canonical (contextBackward canonical W))
        transportedSupport) = T.supportComp W support
  have htarget : compositeTailContextSection_eq G sigma tail W =
      congrArg (fun X => contextForward tail X) hsection :=
    Subsingleton.elim _ _
  rw [htarget]
  calc
    _ = T.supportComp W
        (supportEquivOfContextEq hsection transportedSupport) := by
      exact supportEquivOfContextEq_family
        (fun X => contextForward tail X) T.supportComp hsection transportedSupport
    _ = T.supportComp W support := by
      apply congrArg (T.supportComp W)
      change (canonicalSectionSupportEquiv G sigma W)
          ((canonicalSectionSupportEquiv G sigma W).symm support) = support
      exact (canonicalSectionSupportEquiv G sigma W).apply_symm_apply support

/-- Factoring a canonical composite recovers the tail axis comparison. -/
theorem geometryFactor_axis_of_composite {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (T : GeomReadHom (geomTransportAlong G sigma) K tail) :
    HEq
      (geometryFactorGeometryHom G sigma tail
        (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma) T)).axisComp
      T.axisComp := by
  apply heq_of_eq
  funext W axis
  let canonical : PackageTotalHom G.core (geomTransportAlong G sigma).core :=
    transportAlongHom G.core sigma
  let hsection := canonicalContextSection_eq G sigma W
  let sourceAxis := (canonicalSectionAxisEquiv G sigma W).symm axis
  let transportedAxis := geomTransportAxisComp G sigma
    (contextBackward canonical W) sourceAxis
  change axisEquivOfContextEq
      (compositeTailContextSection_eq G sigma tail W)
      (T.axisComp (contextForward canonical (contextBackward canonical W))
        transportedAxis) = T.axisComp W axis
  have htarget : compositeTailContextSection_eq G sigma tail W =
      congrArg (fun X => contextForward tail X) hsection :=
    Subsingleton.elim _ _
  rw [htarget]
  calc
    _ = T.axisComp W (axisEquivOfContextEq hsection transportedAxis) := by
      exact axisEquivOfContextEq_family
        (fun X => contextForward tail X) T.axisComp hsection transportedAxis
    _ = T.axisComp W axis := by
      apply congrArg (T.axisComp W)
      change (canonicalSectionAxisEquiv G sigma W)
          ((canonicalSectionAxisEquiv G sigma W).symm axis) = axis
      exact (canonicalSectionAxisEquiv G sigma W).apply_symm_apply axis

/-- Factoring a canonical composite recovers the tail observable comparison. -/
theorem geometryFactor_observable_of_composite {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (T : GeomReadHom (geomTransportAlong G sigma) K tail) :
    HEq
      (geometryFactorGeometryHom G sigma tail
        (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma) T)).observableComp
      T.observableComp := by
  apply heq_of_eq
  funext W observable
  let canonical : PackageTotalHom G.core (geomTransportAlong G sigma).core :=
    transportAlongHom G.core sigma
  let hsection := canonicalContextSection_eq G sigma W
  let sourceObservable := (canonicalSectionObservableEquiv G sigma W).symm observable
  let transportedObservable := geomTransportObservableComp G sigma
    (contextBackward canonical W) sourceObservable
  change observableEquivOfContextEq
      (compositeTailContextSection_eq G sigma tail W)
      (T.observableComp (contextForward canonical (contextBackward canonical W))
        transportedObservable) = T.observableComp W observable
  have htarget : compositeTailContextSection_eq G sigma tail W =
      congrArg (fun X => contextForward tail X) hsection :=
    Subsingleton.elim _ _
  rw [htarget]
  calc
    _ = T.observableComp W
        (observableEquivOfContextEq hsection transportedObservable) := by
      exact observableEquivOfContextEq_family
        (fun X => contextForward tail X) T.observableComp hsection
          transportedObservable
    _ = T.observableComp W observable := by
      apply congrArg (T.observableComp W)
      change (canonicalSectionObservableEquiv G sigma W)
          ((canonicalSectionObservableEquiv G sigma W).symm observable) = observable
      exact (canonicalSectionObservableEquiv G sigma W).apply_symm_apply observable

/-- Componentwise deconjugation is a left inverse to canonical composition. -/
theorem geometryFactor_of_composite {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (T : GeomReadHom (geomTransportAlong G sigma) K tail) :
    geometryFactorGeometryHom G sigma tail
        (GeomReadHom.comp (geomTransportAlongGeometryHom G sigma) T) = T := by
  apply GeomReadHom.ext
  · rfl
  · exact geometryFactor_support_of_composite G sigma tail T
  · exact geometryFactor_axis_of_composite G sigma tail T
  · exact geometryFactor_observable_of_composite G sigma tail T

/-- The canonical total geometry hom followed by its constructed factor is
the supplied total hom. -/
theorem geometryTotalFactor_fac {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (h : GeometryTotalHom G K)
    (hbase : h.base = PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail) :
    GeometryTotalHom.comp (geomTransportAlongHom G sigma)
      (geometryTotalFactor G sigma tail h hbase) = h := by
  apply GeometryTotalHom.ext
  · exact hbase.symm
  · exact (heq_of_eq (geometryFactor_fac G sigma tail
      (GeomReadHom.castBase hbase h.geometry))).trans
        (castBase_heq hbase h.geometry)

/-- Every total factor over the supplied core-package tail is the constructed
one. -/
theorem geometryTotalFactor_unique {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (h : GeometryTotalHom G K)
    (hbase : h.base = PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail)
    (k : GeometryTotalHom (geomTransportAlong G sigma) K)
    (hkbase : k.base = tail)
    (hkfac : GeometryTotalHom.comp (geomTransportAlongHom G sigma) k = h) :
    k = geometryTotalFactor G sigma tail h hbase := by
  let canonicalGeometry := geomTransportAlongGeometryHom G sigma
  let kGeometry := GeomReadHom.castBase hkbase k.geometry
  let normalizedH := GeomReadHom.castBase hbase h.geometry
  have hnormalized : GeomReadHom.comp canonicalGeometry kGeometry = normalizedH := by
    apply eq_of_heq
    exact ((comp_castBase_heq hkbase canonicalGeometry k.geometry).trans
      (geometry_heq_of_eq hkfac)).trans
        (castBase_heq hbase h.geometry).symm
  have hkGeometry : kGeometry =
      geometryFactorGeometryHom G sigma tail normalizedH := by
    calc
      kGeometry = geometryFactorGeometryHom G sigma tail
          (GeomReadHom.comp canonicalGeometry kGeometry) :=
        (geometryFactor_of_composite G sigma tail kGeometry).symm
      _ = geometryFactorGeometryHom G sigma tail normalizedH :=
        congrArg (geometryFactorGeometryHom G sigma tail) hnormalized
  apply GeometryTotalHom.ext
  · exact hkbase
  · exact (castBase_heq hkbase k.geometry).symm.trans (heq_of_eq hkGeometry)

/-- Explicit unique-factor form of canonical geometry transport. -/
theorem geomTransportAlongHom_factor_existsUnique {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {K : GeometryPackage.{u, v} U}
    (tail : PackageTotalHom (geomTransportAlong G sigma).core K.core)
    (h : GeometryTotalHom G K)
    (hbase : h.base = PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail) :
    ∃! k : GeometryTotalHom (geomTransportAlong G sigma) K,
      k.base = tail ∧
        GeometryTotalHom.comp (geomTransportAlongHom G sigma) k = h := by
  refine ⟨geometryTotalFactor G sigma tail h hbase, ⟨rfl, ?_⟩, ?_⟩
  · exact geometryTotalFactor_fac G sigma tail h hbase
  · intro k hk
    exact geometryTotalFactor_unique G sigma tail h hbase k hk.1 hk.2

/-- Canonical geometry transport is strongly cocartesian over the projection
to complete G-101 core packages.  The universal property ranges over every
core-package tail. -/
theorem geomTransportAlongHom_isStronglyCocartesian {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geometryProjection U).IsStronglyCocartesian
      (transportAlongHom G.core sigma) (geomTransportAlongHom G sigma) := by
  letI : (geometryProjection U).IsHomLift
      (transportAlongHom G.core sigma) (geomTransportAlongHom G sigma) := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map (geomTransportAlongHom G sigma))
      (geomTransportAlongHom G sigma)
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCocartesian.mk
  intro K tail h hLift
  have hbase : h.base = PackageTotalHom.comp
      (transportAlongHom G.core sigma) tail := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (geometryProjection U)
      (PackageTotalHom.comp (transportAlongHom G.core sigma) tail) h).symm
  rcases geomTransportAlongHom_factor_existsUnique G sigma tail h hbase with
    ⟨k, hk, hunique⟩
  refine ⟨k, ?_, ?_⟩
  · constructor
    · rw [← hk.1]
      change (geometryProjection U).IsHomLift
        ((geometryProjection U).map k) k
      infer_instance
    · exact hk.2
  · intro k' hk'
    apply hunique k'
    constructor
    · letI : (geometryProjection U).IsHomLift tail k' := hk'.1
      exact (CategoryTheory.IsHomLift.eq_of_isHomLift
        (p := geometryProjection U)
        (a := geomTransportAlong G sigma) (b := K) tail k').symm
    · exact hk'.2

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
