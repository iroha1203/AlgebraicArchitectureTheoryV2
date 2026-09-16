import ResearchLean.AG.RealizationReconstruction.CSAATCoefficientRawExactMap
import Formal.Util.AssertStandardAxioms

/-!
# Geometry morphisms with exact typed raw action

This module gives the parallel geometry-morphism layer required after the
strict raw-equality obstruction.  It retains the accepted G-108 coverage,
overlap, coefficient, and realization-comparison components, and replaces
only literal raw-system equality by the coefficient-aware exact typed raw map
of Cycle 153.  Identity, composition, and the embedding of every existing
strict geometry morphism are constructed.

Category laws and the concrete genuine-CS bridges remain subsequent
obligations.  In particular this exact layer does not claim to encode the
arbitrary noninjective CS coordinate maps retained by the earlier forward
translation layer.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u v

namespace RealizationTransportSupply

/-- Identity realization comparison supply. -/
def exactId {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    RealizationTransportSupply G.core G.core (PackageTotalHom.id G.core) where
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Composition of realization comparison supplies. -/
def exactComp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    {g : PackageTotalHom H.core K.core}
    (first : RealizationTransportSupply G.core H.core f)
    (second : RealizationTransportSupply H.core K.core g) :
    RealizationTransportSupply G.core K.core (PackageTotalHom.comp f g) where
  supportComp W support := second.supportComp _ (first.supportComp W support)
  axisComp W axis := second.axisComp _ (first.axisComp W axis)
  observableComp W observable := second.observableComp _ (first.observableComp W observable)
  supportReads W support atom h := second.supportReads _ _ _ (first.supportReads W support atom h)
  axisReads W axis h := second.axisReads _ _ (first.axisReads W axis h)
  observableReads W observable h := second.observableReads _ _ (first.observableReads W observable h)
  support_naturality w support := by
    rw [second.support_naturality ((coreContextFunctor f).map w),
      first.support_naturality w]
  axis_naturality w axis := by
    rw [second.axis_naturality ((coreContextFunctor f).map w),
      first.axis_naturality w]
  observable_naturality w observable := by
    rw [second.observable_naturality ((coreContextFunctor f).map w),
      first.observable_naturality w]

/-- Extract the accepted non-raw realization data from a strict geometry hom. -/
def ofGeomReadHom {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    (hom : GeomReadHom G H baseHom) :
    RealizationTransportSupply G.core H.core baseHom where
  supportComp := hom.supportComp
  axisComp := hom.axisComp
  observableComp := hom.observableComp
  supportReads := hom.supportReads
  axisReads := hom.axisReads
  observableReads := hom.observableReads
  support_naturality := hom.support_naturality
  axis_naturality := hom.axis_naturality
  observable_naturality := hom.observable_naturality

end RealizationTransportSupply

/-- A geometry hom whose raw component records the actual typed action rather
than requiring literal equality of endpoint raw systems. -/
structure ExactGeomReadHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (baseHom : PackageTotalHom G.core H.core) where
  coverage : CoverageTransport G H baseHom
  overlap : OverlapTransport G H baseHom
  coefficientHom : G.Coefficient →+* H.Coefficient
  raw : RawAmbientRestrictionSystemExactMapAgainst G.site H.site
    (coreContextInverse baseHom) coefficientHom G.raw H.raw
  realization : RealizationTransportSupply G.core H.core baseHom

namespace ExactGeomReadHom

/-- Identity exact geometry hom. -/
noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    ExactGeomReadHom G G (PackageTotalHom.id G.core) where
  coverage := CoverageTransport.id G
  overlap := OverlapTransport.id G
  coefficientHom := RingHom.id G.Coefficient
  raw := RawAmbientRestrictionSystemExactMapAgainst.refl G.site G.Coefficient G.raw
  realization := RealizationTransportSupply.exactId G

/-- Composition retains all non-raw G-108 data and composes the actual typed
raw action. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {f : PackageTotalHom G.core H.core}
    {g : PackageTotalHom H.core K.core}
    (first : ExactGeomReadHom G H f) (second : ExactGeomReadHom H K g) :
    ExactGeomReadHom G K (PackageTotalHom.comp f g) where
  coverage := first.coverage.comp second.coverage
  overlap := first.overlap.comp second.overlap
  coefficientHom := second.coefficientHom.comp first.coefficientHom
  raw := first.raw.trans second.raw
  realization := RealizationTransportSupply.exactComp
    first.realization second.realization

/-- Every existing strict geometry hom embeds by constructing its exact typed
raw action from the strict raw equality. -/
noncomputable def ofStrict {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    (hom : GeomReadHom G H baseHom) : ExactGeomReadHom G H baseHom where
  coverage := hom.coverage
  overlap := hom.overlap
  coefficientHom := hom.coefficientHom
  raw := RawAmbientRestrictionSystemExactMapAgainst.ofGeomReadHom hom
  realization := RealizationTransportSupply.ofGeomReadHom hom

end ExactGeomReadHom

/-- Total exact geometry morphism over the accepted core-package base. -/
structure ExactGeometryTotalHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  base : PackageTotalHom G.core H.core
  geometry : ExactGeomReadHom G H base

namespace ExactGeometryTotalHom

noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    ExactGeometryTotalHom G G where
  base := PackageTotalHom.id G.core
  geometry := ExactGeomReadHom.id G

noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : ExactGeometryTotalHom G H) (second : ExactGeometryTotalHom H K) :
    ExactGeometryTotalHom G K where
  base := PackageTotalHom.comp first.base second.base
  geometry := first.geometry.comp second.geometry

/-- Strict total geometry morphisms embed without changing their base or any
non-raw component. -/
noncomputable def ofStrict {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (hom : GeometryTotalHom G H) : ExactGeometryTotalHom G H where
  base := hom.base
  geometry := ExactGeomReadHom.ofStrict hom.geometry

end ExactGeometryTotalHom

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
