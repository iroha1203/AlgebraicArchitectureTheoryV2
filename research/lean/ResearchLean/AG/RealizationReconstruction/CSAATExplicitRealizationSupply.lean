import ResearchLean.AG.RealizationReconstruction.CSAATExactGeometryRawCheckpoint
import ResearchLean.AG.RealizationReconstruction.CSAATExplicitContextAction
import Formal.Util.AssertStandardAxioms

/-!
# Explicit realization supply for the generated CS cores

This file indexes realization naturality by the actual `ContextMorphism`
rather than by a representative independently re-selected after thin-arrow
erasure.  It constructs the complete explicit supply for both generated CS
cores and combines it with the already constructed base, coefficient, and
typed raw action.

Coverage and overlap are intentionally absent from the final checkpoint.  It
is therefore not an exact geometry hom and is not presented as one.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u v

/-- Realization comparison indexed by the actual context morphism rather than
an independently re-selected representative of its thin-category image. -/
structure EquationExplicitRealizationSupply
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (T : EquationSystemExactTransport E F atomEquiv objectMap) where
  contextMorphism : ∀ {W V : Site.ContextCategoryObject C},
    Site.ContextMorphism W.ctx V.ctx →
      Site.ContextMorphism (T.contextEquivalence.functor.obj W).ctx
        (T.contextEquivalence.functor.obj V).ctx
  contextMorphism_isRestriction : ∀ {W V : Site.ContextCategoryObject C}
      (f : Site.ContextMorphism W.ctx V.ctx), f.IsRestriction →
        (contextMorphism f).IsRestriction
  supportEquiv : ∀ W, W.ctx.Support ≃
    (T.contextEquivalence.functor.obj W).ctx.Support
  axisEquiv : ∀ W, W.ctx.Axis ≃
    (T.contextEquivalence.functor.obj W).ctx.Axis
  observableEquiv : ∀ W, W.ctx.Observable ≃
    (T.contextEquivalence.functor.obj W).ctx.Observable
  supportReads_iff : ∀ W support atom,
    W.ctx.minimal.supportReads support atom ↔
      (T.contextEquivalence.functor.obj W).ctx.minimal.supportReads
        (supportEquiv W support) (atomEquiv atom)
  axisReads_iff : ∀ W axis,
    W.ctx.minimal.axisReads axis ↔
      (T.contextEquivalence.functor.obj W).ctx.minimal.axisReads (axisEquiv W axis)
  observableReads_iff : ∀ W observable,
    W.ctx.minimal.observableReads observable ↔
      (T.contextEquivalence.functor.obj W).ctx.minimal.observableReads
        (observableEquiv W observable)
  support_naturality : ∀ {W V} (f : Site.ContextMorphism W.ctx V.ctx) support,
    (contextMorphism f).supportMap (supportEquiv W support) =
      supportEquiv V (f.supportMap support)
  axis_naturality : ∀ {W V} (f : Site.ContextMorphism W.ctx V.ctx) axis,
    (contextMorphism f).axisMap (axisEquiv W axis) =
      axisEquiv V (f.axisMap axis)
  observable_naturality : ∀ {W V} (f : Site.ContextMorphism W.ctx V.ctx) observable,
    (contextMorphism f).observableRestrict (observableEquiv V observable) =
      observableEquiv W (f.observableRestrict observable)

/-- Endpoint lens supply, constructed from full-family rebase. -/
noncomputable def lensIsoEndpointExplicitRealizationSupply
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    EquationExplicitRealizationSupply (lensIsoEndpointEquationTransport e) where
  contextMorphism := (lensIsoEndpointExplicitContextAction e).contextMorphism
  contextMorphism_isRestriction :=
    (lensIsoEndpointExplicitContextAction e).contextMorphism_isRestriction
  supportEquiv := fun W => (lensIsoEndpointExplicitContextAction e).supportEquiv W.ctx
  axisEquiv := fun W => (lensIsoEndpointExplicitContextAction e).axisEquiv W.ctx
  observableEquiv := fun W =>
    (lensIsoEndpointExplicitContextAction e).observableEquiv W.ctx
  supportReads_iff := fun W =>
    (lensIsoEndpointExplicitContextAction e).supportReads_iff W.ctx
  axisReads_iff := fun W =>
    (lensIsoEndpointExplicitContextAction e).axisReads_iff W.ctx
  observableReads_iff := fun W =>
    (lensIsoEndpointExplicitContextAction e).observableReads_iff W.ctx
  support_naturality := (lensIsoEndpointExplicitContextAction e).support_naturality
  axis_naturality := (lensIsoEndpointExplicitContextAction e).axis_naturality
  observable_naturality :=
    (lensIsoEndpointExplicitContextAction e).observable_naturality

/-- Endpoint protocol supply, with dependent operation names retained by the
same full-family rebase. -/
noncomputable def protocolIsoEndpointExplicitRealizationSupply
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    EquationExplicitRealizationSupply (protocolIsoEndpointEquationTransport e) where
  contextMorphism := (protocolIsoEndpointExplicitContextAction e).contextMorphism
  contextMorphism_isRestriction :=
    (protocolIsoEndpointExplicitContextAction e).contextMorphism_isRestriction
  supportEquiv := fun W =>
    (protocolIsoEndpointExplicitContextAction e).supportEquiv W.ctx
  axisEquiv := fun W =>
    (protocolIsoEndpointExplicitContextAction e).axisEquiv W.ctx
  observableEquiv := fun W =>
    (protocolIsoEndpointExplicitContextAction e).observableEquiv W.ctx
  supportReads_iff := fun W =>
    (protocolIsoEndpointExplicitContextAction e).supportReads_iff W.ctx
  axisReads_iff := fun W =>
    (protocolIsoEndpointExplicitContextAction e).axisReads_iff W.ctx
  observableReads_iff := fun W =>
    (protocolIsoEndpointExplicitContextAction e).observableReads_iff W.ctx
  support_naturality :=
    (protocolIsoEndpointExplicitContextAction e).support_naturality
  axis_naturality := (protocolIsoEndpointExplicitContextAction e).axis_naturality
  observable_naturality :=
    (protocolIsoEndpointExplicitContextAction e).observable_naturality

/-- Cast explicit realization data through the same generated-object
provenance equalities used by the equation transport itself. -/
noncomputable def coreGeometryExplicitRealizationSupplyCast
    {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (atomEquiv : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (transport : EquationSystemExactTransport
      sourceData.equationReading.equationSystem
      targetData.equationReading.equationSystem atomEquiv objectMap)
    (supply : EquationExplicitRealizationSupply transport) :
    EquationExplicitRealizationSupply
      (coreGeometryEquationTransportCast source_eq target_eq sourceData targetData
        atomEquiv objectMap transport) := by
  cases source_eq
  cases target_eq
  exact supply

noncomputable def lensIsoGeneratedExplicitRealizationSupply
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    EquationExplicitRealizationSupply (lensIsoGeneratedEquationTransport e) := by
  unfold lensIsoGeneratedEquationTransport lensAATCoreGeneratedGeometryData
  exact coreGeometryExplicitRealizationSupplyCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y)
    (Equiv.refl _) (lensIsoObjectMap e)
    (lensIsoEndpointEquationTransport e)
    (lensIsoEndpointExplicitRealizationSupply e)

noncomputable def protocolIsoGeneratedExplicitRealizationSupply
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    EquationExplicitRealizationSupply (protocolIsoGeneratedEquationTransport e) := by
  unfold protocolIsoGeneratedEquationTransport protocolAATCoreGeneratedGeometryData
  exact coreGeometryExplicitRealizationSupplyCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y)
    (Equiv.refl _) (protocolIsoObjectMap e)
    (protocolIsoEndpointEquationTransport e)
    (protocolIsoEndpointExplicitRealizationSupply e)

/-- Package-level name for the explicit equation supply carried by a complete
base hom. -/
abbrev ExplicitRealizationTransportSupply {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) (f : PackageTotalHom P Q) :=
  EquationExplicitRealizationSupply f.upper.equationTransport

noncomputable def lensIsoExplicitRealizationTransportSupply
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    ExplicitRealizationTransportSupply (lensAATReadingCore input X).core
      (lensAATReadingCore input Y).core (lensIsoPackageTotalHom e) :=
  lensIsoGeneratedExplicitRealizationSupply e

noncomputable def protocolIsoExplicitRealizationTransportSupply
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ExplicitRealizationTransportSupply (protocolAATReadingCore input X).core
      (protocolAATReadingCore input Y).core (protocolIsoPackageTotalHom e) :=
  protocolIsoGeneratedExplicitRealizationSupply e

/-- Honest checkpoint: every currently constructed computational component
plus explicit realization transport.  Coverage and overlap are absent rather
than accepted as fields. -/
structure ExplicitExactGeometryCheckpoint {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  base : PackageTotalHom G.core H.core
  coefficientHom : G.Coefficient →+* H.Coefficient
  raw : RawAmbientRestrictionSystemExactMapAgainst G.site H.site
    (coreContextInverse base) coefficientHom G.raw H.raw
  realization : ExplicitRealizationTransportSupply G.core H.core base

noncomputable def lensIsoExplicitExactGeometryCheckpoint
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    ExplicitExactGeometryCheckpoint (lensAATReadingCore input X)
      (lensAATReadingCore input Y) where
  base := lensIsoPackageTotalHom e
  coefficientHom := RingHom.id Int
  raw := lensIsoReadingCoreRawExactMapAgainst e (lensIsoPackageTotalHom e)
  realization := lensIsoExplicitRealizationTransportSupply e

noncomputable def protocolIsoExplicitExactGeometryCheckpoint
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ExplicitExactGeometryCheckpoint (protocolAATReadingCore input X)
      (protocolAATReadingCore input Y) where
  base := protocolIsoPackageTotalHom e
  coefficientHom := RingHom.id Int
  raw := protocolIsoReadingCoreRawExactMapAgainst e (protocolIsoPackageTotalHom e)
  realization := protocolIsoExplicitRealizationTransportSupply e

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
