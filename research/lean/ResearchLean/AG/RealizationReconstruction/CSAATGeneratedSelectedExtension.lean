import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedDirectedForward
import Formal.Util.AssertStandardAxioms

/-!
# Selected Extension actions on generated ReadingCores

`CSAATCoreGeometryData` deliberately has no distinguished context, so a map on
all possible Extension carriers cannot be inferred from it.  This module
instead transports the canonical CS-selected reading context to the generated
core object, decodes its exact fixed-input payload, and proves the named
operation equations from the primitive CS morphism.  No whole-Extension map or
prepackaged semantic hom is accepted.
-/

namespace AAT.AG.RealizationReconstruction

universe u

private theorem transportedArchitectureContextExtension_heq
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (h : A = B) (context : Site.ArchCtx A) :
    HEq (h ▸ context).extension context.extension := by
  cases h
  rfl

private theorem transportedArchitectureContextExtension_type
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (h : A = B) (context : Site.ArchCtx A) :
    (h ▸ context).Extension = context.Extension := by
  cases h
  rfl

private theorem transportedArchitectureContextExtension_cast
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (h : A = B) (context : Site.ArchCtx A) :
    cast (transportedArchitectureContextExtension_type h context)
        (h ▸ context).extension = context.extension := by
  cases h
  rfl

/-- Canonical selected lens context on the generated core object. -/
noncomputable def lensAATGeneratedReadingContext
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    Site.ArchCtx (lensAATCorePackage input X).object :=
  (lensAATCorePackage_object_eq input X).symm ▸
    lensAATGeometryReadingContext input X

/-- Canonical selected protocol context on the generated core object. -/
noncomputable def protocolAATGeneratedReadingContext
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    Site.ArchCtx (protocolAATCorePackage input X).object :=
  (protocolAATCorePackage_object_eq input X).symm ▸
    protocolAATGeometryReadingContext input X

theorem lensAATGeneratedReadingContext_extension_heq
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    HEq (lensAATGeneratedReadingContext input X).extension
      (lensAATGeometryReadingContext input X).extension := by
  unfold lensAATGeneratedReadingContext
  exact transportedArchitectureContextExtension_heq _ _

theorem protocolAATGeneratedReadingContext_extension_heq
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    HEq (protocolAATGeneratedReadingContext input X).extension
      (protocolAATGeometryReadingContext input X).extension := by
  unfold protocolAATGeneratedReadingContext
  exact transportedArchitectureContextExtension_heq _ _

/-- Generated lens Extension decoded into its fixed-input get/put payload. -/
noncomputable def lensAATGeneratedExtensionPayload
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    ULift.{u + 1, u} (LensLawStructure input.View X.Carrier) × LensAATSource X :=
  cast (transportedArchitectureContextExtension_type
      (lensAATCorePackage_object_eq input X).symm
      (lensAATGeometryReadingContext input X))
    (lensAATGeneratedReadingContext input X).extension

@[simp] theorem lensAATGeneratedExtensionPayload_eq
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    lensAATGeneratedExtensionPayload input X =
      (lensAATGeometryReadingContext input X).extension := by
  unfold lensAATGeneratedExtensionPayload lensAATGeneratedReadingContext
  exact transportedArchitectureContextExtension_cast _ _

/-- Named lens Extension equations stated through the actual generated
payload.  They are constructed from `f`; they are not input certificates. -/
structure LensAATGeneratedExtensionCoherence
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) : Prop where
  point_map : f.sourceMap (lensAATGeneratedExtensionPayload input X).2 =
    (lensAATGeneratedExtensionPayload input Y).2
  get_map : ∀ state,
    (lensAATGeneratedExtensionPayload input Y).1.down.get (f.stateMap state) =
      (lensAATGeneratedExtensionPayload input X).1.down.get state
  put_map : ∀ state view,
    f.stateMap ((lensAATGeneratedExtensionPayload input X).1.down.put state view) =
      (lensAATGeneratedExtensionPayload input Y).1.down.put (f.stateMap state) view

def lensAATGeneratedExtensionCoherence
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATGeneratedExtensionCoherence input f where
  point_map := by
    simpa using (lensAATForwardExtensionCoherence input f).point_map
  get_map := by
    simpa using (lensAATForwardExtensionCoherence input f).get_map
  put_map := by
    simpa using (lensAATForwardExtensionCoherence input f).put_map

/-- Generated protocol Extension decoded into the fixed schema-indexed
edge/observation payload. -/
noncomputable def protocolAATGeneratedExtensionPayload
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ULift.{u + 1, u} (ProtocolLawStructure input X.State) × ProtocolAATSource X :=
  cast (transportedArchitectureContextExtension_type
      (protocolAATCorePackage_object_eq input X).symm
      (protocolAATGeometryReadingContext input X))
    (protocolAATGeneratedReadingContext input X).extension

@[simp] theorem protocolAATGeneratedExtensionPayload_eq
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    protocolAATGeneratedExtensionPayload input X =
      (protocolAATGeometryReadingContext input X).extension := by
  unfold protocolAATGeneratedExtensionPayload protocolAATGeneratedReadingContext
  exact transportedArchitectureContextExtension_cast _ _

/-- Named protocol Extension equations for every schema edge and observation,
stated through the generated payload. -/
structure ProtocolAATGeneratedExtensionCoherence
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) : Prop where
  point_map : f.sourceMap (protocolAATGeneratedExtensionPayload input X).2 =
    (protocolAATGeneratedExtensionPayload input Y).2
  edge_map : ∀ {source target} (edge : input.schema.Edge source target)
      (state : X.State source),
    f.stateMap target
        ((protocolAATGeneratedExtensionPayload input X).1.down.edgeAction edge state) =
      (protocolAATGeneratedExtensionPayload input Y).1.down.edgeAction edge
        (f.stateMap source state)
  observation_map : ∀ vertex (state : X.State vertex),
    (protocolAATGeneratedExtensionPayload input Y).1.down.observe vertex
        (f.stateMap vertex state) =
      (protocolAATGeneratedExtensionPayload input X).1.down.observe vertex state

def protocolAATGeneratedExtensionCoherence
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    ProtocolAATGeneratedExtensionCoherence input f where
  point_map := by
    simpa using (protocolAATForwardExtensionCoherence input f).point_map
  edge_map := by
    intro source target edge state
    simp only [protocolAATGeneratedExtensionPayload_eq]
    exact (protocolAATForwardExtensionCoherence input f).edge_map edge state
  observation_map := by
    simpa using (protocolAATForwardExtensionCoherence input f).observation_map

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
