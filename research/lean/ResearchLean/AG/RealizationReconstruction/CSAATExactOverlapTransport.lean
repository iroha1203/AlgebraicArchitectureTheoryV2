import ResearchLean.AG.RealizationReconstruction.CSAATExactGeometryRawCheckpoint
import Formal.Util.AssertStandardAxioms

/-!
# Exact overlap transport for the generated CS cores

This file constructs the overlap component required by the authoritative
geometry-hom contract for genuine lens and protocol isomorphisms.  The
comparison is built on the actual generated equation transport: on the
endpoint product overlaps both directions are explicit identity-on-data
restrictions between the two full-family rebases, and the construction is
then transported along the proved generated-object equalities.

Coverage and the parallel exact geometry hom are intentionally not assembled
here.  In particular, no completed overlap certificate is accepted by either
final CS constructor.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u

/-- Overlap comparison attached to one exact equation transport between the
dependent endpoint geometry bundles. -/
structure CoreGeometryOverlapTransport
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (sourceData : CSAATCoreGeometryData A)
    (targetData : CSAATCoreGeometryData B)
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (T : EquationSystemExactTransport
      sourceData.equationReading.equationSystem
      targetData.equationReading.equationSystem atomEquiv objectMap) where
  overlapIso : ∀ base left right,
    T.contextEquivalence.functor.obj
        ⟨sourceData.overlap.overlap
          (T.contextEquivalence.inverse.obj ⟨base⟩).ctx
          (T.contextEquivalence.inverse.obj ⟨left⟩).ctx
          (T.contextEquivalence.inverse.obj ⟨right⟩).ctx⟩ ≅
      ⟨targetData.overlap.overlap base left right⟩

/-- Lens endpoint overlaps are isomorphic by explicit restrictions in both
directions on the doubly rebased product context. -/
noncomputable def lensIsoEndpointCoreGeometryOverlapTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    CoreGeometryOverlapTransport
      (lensAATCoreEndpointGeometryData input X)
      (lensAATCoreEndpointGeometryData input Y)
      (lensIsoEndpointEquationTransport e) where
  overlapIso base left right := by
    refine Iso.mk (homOfLE ?_) (homOfLE ?_)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    · refine ⟨{ supportMap := id, axisMap := id, observableRestrict := id }, ?_⟩
      exact ⟨(fun h => h), (fun h => h),
        (by intro observable h; cases observable <;> exact h),
        (fun _ => typedRoleConfiguration_mem _ _)⟩
    · refine ⟨{ supportMap := id, axisMap := id, observableRestrict := id }, ?_⟩
      exact ⟨(fun h => h), (fun h => h),
        (by intro observable h; cases observable <;> exact h),
        (fun _ => typedRoleConfiguration_mem _ _)⟩

/-- Protocol endpoint overlaps have the same explicit two-sided comparison. -/
noncomputable def protocolIsoEndpointCoreGeometryOverlapTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    CoreGeometryOverlapTransport
      (protocolAATCoreEndpointGeometryData input X)
      (protocolAATCoreEndpointGeometryData input Y)
      (protocolIsoEndpointEquationTransport e) where
  overlapIso base left right := by
    refine Iso.mk (homOfLE ?_) (homOfLE ?_)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    · refine ⟨{ supportMap := id, axisMap := id, observableRestrict := id }, ?_⟩
      exact ⟨(fun h => h), (fun h => h),
        (by intro observable h; cases observable <;> exact h),
        (fun _ => typedRoleConfiguration_mem _ _)⟩
    · refine ⟨{ supportMap := id, axisMap := id, observableRestrict := id }, ?_⟩
      exact ⟨(fun h => h), (fun h => h),
        (by intro observable h; cases observable <;> exact h),
        (fun _ => typedRoleConfiguration_mem _ _)⟩

/-- Transport an already constructed endpoint overlap comparison through the
same generated-object equalities used by the equation transport. -/
noncomputable def coreGeometryOverlapTransportCast
    {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (atomEquiv : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport sourceData.equationReading.equationSystem
      targetData.equationReading.equationSystem atomEquiv objectMap)
    (overlap : CoreGeometryOverlapTransport sourceData targetData T) :
    CoreGeometryOverlapTransport (source_eq.symm ▸ sourceData)
      (target_eq.symm ▸ targetData)
      (coreGeometryEquationTransportCast source_eq target_eq sourceData targetData
        atomEquiv objectMap T) := by
  cases source_eq
  cases target_eq
  exact overlap

noncomputable def lensIsoGeneratedCoreGeometryOverlapTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    CoreGeometryOverlapTransport
      (lensAATCoreGeneratedGeometryData input X)
      (lensAATCoreGeneratedGeometryData input Y)
      (lensIsoGeneratedEquationTransport e) := by
  unfold lensAATCoreGeneratedGeometryData lensIsoGeneratedEquationTransport
  exact coreGeometryOverlapTransportCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    _ _ _ _ _ (lensIsoEndpointCoreGeometryOverlapTransport e)

noncomputable def protocolIsoGeneratedCoreGeometryOverlapTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    CoreGeometryOverlapTransport
      (protocolAATCoreGeneratedGeometryData input X)
      (protocolAATCoreGeneratedGeometryData input Y)
      (protocolIsoGeneratedEquationTransport e) := by
  unfold protocolAATCoreGeneratedGeometryData protocolIsoGeneratedEquationTransport
  exact coreGeometryOverlapTransportCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    _ _ _ _ _ (protocolIsoEndpointCoreGeometryOverlapTransport e)

/-- Authoritative overlap transport constructed from a primitive lens
isomorphism, with no completed overlap input. -/
noncomputable def lensIsoOverlapTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    OverlapTransport (lensAATReadingCore input X) (lensAATReadingCore input Y)
      (lensIsoPackageTotalHom e) where
  overlapIso := (lensIsoGeneratedCoreGeometryOverlapTransport e).overlapIso

/-- Authoritative overlap transport constructed from a primitive protocol
isomorphism, with no completed overlap input. -/
noncomputable def protocolIsoOverlapTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    OverlapTransport (protocolAATReadingCore input X)
      (protocolAATReadingCore input Y) (protocolIsoPackageTotalHom e) where
  overlapIso := (protocolIsoGeneratedCoreGeometryOverlapTransport e).overlapIso

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
