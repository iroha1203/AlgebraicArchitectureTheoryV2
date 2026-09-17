import ResearchLean.AG.RealizationReconstruction.CSAATPackageTotalIso
import Formal.Util.AssertStandardAxioms

/-!
# Generated-context carrier equivalences for the genuine CS isomorphisms

For every generated context of either CS model, this file constructs genuine
equivalences on `Support`, `Axis`, and `Observable`, together with preservation
and reflection of the three reading predicates.  The endpoint equivalences are
definitionally reflexive; the generated versions are obtained by transporting
them along the already proved generated-object provenance equalities.

This deliberately does not claim `RealizationTransportSupply`: naturality of
the component maps still requires coherence between independently selected
representatives of thin context morphisms.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- Carrier-level equivalences and exact reading preservation for every source
context of an exact equation-system transport.  These are stronger data than
the forward component maps and one-way reading preservation eventually needed
by `RealizationTransportSupply`, but contain no naturality certificate. -/
structure EquationContextCarrierEquiv
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (T : EquationSystemExactTransport E F atomEquiv objectMap) where
  supportEquiv : ∀ W : Site.ContextCategoryObject C,
    W.ctx.Support ≃ (T.contextEquivalence.functor.obj W).ctx.Support
  axisEquiv : ∀ W : Site.ContextCategoryObject C,
    W.ctx.Axis ≃ (T.contextEquivalence.functor.obj W).ctx.Axis
  observableEquiv : ∀ W : Site.ContextCategoryObject C,
    W.ctx.Observable ≃ (T.contextEquivalence.functor.obj W).ctx.Observable
  supportReads_iff : ∀ (W : Site.ContextCategoryObject C) support atom,
    W.ctx.minimal.supportReads support atom ↔
      (T.contextEquivalence.functor.obj W).ctx.minimal.supportReads
        (supportEquiv W support) (atomEquiv atom)
  axisReads_iff : ∀ (W : Site.ContextCategoryObject C) axis,
    W.ctx.minimal.axisReads axis ↔
      (T.contextEquivalence.functor.obj W).ctx.minimal.axisReads (axisEquiv W axis)
  observableReads_iff : ∀ (W : Site.ContextCategoryObject C) observable,
    W.ctx.minimal.observableReads observable ↔
      (T.contextEquivalence.functor.obj W).ctx.minimal.observableReads
        (observableEquiv W observable)

/-- At a lens endpoint, full-family rebasing leaves all three context carriers
and reading predicates definitionally unchanged. -/
noncomputable def lensIsoEndpointContextCarrierEquiv
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    EquationContextCarrierEquiv (lensIsoEndpointEquationTransport e) where
  supportEquiv := fun _ => Equiv.refl _
  axisEquiv := fun _ => Equiv.refl _
  observableEquiv := fun _ => Equiv.refl _
  supportReads_iff := fun _ _ _ => Iff.rfl
  axisReads_iff := fun _ _ => Iff.rfl
  observableReads_iff := fun _ _ => Iff.rfl

/-- At a protocol endpoint, full-family rebasing leaves all three context
carriers and reading predicates definitionally unchanged. -/
noncomputable def protocolIsoEndpointContextCarrierEquiv
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    EquationContextCarrierEquiv (protocolIsoEndpointEquationTransport e) where
  supportEquiv := fun _ => Equiv.refl _
  axisEquiv := fun _ => Equiv.refl _
  observableEquiv := fun _ => Equiv.refl _
  supportReads_iff := fun _ _ _ => Iff.rfl
  axisReads_iff := fun _ _ => Iff.rfl
  observableReads_iff := fun _ _ => Iff.rfl

/-- Transport carrier equivalences through the source and target generated-
object provenance equalities. -/
noncomputable def coreGeometryContextCarrierEquivCast
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
    (carrier : EquationContextCarrierEquiv transport) :
    EquationContextCarrierEquiv
      (coreGeometryEquationTransportCast source_eq target_eq sourceData targetData
        atomEquiv objectMap transport) := by
  cases source_eq
  cases target_eq
  exact carrier

/-- Every generated lens context receives the full carrier equivalences and
reading iff facts induced by the genuine lens isomorphism. -/
noncomputable def lensIsoGeneratedContextCarrierEquiv
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    EquationContextCarrierEquiv (lensIsoGeneratedEquationTransport e) := by
  unfold lensIsoGeneratedEquationTransport lensAATCoreGeneratedGeometryData
  exact coreGeometryContextCarrierEquivCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y)
    (Equiv.refl _) (lensIsoObjectMap e)
    (lensIsoEndpointEquationTransport e)
    (lensIsoEndpointContextCarrierEquiv e)

/-- Every generated protocol context receives the full carrier equivalences
and reading iff facts induced by the genuine protocol isomorphism. -/
noncomputable def protocolIsoGeneratedContextCarrierEquiv
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    EquationContextCarrierEquiv (protocolIsoGeneratedEquationTransport e) := by
  unfold protocolIsoGeneratedEquationTransport protocolAATCoreGeneratedGeometryData
  exact coreGeometryContextCarrierEquivCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y)
    (Equiv.refl _) (protocolIsoObjectMap e)
    (protocolIsoEndpointEquationTransport e)
    (protocolIsoEndpointContextCarrierEquiv e)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
