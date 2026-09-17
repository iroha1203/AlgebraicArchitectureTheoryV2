import ResearchLean.AG.RealizationReconstruction.CSAATProtocolCoreExactPrefix
import Formal.Util.AssertStandardAxioms

/-!
# Generated-core equation transport for genuine CS isomorphisms

The lens and protocol object maps constructed from their primitive semantics
are assembled into full equation-system transports.  Context equivalences are
constructed from the forward and inverse Law homs; equation indices and every
polynomial coordinate use the genuine semantic isomorphism.  Existing
generated-object equalities then transport the endpoint construction to the
source-generated `AATCorePackage` equation systems.

The generic cast helper is conditional on an already constructed endpoint
transport.  The exported lens and protocol generated-core constructors
discharge that premise with their CS-specific endpoint construction and accept
no completed equation transport, core hom, or geometry hom as an input.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- The context categories of genuinely isomorphic lens Law objects are
equivalent by the forward and inverse full-family context functors. -/
noncomputable def lensIsoEndpointContextEquivalence
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (lensLawObject input X.Carrier X.toLensData.toLawStructure)) ≌
      Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (lensLawObject input Y.Carrier Y.toLensData.toLawStructure)) := by
  let F := lensLawContextFunctor e.hom.toLawHom
  let G := lensLawContextFunctor e.inv.toLawHom
  refine CategoryTheory.Equivalence.mk F G ?_ ?_
  · refine NatIso.ofComponents (fun W => Iso.mk ?_ ?_ ?_ ?_)
      (by intros; apply Subsingleton.elim)
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply Subsingleton.elim
    · apply Subsingleton.elim
  · refine NatIso.ofComponents (fun W => Iso.mk ?_ ?_ ?_ ?_)
      (by intros; apply Subsingleton.elim)
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply Subsingleton.elim
    · apply Subsingleton.elim

/-- Full endpoint equation transport for a genuine lens isomorphism. -/
noncomputable def lensIsoEndpointEquationTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    EquationSystemExactTransport
      (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)
      (lensLawEquationSystem input Y.Carrier Y.toLensData.toLawStructure)
      (Equiv.refl (LensAATAtom input)) (lensIsoObjectMap e) where
  contextEquivalence := lensIsoEndpointContextEquivalence e
  equationEquiv :=
    Equiv.ulift.trans ((lensIsoLawIndexEquiv e).trans Equiv.ulift.symm)
  role_eq := by
    intro index
    rfl
  observableEquiv := fun _ => (lensIsoLawCoordinateEquiv e).toRingEquiv
  observable_naturality := by
    intros
    rfl
  violationCoordinate_eq := by
    intro W index atom
    cases index with
    | up index =>
      exact lensIsoLawCoordinateEquiv_X e index atom
  equationResidual_eq := by
    intro W object index atom
    cases index with
    | up index =>
      exact lensIsoObjectMap_equationResidual_eq e W.ctx
        ((lensIsoEndpointContextEquivalence e).functor.obj W).ctx
        object index atom

/-- Conditional generic helper: change only the generated-object equalities
around an already constructed endpoint equation transport.  The exported
CS-specific constructors below construct and supply this premise. -/
noncomputable def coreGeometryEquationTransportCast
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
      targetData.equationReading.equationSystem atomEquiv objectMap) :
    EquationSystemExactTransport
      (source_eq.symm ▸ sourceData).equationReading.equationSystem
      (target_eq.symm ▸ targetData).equationReading.equationSystem
      atomEquiv objectMap := by
  cases source_eq
  cases target_eq
  exact transport

/-- Generated-core equation transport for a genuine lens isomorphism. -/
noncomputable def lensIsoGeneratedEquationTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    EquationSystemExactTransport
      (lensAATCorePackage input X).algebra.equationSystem
      (lensAATCorePackage input Y).algebra.equationSystem
      (Equiv.refl (LensAATAtom input)) (lensIsoObjectMap e) := by
  change EquationSystemExactTransport
    (lensAATCoreGeneratedGeometryData input X).equationReading.equationSystem
    (lensAATCoreGeneratedGeometryData input Y).equationReading.equationSystem
    (Equiv.refl (LensAATAtom input)) (lensIsoObjectMap e)
  unfold lensAATCoreGeneratedGeometryData
  exact coreGeometryEquationTransportCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y)
    (Equiv.refl _) (lensIsoObjectMap e)
    (lensIsoEndpointEquationTransport e)

/-- The context categories of genuinely isomorphic protocol Law objects are
equivalent by the forward and inverse full-family context functors. -/
noncomputable def protocolIsoEndpointContextEquivalence
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (protocolLawObject input X.State X.toLawStructure)) ≌
      Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory
          (protocolLawObject input Y.State Y.toLawStructure)) := by
  let F := protocolLawContextFunctor e.hom.toLawHom
  let G := protocolLawContextFunctor e.inv.toLawHom
  refine CategoryTheory.Equivalence.mk F G ?_ ?_
  · refine NatIso.ofComponents (fun W => Iso.mk ?_ ?_ ?_ ?_)
      (by intros; apply Subsingleton.elim)
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply Subsingleton.elim
    · apply Subsingleton.elim
  · refine NatIso.ofComponents (fun W => Iso.mk ?_ ?_ ?_ ?_)
      (by intros; apply Subsingleton.elim)
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply homOfLE
      refine ⟨?_, ?_⟩
      · exact {
          supportMap := id
          axisMap := id
          observableRestrict := id }
      · exact ⟨(fun h => h), (fun h => h), (fun h => h),
          (fun h => W.ctx.supportReads_objectFamily h)⟩
    · apply Subsingleton.elim
    · apply Subsingleton.elim

/-- Full endpoint equation transport for a genuine protocol isomorphism. -/
noncomputable def protocolIsoEndpointEquationTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    EquationSystemExactTransport
      (protocolLawEquationSystem input X.State X.toLawStructure)
      (protocolLawEquationSystem input Y.State Y.toLawStructure)
      (Equiv.refl (ProtocolAATAtom input)) (protocolIsoObjectMap e) where
  contextEquivalence := protocolIsoEndpointContextEquivalence e
  equationEquiv :=
    Equiv.ulift.trans ((protocolIsoLawIndexEquiv e).trans Equiv.ulift.symm)
  role_eq := by
    intro index
    rfl
  observableEquiv := fun _ => (protocolIsoLawCoordinateEquiv e).toRingEquiv
  observable_naturality := by
    intros
    rfl
  violationCoordinate_eq := by
    intro W index atom
    cases index with
    | up index =>
      exact protocolIsoLawCoordinateEquiv_X e index atom
  equationResidual_eq := by
    intro W object index atom
    cases index with
    | up index =>
      exact protocolIsoObjectMap_equationResidual_eq e W.ctx
        ((protocolIsoEndpointContextEquivalence e).functor.obj W).ctx
        object index atom

/-- Generated-core equation transport for a genuine protocol isomorphism. -/
noncomputable def protocolIsoGeneratedEquationTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    EquationSystemExactTransport
      (protocolAATCorePackage input X).algebra.equationSystem
      (protocolAATCorePackage input Y).algebra.equationSystem
      (Equiv.refl (ProtocolAATAtom input)) (protocolIsoObjectMap e) := by
  change EquationSystemExactTransport
    (protocolAATCoreGeneratedGeometryData input X).equationReading.equationSystem
    (protocolAATCoreGeneratedGeometryData input Y).equationReading.equationSystem
    (Equiv.refl (ProtocolAATAtom input)) (protocolIsoObjectMap e)
  unfold protocolAATCoreGeneratedGeometryData
  exact coreGeometryEquationTransportCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y)
    (Equiv.refl _) (protocolIsoObjectMap e)
    (protocolIsoEndpointEquationTransport e)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
