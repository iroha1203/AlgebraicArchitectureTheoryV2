import ResearchLean.AG.RealizationReconstruction.CSAATExactGeometryRawCheckpoint
import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedContextCarrierEquiv
import Formal.Util.AssertStandardAxioms

/-!
# Endpoint coverage transport for genuine CS isomorphisms

This file constructs all nine authoritative coverage clauses on the concrete
lens and protocol endpoint geometry bundles.  A source restriction is sent to
the target reading by pulling every target polynomial back through the inverse
genuine Law-coordinate equivalence.  Thus equation, violation, and axis
visibility all use one actual total target restriction; no selected-coordinate
constant map or completed coverage certificate is accepted.

Transport through the dependent generated-object provenance, and projection
to package-level `CoverageTransport`, remain separate obligations.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation

universe u

/-- Transport an actual restriction into the target lens reading using the
inverse genuine coordinate equivalence on every observable. -/
noncomputable def lensIsoCoverageContextMorphism
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    {W : Site.ArchCtx (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (f : Site.ContextMorphism W (lensAATGeometryReadingContext input X)) :
    Site.ContextMorphism
      (fullFamilyContextRebase
        (lensLawObject input Y.Carrier Y.toLensData.toLawStructure)
        (fun atom => typedRoleConfiguration_mem _ atom) W)
      (lensAATGeometryReadingContext input Y) where
  supportMap := f.supportMap
  axisMap := f.axisMap
  observableRestrict polynomial :=
    f.observableRestrict ((lensIsoLawCoordinateEquiv e).symm polynomial)

theorem lensIsoCoverageContextMorphism_isRestriction
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    {W : Site.ArchCtx (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (f : Site.ContextMorphism W (lensAATGeometryReadingContext input X))
    (hf : f.IsRestriction) :
    (lensIsoCoverageContextMorphism e f).IsRestriction := by
  refine ⟨hf.1, hf.2.1, ?_, ?_⟩
  · intro polynomial h
    rcases h with ⟨coordinate, rfl⟩
    apply hf.2.2.1
    refine ⟨(lensIsoLawCoordinateIndexEquiv e).symm coordinate, ?_⟩
    simp [lensIsoLawCoordinateEquiv, lensIsoLawCoordinateIndexEquiv]
  · intro support atom _
    exact typedRoleConfiguration_mem _ atom

/-- The nine coverage clauses before transport from the concrete endpoint
bundle to the source-generated core. -/
structure CoreGeometryCoverageTransport
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (sourceData : CSAATCoreGeometryData A)
    (targetData : CSAATCoreGeometryData B)
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (axisMap : sourceData.signature.Axis → targetData.signature.Axis)
    (T : EquationSystemExactTransport
      sourceData.equationReading.equationSystem
      targetData.equationReading.equationSystem atomEquiv objectMap) : Prop where
  requiredSupport : ∀ atom,
    sourceData.requirements.requiredSupport atom →
      targetData.requirements.requiredSupport (atomEquiv atom)
  requiredEquationCoordinate : ∀ coordinate,
    sourceData.requirements.requiredEquationCoordinate coordinate →
      targetData.requirements.requiredEquationCoordinate
        (⟨T.equationEquiv coordinate.1.1,
          (T.required_iff coordinate.1.1).mp coordinate.1.2⟩, atomEquiv coordinate.2)
  selectedViolationWitness : ∀ coordinate,
    sourceData.requirements.selectedViolationWitness coordinate →
      targetData.requirements.selectedViolationWitness
        (T.equationEquiv coordinate.1, atomEquiv coordinate.2)
  requiredAxis : ∀ axis,
    sourceData.requirements.requiredAxis axis →
      targetData.requirements.requiredAxis (axisMap axis)
  supportVisibleOn : ∀ W atom,
    sourceData.requirements.supportVisibleOn W atom →
      targetData.requirements.supportVisibleOn
        (T.contextEquivalence.functor.obj ⟨W⟩).ctx (atomEquiv atom)
  equationCoordinateVisibleOn : ∀ W coordinate,
    sourceData.requirements.equationCoordinateVisibleOn W coordinate →
      targetData.requirements.equationCoordinateVisibleOn
        (T.contextEquivalence.functor.obj ⟨W⟩).ctx
        (⟨T.equationEquiv coordinate.1.1,
          (T.required_iff coordinate.1.1).mp coordinate.1.2⟩, atomEquiv coordinate.2)
  violationWitnessVisibleOn : ∀ W coordinate,
    sourceData.requirements.violationWitnessVisibleOn W coordinate →
      targetData.requirements.violationWitnessVisibleOn
        (T.contextEquivalence.functor.obj ⟨W⟩).ctx
        (T.equationEquiv coordinate.1, atomEquiv coordinate.2)
  axisReadableOn : ∀ W axis,
    sourceData.requirements.axisReadableOn W axis →
      targetData.requirements.axisReadableOn
        (T.contextEquivalence.functor.obj ⟨W⟩).ctx (axisMap axis)
  boundaryVisibleOn : ∀ W V,
    sourceData.requirements.boundaryVisibleOn W V →
      targetData.requirements.boundaryVisibleOn
        (T.contextEquivalence.functor.obj ⟨W⟩).ctx
        (T.contextEquivalence.functor.obj ⟨V⟩).ctx

/-- All nine concrete lens endpoint coverage clauses, constructed from the
primitive genuine CS isomorphism. -/
noncomputable def lensIsoEndpointCoreGeometryCoverageTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    CoreGeometryCoverageTransport
      (lensAATCoreEndpointGeometryData input X)
      (lensAATCoreEndpointGeometryData input Y) id
      (lensIsoEndpointEquationTransport e) where
  requiredSupport _ _ := trivial
  requiredEquationCoordinate _ _ := trivial
  selectedViolationWitness _ _ := trivial
  requiredAxis _ _ := trivial
  supportVisibleOn _ _ h := h
  equationCoordinateVisibleOn W coordinate h := by
    rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
    rcases h with ⟨f, hf, hread⟩
    refine ⟨lensIsoCoverageContextMorphism e f,
      lensIsoCoverageContextMorphism_isRestriction e f hf, ?_⟩
    apply ((lensIsoEndpointContextCarrierEquiv e).observableReads_iff ⟨W⟩ _).mp
    dsimp [lensIsoEndpointEquationTransport]
    let sourcePair :
        ULift.{u + 1, u} (LensLawIndex input.View X.Carrier) × LensAATAtom input :=
      (ULift.up index, atom)
    have hcoordinate :
        (lensIsoLawCoordinateEquiv e).symm
          (MvPolynomial.X (lensIsoLawCoordinateIndexEquiv e sourcePair)) =
            MvPolynomial.X sourcePair := by
      simp [lensIsoLawCoordinateEquiv, sourcePair]
    have hobs := congrArg f.observableRestrict hcoordinate
    rw [← hobs] at hread
    exact hread
  violationWitnessVisibleOn W coordinate h := by
    rcases coordinate with ⟨⟨index⟩, atom⟩
    rcases h with ⟨f, hf, hread⟩
    refine ⟨lensIsoCoverageContextMorphism e f,
      lensIsoCoverageContextMorphism_isRestriction e f hf, ?_⟩
    apply ((lensIsoEndpointContextCarrierEquiv e).observableReads_iff ⟨W⟩ _).mp
    dsimp [lensIsoEndpointEquationTransport]
    let sourcePair :
        ULift.{u + 1, u} (LensLawIndex input.View X.Carrier) × LensAATAtom input :=
      (ULift.up index, atom)
    have hcoordinate :
        (lensIsoLawCoordinateEquiv e).symm
          (MvPolynomial.X (lensIsoLawCoordinateIndexEquiv e sourcePair)) =
            MvPolynomial.X sourcePair := by
      simp [lensIsoLawCoordinateEquiv, sourcePair]
    have hobs := congrArg f.observableRestrict hcoordinate
    rw [← hobs] at hread
    exact hread
  axisReadableOn _ _ h := by
    rcases h with ⟨f, hf, localAxis, hlocal, heq⟩
    exact ⟨lensIsoCoverageContextMorphism e f,
      lensIsoCoverageContextMorphism_isRestriction e f hf,
      localAxis, hlocal, heq⟩
  boundaryVisibleOn _ _ h := by
    rcases h with ⟨f, hf⟩
    exact ⟨fullFamilyContextMorphismRebase _
      (fun atom => typedRoleConfiguration_mem _ atom) f,
      fullFamilyContextMorphismRebase_isRestriction _ _ f hf⟩

/-- Protocol analogue of the total target restriction. -/
noncomputable def protocolIsoCoverageContextMorphism
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (f : Site.ContextMorphism W (protocolAATGeometryReadingContext input X)) :
    Site.ContextMorphism
      (fullFamilyContextRebase
        (protocolLawObject input Y.State Y.toLawStructure)
        (fun atom => typedRoleConfiguration_mem _ atom) W)
      (protocolAATGeometryReadingContext input Y) where
  supportMap := f.supportMap
  axisMap := f.axisMap
  observableRestrict polynomial :=
    f.observableRestrict ((protocolIsoLawCoordinateEquiv e).symm polynomial)

theorem protocolIsoCoverageContextMorphism_isRestriction
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (f : Site.ContextMorphism W (protocolAATGeometryReadingContext input X))
    (hf : f.IsRestriction) :
    (protocolIsoCoverageContextMorphism e f).IsRestriction := by
  refine ⟨hf.1, hf.2.1, ?_, ?_⟩
  · intro polynomial h
    rcases h with ⟨coordinate, rfl⟩
    apply hf.2.2.1
    refine ⟨(protocolIsoLawCoordinateIndexEquiv e).symm coordinate, ?_⟩
    simp [protocolIsoLawCoordinateEquiv, protocolIsoLawCoordinateIndexEquiv]
  · intro support atom _
    exact typedRoleConfiguration_mem _ atom

/-- All nine concrete protocol endpoint coverage clauses, constructed from
the primitive genuine CS isomorphism. -/
noncomputable def protocolIsoEndpointCoreGeometryCoverageTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    CoreGeometryCoverageTransport
      (protocolAATCoreEndpointGeometryData input X)
      (protocolAATCoreEndpointGeometryData input Y) id
      (protocolIsoEndpointEquationTransport e) where
  requiredSupport _ _ := trivial
  requiredEquationCoordinate _ _ := trivial
  selectedViolationWitness _ _ := trivial
  requiredAxis _ _ := trivial
  supportVisibleOn _ _ h := h
  equationCoordinateVisibleOn W coordinate h := by
    rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
    rcases h with ⟨f, hf, hread⟩
    refine ⟨protocolIsoCoverageContextMorphism e f,
      protocolIsoCoverageContextMorphism_isRestriction e f hf, ?_⟩
    apply ((protocolIsoEndpointContextCarrierEquiv e).observableReads_iff ⟨W⟩ _).mp
    dsimp [protocolIsoEndpointEquationTransport]
    let sourcePair :
        ULift.{u + 1, u} (ProtocolLawIndex X.State) × ProtocolAATAtom input :=
      (ULift.up index, atom)
    have hcoordinate :
        (protocolIsoLawCoordinateEquiv e).symm
          (MvPolynomial.X (protocolIsoLawCoordinateIndexEquiv e sourcePair)) =
            MvPolynomial.X sourcePair := by
      simp [protocolIsoLawCoordinateEquiv, sourcePair]
    have hobs := congrArg f.observableRestrict hcoordinate
    rw [← hobs] at hread
    exact hread
  violationWitnessVisibleOn W coordinate h := by
    rcases coordinate with ⟨⟨index⟩, atom⟩
    rcases h with ⟨f, hf, hread⟩
    refine ⟨protocolIsoCoverageContextMorphism e f,
      protocolIsoCoverageContextMorphism_isRestriction e f hf, ?_⟩
    apply ((protocolIsoEndpointContextCarrierEquiv e).observableReads_iff ⟨W⟩ _).mp
    dsimp [protocolIsoEndpointEquationTransport]
    let sourcePair :
        ULift.{u + 1, u} (ProtocolLawIndex X.State) × ProtocolAATAtom input :=
      (ULift.up index, atom)
    have hcoordinate :
        (protocolIsoLawCoordinateEquiv e).symm
          (MvPolynomial.X (protocolIsoLawCoordinateIndexEquiv e sourcePair)) =
            MvPolynomial.X sourcePair := by
      simp [protocolIsoLawCoordinateEquiv, sourcePair]
    have hobs := congrArg f.observableRestrict hcoordinate
    rw [← hobs] at hread
    exact hread
  axisReadableOn _ _ h := by
    rcases h with ⟨f, hf, localAxis, hlocal, heq⟩
    exact ⟨protocolIsoCoverageContextMorphism e f,
      protocolIsoCoverageContextMorphism_isRestriction e f hf,
      localAxis, hlocal, heq⟩
  boundaryVisibleOn _ _ h := by
    rcases h with ⟨f, hf⟩
    exact ⟨fullFamilyContextMorphismRebase _
      (fun atom => typedRoleConfiguration_mem _ atom) f,
      fullFamilyContextMorphismRebase_isRestriction _ _ f hf⟩

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
