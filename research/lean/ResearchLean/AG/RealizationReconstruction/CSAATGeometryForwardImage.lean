import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardStructural
import Formal.Util.AssertStandardAxioms

/-!
# Forward-image geometry for arbitrary CS morphisms

The existing AAT context morphism restricts observables contravariantly.  The
Cycle 138 empty-to-unit example shows that no such global restriction into the
target reading exists for every non-surjective CS morphism.  This module keeps
the honest covariant data instead: every source support, Law coordinate,
violation coordinate, axis, and boundary is carried to its exact generated
target image.

Axis visibility is stated directly on the rebased target context.  Its witness
uses a genuine source restriction, readability of the same local axis after
rebasing, and the exact covariant axis equation.  It never asks for a map from
all target observables back to source observables.

The aggregate records below are constructed from each primitive lens or
protocol morphism.  They contain the generated equation transport, raw
presheaf map, and source-role image coverage.  They do not contain a
target-wide `AATCoverageFamily`, overlap comparison, `ReadingCore`,
`GeometryTotalHom`, inverse, or target-surjectivity assertion.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Covariant axis visibility -/

/-- A source-readable local axis remains readable in the rebased target
context, and its source-reading image is carried to the named target axis by
the covariant axis map.  No target-observable restriction is involved. -/
def ForwardAxisVisibility {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (targetReading : Site.ArchCtx targetObject)
    (axisForward : sourceReading.Axis → targetReading.Axis)
    {W : Site.ArchCtx sourceObject}
    (targetAxis : targetReading.Axis) : Prop :=
  ∃ sourceMap : Site.ContextMorphism W sourceReading,
    sourceMap.IsRestriction ∧
    ∃ localAxis : W.Axis,
      (fullFamilyContextRebase targetObject target_all W).minimal.axisReads
        localAxis ∧
      axisForward (sourceMap.axisMap localAxis) = targetAxis

/-- Exact lens-axis visibility is preserved covariantly for every source
context and every required axis. -/
theorem lensAATForwardAxisCoherent
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (_f : LensAATForwardMorphism X Y)
    {W : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (axis : LensAATAtom input)
    (hvisible : (lensAATGeometryCoverageRequirements input X).axisReadableOn
      W axis) :
    ForwardAxisVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (lensAATGeometryReadingContext input X)
      (lensAATGeometryReadingContext input Y)
      _root_.id axis := by
  rcases hvisible with ⟨sourceMap, hsource, localAxis, hlocal, heq⟩
  exact ⟨sourceMap, hsource, localAxis, hlocal, heq⟩

/-- Exact protocol-axis visibility is preserved covariantly for every source
context and every required axis. -/
theorem protocolAATForwardAxisCoherent
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (_f : ProtocolAATForwardMorphism X Y)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (axis : ProtocolAATAtom input)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).axisReadableOn
      W axis) :
    ForwardAxisVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input Y)
      _root_.id axis := by
  rcases hvisible with ⟨sourceMap, hsource, localAxis, hlocal, heq⟩
  exact ⟨sourceMap, hsource, localAxis, hlocal, heq⟩

/-! ## Source-role image coverage -/

/-- Every required role of a lens source endpoint is carried to its exact
generated target image.  The coordinate and axis clauses deliberately use
the forward-image predicates rather than target-wide coverage predicates. -/
structure LensAATForwardCoverageImage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) : Prop where
  requiredSupport : ∀ atom,
    (lensAATGeometryCoverageRequirements input X).requiredSupport atom →
      (lensAATGeometryCoverageRequirements input Y).requiredSupport atom
  requiredEquationCoordinate : ∀ coordinate,
    (lensAATGeometryCoverageRequirements input X).requiredEquationCoordinate
        coordinate →
      (lensAATGeometryCoverageRequirements input Y).requiredEquationCoordinate
        (lensAATForwardRequiredCoordinate input f coordinate)
  selectedViolationWitness : ∀ coordinate,
    (lensAATGeometryCoverageRequirements input X).selectedViolationWitness
        coordinate →
      (lensAATGeometryCoverageRequirements input Y).selectedViolationWitness
        (lensAATForwardCoordinate input f coordinate)
  requiredAxis : ∀ axis,
    (lensAATGeometryCoverageRequirements input X).requiredAxis axis →
      (lensAATGeometryCoverageRequirements input Y).requiredAxis axis
  supportVisibleOn : ∀ W atom,
    (lensAATGeometryCoverageRequirements input X).supportVisibleOn W atom →
      (lensAATGeometryCoverageRequirements input Y).supportVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx atom
  equationCoordinateVisibleOn : ∀ W coordinate,
    (lensAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
        W coordinate →
      ForwardObservableVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (lensAATGeometryReadingContext input X)
        (lensAATGeometryReadingContext input Y)
        f.lawCoordinateMap
        (MvPolynomial.X (coordinate.1.1, coordinate.2) :
          LensLawCoordinateRing input X.Carrier)
        (MvPolynomial.X
          ((lensAATForwardRequiredCoordinate input f coordinate).1.1,
            (lensAATForwardRequiredCoordinate input f coordinate).2) :
          LensLawCoordinateRing input Y.Carrier)
  violationWitnessVisibleOn : ∀ W coordinate,
    (lensAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
        W coordinate →
      ForwardObservableVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (lensAATGeometryReadingContext input X)
        (lensAATGeometryReadingContext input Y)
        f.lawCoordinateMap
        (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
        (MvPolynomial.X (lensAATForwardCoordinate input f coordinate) :
          LensLawCoordinateRing input Y.Carrier)
  axisReadableOn : ∀ W axis,
    (lensAATGeometryCoverageRequirements input X).axisReadableOn W axis →
      ForwardAxisVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (lensAATGeometryReadingContext input X)
        (lensAATGeometryReadingContext input Y) _root_.id axis
  boundaryVisibleOn : ∀ W base,
    (lensAATGeometryCoverageRequirements input X).boundaryVisibleOn W base →
      (lensAATGeometryCoverageRequirements input Y).boundaryVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx
        ((f.lawContextFunctor).obj ⟨base⟩).ctx

/-- The complete lens source-role image record is generated from each
primitive get/put-preserving morphism. -/
def lensAATForwardCoverageImage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATForwardCoverageImage input f where
  requiredSupport _ _ := trivial
  requiredEquationCoordinate _ _ := trivial
  selectedViolationWitness _ _ := trivial
  requiredAxis _ _ := trivial
  supportVisibleOn _ atom := lensAATForwardSupportVisible input f atom
  equationCoordinateVisibleOn _ coordinate :=
    lensAATForwardEquationCoordinateCoherent input f coordinate
  violationWitnessVisibleOn _ coordinate :=
    lensAATForwardViolationCoordinateCoherent input f coordinate
  axisReadableOn _ axis := lensAATForwardAxisCoherent input f axis
  boundaryVisibleOn _ _ := lensAATForwardBoundaryVisible input f

/-- Every required role of a protocol source endpoint is carried to its exact
generated target image, including every relation/observation coordinate. -/
structure ProtocolAATForwardCoverageImage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) : Prop where
  requiredSupport : ∀ atom,
    (protocolAATGeometryCoverageRequirements input X).requiredSupport atom →
      (protocolAATGeometryCoverageRequirements input Y).requiredSupport atom
  requiredEquationCoordinate : ∀ coordinate,
    (protocolAATGeometryCoverageRequirements input X).requiredEquationCoordinate
        coordinate →
      (protocolAATGeometryCoverageRequirements input Y).requiredEquationCoordinate
        (protocolAATForwardRequiredCoordinate input f coordinate)
  selectedViolationWitness : ∀ coordinate,
    (protocolAATGeometryCoverageRequirements input X).selectedViolationWitness
        coordinate →
      (protocolAATGeometryCoverageRequirements input Y).selectedViolationWitness
        (protocolAATForwardCoordinate input f coordinate)
  requiredAxis : ∀ axis,
    (protocolAATGeometryCoverageRequirements input X).requiredAxis axis →
      (protocolAATGeometryCoverageRequirements input Y).requiredAxis axis
  supportVisibleOn : ∀ W atom,
    (protocolAATGeometryCoverageRequirements input X).supportVisibleOn W atom →
      (protocolAATGeometryCoverageRequirements input Y).supportVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx atom
  equationCoordinateVisibleOn : ∀ W coordinate,
    (protocolAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
        W coordinate →
      ForwardObservableVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (protocolAATGeometryReadingContext input X)
        (protocolAATGeometryReadingContext input Y)
        f.lawCoordinateMap
        (MvPolynomial.X (coordinate.1.1, coordinate.2) :
          ProtocolLawCoordinateRing input X.State)
        (MvPolynomial.X
          ((protocolAATForwardRequiredCoordinate input f coordinate).1.1,
            (protocolAATForwardRequiredCoordinate input f coordinate).2) :
          ProtocolLawCoordinateRing input Y.State)
  violationWitnessVisibleOn : ∀ W coordinate,
    (protocolAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
        W coordinate →
      ForwardObservableVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (protocolAATGeometryReadingContext input X)
        (protocolAATGeometryReadingContext input Y)
        f.lawCoordinateMap
        (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
        (MvPolynomial.X (protocolAATForwardCoordinate input f coordinate) :
          ProtocolLawCoordinateRing input Y.State)
  axisReadableOn : ∀ W axis,
    (protocolAATGeometryCoverageRequirements input X).axisReadableOn W axis →
      ForwardAxisVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (protocolAATGeometryReadingContext input X)
        (protocolAATGeometryReadingContext input Y) _root_.id axis
  boundaryVisibleOn : ∀ W base,
    (protocolAATGeometryCoverageRequirements input X).boundaryVisibleOn W base →
      (protocolAATGeometryCoverageRequirements input Y).boundaryVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx
        ((f.lawContextFunctor).obj ⟨base⟩).ctx

/-- The complete protocol source-role image record is generated from every
primitive edge/observation-preserving morphism. -/
def protocolAATForwardCoverageImage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    ProtocolAATForwardCoverageImage input f where
  requiredSupport _ _ := trivial
  requiredEquationCoordinate _ _ := trivial
  selectedViolationWitness _ _ := trivial
  requiredAxis _ _ := trivial
  supportVisibleOn _ atom := protocolAATForwardSupportVisible input f atom
  equationCoordinateVisibleOn _ coordinate :=
    protocolAATForwardEquationCoordinateCoherent input f coordinate
  violationWitnessVisibleOn _ coordinate :=
    protocolAATForwardViolationCoordinateCoherent input f coordinate
  axisReadableOn _ axis := protocolAATForwardAxisCoherent input f axis
  boundaryVisibleOn _ _ := protocolAATForwardBoundaryVisible input f

/-! ## Generated aggregate image morphisms -/

/-- The generated one-way lens geometry data.  Each field is constructed from
the same primitive operation-preserving morphism. -/
structure LensAATForwardGeometryImage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) where
  equation : EndpointEquationForwardTransport
    (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)
    (lensLawEquationSystem input Y.Carrier Y.toLensData.toLawStructure)
  raw : (lensAATGeometryReadingRawSystem input X).toPresheaf ⟶
    (f.lawContextFunctor).op ⋙
      (lensAATGeometryReadingRawSystem input Y).toPresheaf
  coverage : LensAATForwardCoverageImage input f

/-- Construct the complete forward-image lens record from the named get/put
squares; no additional certificate is an input. -/
noncomputable def lensAATForwardGeometryImage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATForwardGeometryImage input f where
  equation := lensAATEndpointEquationForwardTransport input f
  raw := lensAATGeometryReadingRawForwardHom input f
  coverage := lensAATForwardCoverageImage input f

/-- The generated one-way protocol geometry data for every named edge and
observation operation. -/
structure ProtocolAATForwardGeometryImage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) where
  equation : EndpointEquationForwardTransport
    (protocolLawEquationSystem input X.State X.toLawStructure)
    (protocolLawEquationSystem input Y.State Y.toLawStructure)
  raw : (protocolAATGeometryReadingRawSystem input X).toPresheaf ⟶
    (f.lawContextFunctor).op ⋙
      (protocolAATGeometryReadingRawSystem input Y).toPresheaf
  coverage : ProtocolAATForwardCoverageImage input f

/-- Construct the complete forward-image protocol record from the named
edge/observation squares; no inverse or completion field is accepted. -/
noncomputable def protocolAATForwardGeometryImage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    ProtocolAATForwardGeometryImage input f where
  equation := protocolAATEndpointEquationForwardTransport input f
  raw := protocolAATGeometryReadingRawForwardHom input f
  coverage := protocolAATForwardCoverageImage input f

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
