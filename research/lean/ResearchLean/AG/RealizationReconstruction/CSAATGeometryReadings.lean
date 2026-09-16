import ResearchLean.AG.RealizationReconstruction.CSAATGeometryScaffolds
import Formal.AG.Site.Topology
import Formal.Util.AssertStandardAxioms

/-!
# CS-derived geometry readings and admissible endpoint covers

This module replaces the marker-only visibility predicates of the Cycle 130
scaffold by readings derived from the actual lens and protocol data.  Support
is the exact n1015 (A1) source.  Axes are the actual AAT atoms.  Observables are the
actual Law polynomial rings, and a readable observable is exactly a named
polynomial variable.

The singleton identity family is proved to cover every source atom, signature
axis, required equation coordinate, and violation coordinate.  This is an
endpoint cover: nontrivial localizations, ReadingCore provenance, quotient
identification, and geometry morphism/readback remain later obligations.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-! ## Shared restriction fact -/

/-- Identity on a concrete reading context is a selected restriction. -/
theorem identityContextMorphism_isRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (W : Site.ArchCtx A) :
    (Site.identityContextMorphism W).IsRestriction :=
  ⟨fun h => h, fun h => h, fun h => h,
    fun h => W.supportReads_objectFamily h⟩

/-! ## Lens reading -/

/-- The signature retains each lens atom as both axis and its exact coordinate. -/
def lensAATGeometrySignature (input : LensFamilyInput.{u}) :
    ArchitectureSignature (lensAATCarrier input) where
  Axis := LensAATAtom input
  Coordinate _ := LensAATAtom input
  selected _ := True
  coordinate _ axis := axis

/-- The lens context reads the actual A1 source, actual atom axes, actual Law
polynomial variables, and the original raw get/put structure. -/
def lensAATGeometryReadingContext (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    Site.ArchCtx (lensLawObject input X.Carrier X.toLensData.toLawStructure) where
  minimal := {
    Support := LensAATSource X
    Axis := LensAATAtom input
    Observable := LensLawCoordinateRing input X.Carrier
    supportReads := fun source atom =>
      lensAATExtracts source atom
    supportReads_objectFamily := fun {_ atom} _ =>
      typedRoleConfiguration_mem _ atom
    axisReads := fun axis =>
      (lensLawObject input X.Carrier
        X.toLensData.toLawStructure).configuration.family.mem axis
    observableReads := fun polynomial =>
      ∃ coordinate :
          (lensLawEquationSystem input X.Carrier
            X.toLensData.toLawStructure).Coordinate,
        polynomial = MvPolynomial.X coordinate }
  Extension := ULift.{u + 1, u} (LensLawStructure input.View X.Carrier)
  extension := ULift.up X.toLensData.toLawStructure

/-- Coverage requirements expose exact A1 support, exact polynomial variables,
and exact atom axes through restrictions into the canonical lens context. -/
def lensAATGeometryCoverageRequirements (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    Site.CoverageRequirements
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)
      (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)
      (lensAATGeometrySignature input) where
  requiredSupport _ := True
  requiredEquationCoordinate _ := True
  selectedViolationWitness _ := True
  requiredAxis axis := (lensAATGeometrySignature input).selected axis
  supportVisibleOn W atom := ∃ support, W.minimal.supportReads support atom
  equationCoordinateVisibleOn W coordinate :=
    ∃ f : Site.ContextMorphism W (lensAATGeometryReadingContext input X),
      f.IsRestriction ∧ W.minimal.observableReads
        (f.observableRestrict
          (MvPolynomial.X (coordinate.1.1, coordinate.2) :
            LensLawCoordinateRing input X.Carrier))
  violationWitnessVisibleOn W coordinate :=
    ∃ f : Site.ContextMorphism W (lensAATGeometryReadingContext input X),
      f.IsRestriction ∧ W.minimal.observableReads
        (f.observableRestrict
          (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier))
  axisReadableOn W axis :=
    ∃ f : Site.ContextMorphism W (lensAATGeometryReadingContext input X),
      f.IsRestriction ∧ ∃ localAxis,
        W.minimal.axisReads localAxis ∧
          f.axisMap localAxis = (show LensAATAtom input from axis)
  boundaryVisibleOn W base :=
    (Site.contextMorphismPreorderCategory
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)).Hom W base

/-- The lens AAT site with concrete CS-derived readings. -/
noncomputable def lensAATGeometryReadingSite (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    Site.AATSite (lensLawObject input X.Carrier X.toLensData.toLawStructure) where
  contextPreorder := Site.contextMorphismPreorderCategory _
  equationSystem := lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure
  signature := lensAATGeometrySignature input
  requirements := lensAATGeometryCoverageRequirements input X
  overlap := completeLawOverlap _

/-- The singleton identity patch is an admissible cover of the lens context. -/
noncomputable def lensAATGeometryReadingCover (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    Site.AATCoverageFamily
      (lensAATGeometryCoverageRequirements input X)
      (completeLawOverlap _)
      (Site.ContextCategoryObject.of
        (Site.contextMorphismPreorderCategory _)
        (lensAATGeometryReadingContext input X)) where
  Index := PUnit
  patch _ := lensAATGeometryReadingContext input X
  inclusion _ := (Site.contextMorphismPreorderCategory _).refl _
  admissible := {
    atomSupportCoverage := by
      intro atom _
      exact ⟨PUnit.unit, (.point : LensAATSource X),
        lensAATExtracts_point (X := X) atom⟩
    equationCoordinateCoverage := by
      intro coordinate _
      left
      exact ⟨PUnit.unit, Site.identityContextMorphism _,
        identityContextMorphism_isRestriction _,
        (coordinate.1.1, coordinate.2), rfl⟩
    violationWitnessCoverage := by
      intro coordinate _
      left
      exact ⟨PUnit.unit, Site.identityContextMorphism _,
        identityContextMorphism_isRestriction _, coordinate, rfl⟩
    signatureAxisCoverage := by
      intro axis _
      exact ⟨PUnit.unit, Site.identityContextMorphism _,
        identityContextMorphism_isRestriction _, axis,
        typedRoleConfiguration_mem (U := lensAATCarrier input) (.point)
          (show LensAATAtom input from axis), rfl⟩
    boundaryCoverage := by
      intro _ _
      exact (completeLawOverlap _).base
        ((Site.contextMorphismPreorderCategory _).refl _)
        ((Site.contextMorphismPreorderCategory _).refl _)
    nonGeneration := by
      intro i
      exact Site.ContextMorphism.nonGenerating_of_restriction
        ((Site.contextMorphismPreorderCategory _).morphism_isRestriction
          ((Site.contextMorphismPreorderCategory _).refl _)) }

/-! ## Protocol reading -/

/-- The signature retains each protocol atom as both axis and exact coordinate. -/
def protocolAATGeometrySignature (input : ProtocolFamilyInput.{u}) :
    ArchitectureSignature (protocolAATCarrier input) where
  Axis := ProtocolAATAtom input
  Coordinate _ := ProtocolAATAtom input
  selected _ := True
  coordinate _ axis := axis

/-- The protocol context reads the actual A1 source, actual atom axes, actual
Law polynomial variables, and the original edge-action/observation structure. -/
def protocolAATGeometryReadingContext (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    Site.ArchCtx (protocolLawObject input X.State X.toLawStructure) where
  minimal := {
    Support := ProtocolAATSource X
    Axis := ProtocolAATAtom input
    Observable := ProtocolLawCoordinateRing input X.State
    supportReads := fun source atom =>
      protocolAATExtracts source atom
    supportReads_objectFamily := fun {_ atom} _ =>
      typedRoleConfiguration_mem _ atom
    axisReads := fun axis =>
      (protocolLawObject input X.State
        X.toLawStructure).configuration.family.mem axis
    observableReads := fun polynomial =>
      ∃ coordinate :
          (protocolLawEquationSystem input X.State X.toLawStructure).Coordinate,
        polynomial = MvPolynomial.X coordinate }
  Extension := ULift.{u + 1, u} (ProtocolLawStructure input X.State)
  extension := ULift.up X.toLawStructure

/-- Coverage requirements expose exact A1 support, exact polynomial variables,
and exact atom axes through restrictions into the canonical protocol context. -/
def protocolAATGeometryCoverageRequirements (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    Site.CoverageRequirements
      (protocolLawObject input X.State X.toLawStructure)
      (protocolLawEquationSystem input X.State X.toLawStructure)
      (protocolAATGeometrySignature input) where
  requiredSupport _ := True
  requiredEquationCoordinate _ := True
  selectedViolationWitness _ := True
  requiredAxis axis := (protocolAATGeometrySignature input).selected axis
  supportVisibleOn W atom := ∃ support, W.minimal.supportReads support atom
  equationCoordinateVisibleOn W coordinate :=
    ∃ f : Site.ContextMorphism W (protocolAATGeometryReadingContext input X),
      f.IsRestriction ∧ W.minimal.observableReads
        (f.observableRestrict
          (MvPolynomial.X (coordinate.1.1, coordinate.2) :
            ProtocolLawCoordinateRing input X.State))
  violationWitnessVisibleOn W coordinate :=
    ∃ f : Site.ContextMorphism W (protocolAATGeometryReadingContext input X),
      f.IsRestriction ∧ W.minimal.observableReads
        (f.observableRestrict
          (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State))
  axisReadableOn W axis :=
    ∃ f : Site.ContextMorphism W (protocolAATGeometryReadingContext input X),
      f.IsRestriction ∧ ∃ localAxis,
        W.minimal.axisReads localAxis ∧
          f.axisMap localAxis = (show ProtocolAATAtom input from axis)
  boundaryVisibleOn W base :=
    (Site.contextMorphismPreorderCategory
      (protocolLawObject input X.State X.toLawStructure)).Hom W base

/-- The protocol AAT site with concrete CS-derived readings. -/
noncomputable def protocolAATGeometryReadingSite
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    Site.AATSite (protocolLawObject input X.State X.toLawStructure) where
  contextPreorder := Site.contextMorphismPreorderCategory _
  equationSystem := protocolLawEquationSystem input X.State X.toLawStructure
  signature := protocolAATGeometrySignature input
  requirements := protocolAATGeometryCoverageRequirements input X
  overlap := completeLawOverlap _

/-- The singleton identity patch is an admissible cover of the protocol context. -/
noncomputable def protocolAATGeometryReadingCover
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    Site.AATCoverageFamily
      (protocolAATGeometryCoverageRequirements input X)
      (completeLawOverlap _)
      (Site.ContextCategoryObject.of
        (Site.contextMorphismPreorderCategory _)
        (protocolAATGeometryReadingContext input X)) where
  Index := PUnit
  patch _ := protocolAATGeometryReadingContext input X
  inclusion _ := (Site.contextMorphismPreorderCategory _).refl _
  admissible := {
    atomSupportCoverage := by
      intro atom _
      exact ⟨PUnit.unit, (.point : ProtocolAATSource X),
        protocolAATExtracts_point (X := X) atom⟩
    equationCoordinateCoverage := by
      intro coordinate _
      left
      exact ⟨PUnit.unit, Site.identityContextMorphism _,
        identityContextMorphism_isRestriction _,
        (coordinate.1.1, coordinate.2), rfl⟩
    violationWitnessCoverage := by
      intro coordinate _
      left
      exact ⟨PUnit.unit, Site.identityContextMorphism _,
        identityContextMorphism_isRestriction _, coordinate, rfl⟩
    signatureAxisCoverage := by
      intro axis _
      exact ⟨PUnit.unit, Site.identityContextMorphism _,
        identityContextMorphism_isRestriction _, axis,
        typedRoleConfiguration_mem (U := protocolAATCarrier input) (.point)
          (show ProtocolAATAtom input from axis), rfl⟩
    boundaryCoverage := by
      intro _ _
      exact (completeLawOverlap _).base
        ((Site.contextMorphismPreorderCategory _).refl _)
        ((Site.contextMorphismPreorderCategory _).refl _)
    nonGeneration := by
      intro i
      exact Site.ContextMorphism.nonGenerating_of_restriction
        ((Site.contextMorphismPreorderCategory _).morphism_isRestriction
          ((Site.contextMorphismPreorderCategory _).refl _)) }

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
