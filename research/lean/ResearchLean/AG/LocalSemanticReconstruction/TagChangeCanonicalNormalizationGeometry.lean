import ResearchLean.AG.LocalSemanticReconstruction.TagChangeAmbientCategory
import ResearchLean.AG.RealizationReconstruction.AATClosedRealizationCategory
import Formal.Util.AssertStandardAxioms

/-!
# Canonical tagged normalization on the common exact-geometry surface

The generated tagged category of Cycles 36--38 uses canonical normalization
as an actual package endomorphism.  The common four-family realization fiber,
however, uses `ExplicitExactGeometryHom`.  This module constructs the missing
exact-geometry lift from the existing tagged data.  Coverage, overlap,
coefficient, raw, and explicit realization components are constructed rather
than accepted as a certificate.

This is the global-surface prerequisite for embedding the generated tagged
branch into `FamilyRealization .taggedOperation`.  It does not yet claim that
the generated package submonoid is the full tagged Hom, nor does it construct
the common local-model category or its arbitrary-object assembly.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open AAT.AG.RealizationComparisonIdempotents
open AAT.AG.RealizationReconstruction

namespace TagChangeCanonicalNormalizationGeometry

noncomputable section

/-- Canonical tagged package normalization with all six explicit exact-
geometry components. -/
noncomputable def normalizationExplicitExactGeometryHom :
    ExplicitExactGeometryHom taggedOperationGeometryPackage
      taggedOperationGeometryPackage where
  base := canonicalObjectNormalizationTotal taggedOperationPackage
    taggedOperationPackage_admissible
  coverage :=
    { requiredSupport := fun _ => _root_.id
      requiredEquationCoordinate := fun _ => _root_.id
      selectedViolationWitness := fun _ => _root_.id
      requiredAxis := fun _ => _root_.id
      supportVisibleOn := fun _ _ => _root_.id
      equationCoordinateVisibleOn := fun _ _ => _root_.id
      violationWitnessVisibleOn := fun _ _ => _root_.id
      axisReadableOn := fun _ _ => _root_.id
      boundaryVisibleOn := fun _ _ => _root_.id }
  overlap :=
    { overlapIso := fun _ _ _ => Iso.refl _ }
  coefficientHom := RingHom.id _
  raw := by
    exact RawAmbientRestrictionSystemExactMapAgainst.refl
      taggedOperationGeometryPackage.site
      taggedOperationGeometryPackage.Coefficient
      taggedOperationGeometryPackage.raw
  realization :=
    { contextMorphism := fun morphism => morphism
      contextMorphism_isRestriction := fun _ hypothesis => hypothesis
      supportEquiv := fun _ => Equiv.refl _
      axisEquiv := fun _ => Equiv.refl _
      observableEquiv := fun _ => Equiv.refl _
      supportReads_iff := fun _ _ _ => Iff.rfl
      axisReads_iff := fun _ _ => Iff.rfl
      observableReads_iff := fun _ _ => Iff.rfl
      support_naturality := fun _ _ => rfl
      axis_naturality := fun _ _ => rfl
      observable_naturality := fun _ _ => rfl }

/-- The new exact-geometry morphism has the accepted canonical package
normalization as its base, with no replacement membership premise. -/
@[simp] theorem normalizationExplicitExactGeometryHom_base :
    normalizationExplicitExactGeometryHom.base =
      canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible :=
  rfl

/-- The same constructed normalization is an actual Hom in the tagged fiber
of the common closed-family realization category. -/
noncomputable def closedFamilyTaggedNormalization :
    (FamilyRealization.taggedOperation :
      FamilyRealization (ClosedFamilyParameter.taggedOperation :
        ClosedFamilyParameter.{0, 0})) ⟶ .taggedOperation :=
  ULift.up normalizationExplicitExactGeometryHom

/-- Reading the common Hom back to its package base recovers canonical
normalization exactly. -/
@[simp] theorem closedFamilyTaggedNormalization_base :
    closedFamilyTaggedNormalization.down.base =
      canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible :=
  rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry

end

end TagChangeCanonicalNormalizationGeometry

end AAT.AG.LocalSemanticReconstruction
