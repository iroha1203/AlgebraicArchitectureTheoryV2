import ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm
import Formal.Util.AssertStandardAxioms

/-!
# Canonical tagged rewrite on the common exact-geometry surface

The package-level generated normal form moves canonical normalization past an
arbitrary source choice by first restricting that choice to the normalization
image.  This module proves the same rewrite as an equality of actual Homs in
the common tagged `FamilyRealization` fiber.

The proof compares the dependent realization transports as well as the base,
coefficient, and raw components.  It does not yet construct the exact-geometry
normal-form image or its local reading.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open AAT.AG.RealizationReconstruction

namespace TagChangeCanonicalNormalizationGeometryRewrite

noncomputable section

open TagChangeCanonicalNormalizationGeometry
open TagChangeCanonicalNormalizationGeometryLaws
open TagChangeKaroubiReconstruction
open TagChangeNormalizedChoiceKernel

/-- Canonical normalization moves past an arbitrary source choice in the
common tagged fiber after restricting that choice to the normalization image.
This is the exact-geometry rewrite needed by generated normal forms. -/
theorem closedFamilyTaggedNormalization_comp_sourceChoice_rewrite
    (choice : Choice) :
    closedFamilyTaggedNormalization ≫ closedFamilyTaggedSourceChoice choice =
      closedFamilyTaggedSourceChoice (normalizeChoice choice) ≫
        closedFamilyTaggedNormalization := by
  apply ULift.ext
  change ExplicitExactGeometryHom.comp
      normalizationExplicitExactGeometryHom
      (taggedSourceChoiceExplicitExactGeometryHom choice) =
    ExplicitExactGeometryHom.comp
      (taggedSourceChoiceExplicitExactGeometryHom (normalizeChoice choice))
      normalizationExplicitExactGeometryHom
  have base_rewrite :
      (ExplicitExactGeometryHom.comp
        normalizationExplicitExactGeometryHom
        (taggedSourceChoiceExplicitExactGeometryHom choice)).base =
      (ExplicitExactGeometryHom.comp
        (taggedSourceChoiceExplicitExactGeometryHom (normalizeChoice choice))
        normalizationExplicitExactGeometryHom).base := by
    calc
      _ = (canonicalObjectNormalizationTotal taggedOperationPackage
            taggedOperationPackage_admissible).comp
          (taggedSourceChoiceTotal (normalizeChoice choice)) :=
        normalization_comp_sourceChoice_eq_normalized choice
      _ = _ := taggedSourceChoiceTotal_commutes_normalization
        (normalizeChoice choice) (normalizeChoice_invariant choice)
  apply ExplicitExactGeometryHom.ext
  · exact base_rewrite
  · apply RingHom.ext
    intro coefficient
    rfl
  · apply RawAmbientRestrictionSystemExactMapAgainst.hext
    · rfl
    · apply RingHom.ext
      intro coefficient
      rfl
    · apply heq_of_eq
      funext W
      apply CoordinateFamilyExactEquiv.ext
      · apply Equiv.ext
        intro coordinate
        rfl
      · apply heq_of_eq
        funext coordinate
        apply Equiv.ext
        intro datum
        rfl
    · apply heq_of_eq
      funext W
      apply StructuralRelationFamilyExactEquiv.ext
      apply Equiv.ext
      intro relation
      rfl
  · apply taggedExplicitRealizationSupply_hext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · apply equationSystemExactTransport_hext
      · apply Equiv.ext
        intro atom
        rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · intro W V morphism
      rfl
    · intro W support
      rfl
    · intro W axis
      rfl
    · intro W observable
      rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryRewrite

end

end TagChangeCanonicalNormalizationGeometryRewrite

end AAT.AG.LocalSemanticReconstruction
