import ResearchLean.AG.LocalSemanticReconstruction.G124PrimitiveNormalization
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryRewrite
import Formal.Util.AssertStandardAxioms

/-! The fixed tagged explicit normalization under the one primitive reader. -/

namespace AAT.AG.LocalSemanticReconstruction.G124TaggedNormalization

open CategoryTheory IndependentAATPrimitiveReconstruction
open TagChangeCanonicalNormalizationGeometryRewrite
open TagChangeNormalizedChoiceKernel
open IndependentGeometryHomPrimitive

/-- The main explicit reader's value on the existing tagged normalization
Hom, as an actual local idempotent. -/
noncomputable def taggedLocalProjector :
    (reading (Parameter.geometry FiniteModel.carrier Mode.explicit :
      Parameter.{0, 0})).obj taggedNativeObject ⟶
    (reading (Parameter.geometry FiniteModel.carrier Mode.explicit :
      Parameter.{0, 0})).obj taggedNativeObject :=
  (reading (Parameter.geometry FiniteModel.carrier Mode.explicit :
    Parameter.{0, 0})).map taggedNormalizationNativeHom

@[simp] theorem taggedLocalProjector_idem :
    taggedLocalProjector ≫ taggedLocalProjector = taggedLocalProjector := by
  unfold taggedLocalProjector
  rw [← Functor.map_comp, taggedNormalizationNativeHom_idempotent]

/-- Every retained explicit primitive point, including raw and actual
context-action points, is the existing tagged normalization evaluation. -/
theorem taggedLocalProjector_point
    (query : Query.{0, 0} FiniteModel.carrier Mode.explicit) :
    InvariantWitness.point _ _ taggedLocalProjector.down.val query =
      NativeReader.readExplicit
        TagChangeCanonicalNormalizationGeometry.normalizationExplicitExactGeometryHom
          query :=
  taggedNormalization_read_point query

/-- The accepted generated normal-form rewrite also holds after the tagged
normalization and every source-choice generator are read by the main N. -/
theorem taggedLocalProjector_generation
    (choice : TagChangeKaroubiReconstruction.Choice) :
    taggedLocalProjector ≫
        (reading (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})).map (taggedSourceChoiceNativeHom choice) =
      (reading (Parameter.geometry FiniteModel.carrier Mode.explicit :
          Parameter.{0, 0})).map
          (taggedSourceChoiceNativeHom (normalizeChoice choice)) ≫
        taggedLocalProjector := by
  unfold taggedLocalProjector
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ULift.ext
  exact congrArg ULift.down
    (closedFamilyTaggedNormalization_comp_sourceChoice_rewrite choice)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124TaggedNormalization

end AAT.AG.LocalSemanticReconstruction.G124TaggedNormalization
