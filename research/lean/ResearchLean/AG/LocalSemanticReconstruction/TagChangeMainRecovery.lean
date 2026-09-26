import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReconstruction
import Formal.Util.AssertStandardAxioms

/-! The raw tagged coherent family in the common local Hom reconstruction. -/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory RealizationReconstruction
open IndependentAATPrimitiveReconstruction

namespace TagChangeMainRecovery

private abbrev TagParameter : Parameter.{0, 0} :=
  .geometry FiniteModel.carrier IndependentGeometryHomPrimitive.Mode.explicit

/-- The accepted raw tagged section is mapped into the same main local Hom. -/
noncomputable def J (family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex) :
    (reading TagParameter).obj taggedNativeObject ⟶
      (reading TagParameter).obj taggedNativeObject :=
  taggedLocalComparison.map
    (X := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
    (Y := SingleObj.star TagChangeGeneratedLocalModel.LocalSection)
    ⟨false, family⟩

/-- The raw finite section recovers precisely the source-choice native Hom
assembled from its singleton tables. -/
theorem J_eq_read_assembled
    (family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex) :
    J family = (reading TagParameter).map
      (taggedSourceChoiceNativeHom (TagChange.assemble family)) := by
  let form : TagChangeGeneratedNormalForm.NormalForm :=
    .raw (TagChange.assemble family)
  have hread : TagChangeGeneratedLocalModel.read form =
      (⟨false, family⟩ : TagChangeGeneratedLocalModel.LocalSection) := by
    simp [form, TagChangeGeneratedLocalModel.read]
  change taggedLocalComparison.map
      (⟨false, family⟩ : TagChangeGeneratedLocalModel.LocalSection) = _
  rw [← hread]
  change (reading TagParameter).map
      (taggedRepresentedInclusion.map
        (TagChangeExactGeometryLocalModel.equivalence.inverse.map
          (TagChangeGeneratedLocalModel.read form))) = _
  rw [taggedInverse_read_normalForm form]
  rfl

/-- The main B Hom inverse of the same local section is the actual arbitrary
source-choice morphism, with no second tagged assembler. -/
theorem assembleHom_J
    (family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex) :
    assembleHom TagParameter (J family) =
      taggedSourceChoiceNativeHom (TagChange.assemble family) := by
  rw [J_eq_read_assembled]
  exact assembleHom_read TagParameter _

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeMainRecovery

end TagChangeMainRecovery

end AAT.AG.LocalSemanticReconstruction
