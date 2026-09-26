import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReconstruction
import Formal.Util.AssertStandardAxioms

/-! The raw tagged coherent family in the common local Hom reconstruction.

Implementation notes: `J` uses the accepted comparison map on the raw local
section. Its recovery lemmas identify this map with the existing native
source-choice morphism through the main reading and its inverse. -/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory RealizationReconstruction
open IndependentAATPrimitiveReconstruction

namespace TagChangeMainRecovery

/-- The fixed finite-carrier explicit-geometry parameter of the main reading. -/
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

/-- Distinct coherent finite families remain distinct after mapping into the
same main local Hom: its B inverse recovers the actual source-choice map. -/
theorem J_injective : Function.Injective J := by
  intro first second equality
  have hnative := congrArg (assembleHom TagParameter) equality
  rw [assembleHom_J, assembleHom_J] at hnative
  have hchoice := taggedSourceChoiceNativeHom_injective hnative
  have hfamily := congrArg TagChange.read hchoice
  simpa only [TagChange.read_assemble] using hfamily

/-- Every finite source selection misses a distinct actual member of the
same local section map. Its unseen bit is supplied by the existing
outside-point source-choice witness. -/
theorem finite_J_not_separating
    (S : Finset TagChange.TaggedArchitectureIndex) :
    ∃ family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex,
      J family ≠ J (TagChange.read (fun _ => false)) ∧
        ∀ source ∈ S, TagChange.assemble family source = false := by
  obtain ⟨choice, hchoice, hagree⟩ :=
    TagChange.taggedSourceChoice_finite_reading_not_separating S
  refine ⟨TagChange.read choice, ?_, ?_⟩
  · intro equality
    apply hchoice
    have hfamily := J_injective equality
    have hassembled := congrArg TagChange.assemble hfamily
    simpa only [TagChange.assemble_read] using hassembled
  · intro source hsource
    simpa only [TagChange.assemble_read] using hagree source hsource

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeMainRecovery

end TagChangeMainRecovery

end AAT.AG.LocalSemanticReconstruction
