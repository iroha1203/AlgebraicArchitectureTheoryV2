import ResearchLean.AG.LocalSemanticReconstruction.TagChangeInverseLimitUniversal
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeMainRecovery
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeMainFlip
import Formal.Util.AssertStandardAxioms

/-! Design IV-4/E1: the actual C₂-indexed source-choice group, its coherent
all-finite-table inverse limit, and the common main reader are identified on
the same arbitrary choice and the same projection values. -/
namespace AAT.AG.LocalSemanticReconstruction.G124MainTheorem
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction

/-- Both group equivalences are complete, and the finite-table image of an
arbitrary actual source choice has precisely the original coherent family
whose assembled native Hom is read by the common N. -/
theorem tag_group_limit_main
    (choice : Multiplicative
      (TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex)) :
    Function.Bijective taggedSourceChoiceGroupEquiv ∧
    Function.Bijective taggedSourceChoiceSubgroupMulEquivCoherentFamily ∧
    taggedSourceChoiceSubgroupMulEquivCoherentFamily
        (taggedSourceChoiceGroupEquiv choice) =
      Multiplicative.ofAdd (TagChange.read choice.toAdd) ∧
    TagChangeMainRecovery.J (TagChange.read choice.toAdd) =
      (reading (.geometry FiniteModel.carrier
        IndependentGeometryHomPrimitive.Mode.explicit)).map
        (taggedSourceChoiceNativeHom choice.toAdd) := by
  exact ⟨taggedSourceChoiceGroupEquiv.bijective,
    taggedSourceChoiceSubgroupMulEquivCoherentFamily.bijective,
    taggedSourceChoiceSubgroupMulEquivCoherentFamily_apply choice,
    by simpa only [TagChange.assemble_read] using
      TagChangeMainRecovery.J_eq_read_assembled (TagChange.read choice.toAdd)⟩

/-- Every compatible finite group projection lifts to the actual source-
choice subgroup with exactly those finite values, and those values uniquely
determine that very lift. -/
theorem tag_limit_projection_and_unique
    {G : Type*} [Group G]
    (projections : TagChangeInverseLimitUniversal.Projections G) :
    (∀ (g : G) (S : Finset TagChange.TaggedArchitectureIndex),
      (taggedSourceChoiceSubgroupMulEquivCoherentFamily
        (TagChangeInverseLimitUniversal.lift projections g)).toAdd.value S =
        (projections.map S g).toAdd) ∧
    (∀ other : G →* taggedSourceChoiceAutSubgroup,
      (∀ g S,
        (taggedSourceChoiceSubgroupMulEquivCoherentFamily (other g)).toAdd.value S =
          (projections.map S g).toAdd) →
        other = TagChangeInverseLimitUniversal.lift projections) := by
  exact ⟨TagChangeInverseLimitUniversal.lift_value projections,
    fun other h => TagChangeInverseLimitUniversal.lift_unique projections other h⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124MainTheorem

end AAT.AG.LocalSemanticReconstruction.G124MainTheorem
