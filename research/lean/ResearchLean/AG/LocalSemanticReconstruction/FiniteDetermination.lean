import ResearchLean.AG.LocalSemanticReconstruction.TagChangeGroupLaw
import ResearchLean.AG.LocalSemanticReconstruction.FiniteReadingCore
import Formal.Util.AssertStandardAxioms

/-!
# Finite determination for local readings

This file defines separation and extension separately, and defines a
determining set as their conjunction.  It then applies both properties to the
actual tagged source-choice automorphism family.  The third property required
by G-124(D), effectiveness, is not claimed here: it requires separately
supplied finite enumerations and decidable equality.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

/-- The actual automorphisms belonging to the tagged source-choice image. -/
noncomputable def TaggedSourceChoiceAutFamily :
    Set (Aut taggedOperationExplicitExactGeometryObject) :=
  Set.range taggedSourceChoiceAut

/-- Include one source choice in the actual automorphism family. -/
noncomputable def taggedSourceChoiceAutElement
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    TaggedSourceChoiceAutFamily :=
  ⟨taggedSourceChoiceAut choice, ⟨choice, rfl⟩⟩

/-- Pointwise local reading of an actual source-choice automorphism. -/
noncomputable def readTaggedSourceChoiceAutAt
    (automorphism : TaggedSourceChoiceAutFamily)
    (source : ArchitectureObject FiniteModel.carrier) : Bool :=
  readTaggedSourceChoiceExplicitExactGeometry automorphism.1.hom source

/-- Reading the included actual automorphism recovers its source choice. -/
@[simp] theorem readTaggedSourceChoiceAutAt_element
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    readTaggedSourceChoiceAutAt (taggedSourceChoiceAutElement choice) = choice :=
  readTaggedSourceChoiceExplicitExactGeometry_taggedSourceChoice choice

/-- Every finite Bool table extends to an actual source-choice automorphism.
The local coherence predicate is `True` because this family has no edges
relating distinct source indices. -/
theorem taggedSourceChoiceAut_finite_extends
    (S : Finset (ArchitectureObject FiniteModel.carrier)) :
    FiniteReading.Extends readTaggedSourceChoiceAutAt S (fun _ => True) := by
  classical
  intro table _
  let choice : ArchitectureObject FiniteModel.carrier → Bool :=
    fun source => if hsource : source ∈ S then table ⟨source, hsource⟩ else false
  refine ⟨taggedSourceChoiceAutElement choice, ?_⟩
  funext source
  simp [FiniteReading.restrict, choice]

/-- No finite set of point readings separates the actual source-choice
automorphism family on the infinite mandatory-C index type. -/
theorem taggedSourceChoiceAut_finite_not_separates
    (S : Finset (ArchitectureObject FiniteModel.carrier)) :
    ¬ FiniteReading.Separates readTaggedSourceChoiceAutAt S := by
  classical
  obtain ⟨outside, houtside⟩ := Infinite.exists_notMem_finset S
  let choice : ArchitectureObject FiniteModel.carrier → Bool :=
    fun source => if source = outside then true else false
  intro separates
  have htable :
      FiniteReading.restrict readTaggedSourceChoiceAutAt S
          (taggedSourceChoiceAutElement choice) =
        FiniteReading.restrict readTaggedSourceChoiceAutAt S
          (taggedSourceChoiceAutElement (fun _ => false)) := by
    funext source
    have hne : source.1 ≠ outside := by
      intro equality
      subst outside
      exact houtside source.2
    simp [FiniteReading.restrict, choice, hne]
  have helement := separates htable
  have haut : taggedSourceChoiceAut choice =
      taggedSourceChoiceAut (fun _ => false) := congrArg Subtype.val helement
  have hchoice := taggedSourceChoiceAut_injective haut
  have hat := congrFun hchoice outside
  simp [choice] at hat

/-- Consequently no finite set is determining for the actual tagged
source-choice automorphism family, even though every finite table extends. -/
theorem taggedSourceChoiceAut_no_finite_determining :
    ¬ ∃ S : Finset (ArchitectureObject FiniteModel.carrier),
      FiniteReading.Determining readTaggedSourceChoiceAutAt S (fun _ => True) := by
  rintro ⟨S, hS⟩
  exact taggedSourceChoiceAut_finite_not_separates S hS.1

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
