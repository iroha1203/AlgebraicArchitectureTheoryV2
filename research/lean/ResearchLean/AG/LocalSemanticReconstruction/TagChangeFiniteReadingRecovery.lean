import ResearchLean.AG.LocalSemanticReconstruction.FiniteEffectiveness
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Actual source-choice recovery from all finite readings

This module connects G-124(E1b)'s coherent family of all finite Bool tables to
the actual tagged source-choice automorphism image.  The forward map is actual
source-choice readback, the inverse is the accepted source-choice
automorphism constructor, and every finite component is expressed through the
common `FiniteReading.restrict` surface.

The local-model category and main equivalence required by G-124(B) have not
yet been constructed.  Consequently the uniqueness theorem below is the
criterion that a future B-level recovery must satisfy; it is not presented as
the B equivalence itself.  Likewise this file does not promote the existing
type equivalence to the group-level inverse-limit isomorphism.

Implementation notes:

* Using the full automorphism type was rejected because finite Bool readback
  classifies only the accepted tagged source-choice image.
* Choosing an arbitrary witness from the image was rejected.  The inverse is
  the named `taggedSourceChoiceAutElement` constructor, so its provenance and
  readback theorem remain visible.
* The finite effectiveness program takes a raw table and uses explicit
  decidable membership.  Its global Bool extension is a computable definition;
  the separate final inclusion into the proof-carrying categorical
  automorphism is noncomputable.  Neither route accepts a coherence proof or a
  completed extension as input.
-/

namespace AAT.AG.LocalSemanticReconstruction

open AAT.AG.RealizationReconstruction

/-- Actual tagged source-choice automorphisms are exactly their global Bool
readbacks.  The inverse is the accepted actual automorphism constructor. -/
noncomputable def taggedSourceChoiceAutEquivGlobalTagChange :
    TaggedSourceChoiceAutFamily ≃
      TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex where
  toFun := readTaggedSourceChoiceAutAt
  invFun := taggedSourceChoiceAutElement
  left_inv automorphism := by
    rcases automorphism with ⟨_, ⟨choice, rfl⟩⟩
    apply Subtype.ext
    change taggedSourceChoiceAut
        (readTaggedSourceChoiceAutAt (taggedSourceChoiceAutElement choice)) =
      taggedSourceChoiceAut choice
    rw [readTaggedSourceChoiceAutAt_element]
  right_inv choice := readTaggedSourceChoiceAutAt_element choice

/-- The actual automorphism image is reconstructed by the coherent family of
all finite source-choice readings. -/
noncomputable def taggedSourceChoiceAutEquivCoherentFamily :
    TaggedSourceChoiceAutFamily ≃
      TagChange.CoherentFamily TagChange.TaggedArchitectureIndex :=
  taggedSourceChoiceAutEquivGlobalTagChange.trans
    TagChange.taggedSourceChoiceEquivCoherentFamily

/-- The component at every finite set is exactly the common finite-reading
restriction of the actual automorphism readback. -/
@[simp] theorem taggedSourceChoiceAutEquivCoherentFamily_value
    (automorphism : TaggedSourceChoiceAutFamily)
    (S : Finset TagChange.TaggedArchitectureIndex) :
    (taggedSourceChoiceAutEquivCoherentFamily automorphism).value S =
      FiniteReading.restrict readTaggedSourceChoiceAutAt S automorphism := by
  rfl

/-- Recovery from a coherent family uses the accepted actual source-choice
automorphism constructor applied to singleton assembly. -/
@[simp] theorem taggedSourceChoiceAutEquivCoherentFamily_symm
    (family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex) :
    taggedSourceChoiceAutEquivCoherentFamily.symm family =
      taggedSourceChoiceAutElement (TagChange.assemble family) := by
  rfl

/-- Any future recovery equivalence with the same actual finite-readback law
is forced to be the E1b source-choice recovery constructed here. -/
theorem taggedSourceChoiceRecovery_unique
    (recovery : TaggedSourceChoiceAutFamily ≃
      TagChange.CoherentFamily TagChange.TaggedArchitectureIndex)
    (hread : ∀ automorphism S,
      (recovery automorphism).value S =
        FiniteReading.restrict readTaggedSourceChoiceAutAt S automorphism) :
    recovery = taggedSourceChoiceAutEquivCoherentFamily := by
  apply Equiv.ext
  intro automorphism
  apply TagChange.CoherentFamily.ext
  intro S
  rw [hread]
  exact (taggedSourceChoiceAutEquivCoherentFamily_value automorphism S).symm

/-- Pointwise reading of a global Bool source choice. -/
def readGlobalTagChangeAt
    (change : TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex)
    (source : TagChange.TaggedArchitectureIndex) : Bool :=
  change source

/-- The computable raw-table extension for a finite source-choice reading. -/
def extendGlobalTagChange
    [DecidableEq TagChange.TaggedArchitectureIndex]
    (S : Finset TagChange.TaggedArchitectureIndex)
    (table : {source // source ∈ S} → Bool) :
    TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex :=
  fun source => if hsource : source ∈ S then table ⟨source, hsource⟩ else false

/-- The executable effectiveness core for finite Bool source-choice tables. -/
def globalTagChangeEffectivenessProgram
    [DecidableEq TagChange.TaggedArchitectureIndex]
    (S : Finset TagChange.TaggedArchitectureIndex) :
    FiniteReading.EffectivenessProgram
      readGlobalTagChangeAt S (fun _ => True) where
  coherenceTest _ := true
  coherenceTest_eq_true_iff _ := by simp
  extend? table := some (extendGlobalTagChange S table)
  extend_eq_none_iff _ := by simp
  restrict_eq_of_extend_eq_some table change success := by
    injection success with equality
    subst change
    funext source
    simp [extendGlobalTagChange, FiniteReading.restrict, readGlobalTagChangeAt]

/-- Every finite global source-choice reading has an executable common
effectiveness program. -/
theorem globalTagChange_finite_effective
    [DecidableEq TagChange.TaggedArchitectureIndex]
    (S : Finset TagChange.TaggedArchitectureIndex) :
    FiniteReading.Effective readGlobalTagChangeAt S (fun _ => True) :=
  ⟨globalTagChangeEffectivenessProgram S⟩

/-- Extend a raw finite Bool table by `false` outside its finite index set and
include the resulting global choice in the actual automorphism image. -/
noncomputable def extendTaggedSourceChoiceAut
    [DecidableEq TagChange.TaggedArchitectureIndex]
    (S : Finset TagChange.TaggedArchitectureIndex)
    (table : {source // source ∈ S} → Bool) :
    TaggedSourceChoiceAutFamily :=
  taggedSourceChoiceAutElement (extendGlobalTagChange S table)

/-- Every finite source-choice reading has a common effectiveness program.
Its independently fixed coherence predicate is `True`, and its extension is
the explicit global computation followed by categorical inclusion. -/
noncomputable def taggedSourceChoiceAutEffectivenessProgram
    [DecidableEq TagChange.TaggedArchitectureIndex]
    (S : Finset TagChange.TaggedArchitectureIndex) :
    FiniteReading.EffectivenessProgram
      readTaggedSourceChoiceAutAt S (fun _ => True) where
  coherenceTest _ := true
  coherenceTest_eq_true_iff _ := by simp
  extend? table := some (extendTaggedSourceChoiceAut S table)
  extend_eq_none_iff _ := by simp
  restrict_eq_of_extend_eq_some table automorphism success := by
    injection success with equality
    subst automorphism
    funext source
    simp [extendTaggedSourceChoiceAut, extendGlobalTagChange,
      FiniteReading.restrict]

/-- The actual source-choice family realizes the common effectiveness
property on every finite reading. -/
theorem taggedSourceChoiceAut_finite_effective
    [DecidableEq TagChange.TaggedArchitectureIndex]
    (S : Finset TagChange.TaggedArchitectureIndex) :
    FiniteReading.Effective
      readTaggedSourceChoiceAutAt S (fun _ => True) :=
  ⟨taggedSourceChoiceAutEffectivenessProgram S⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
