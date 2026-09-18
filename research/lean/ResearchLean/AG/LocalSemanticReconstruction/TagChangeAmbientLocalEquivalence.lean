import ResearchLean.AG.LocalSemanticReconstruction.TagChangeAmbientCategory
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# Finite-local reconstruction of the ambient tagged source-choice subgroup

Cycle 33 retains the full source-choice family faithfully on the actual tagged
admissible package before canonical normalization.  This module identifies
that package-level subgroup with the compatible sections of the actual finite
Bool-table restriction diagram from Cycle 31.  The forward map is verified at
every finite index against tagged-identity-operation readback, and the inverse
is the singleton-assembly constructor followed by the ambient package
automorphism constructor.

## Implementation notes

The local category is reused from Cycle 31 rather than copied.  The global
category deloops only the ambient source-choice subgroup, not every package
endomorphism: finite Bool tables do not read canonical normalization or an
arbitrary `PackageTotalHom`.  Keeping that limitation explicit prevents the
source-choice equivalence from being overstated as the final G-124(B)
equivalence.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct
open AAT.AG.RealizationReconstruction

namespace TagChangeAmbientLocalEquivalence

noncomputable section

open TagChangeAmbientCategory

/-- The actual ambient package-level source-choice subgroup is the group of
compatible all-finite Bool-table sections. -/
noncomputable def subgroupMulEquivCoherentFamily :
    sourceChoiceSubgroup ≃*
      Multiplicative
        (TagChange.CoherentFamily TagChange.TaggedArchitectureIndex) :=
  sourceChoiceGroupEquiv.symm.trans
    TagChange.globalTagChangeMulEquivCoherentFamily

/-- The forward group equivalence is exactly all-finite reading on every
named ambient source choice. -/
@[simp] theorem subgroupMulEquivCoherentFamily_apply
    (choice : Multiplicative TagChangeKaroubiReconstruction.Choice) :
    subgroupMulEquivCoherentFamily (sourceChoiceGroupEquiv choice) =
      Multiplicative.ofAdd (TagChange.read choice.toAdd) := by
  simp [subgroupMulEquivCoherentFamily,
    TagChange.globalTagChangeMulEquivCoherentFamily_apply]

/-- Read one source from an actual ambient package-level subgroup element. -/
noncomputable def readAmbientSourceChoiceAt
    (automorphism : sourceChoiceSubgroup)
    (source : TagChange.TaggedArchitectureIndex) : Bool :=
  readTaggedSourceChoice automorphism.1.hom.hom source

/-- Ambient package readback recovers the global choice classified by the
faithful source-choice group equivalence. -/
theorem readAmbientSourceChoiceAt_eq
    (automorphism : sourceChoiceSubgroup) :
    readAmbientSourceChoiceAt automorphism =
      (sourceChoiceGroupEquiv.symm automorphism).toAdd := by
  let choice := sourceChoiceGroupEquiv.symm automorphism
  have hchoice : sourceChoiceGroupEquiv choice = automorphism :=
    sourceChoiceGroupEquiv.apply_symm_apply automorphism
  calc
    readAmbientSourceChoiceAt automorphism =
        readAmbientSourceChoiceAt (sourceChoiceGroupEquiv choice) := by
      rw [hchoice]
    _ = choice.toAdd := by
      change readTaggedSourceChoice (taggedSourceChoiceTotal choice.toAdd) =
        choice.toAdd
      exact readTaggedSourceChoice_taggedSourceChoiceTotal choice.toAdd
    _ = (sourceChoiceGroupEquiv.symm automorphism).toAdd := rfl

/-- Every finite component is the primitive finite restriction of actual
ambient package readback. -/
theorem subgroupMulEquivCoherentFamily_value
    (automorphism : sourceChoiceSubgroup)
    (S : Finset TagChange.TaggedArchitectureIndex) :
    (subgroupMulEquivCoherentFamily automorphism).toAdd.value S =
      FiniteReading.restrict readAmbientSourceChoiceAt S automorphism := by
  let choice := sourceChoiceGroupEquiv.symm automorphism
  have hchoice : sourceChoiceGroupEquiv choice = automorphism :=
    sourceChoiceGroupEquiv.apply_symm_apply automorphism
  rw [← hchoice]
  rw [subgroupMulEquivCoherentFamily_apply]
  funext source
  change choice.toAdd source.1 =
    readAmbientSourceChoiceAt (sourceChoiceGroupEquiv choice) source.1
  rw [readAmbientSourceChoiceAt_eq]
  simp

/-- The inverse is singleton assembly followed by the actual ambient package
automorphism constructor. -/
@[simp] theorem subgroupMulEquivCoherentFamily_symm
    (family : Multiplicative
      (TagChange.CoherentFamily TagChange.TaggedArchitectureIndex)) :
    subgroupMulEquivCoherentFamily.symm family =
      sourceChoiceGroupEquiv
        (Multiplicative.ofAdd (TagChange.assemble family.toAdd)) := by
  rfl

/-- The ambient package-level subgroup as a one-object global Hom slice. -/
abbrev GlobalCategory := SingleObj sourceChoiceSubgroup

/-- The existing actual finite-local section category from Cycle 31. -/
abbrev LocalCategory := TagChangeLocalModelEquivalence.LocalCategory

/-- Primitive finite-local reading for the ambient package-level subgroup. -/
noncomputable def reading : GlobalCategory ⥤ LocalCategory :=
  SingleObj.mapHom sourceChoiceSubgroup
    TagChangeLocalModelEquivalence.LocalGroup
    subgroupMulEquivCoherentFamily.toMonoidHom

/-- Categorical reading agrees at every finite index with primitive ambient
package readback. -/
theorem reading_map_value {X Y : GlobalCategory} (f : X ⟶ Y)
    (S : TagChangeLocalModelEquivalence.RestrictionIndex) :
    (reading.map f).toAdd.value S =
      FiniteReading.restrict readAmbientSourceChoiceAt S f :=
  subgroupMulEquivCoherentFamily_value f S

/-- Hom reading separates actual ambient package-level source choices. -/
theorem morphismSeparates {X Y : GlobalCategory} :
    Function.Injective
      (reading.map : (X ⟶ Y) → (reading.obj X ⟶ reading.obj Y)) :=
  subgroupMulEquivCoherentFamily.injective

/-- Every compatible finite-local section assembles to an actual ambient
package-level source-choice automorphism. -/
theorem morphismAssembles {X Y : GlobalCategory} :
    Function.Surjective
      (reading.map : (X ⟶ Y) → (reading.obj X ⟶ reading.obj Y)) :=
  subgroupMulEquivCoherentFamily.surjective

/-- Object assembly for this explicitly limited one-object Hom slice. -/
theorem objectAssembles (Z : LocalCategory) :
    ∃ X : GlobalCategory, Nonempty (reading.obj X ≅ Z) := by
  exact ⟨SingleObj.star sourceChoiceSubgroup,
    ⟨eqToIso (Subsingleton.elim _ _)⟩⟩

/-- The actual ambient package-level subgroup is categorically equivalent to
the compatible sections of the finite-local restriction diagram. -/
noncomputable def equivalence : GlobalCategory ≌ LocalCategory :=
  subgroupMulEquivCoherentFamily.toSingleObjEquiv

/-- The categorical equivalence uses primitive reading as its forward
functor. -/
@[simp] theorem equivalence_functor : equivalence.functor = reading :=
  rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence

end


end TagChangeAmbientLocalEquivalence

end AAT.AG.LocalSemanticReconstruction
