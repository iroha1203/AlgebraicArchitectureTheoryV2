import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Ring.BooleanRing
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReadingRecovery
import Formal.Util.AssertStandardAxioms

/-!
# Group-level reconstruction of tagged source choices

The coherent-family presentation of all finite Bool readings carries the
pointwise xor group law.  This module upgrades the E1b read/assemble
equivalence to an additive equivalence, converts it to multiplicative form,
and composes it with the accepted E1a equivalence onto the actual tagged
source-choice automorphism subgroup.

This is a group isomorphism with the coherent-family inverse-limit
presentation.  It is not a categorical limit construction and it is not the
still-unconstructed G-124(B) local-model equivalence.
-/

namespace AAT.AG.LocalSemanticReconstruction

open AAT.AG.RealizationReconstruction

namespace TagChange.CoherentFamily

variable {Ω : Type*}

/-- The neutral coherent family is pointwise the false Bool value. -/
instance : Zero (TagChange.CoherentFamily Ω) where
  zero :=
    { value := fun _ _ => 0
      coherent := by intros; rfl }

/-- Addition of coherent families is pointwise Bool xor. -/
instance : Add (TagChange.CoherentFamily Ω) where
  add left right :=
    { value := fun S x => left.value S x + right.value S x
      coherent := by
        intro S T h
        funext x
        have hleft := congrFun (left.coherent S T h) x
        have hright := congrFun (right.coherent S T h) x
        exact congrArg₂ (· + ·) hleft hright }

/-- Negation of a coherent family is pointwise Bool negation in the xor group. -/
instance : Neg (TagChange.CoherentFamily Ω) where
  neg family :=
    { value := fun S x => -family.value S x
      coherent := by
        intro S T h
        funext x
        exact congrArg Neg.neg (congrFun (family.coherent S T h) x) }

/-- Subtraction of coherent families is pointwise subtraction in the Bool xor group. -/
instance : Sub (TagChange.CoherentFamily Ω) where
  sub left right :=
    { value := fun S x => left.value S x - right.value S x
      coherent := by
        intro S T h
        funext x
        exact congrArg₂ (· - ·)
          (congrFun (left.coherent S T h) x)
          (congrFun (right.coherent S T h) x) }

/-- Natural scalar multiplication of coherent families is pointwise. -/
instance : SMul ℕ (TagChange.CoherentFamily Ω) where
  smul n family :=
    { value := fun S x => n • family.value S x
      coherent := by
        intro S T h
        funext x
        exact congrArg (n • ·) (congrFun (family.coherent S T h) x) }

/-- Integer scalar multiplication of coherent families is pointwise. -/
instance : SMul ℤ (TagChange.CoherentFamily Ω) where
  smul n family :=
    { value := fun S x => n • family.value S x
      coherent := by
        intro S T h
        funext x
        exact congrArg (n • ·) (congrFun (family.coherent S T h) x) }

/-- Coherent finite Bool families form the pointwise xor additive group. -/
instance : AddCommGroup (TagChange.CoherentFamily Ω) :=
  Function.Injective.addCommGroup
    (fun family : TagChange.CoherentFamily Ω => family.value)
    (fun _ _ equality => TagChange.CoherentFamily.ext (congrFun equality))
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- Simplify the value of the neutral family to the pointwise Bool normal form. -/
@[simp] theorem value_zero (S : Finset Ω) :
    (0 : TagChange.CoherentFamily Ω).value S = 0 :=
  rfl

/-- Simplify family addition to pointwise Bool xor on each finite table. -/
@[simp] theorem value_add (left right : TagChange.CoherentFamily Ω)
    (S : Finset Ω) :
    (left + right).value S = left.value S + right.value S :=
  rfl

/-- Simplify family negation to pointwise Bool negation on each finite table. -/
@[simp] theorem value_neg (family : TagChange.CoherentFamily Ω)
    (S : Finset Ω) :
    (-family).value S = -family.value S :=
  rfl

/-- Simplify family subtraction to pointwise subtraction on each finite table. -/
@[simp] theorem value_sub (left right : TagChange.CoherentFamily Ω)
    (S : Finset Ω) :
    (left - right).value S = left.value S - right.value S :=
  rfl

/-- Simplify natural scalar multiplication to its pointwise finite-table form. -/
@[simp] theorem value_nsmul (n : ℕ) (family : TagChange.CoherentFamily Ω)
    (S : Finset Ω) :
    (n • family).value S = n • family.value S :=
  rfl

/-- Simplify integer scalar multiplication to its pointwise finite-table form. -/
@[simp] theorem value_zsmul (n : ℤ) (family : TagChange.CoherentFamily Ω)
    (S : Finset Ω) :
    (n • family).value S = n • family.value S :=
  rfl

end TagChange.CoherentFamily

namespace TagChange

variable {Ω : Type*}

/-- Global Bool choices and coherent all-finite readings are additively
equivalent for their pointwise xor laws. -/
noncomputable def globalTagChangeAddEquivCoherentFamily :
    GlobalTagChange Ω ≃+ CoherentFamily Ω where
  toEquiv := globalTagChangeEquivCoherentFamily
  map_add' _ _ := rfl

/-- The forward additive equivalence is exactly all-finite reading. -/
@[simp] theorem globalTagChangeAddEquivCoherentFamily_apply
    (change : GlobalTagChange Ω) :
    globalTagChangeAddEquivCoherentFamily change = read change :=
  rfl

/-- The inverse additive equivalence is exactly singleton assembly. -/
@[simp] theorem globalTagChangeAddEquivCoherentFamily_symm_apply
    (family : CoherentFamily Ω) :
    globalTagChangeAddEquivCoherentFamily.symm family = assemble family :=
  rfl

/-- Multiplicative form of the group-level E1b equivalence. -/
noncomputable def globalTagChangeMulEquivCoherentFamily :
    Multiplicative (GlobalTagChange Ω) ≃*
      Multiplicative (CoherentFamily Ω) :=
  globalTagChangeAddEquivCoherentFamily.toMultiplicative

/-- The forward multiplicative equivalence is all-finite reading under type tags. -/
@[simp] theorem globalTagChangeMulEquivCoherentFamily_apply
    (change : Multiplicative (GlobalTagChange Ω)) :
    globalTagChangeMulEquivCoherentFamily change =
      Multiplicative.ofAdd (read change.toAdd) :=
  rfl

/-- The inverse multiplicative equivalence is singleton assembly under type tags. -/
@[simp] theorem globalTagChangeMulEquivCoherentFamily_symm_apply
    (family : Multiplicative (CoherentFamily Ω)) :
    globalTagChangeMulEquivCoherentFamily.symm family =
      Multiplicative.ofAdd (assemble family.toAdd) :=
  rfl

end TagChange

/-- The accepted actual source-choice automorphism subgroup is the group of
coherent families of all finite Bool readings. -/
noncomputable def taggedSourceChoiceSubgroupMulEquivCoherentFamily :
    taggedSourceChoiceAutSubgroup ≃*
      Multiplicative
        (TagChange.CoherentFamily TagChange.TaggedArchitectureIndex) :=
  taggedSourceChoiceGroupEquiv.symm.trans
    TagChange.globalTagChangeMulEquivCoherentFamily

/-- The group-level equivalence agrees with finite reading on every named
source choice in the accepted actual subgroup. -/
@[simp] theorem taggedSourceChoiceSubgroupMulEquivCoherentFamily_apply
    (choice : Multiplicative
      (TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex)) :
    taggedSourceChoiceSubgroupMulEquivCoherentFamily
        (taggedSourceChoiceGroupEquiv choice) =
      Multiplicative.ofAdd (TagChange.read choice.toAdd) := by
  simp [taggedSourceChoiceSubgroupMulEquivCoherentFamily,
    TagChange.globalTagChangeMulEquivCoherentFamily_apply]

/-- Read one source from an element of the actual source-choice subgroup. -/
noncomputable def readTaggedSourceChoiceSubgroupAt
    (automorphism : taggedSourceChoiceAutSubgroup)
    (source : TagChange.TaggedArchitectureIndex) : Bool :=
  readTaggedSourceChoiceExplicitExactGeometry automorphism.1.hom source

/-- Actual subgroup readback is the global choice classified by E1a. -/
theorem readTaggedSourceChoiceSubgroupAt_eq
    (automorphism : taggedSourceChoiceAutSubgroup) :
    readTaggedSourceChoiceSubgroupAt automorphism =
      (taggedSourceChoiceGroupEquiv.symm automorphism).toAdd := by
  let choice := taggedSourceChoiceGroupEquiv.symm automorphism
  have hchoice : taggedSourceChoiceGroupEquiv choice = automorphism :=
    taggedSourceChoiceGroupEquiv.apply_symm_apply automorphism
  calc
    readTaggedSourceChoiceSubgroupAt automorphism =
        readTaggedSourceChoiceSubgroupAt
          (taggedSourceChoiceGroupEquiv choice) := by rw [hchoice]
    _ = choice.toAdd := by
      exact readTaggedSourceChoiceExplicitExactGeometry_taggedSourceChoice choice.toAdd
    _ = (taggedSourceChoiceGroupEquiv.symm automorphism).toAdd := rfl

/-- Every finite component of the group-level reconstruction is exactly the
common finite restriction of actual subgroup readback. -/
theorem taggedSourceChoiceSubgroupMulEquivCoherentFamily_value
    (automorphism : taggedSourceChoiceAutSubgroup)
    (S : Finset TagChange.TaggedArchitectureIndex) :
    (taggedSourceChoiceSubgroupMulEquivCoherentFamily automorphism).toAdd.value S =
      FiniteReading.restrict readTaggedSourceChoiceSubgroupAt S automorphism := by
  let choice := taggedSourceChoiceGroupEquiv.symm automorphism
  have hchoice : taggedSourceChoiceGroupEquiv choice = automorphism :=
    taggedSourceChoiceGroupEquiv.apply_symm_apply automorphism
  rw [← hchoice]
  rw [taggedSourceChoiceSubgroupMulEquivCoherentFamily_apply]
  funext source
  change choice.toAdd source.1 =
    readTaggedSourceChoiceSubgroupAt
      (taggedSourceChoiceGroupEquiv choice) source.1
  rw [readTaggedSourceChoiceSubgroupAt_eq]
  simp

/-- The inverse reconstructs the actual subgroup element classified by the
singleton-assembled global source choice. -/
@[simp] theorem taggedSourceChoiceSubgroupMulEquivCoherentFamily_symm
    (family : Multiplicative
      (TagChange.CoherentFamily TagChange.TaggedArchitectureIndex)) :
    taggedSourceChoiceSubgroupMulEquivCoherentFamily.symm family =
      taggedSourceChoiceGroupEquiv
        (Multiplicative.ofAdd (TagChange.assemble family.toAdd)) := by
  rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChange
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
