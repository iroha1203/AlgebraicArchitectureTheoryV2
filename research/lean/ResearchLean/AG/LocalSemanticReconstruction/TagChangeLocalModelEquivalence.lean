import ResearchLean.AG.LocalSemanticReconstruction.LocalModelCategory
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteGroupReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Local-model equivalence for the tagged source-choice subgroup

The global category in this tagged slice has one object and the accepted
actual `taggedSourceChoiceAutSubgroup` as its endomorphism group.  The local
value is the independently defined group of coherent finite Bool tables, and
the local-model category is the genuine one-point restriction-diagram
category with that value category.

The primitive reading uses the accepted group equivalence on the unique local
component.  Morphism separation, morphism assembly, and object assembly are
proved independently before applying the general Cycle 19 reconstruction
theorem.  Local coherence remains exactly the finite restriction equations in
`TagChange.CoherentFamily`; no global automorphism or extension witness is
stored in a local object or morphism.

This is the G-124(B/E1) source-choice Hom slice.  It does not include the
canonical-normalization arrow or claim the final all-four realization/local-
model equivalence.  The categorical equivalence is noncomputable and does not
remove the separate actual-output effectiveness obstruction from Cycle 17.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory

namespace TagChangeLocalModelEquivalence

noncomputable section

/-- G-124(B/E1) global value group: the accepted actual source-choice
automorphism subgroup, not the full automorphism group or a function proxy. -/
abbrev GlobalGroup := taggedSourceChoiceAutSubgroup

/-- G-124(B/E1) local value group: coherent families of all finite Bool
tables under their explicit pointwise xor law. -/
abbrev LocalGroup :=
  Multiplicative
    (TagChange.CoherentFamily TagChange.TaggedArchitectureIndex)

/-- The actual source-choice subgroup as a one-object global category. -/
abbrev GlobalCategory := SingleObj GlobalGroup

/-- Local values form the one-object category carried by the coherent-family
group. -/
abbrev LocalValueCategory := SingleObj LocalGroup

/-- The independently chosen one-point restriction index for this Hom slice. -/
abbrev RestrictionIndex := Discrete PUnit

/-- The genuine restriction-diagram category used as the local-model side. -/
abbrev LocalCategory :=
  LocalModelCategory RestrictionIndex LocalValueCategory

/-- The unique object of the opposite one-point restriction index. -/
def restrictionPoint : RestrictionIndexᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- G-124(B/E1) primitive reading functor.  Its only component is the accepted
actual-subgroup/coherent-family `MulEquiv`; the constant-diagram functor adds
only the independently chosen one-point restriction presentation. -/
noncomputable def reading : GlobalCategory ⥤ LocalCategory :=
  SingleObj.mapHom GlobalGroup LocalGroup
      taggedSourceChoiceSubgroupMulEquivCoherentFamily.toMonoidHom ⋙
    Functor.const RestrictionIndexᵒᵖ

/-- The unique local component of primitive reading is exactly the accepted
group-level all-finite reading. -/
@[simp] theorem reading_map_app
    {X Y : GlobalCategory} (f : X ⟶ Y) :
    (reading.map f).app restrictionPoint =
      taggedSourceChoiceSubgroupMulEquivCoherentFamily f :=
  rfl

/-- Every finite table of the unique local component is the common
`FiniteReading.restrict` of the actual subgroup readback. -/
theorem reading_map_app_value
    {X Y : GlobalCategory} (f : X ⟶ Y)
    (S : Finset TagChange.TaggedArchitectureIndex) :
    ((reading.map f).app restrictionPoint).toAdd.value S =
      FiniteReading.restrict readTaggedSourceChoiceSubgroupAt S f := by
  rw [reading_map_app]
  exact taggedSourceChoiceSubgroupMulEquivCoherentFamily_value f S

/-- G-124(B) morphism separation: the unique component is injective because
the accepted group map is an equivalence. -/
theorem morphismSeparates : LocalReading.MorphismSeparates reading := by
  intro X Y first second equality
  apply taggedSourceChoiceSubgroupMulEquivCoherentFamily.injective
  exact NatTrans.congr_app equality restrictionPoint

/-- G-124(B) morphism assembly: extract the unique coherent-family component
and apply the inverse accepted group equivalence. -/
theorem morphismAssembles : LocalReading.MorphismAssembles reading := by
  intro X Y localMorphism
  let global : X ⟶ Y :=
    taggedSourceChoiceSubgroupMulEquivCoherentFamily.symm
      (localMorphism.app restrictionPoint)
  refine ⟨global, ?_⟩
  apply NatTrans.ext
  funext index
  have indexEquality : index = restrictionPoint := Subsingleton.elim _ _
  subst index
  exact taggedSourceChoiceSubgroupMulEquivCoherentFamily.apply_symm_apply
    (localMorphism.app restrictionPoint)

/-- Every one-point coherent-family diagram is isomorphic to the reading of
the unique global object.  This proves object assembly separately from Hom
fullness. -/
theorem objectAssembles : LocalReading.ObjectAssembles reading := by
  intro localObject
  refine ⟨SingleObj.star GlobalGroup, ?_⟩
  refine ⟨NatIso.ofComponents (fun index => ?_) ?_⟩
  · exact eqToIso (Subsingleton.elim _ _)
  · intro first second arrow
    have objectEquality : first = second := Subsingleton.elim _ _
    subst second
    have arrowEquality : arrow = 𝟙 first := Subsingleton.elim _ _
    subst arrow
    simp

/-- The general Cycle 19 reconstruction theorem applied to the actual tagged
source-choice slice. -/
noncomputable def equivalence : GlobalCategory ≌ LocalCategory :=
  LocalReading.reconstructionEquivalence reading morphismSeparates
    morphismAssembles objectAssembles

/-- The forward functor of the tagged slice equivalence is definitionally the
primitive all-finite reading. -/
@[simp] theorem equivalence_functor : equivalence.functor = reading :=
  rfl

/-- The Hom equivalence supplied by the general reconstruction spine reads by
the primitive tagged local functor. -/
@[simp] theorem homEquiv_apply
    {X Y : GlobalCategory} (f : X ⟶ Y) :
    LocalReading.homEquiv reading morphismSeparates morphismAssembles X Y f =
      reading.map f :=
  rfl

/-- Assembly in the general reconstruction spine is the inverse accepted
group equivalence, characterized at the unique local component. -/
theorem homEquiv_symm
    {X Y : GlobalCategory}
    (localMorphism : reading.obj X ⟶ reading.obj Y) :
    (LocalReading.homEquiv reading morphismSeparates morphismAssembles X Y).symm
        localMorphism =
      taggedSourceChoiceSubgroupMulEquivCoherentFamily.symm
        (localMorphism.app restrictionPoint) := by
  apply taggedSourceChoiceSubgroupMulEquivCoherentFamily.injective
  have readback := NatTrans.congr_app
    (LocalReading.read_assemble reading morphismSeparates morphismAssembles localMorphism)
    restrictionPoint
  rw [reading_map_app] at readback
  exact readback.trans
    (taggedSourceChoiceSubgroupMulEquivCoherentFamily.apply_symm_apply
      (localMorphism.app restrictionPoint)).symm

/-- The assembled global arrow is exactly the accepted Cycle 18 constructor
applied to singleton assembly of the unique coherent-family component. -/
theorem homEquiv_symm_eq_accepted_constructor
    {X Y : GlobalCategory}
    (localMorphism : reading.obj X ⟶ reading.obj Y) :
    (LocalReading.homEquiv reading morphismSeparates morphismAssembles X Y).symm
        localMorphism =
      taggedSourceChoiceGroupEquiv
        (Multiplicative.ofAdd
          (TagChange.assemble (localMorphism.app restrictionPoint).toAdd)) := by
  rw [homEquiv_symm]
  exact taggedSourceChoiceSubgroupMulEquivCoherentFamily_symm
    (localMorphism.app restrictionPoint)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence

end

end TagChangeLocalModelEquivalence

end AAT.AG.LocalSemanticReconstruction
