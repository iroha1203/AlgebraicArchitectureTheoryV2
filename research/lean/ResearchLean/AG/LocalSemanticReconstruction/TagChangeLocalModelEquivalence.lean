import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.SingleObj
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteGroupReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Finite-local model equivalence for the tagged source-choice subgroup

The local index is the actual poset of finite subsets of
`TagChange.TaggedArchitectureIndex`.  At `S` the local value is exactly the
finite Bool table `TagChange.LocalTagTable S`; an inclusion is read
contravariantly by table restriction.  The compatible sections of this
finite-valued presheaf are the independently defined
`TagChange.CoherentFamily` values, which contain only local tables and their
restriction equations.

The accepted Cycle 18 group equivalence identifies the actual
`taggedSourceChoiceAutSubgroup` with those compatible sections.  Delooping
that equivalence gives the categorical Hom-slice equivalence, and its Hom
inverse is identified with the accepted singleton-assembly constructor.

## Implementation notes

Finite subsets are deliberately the outer restriction index; using `PUnit`
and placing the completed coherent family in its sole value would hide the
finite-local structure required by G-124(A/B/E1b).  The category on the local
side is the delooping of the section group, rather than the entire functor
category of arbitrary diagrams: this Cycle reconstructs only the actual
source-choice automorphism Hom slice.  It does not reconstruct the full
tagged normalization category, the other three families, or the final common
G-124(B) realization/local-model equivalence.  The equivalence remains
noncomputable and does not remove Cycle 17's actual-output effectiveness
obstruction.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory

namespace TagChangeLocalModelEquivalence

noncomputable section

/-- G-124(B/E1b) restriction index: all finite subsets of the actual tagged
architecture-object index, ordered by inclusion. -/
abbrev RestrictionIndex := Finset TagChange.TaggedArchitectureIndex

/-- Restriction of finite Bool tables is an additive homomorphism. -/
def restrictionHom {S T : RestrictionIndex} (h : S ⊆ T) :
    TagChange.LocalTagTable T →+
      TagChange.LocalTagTable S :=
  AddMonoidHom.mk'
    (TagChange.LocalTagTable.restrict h)
    (fun _ _ => rfl)

/-- The actual finite-local value diagram.  Every component is a finite Bool
table and every arrow is the primitive restriction map. -/
def localTableDiagram : RestrictionIndexᵒᵖ ⥤ AddCommGrpCat :=
  { obj := fun S => AddCommGrpCat.of (TagChange.LocalTagTable S.unop)
    map := fun h => AddCommGrpCat.ofHom (restrictionHom h.unop.le)
    map_id := by
      intro S
      ext table source
      rfl
    map_comp := by
      intro S T U first second
      ext table source
      rfl }

/-- Each component of the actual local diagram is a finite value type. -/
theorem localTableDiagram_finite (S : RestrictionIndex) :
    Finite (localTableDiagram.obj (Opposite.op S)) :=
  TagChange.LocalTagTable.finite_value_type S

/-- A local section is precisely a family of finite tables compatible with
all arrows of the actual restriction diagram. -/
abbrev LocalSection :=
  TagChange.CoherentFamily TagChange.TaggedArchitectureIndex

/-- Section compatibility is exactly functorial restriction along an index
arrow, not a stored global choice or completed automorphism. -/
theorem localSection_naturality (compatibleSection : LocalSection)
    {S T : RestrictionIndex} (h : S ⊆ T) :
    (localTableDiagram.map (homOfLE h).op) (compatibleSection.value T) =
      compatibleSection.value S :=
  compatibleSection.coherent S T h

/-- Global values are the accepted actual source-choice automorphism subgroup. -/
abbrev GlobalGroup := taggedSourceChoiceAutSubgroup

/-- Local values are compatible sections of the finite-local diagram. -/
abbrev LocalGroup := Multiplicative LocalSection

/-- The actual subgroup as a one-object global Hom-slice category. -/
abbrev GlobalCategory := SingleObj GlobalGroup

/-- The local Hom-slice category deloops the group of compatible finite-local
sections. -/
abbrev LocalCategory := SingleObj LocalGroup

/-- Primitive categorical reading induced by the accepted actual-subgroup to
finite-local-section group equivalence. -/
noncomputable def reading : GlobalCategory ⥤ LocalCategory :=
  SingleObj.mapHom GlobalGroup LocalGroup
    taggedSourceChoiceSubgroupMulEquivCoherentFamily.toMonoidHom

/-- The reading at every actual finite index is the primitive finite
restriction of subgroup readback. -/
theorem reading_map_value {X Y : GlobalCategory} (f : X ⟶ Y)
    (S : RestrictionIndex) :
    (reading.map f).toAdd.value S =
      FiniteReading.restrict readTaggedSourceChoiceSubgroupAt S f :=
  taggedSourceChoiceSubgroupMulEquivCoherentFamily_value f S

/-- G-124(B) Hom separation on this slice. -/
theorem morphismSeparates {X Y : GlobalCategory} :
    Function.Injective
      (reading.map : (X ⟶ Y) → (reading.obj X ⟶ reading.obj Y)) :=
  taggedSourceChoiceSubgroupMulEquivCoherentFamily.injective

/-- G-124(B) Hom assembly on this slice. -/
theorem morphismAssembles {X Y : GlobalCategory} :
    Function.Surjective
      (reading.map : (X ⟶ Y) → (reading.obj X ⟶ reading.obj Y)) :=
  taggedSourceChoiceSubgroupMulEquivCoherentFamily.surjective

/-- Object assembly for this explicitly limited one-object Hom slice. -/
theorem objectAssembles (Z : LocalCategory) :
    ∃ X : GlobalCategory, Nonempty (reading.obj X ≅ Z) := by
  exact ⟨SingleObj.star GlobalGroup, ⟨eqToIso (Subsingleton.elim _ _)⟩⟩

/-- The actual subgroup is categorically equivalent to the compatible
sections of its finite-local restriction diagram. -/
noncomputable def equivalence : GlobalCategory ≌ LocalCategory :=
  taggedSourceChoiceSubgroupMulEquivCoherentFamily.toSingleObjEquiv

/-- The forward functor is definitionally primitive reading. -/
@[simp] theorem equivalence_functor : equivalence.functor = reading :=
  rfl

/-- The categorical Hom equivalence is the accepted group equivalence. -/
noncomputable def homEquiv {X Y : GlobalCategory} :
    (X ⟶ Y) ≃ (reading.obj X ⟶ reading.obj Y) :=
  taggedSourceChoiceSubgroupMulEquivCoherentFamily.toEquiv

/-- Forward Hom reconstruction is exactly primitive reading. -/
@[simp] theorem homEquiv_apply {X Y : GlobalCategory} (f : X ⟶ Y) :
    homEquiv f = reading.map f :=
  rfl

/-- Hom assembly is the inverse accepted section equivalence. -/
@[simp] theorem homEquiv_symm {X Y : GlobalCategory}
    (localSection : reading.obj X ⟶ reading.obj Y) :
    homEquiv.symm localSection =
      taggedSourceChoiceSubgroupMulEquivCoherentFamily.symm localSection :=
  rfl

/-- Hom assembly is exactly the accepted Cycle 18 constructor applied to
singleton assembly of the compatible finite-local section. -/
theorem homEquiv_symm_eq_accepted_constructor {X Y : GlobalCategory}
    (localSection : reading.obj X ⟶ reading.obj Y) :
    homEquiv.symm localSection =
      taggedSourceChoiceGroupEquiv
        (Multiplicative.ofAdd (TagChange.assemble localSection.toAdd)) :=
  taggedSourceChoiceSubgroupMulEquivCoherentFamily_symm localSection

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence

end


end TagChangeLocalModelEquivalence

end AAT.AG.LocalSemanticReconstruction
