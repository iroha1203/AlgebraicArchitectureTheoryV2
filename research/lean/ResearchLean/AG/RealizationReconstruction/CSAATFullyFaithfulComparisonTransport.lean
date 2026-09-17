import ResearchLean.AG.RealizationReconstruction.CSAATIndependentPackageCategories
import ResearchLean.AG.RealizationReconstruction.G122GeneratedComparisonGroup
import Formal.Util.AssertStandardAxioms

/-!
# Comparison-group transport along a fully faithful realization

A fully faithful functor transports every comparison-preserving endpoint pair
to the corresponding pair on the realized arrow.  Faithfulness reflects the
commuting square, while fullness lifts arbitrary endpoint automorphisms.
Consequently the whole comparison subgroup, not only selected elements, is
transported by a group equivalence.  The source projection and the canonical
conjugation section for isomorphism comparisons commute with this transport.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v w x

noncomputable section

/-- Endpoint automorphisms transported by the supplied fully faithful data. -/
noncomputable def fullyFaithfulEndpointAutMulEquiv
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) (X : C) :
    Aut X ≃* Aut (F.obj X) :=
  hf.autMulEquivOfFullyFaithful X

/-- Every functor preserves comparison squares; the fully faithful parameter
also fixes the endpoint automorphism equivalences used by the later inverse. -/
noncomputable def generatedArrowComparisonHomOfFullyFaithful
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c →*
      GeneratedArrowComparisonSubgroup (F.map c) where
  toFun pair :=
    ⟨(fullyFaithfulEndpointAutMulEquiv F hf X pair.1.1,
      fullyFaithfulEndpointAutMulEquiv F hf Y pair.1.2), by
        change F.map pair.1.1.hom ≫ F.map c =
          F.map c ≫ F.map pair.1.2.hom
        rw [← F.map_comp, ← F.map_comp, pair.2]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one (fullyFaithfulEndpointAutMulEquiv F hf X)
    · exact map_one (fullyFaithfulEndpointAutMulEquiv F hf Y)
  map_mul' first second := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul (fullyFaithfulEndpointAutMulEquiv F hf X) first.1.1 second.1.1
    · exact map_mul (fullyFaithfulEndpointAutMulEquiv F hf Y) first.1.2 second.1.2

theorem generatedArrowComparisonHomOfFullyFaithful_injective
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y) :
    Function.Injective (generatedArrowComparisonHomOfFullyFaithful F hf c) := by
  intro first second equality
  apply Subtype.ext
  apply Prod.ext
  · apply (fullyFaithfulEndpointAutMulEquiv F hf X).injective
    exact congrArg (fun pair => pair.1.1) equality
  · apply (fullyFaithfulEndpointAutMulEquiv F hf Y).injective
    exact congrArg (fun pair => pair.1.2) equality

theorem generatedArrowComparisonHomOfFullyFaithful_surjective
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y) :
    Function.Surjective (generatedArrowComparisonHomOfFullyFaithful F hf c) := by
  intro target
  let sourceAut : Aut X :=
    (fullyFaithfulEndpointAutMulEquiv F hf X).symm target.1.1
  let targetAut : Aut Y :=
    (fullyFaithfulEndpointAutMulEquiv F hf Y).symm target.1.2
  have relation : sourceAut.hom ≫ c = c ≫ targetAut.hom := by
    apply hf.map_injective
    rw [F.map_comp, F.map_comp]
    change
      (fullyFaithfulEndpointAutMulEquiv F hf X sourceAut).hom ≫ F.map c =
        F.map c ≫ (fullyFaithfulEndpointAutMulEquiv F hf Y targetAut).hom
    rw [(fullyFaithfulEndpointAutMulEquiv F hf X).apply_symm_apply target.1.1,
      (fullyFaithfulEndpointAutMulEquiv F hf Y).apply_symm_apply target.1.2]
    exact target.2
  refine ⟨⟨(sourceAut, targetAut), relation⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact (fullyFaithfulEndpointAutMulEquiv F hf X).apply_symm_apply target.1.1
  · exact (fullyFaithfulEndpointAutMulEquiv F hf Y).apply_symm_apply target.1.2

/-- Fullness and faithfulness together transport the complete comparison
subgroup of every arrow. -/
noncomputable def generatedArrowComparisonMulEquivOfFullyFaithful
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup (F.map c) :=
  MulEquiv.ofBijective (generatedArrowComparisonHomOfFullyFaithful F hf c)
    ⟨generatedArrowComparisonHomOfFullyFaithful_injective F hf c,
      generatedArrowComparisonHomOfFullyFaithful_surjective F hf c⟩

/-- The comparison-group equivalence commutes with the source endpoint
projection. -/
theorem generatedArrowComparison_source_compatibility
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    generatedArrowComparisonSourceHom (F.map c)
        (generatedArrowComparisonMulEquivOfFullyFaithful F hf c pair) =
      fullyFaithfulEndpointAutMulEquiv F hf X
        (generatedArrowComparisonSourceHom c pair) :=
  rfl

/-- For an isomorphism comparison, the transported canonical conjugation
section is the canonical section of the realized isomorphism. -/
theorem generatedArrowComparison_section_compatibility
    {C : Type u} {D : Type v} [Category.{w, u} C] [Category.{x, v} D]
    (F : C ⥤ D) (hf : F.FullyFaithful) {X Y : C} (c : X ≅ Y)
    (a : Aut X) :
    generatedArrowComparisonMulEquivOfFullyFaithful F hf c.hom
        (generatedArrowComparisonSectionHom c a) =
      generatedArrowComparisonSectionHom (F.mapIso c)
        (fullyFaithfulEndpointAutMulEquiv F hf X a) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Iso.ext
    change F.map (c.inv ≫ a.hom ≫ c.hom) =
      F.map c.inv ≫ F.map a.hom ≫ F.map c.hom
    simp

/-! ## Independent generated-package applications -/

/-- Every comparison-preserving pair of generated lens package
automorphisms is exactly equivalent, as a group, to the pair on the original
semantic lens arrow. -/
noncomputable def lensAATIndependentPackageComparisonMulEquiv
    (input : LensFamilyInput.{u})
    {X Y : LensAATIndependentPackageObject input} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup
        ((lensAATIndependentPackageSemanticFunctor input).map c) :=
  generatedArrowComparisonMulEquivOfFullyFaithful
    (lensAATIndependentPackageSemanticFunctor input)
    (lensAATIndependentPackageSemanticFullyFaithful input) c

/-- Protocol analogue: the same theorem transports the whole comparison
group of an arbitrary generated package arrow, including noninvertible
underlying semantic adapters. -/
noncomputable def protocolAATIndependentPackageComparisonMulEquiv
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolAATIndependentPackageObject input} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c ≃*
      GeneratedArrowComparisonSubgroup
        ((protocolAATIndependentPackageSemanticFunctor input).map c) :=
  generatedArrowComparisonMulEquivOfFullyFaithful
    (protocolAATIndependentPackageSemanticFunctor input)
    (protocolAATIndependentPackageSemanticFullyFaithful input) c

end

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
