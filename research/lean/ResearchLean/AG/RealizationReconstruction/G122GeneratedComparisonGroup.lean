import ResearchLean.AG.RealizationReconstruction.G122GeneratedComparisonQuotient
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldAmbientKernelComparison
import Formal.Util.AssertStandardAxioms

/-!
# Comparison groups generated inside the G-122 presentation

The source-law quotient category already contains the actual generated
`barAlpha` and its source-constructed inverse.  This file forms the comparison
group inside that presentation category.  Because `barAlpha` is an isomorphism,
the whole displayed comparison group is classified by its displayed source
automorphism: the target component is forced by conjugation.  Thus every group
element here consists of finite syntax quotient morphisms; no completed
complete-geometry automorphism or comparison-group element is a syntax leaf.

For the mandated finite axis-fold input, decoding both endpoint automorphisms
gives a homomorphism from this displayed group to G-122's actual raw
comparison group.  The homomorphism commutes with the source-conjugation
section.  This is an all-elements statement for the displayed group, but it
does not assert that every semantic endpoint automorphism is represented.
Consequently surjectivity onto the actual raw group, the normalization section,
its restricted kernel, and its lift fibers remain subsequent obligations.

## Implementation notes

`GeneratedArrowComparisonSubgroup` and its section are category-theoretic and
independent of semantic evaluation.  The fixed evaluator is defined only
afterward by applying the existing decoder to each finite syntax quotient and
wrapping the resulting morphisms in the independently proved admissible
endpoint objects.  The actual commuting-square proof is obtained by applying
the decoder to the displayed commuting square.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence
open FullGeometryNormalization

universe u v

noncomputable section

local instance finiteAxisFoldGeneratedComparisonGroupAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Endpoint automorphism pairs preserving one displayed arrow.  Its carrier
equation is the displayed commuting square, not equality after decoding. -/
def GeneratedArrowComparisonSubgroup {C : Type u} [Category.{v, u} C]
    {X Y : C} (c : X ⟶ Y) : Subgroup (Aut X × Aut Y) where
  carrier pair := pair.1.hom ≫ c = c ≫ pair.2.hom
  one_mem' := by
    change (𝟙 X) ≫ c = c ≫ (𝟙 Y)
    simp
  mul_mem' := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ first second
    change (a₂.hom ≫ a₁.hom) ≫ c = c ≫ (b₂.hom ≫ b₁.hom)
    rw [Category.assoc, first, ← Category.assoc, second, Category.assoc]
  inv_mem' := by
    rintro ⟨a, b⟩ relation
    change a.inv ≫ c = c ≫ b.inv
    calc
      a.inv ≫ c = a.inv ≫ ((c ≫ b.hom) ≫ b.inv) := by simp
      _ = a.inv ≫ ((a.hom ≫ c) ≫ b.inv) := by rw [relation]
      _ = c ≫ b.inv := by simp

/-- The identity pair is a genuine positive inhabitant of every displayed
comparison subgroup. -/
theorem generatedArrowComparisonSubgroup_one_mem
    {C : Type u} [Category.{v, u} C] {X Y : C} (c : X ⟶ Y) :
    (1 : Aut X × Aut Y) ∈ GeneratedArrowComparisonSubgroup c :=
  (GeneratedArrowComparisonSubgroup c).one_mem

/-- Conjugation along a displayed isomorphism, constructed within the same
presentation category. -/
noncomputable def presentationIsoConjugationAutomorphismHom
    {C : Type u} [Category.{v, u} C] {X Y : C} (c : X ≅ Y) :
    Aut X →* Aut Y where
  toFun a :=
    { hom := c.inv ≫ a.hom ≫ c.hom
      inv := c.inv ≫ a.inv ≫ c.hom
      hom_inv_id := by simp
      inv_hom_id := by simp }
  map_one' := by
    apply Iso.ext
    change c.inv ≫ (𝟙 X) ≫ c.hom = 𝟙 Y
    simp
  map_mul' a b := by
    apply Iso.ext
    change c.inv ≫ (b.hom ≫ a.hom) ≫ c.hom =
      (c.inv ≫ b.hom ≫ c.hom) ≫ (c.inv ≫ a.hom ≫ c.hom)
    simp [Category.assoc]

/-- A displayed source automorphism determines a comparison-preserving pair
by conjugation across the displayed isomorphism. -/
noncomputable def generatedArrowComparisonSectionHom
    {C : Type u} [Category.{v, u} C] {X Y : C} (c : X ≅ Y) :
    Aut X →* GeneratedArrowComparisonSubgroup c.hom where
  toFun a := ⟨(a, presentationIsoConjugationAutomorphismHom c a), by
    change a.hom ≫ c.hom = c.hom ≫ (c.inv ≫ a.hom ≫ c.hom)
    simp⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_one (presentationIsoConjugationAutomorphismHom c)
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_mul (presentationIsoConjugationAutomorphismHom c) a b

/-- Project a displayed comparison-preserving pair to its source
automorphism. -/
noncomputable def generatedArrowComparisonSourceHom
    {C : Type u} [Category.{v, u} C] {X Y : C} (c : X ⟶ Y) :
    GeneratedArrowComparisonSubgroup c →* Aut X :=
  (MonoidHom.fst _ _).comp (GeneratedArrowComparisonSubgroup c).subtype

/-- Every displayed comparison pair is recovered from its source component;
the target component is forced by the displayed comparison equation. -/
theorem generatedArrowComparisonSection_source_rightInverse
    {C : Type u} [Category.{v, u} C] {X Y : C} (c : X ≅ Y)
    (pair : GeneratedArrowComparisonSubgroup c.hom) :
    generatedArrowComparisonSectionHom c
        (generatedArrowComparisonSourceHom c.hom pair) = pair := by
  apply Subtype.ext
  apply Prod.ext
  · change generatedArrowComparisonSourceHom c.hom pair = pair.1.1
    rfl
  · apply Iso.ext
    change (presentationIsoConjugationAutomorphismHom c
      (generatedArrowComparisonSourceHom c.hom pair)).hom = pair.1.2.hom
    dsimp [presentationIsoConjugationAutomorphismHom,
      generatedArrowComparisonSourceHom]
    calc
      c.inv ≫ pair.1.1.hom ≫ c.hom =
          c.inv ≫ (pair.1.1.hom ≫ c.hom) := rfl
      _ = c.inv ≫ (c.hom ≫ pair.1.2.hom) := by rw [pair.2]
      _ = pair.1.2.hom := by simp

/-- Hence comparison-preserving changes of a displayed isomorphism are, as a
group, exactly its displayed source automorphisms. -/
noncomputable def generatedArrowComparisonSourceEquiv
    {C : Type u} [Category.{v, u} C] {X Y : C} (c : X ≅ Y) :
    GeneratedArrowComparisonSubgroup c.hom ≃* Aut X where
  toFun := generatedArrowComparisonSourceHom c.hom
  invFun := generatedArrowComparisonSectionHom c
  left_inv := generatedArrowComparisonSection_source_rightInverse c
  right_inv := by
    intro a
    change a = a
    rfl
  map_mul' := map_mul (generatedArrowComparisonSourceHom c.hom)

/-! ## Fixed finite-axis-fold evaluation -/

/-- The direct endpoint object in the source-law quotient presentation. -/
noncomputable abbrev FiniteAxisFoldDirectPresentationObject :=
  G122GeneratedComparisonPresentation.ofObject
    (.direct finiteAxisFoldG122CellInput)

/-- The via-base endpoint object in the source-law quotient presentation. -/
noncomputable abbrev FiniteAxisFoldViaBasePresentationObject :=
  G122GeneratedComparisonPresentation.ofObject
    (.viaBase finiteAxisFoldG122CellInput)

/-- Decode every displayed direct-endpoint automorphism into the actual
admissible direct endpoint. -/
noncomputable def finiteAxisFoldDirectPresentationAutomorphismHom :
    Aut FiniteAxisFoldDirectPresentationObject →*
      Aut (authoredExactDirectAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible) where
  toFun a :=
    { hom := ObjectProperty.homMk
        (G122GeneratedComparisonPresentation.decoder.map a.hom)
      inv := ObjectProperty.homMk
        (G122GeneratedComparisonPresentation.decoder.map a.inv)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact (G122GeneratedComparisonPresentation.decoder.mapIso a).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact (G122GeneratedComparisonPresentation.decoder.mapIso a).inv_hom_id }
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact G122GeneratedComparisonPresentation.decoder.map_id _
  map_mul' a b := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact G122GeneratedComparisonPresentation.decoder.map_comp b.hom a.hom

/-- Decode every displayed via-base-endpoint automorphism into the actual
admissible via-base endpoint. -/
noncomputable def finiteAxisFoldViaBasePresentationAutomorphismHom :
    Aut FiniteAxisFoldViaBasePresentationObject →*
      Aut (authoredExactViaBaseAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible) where
  toFun a :=
    { hom := ObjectProperty.homMk
        (G122GeneratedComparisonPresentation.decoder.map a.hom)
      inv := ObjectProperty.homMk
        (G122GeneratedComparisonPresentation.decoder.map a.inv)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact (G122GeneratedComparisonPresentation.decoder.mapIso a).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact (G122GeneratedComparisonPresentation.decoder.mapIso a).inv_hom_id }
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact G122GeneratedComparisonPresentation.decoder.map_id _
  map_mul' a b := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact G122GeneratedComparisonPresentation.decoder.map_comp b.hom a.hom

/-- The displayed comparison group for the fixed generated `barAlpha`. -/
noncomputable abbrev FiniteAxisFoldGeneratedComparisonSubgroup :=
  GeneratedArrowComparisonSubgroup
    (G122GeneratedComparisonPresentation.barAlphaIso
      finiteAxisFoldG122CellInput).hom

/-- Decoding a displayed comparison square produces the actual raw
comparison square on the fixed admissible endpoints. -/
theorem finiteAxisFoldPresentationEndpointAutomorphisms_preserve_barAlpha
    (pair : Aut FiniteAxisFoldDirectPresentationObject ×
      Aut FiniteAxisFoldViaBasePresentationObject)
    (preserves : pair ∈ FiniteAxisFoldGeneratedComparisonSubgroup) :
    (finiteAxisFoldDirectPresentationAutomorphismHom pair.1,
        finiteAxisFoldViaBasePresentationAutomorphismHom pair.2) ∈
      rawGeometryNormalizationComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible).hom := by
  change (finiteAxisFoldDirectPresentationAutomorphismHom pair.1).hom ≫ _ =
    _ ≫ (finiteAxisFoldViaBasePresentationAutomorphismHom pair.2).hom
  apply ObjectProperty.hom_ext
  have mapped := congrArg
    (fun f => G122GeneratedComparisonPresentation.decoder.map f) preserves
  simpa [finiteAxisFoldDirectPresentationAutomorphismHom,
    finiteAxisFoldViaBasePresentationAutomorphismHom] using mapped

/-- Evaluate every source-provenanced displayed comparison-group element in
G-122's actual raw comparison group. -/
noncomputable def finiteAxisFoldGeneratedComparisonEvaluationHom :
    FiniteAxisFoldGeneratedComparisonSubgroup →*
      rawGeometryNormalizationComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible).hom where
  toFun pair :=
    ⟨(finiteAxisFoldDirectPresentationAutomorphismHom pair.1.1,
        finiteAxisFoldViaBasePresentationAutomorphismHom pair.1.2),
      finiteAxisFoldPresentationEndpointAutomorphisms_preserve_barAlpha
        pair.1 pair.2⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one finiteAxisFoldDirectPresentationAutomorphismHom
    · exact map_one finiteAxisFoldViaBasePresentationAutomorphismHom
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul finiteAxisFoldDirectPresentationAutomorphismHom a.1.1 b.1.1
    · exact map_mul finiteAxisFoldViaBasePresentationAutomorphismHom a.1.2 b.1.2

/-- The decoder sends the displayed `barAlpha` and its displayed inverse to
the actual five-factor comparison and inverse. -/
theorem finiteAxisFoldGeneratedComparison_barAlpha_hom_inv :
    G122GeneratedComparisonPresentation.decoder.map
        (G122GeneratedComparisonPresentation.barAlphaIso
          finiteAxisFoldG122CellInput).hom =
      (authoredExactBarAlphaIsoAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))).hom.1 ∧
    G122GeneratedComparisonPresentation.decoder.map
        (G122GeneratedComparisonPresentation.barAlphaIso
          finiteAxisFoldG122CellInput).inv =
      (authoredExactBarAlphaIsoAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))).inv.1 :=
  ⟨rfl, rfl⟩

/-- Evaluation commutes with the displayed source-conjugation section for
every displayed source automorphism.  The result is the corresponding actual
raw comparison pair, not merely its source component. -/
theorem finiteAxisFoldGeneratedComparisonEvaluation_section
    (a : Aut FiniteAxisFoldDirectPresentationObject) :
    finiteAxisFoldGeneratedComparisonEvaluationHom
        (generatedArrowComparisonSectionHom
          (G122GeneratedComparisonPresentation.barAlphaIso
            finiteAxisFoldG122CellInput) a) =
      generatedArrowComparisonSectionHom
        (authoredExactBarAlphaAdmissibleIsoAt
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible)
        (finiteAxisFoldDirectPresentationAutomorphismHom a) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Iso.ext
    apply ObjectProperty.hom_ext
    dsimp [finiteAxisFoldGeneratedComparisonEvaluationHom,
      finiteAxisFoldViaBasePresentationAutomorphismHom,
      generatedArrowComparisonSectionHom,
      presentationIsoConjugationAutomorphismHom,
      finiteAxisFoldDirectPresentationAutomorphismHom]
    rw [Functor.map_comp, Functor.map_comp,
      finiteAxisFoldGeneratedComparison_barAlpha_hom_inv.1,
      finiteAxisFoldGeneratedComparison_barAlpha_hom_inv.2]
    rfl

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
