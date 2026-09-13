import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationAutomorphismSection

/-!
# Comparison-group section along an isomorphism

For an isomorphism of admissible complete geometries, a normalized
comparison-preserving pair is lifted by sectioning its source automorphism and
transporting that lift to the target by conjugation.  This avoids assuming that
the objectwise normalization section is natural in an arbitrary comparison.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport

/-- Conjugation along an isomorphism transports endpoint automorphisms as a
group homomorphism. -/
noncomputable def geometryIsoConjugationAutomorphismHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) : Aut G →* Aut H where
  toFun a :=
    { hom := c.inv ≫ a.hom ≫ c.hom
      inv := c.inv ≫ a.inv ≫ c.hom
      hom_inv_id := by simp
      inv_hom_id := by simp }
  map_one' := by
    apply Iso.ext
    change c.inv ≫ (𝟙 G) ≫ c.hom = 𝟙 H
    simp
  map_mul' a b := by
    apply Iso.ext
    change
      c.inv ≫ (b.hom ≫ a.hom) ≫ c.hom =
        (c.inv ≫ b.hom ≫ c.hom) ≫ (c.inv ≫ a.hom ≫ c.hom)
    simp [Category.assoc]

/-- Evaluation of conjugation on the forward morphism. -/
@[simp]
theorem geometryIsoConjugationAutomorphismHom_hom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (a : Aut G) :
    (geometryIsoConjugationAutomorphismHom c a).hom =
      c.inv ≫ a.hom ≫ c.hom :=
  rfl

/-- Lift a normalized pair preserving an isomorphism by lifting the source and
conjugating it across the raw isomorphism. -/
noncomputable def canonicalNormalizationIsoComparisonSectionHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) :
    normalizedGeometryComparisonSubgroup c.hom →*
      rawGeometryNormalizationComparisonSubgroup c.hom where
  toFun pair := by
    let source := canonicalNormalizationAutomorphismSectionHom G pair.1.1
    let target := geometryIsoConjugationAutomorphismHom c source
    refine ⟨(source, target), ?_⟩
    rw [mem_rawGeometryNormalizationComparisonSubgroup]
    dsimp [target]
    simp
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one (canonicalNormalizationAutomorphismSectionHom G)
    · change geometryIsoConjugationAutomorphismHom c
          (canonicalNormalizationAutomorphismSectionHom G 1) = 1
      rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul (canonicalNormalizationAutomorphismSectionHom G) a.1.1 b.1.1
    · change geometryIsoConjugationAutomorphismHom c
          (canonicalNormalizationAutomorphismSectionHom G (a.1.1 * b.1.1)) =
        geometryIsoConjugationAutomorphismHom c
            (canonicalNormalizationAutomorphismSectionHom G a.1.1) *
          geometryIsoConjugationAutomorphismHom c
            (canonicalNormalizationAutomorphismSectionHom G b.1.1)
      rw [map_mul, map_mul]

/-- The underlying endpoint pair of the comparison section. -/
@[simp]
theorem canonicalNormalizationIsoComparisonSectionHom_val
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (pair : normalizedGeometryComparisonSubgroup c.hom) :
    (canonicalNormalizationIsoComparisonSectionHom c pair).1 =
      (canonicalNormalizationAutomorphismSectionHom G pair.1.1,
        geometryIsoConjugationAutomorphismHom c
          (canonicalNormalizationAutomorphismSectionHom G pair.1.1)) :=
  rfl

/-- Normalizing the target conjugate recovers the supplied normalized target
automorphism, using the supplied comparison equation and no naturality premise
for the section. -/
theorem canonicalNormalizationIsoComparisonSection_target_rightInverse
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (pair : normalizedGeometryComparisonSubgroup c.hom) :
    RealizationComparisonIdempotents.functorAutomorphismHom
        (geometryNormalizationFunctor.{u, v} U) H
        (geometryIsoConjugationAutomorphismHom c
          (canonicalNormalizationAutomorphismSectionHom G pair.1.1)) =
      pair.1.2 := by
  apply Iso.ext
  change
    (geometryNormalizationFunctor.{u, v} U).map
        (c.inv ≫
          (canonicalNormalizationAutomorphismSectionHom G pair.1.1).hom ≫
          c.hom) = pair.1.2.hom
  rw [Functor.map_comp, Functor.map_comp]
  have hsource := congrArg Iso.hom
    (canonicalNormalizationAutomorphismSection_rightInverse G pair.1.1)
  change
    (geometryNormalizationFunctor.{u, v} U).map
        (canonicalNormalizationAutomorphismSectionHom G pair.1.1).hom =
      pair.1.1.hom at hsource
  rw [hsource, pair.2]
  simp

/-- The isomorphism-comparison section is a right inverse of normalization on
the full comparison-preserving subgroup. -/
theorem canonicalNormalizationIsoComparisonSection_rightInverse
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (pair : normalizedGeometryComparisonSubgroup c.hom) :
    geometryNormalizationComparisonSubgroupHom c.hom
        (canonicalNormalizationIsoComparisonSectionHom c pair) = pair := by
  apply Subtype.ext
  apply Prod.ext
  · exact canonicalNormalizationAutomorphismSection_rightInverse G pair.1.1
  · exact canonicalNormalizationIsoComparisonSection_target_rightInverse c pair

/-- The source component of the comparison section retains the supplied
pointed-doctrine morphism. -/
@[simp]
theorem canonicalNormalizationIsoComparisonSection_fst_hom_base_base
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (pair : normalizedGeometryComparisonSubgroup c.hom) :
    (canonicalNormalizationIsoComparisonSectionHom c pair).1.1.hom.hom.base.base =
      pair.1.1.hom.f.hom.base.base :=
  canonicalNormalizationAutomorphismSection_hom_base_base G pair.1.1

/-- The source component of the comparison section retains the supplied
coefficient homomorphism. -/
@[simp]
theorem canonicalNormalizationIsoComparisonSection_fst_hom_coefficientHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (pair : normalizedGeometryComparisonSubgroup c.hom) :
    (canonicalNormalizationIsoComparisonSectionHom c pair).1.1.hom.hom.geometry.coefficientHom =
      pair.1.1.hom.f.hom.geometry.coefficientHom :=
  canonicalNormalizationAutomorphismSection_hom_coefficientHom G pair.1.1

/-- The target component of the comparison section retains the supplied
pointed-doctrine morphism. -/
@[simp]
theorem canonicalNormalizationIsoComparisonSection_snd_hom_base_base
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (pair : normalizedGeometryComparisonSubgroup c.hom) :
    (canonicalNormalizationIsoComparisonSectionHom c pair).1.2.hom.hom.base.base =
      pair.1.2.hom.f.hom.base.base := by
  have h := congrArg
    (fun a : Aut ((geometryNormalizationFunctor.{u, v} U).obj H) =>
      a.hom.f.hom.base.base)
    (canonicalNormalizationIsoComparisonSection_target_rightInverse c pair)
  simpa using h

/-- The target component of the comparison section retains the supplied
coefficient homomorphism. -/
@[simp]
theorem canonicalNormalizationIsoComparisonSection_snd_hom_coefficientHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) (pair : normalizedGeometryComparisonSubgroup c.hom) :
    (canonicalNormalizationIsoComparisonSectionHom c pair).1.2.hom.hom.geometry.coefficientHom =
      pair.1.2.hom.f.hom.geometry.coefficientHom := by
  have h := congrArg
    (fun a : Aut ((geometryNormalizationFunctor.{u, v} U).obj H) =>
      a.hom.f.hom.geometry.coefficientHom)
    (canonicalNormalizationIsoComparisonSection_target_rightInverse c pair)
  simpa using h

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
