import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationIsoComparisonSection
import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaNormalizationNaturality

/-!
# Canonical-normalization comparison section for the actual exact barAlpha

The exact-derived direct and via-base endpoints are packaged in the admissible
complete-geometry category from the single southwest admissibility proof.  The
actual five-factor `barAlpha` is then lifted to an isomorphism in that full
subcategory, so the generic isomorphism-comparison section applies without
accepting any endpoint, comparison, inverse, or section certificate.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct

/-- The generated direct endpoint as an object of the canonical-normalization
admissible complete-geometry category. -/
noncomputable def authoredExactDirectAdmissibleGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U :=
  ⟨(authoredExactDirectGeometryAt A z k g).1,
    authoredExactDirectGeometryAt_admissible A z k g admissible⟩

/-- The generated via-base endpoint as an object of the
canonical-normalization admissible complete-geometry category. -/
noncomputable def authoredExactViaBaseAdmissibleGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U :=
  ⟨(authoredExactViaBaseGeometryAt A z k g).1,
    authoredExactViaBaseGeometryAt_admissible A z k g admissible⟩

/-- The actual five-factor `barAlpha` as an isomorphism between the generated
admissible endpoint objects. -/
noncomputable def authoredExactBarAlphaAdmissibleIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactDirectAdmissibleGeometryAt A z k g admissible ≅
      authoredExactViaBaseAdmissibleGeometryAt A z k g admissible where
  hom := ObjectProperty.homMk (authoredExactBarAlphaIsoAt A z k g).hom.1
  inv := ObjectProperty.homMk (authoredExactBarAlphaIsoAt A z k g).inv.1
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.1) (authoredExactBarAlphaIsoAt A z k g).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.1) (authoredExactBarAlphaIsoAt A z k g).inv_hom_id

/-- The admissible comparison retains the actual complete-geometry hom of
`barAlpha`. -/
@[simp]
theorem authoredExactBarAlphaAdmissibleIsoAt_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom.hom =
      (authoredExactBarAlphaIsoAt A z k g).hom.1 :=
  rfl

/-- The actual canonical-normalization comparison groups admit the
group-homomorphic section constructed from the fixed exact `barAlpha`. -/
noncomputable def authoredExactCanonicalComparisonSectionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    normalizedGeometryComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom →*
      rawGeometryNormalizationComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom :=
  canonicalNormalizationIsoComparisonSectionHom
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible)

/-- Normalizing the actual `barAlpha` comparison section recovers every
normalized comparison-preserving endpoint pair. -/
theorem authoredExactCanonicalComparisonSection_rightInverse
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : normalizedGeometryComparisonSubgroup
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom) :
    geometryNormalizationComparisonSubgroupHom
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
        (authoredExactCanonicalComparisonSectionHom
          A z k g admissible pair) = pair :=
  canonicalNormalizationIsoComparisonSection_rightInverse
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible) pair

/-- The actual section retains the normalized source pointed-doctrine map. -/
@[simp]
theorem authoredExactCanonicalComparisonSection_fst_hom_base_base
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : normalizedGeometryComparisonSubgroup
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom) :
    (authoredExactCanonicalComparisonSectionHom
        A z k g admissible pair).1.1.hom.hom.base.base =
      pair.1.1.hom.f.hom.base.base :=
  canonicalNormalizationIsoComparisonSection_fst_hom_base_base
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible) pair

/-- The actual section retains the normalized source coefficient map. -/
@[simp]
theorem authoredExactCanonicalComparisonSection_fst_hom_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : normalizedGeometryComparisonSubgroup
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom) :
    (authoredExactCanonicalComparisonSectionHom
        A z k g admissible pair).1.1.hom.hom.geometry.coefficientHom =
      pair.1.1.hom.f.hom.geometry.coefficientHom :=
  canonicalNormalizationIsoComparisonSection_fst_hom_coefficientHom
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible) pair

/-- The actual section retains the normalized target pointed-doctrine map. -/
@[simp]
theorem authoredExactCanonicalComparisonSection_snd_hom_base_base
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : normalizedGeometryComparisonSubgroup
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom) :
    (authoredExactCanonicalComparisonSectionHom
        A z k g admissible pair).1.2.hom.hom.base.base =
      pair.1.2.hom.f.hom.base.base :=
  canonicalNormalizationIsoComparisonSection_snd_hom_base_base
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible) pair

/-- The actual section retains the normalized target coefficient map. -/
@[simp]
theorem authoredExactCanonicalComparisonSection_snd_hom_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : normalizedGeometryComparisonSubgroup
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom) :
    (authoredExactCanonicalComparisonSectionHom
        A z k g admissible pair).1.2.hom.hom.geometry.coefficientHom =
      pair.1.2.hom.f.hom.geometry.coefficientHom :=
  canonicalNormalizationIsoComparisonSection_snd_hom_coefficientHom
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible) pair

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
