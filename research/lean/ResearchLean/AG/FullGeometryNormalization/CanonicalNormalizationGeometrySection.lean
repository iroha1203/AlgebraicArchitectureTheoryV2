import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationCoreSectionRetraction

/-!
# Complete-geometry normalization section

The exact-core section extends to complete geometry by retaining the actual
lower doctrine morphism, coefficient homomorphism, overlap comparison, and
local realization maps of the input endomorphism.  These fields are not
assumed as a completed lift: the new core total morphism is constructed first,
and every geometry field is then rebuilt over that morphism.
-/

open CategoryTheory

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation DoctrineFiberProduct GeometryTransport

/-- Core-total morphism underlying the complete-geometry section. -/
noncomputable def canonicalNormalizationSectionTotal
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) : PackageTotalHom G.core G.core where
  base := f.base.base
  upper := canonicalNormalizationSectionUpper G.core admissible f.base.upper
  atomEquiv_eq := by
    exact f.base.atomEquiv_eq

/-- The section retains the actual pointed-doctrine morphism. -/
@[simp]
theorem canonicalNormalizationSectionTotal_base
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    (canonicalNormalizationSectionTotal G admissible f).base = f.base.base :=
  rfl

/-- The section's exact upper morphism is the Cycle 16 raw lift. -/
@[simp]
theorem canonicalNormalizationSectionTotal_upper
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    (canonicalNormalizationSectionTotal G admissible f).upper =
      canonicalNormalizationSectionUpper G.core admissible f.base.upper :=
  rfl

/-- Geometry data over the sectioned core-total morphism. -/
noncomputable def canonicalNormalizationGeometrySectionReadHom
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    GeomReadHom G G (canonicalNormalizationSectionTotal G admissible f) where
  coverage := {
    requiredSupport := f.geometry.coverage.requiredSupport
    requiredEquationCoordinate :=
      f.geometry.coverage.requiredEquationCoordinate
    selectedViolationWitness :=
      f.geometry.coverage.selectedViolationWitness
    requiredAxis := f.geometry.coverage.requiredAxis
    supportVisibleOn := f.geometry.coverage.supportVisibleOn
    equationCoordinateVisibleOn :=
      f.geometry.coverage.equationCoordinateVisibleOn
    violationWitnessVisibleOn :=
      f.geometry.coverage.violationWitnessVisibleOn
    axisReadableOn := f.geometry.coverage.axisReadableOn
    boundaryVisibleOn := f.geometry.coverage.boundaryVisibleOn
  }
  overlap := {
    overlapIso := f.geometry.overlap.overlapIso
  }
  coefficientHom := f.geometry.coefficientHom
  raw_eq := f.geometry.raw_eq
  supportComp := f.geometry.supportComp
  axisComp := f.geometry.axisComp
  observableComp := f.geometry.observableComp
  supportReads := f.geometry.supportReads
  axisReads := f.geometry.axisReads
  observableReads := f.geometry.observableReads
  support_naturality := f.geometry.support_naturality
  axis_naturality := f.geometry.axis_naturality
  observable_naturality := f.geometry.observable_naturality

/-- Complete-geometry endomorphism carried by the normalization section. -/
noncomputable def canonicalNormalizationGeometrySection
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) : GeometryTotalHom G G where
  base := canonicalNormalizationSectionTotal G admissible f
  geometry := canonicalNormalizationGeometrySectionReadHom G admissible f

/-- The complete section retains the input coefficient homomorphism. -/
@[simp]
theorem canonicalNormalizationGeometrySection_coefficientHom
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    (canonicalNormalizationGeometrySection G admissible f).geometry.coefficientHom =
      f.geometry.coefficientHom :=
  rfl

private theorem geometrySection_heq_of_base_eq
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    {firstBase secondBase : PackageTotalHom G.core G.core}
    (first : GeomReadHom G G firstBase)
    (second : GeomReadHom G G secondBase)
    (hbase : firstBase = secondBase)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hsupport : HEq first.supportComp second.supportComp)
    (haxis : HEq first.axisComp second.axisComp)
    (hobservable : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

/-- The core-total section sends complete canonical normalization to the core
identity. -/
theorem canonicalNormalizationSectionTotal_normalization
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    canonicalNormalizationSectionTotal G admissible
        (canonicalGeometryNormalization G admissible) =
      PackageTotalHom.id G.core := by
  apply PackageTotalHom.ext
  · rfl
  · exact canonicalNormalizationSectionUpper_normalization G.core admissible

/-- The core-total section preserves composition. -/
theorem canonicalNormalizationSectionTotal_comp
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f g : GeometryTotalHom G G) :
    canonicalNormalizationSectionTotal G admissible (f.comp g) =
      (canonicalNormalizationSectionTotal G admissible f).comp
        (canonicalNormalizationSectionTotal G admissible g) := by
  apply PackageTotalHom.ext
  · rfl
  · exact canonicalNormalizationSectionUpper_comp
      G.core admissible f.base.upper g.base.upper

/-- The core-total normalization sandwich of the section equals the
normalization sandwich of the input. -/
theorem canonicalNormalizationSectionTotal_sandwich
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    ((canonicalObjectNormalizationTotal G.core admissible).comp
        (canonicalNormalizationSectionTotal G admissible f)).comp
          (canonicalObjectNormalizationTotal G.core admissible) =
      ((canonicalObjectNormalizationTotal G.core admissible).comp f.base).comp
        (canonicalObjectNormalizationTotal G.core admissible) := by
  apply PackageTotalHom.ext
  · rfl
  · exact canonicalNormalizationSectionUpper_sandwich
      G.core admissible f.base.upper

/-- The complete-geometry section sends the normalization Karoubi identity to
the raw complete-geometry identity. -/
theorem canonicalNormalizationGeometrySection_normalization
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    canonicalNormalizationGeometrySection G admissible
        (canonicalGeometryNormalization G admissible) =
      GeometryTotalHom.id G := by
  have hbase := canonicalNormalizationSectionTotal_normalization G admissible
  apply GeometryTotalHom.ext hbase
  apply geometrySection_heq_of_base_eq _ _ hbase rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro support support' hsupport
    cases hsupport
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro axis axis' haxis
    cases haxis
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro observable observable' hobservable
    cases hobservable
    rfl

/-- The complete-geometry section preserves composition strictly. -/
theorem canonicalNormalizationGeometrySection_comp
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f g : GeometryTotalHom G G) :
    canonicalNormalizationGeometrySection G admissible (f.comp g) =
      (canonicalNormalizationGeometrySection G admissible f).comp
        (canonicalNormalizationGeometrySection G admissible g) := by
  have hbase := canonicalNormalizationSectionTotal_comp G admissible f g
  apply GeometryTotalHom.ext hbase
  apply geometrySection_heq_of_base_eq _ _ hbase rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro support support' hsupport
    cases hsupport
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro axis axis' haxis
    cases haxis
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro observable observable' hobservable
    cases hobservable
    rfl

/-- Restricting the complete-geometry section by normalization agrees with
restricting its input by normalization. -/
theorem canonicalNormalizationGeometrySection_sandwich
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    canonicalGeometryNormalization G admissible ≫
        canonicalNormalizationGeometrySection G admissible f ≫
          canonicalGeometryNormalization G admissible =
      canonicalGeometryNormalization G admissible ≫ f ≫
        canonicalGeometryNormalization G admissible := by
  have hbase := canonicalNormalizationSectionTotal_sandwich G admissible f
  apply GeometryTotalHom.ext hbase
  apply geometrySection_heq_of_base_eq _ _ hbase rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro support support' hsupport
    cases hsupport
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro axis axis' haxis
    cases haxis
    rfl
  · apply Function.hfunext rfl
    intro W W' hW
    cases hW
    apply Function.hfunext rfl
    intro observable observable' hobservable
    cases hobservable
    rfl

/-- The complete-geometry section splits normalization restriction on every
normalization-fixed endomorphism. -/
theorem canonicalNormalizationGeometrySection_retraction
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G)
    (fixed : canonicalGeometryNormalization G admissible ≫ f ≫
        canonicalGeometryNormalization G admissible = f) :
    canonicalGeometryNormalization G admissible ≫
        canonicalNormalizationGeometrySection G admissible f ≫
          canonicalGeometryNormalization G admissible = f := by
  rw [canonicalNormalizationGeometrySection_sandwich G admissible f]
  exact fixed

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
