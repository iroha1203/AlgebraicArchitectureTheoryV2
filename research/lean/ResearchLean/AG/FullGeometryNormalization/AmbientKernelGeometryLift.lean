import ResearchLean.AG.FullGeometryNormalization.AmbientKernelCoreLift

/-!
# Complete-geometry lift of the ambient normalization-kernel swap

The ambient object swap has identity atom, context, base-doctrine, coefficient,
and local-realization data.  This module lifts the exact-core involution to a
complete-geometry automorphism and records its two-sided invisibility under
canonical geometry normalization.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation DoctrineFiberProduct GeometryTransport

private theorem ambientKernelGeometryReadHom_heq_of_base_eq
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

/-- Identity local geometry data over the ambient-kernel total core map. -/
noncomputable def ambientKernelGeometryReadHom
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    GeomReadHom G G (ambientKernelTotal G.core admissible) where
  coverage := by
    constructor <;> intros <;> assumption
  overlap := by
    constructor
    intro base left right
    exact Iso.refl _
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := by
    unfold rawTransport
    rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_id]
    apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Complete-geometry ambient-kernel endomorphism. -/
noncomputable def ambientKernelGeometry
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    GeometryTotalHom G G where
  base := ambientKernelTotal G.core admissible
  geometry := ambientKernelGeometryReadHom G admissible

/-- The ambient-kernel geometry lift lies over the pointed-doctrine identity. -/
@[simp]
theorem ambientKernelGeometry_packageBase
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (ambientKernelGeometry G admissible).base.base =
      ExtInstHom.id (packagePoint G.core) :=
  rfl

/-- The ambient-kernel geometry lift fixes coefficients. -/
@[simp]
theorem ambientKernelGeometry_coefficientHom
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (ambientKernelGeometry G admissible).geometry.coefficientHom =
      RingHom.id G.Coefficient :=
  rfl

/-- The complete-geometry ambient-kernel endomorphism is nonidentity. -/
theorem ambientKernelGeometry_ne_id
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    ambientKernelGeometry G admissible ≠ GeometryTotalHom.id G := by
  intro h
  have hbase := congrArg GeometryTotalHom.base h
  exact ambientKernelTotal_ne_id G.core admissible hbase

/-- Applying the complete-geometry ambient-kernel endomorphism twice is the
identity. -/
theorem ambientKernelGeometry_comp_self
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    (ambientKernelGeometry G admissible).comp
        (ambientKernelGeometry G admissible) = GeometryTotalHom.id G := by
  have hbase := ambientKernelTotal_comp_self G.core admissible
  apply GeometryTotalHom.ext hbase
  apply ambientKernelGeometryReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-- Canonical complete normalization absorbs the ambient-kernel geometry lift
on the right. -/
theorem canonicalGeometryNormalization_comp_ambientKernelGeometry
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    canonicalGeometryNormalization G admissible ≫
        ambientKernelGeometry G admissible =
      canonicalGeometryNormalization G admissible := by
  have hbase := canonicalNormalizationTotal_comp_ambientKernelTotal
    G.core admissible
  apply GeometryTotalHom.ext hbase
  apply ambientKernelGeometryReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-- Canonical complete normalization absorbs the ambient-kernel geometry lift
on the left. -/
theorem ambientKernelGeometry_comp_canonicalGeometryNormalization
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    ambientKernelGeometry G admissible ≫
        canonicalGeometryNormalization G admissible =
      canonicalGeometryNormalization G admissible := by
  have hbase := ambientKernelTotal_comp_canonicalNormalizationTotal
    G.core admissible
  apply GeometryTotalHom.ext hbase
  apply ambientKernelGeometryReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-- The ambient-kernel geometry involution as an automorphism. -/
noncomputable def ambientKernelGeometryAut
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) : Aut G where
  hom := ambientKernelGeometry G admissible
  inv := ambientKernelGeometry G admissible
  hom_inv_id := ambientKernelGeometry_comp_self G admissible
  inv_hom_id := ambientKernelGeometry_comp_self G admissible

/-- The ambient-kernel geometry automorphism is nontrivial. -/
theorem ambientKernelGeometryAut_ne_one
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core) :
    ambientKernelGeometryAut G admissible ≠ 1 := by
  intro h
  have hhom := congrArg (fun a : Aut G => a.hom) h
  exact ambientKernelGeometry_ne_id G admissible hhom

/-- The same automorphism internal to the admissible-geometry full
subcategory. -/
noncomputable def ambientKernelAdmissibleGeometryAut
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) : Aut G where
  hom := ObjectProperty.homMk (ambientKernelGeometry G.obj G.property)
  inv := ObjectProperty.homMk (ambientKernelGeometry G.obj G.property)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact ambientKernelGeometry_comp_self G.obj G.property
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact ambientKernelGeometry_comp_self G.obj G.property

/-- The admissible ambient-kernel automorphism remains nontrivial before
normalization. -/
theorem ambientKernelAdmissibleGeometryAut_ne_one
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    ambientKernelAdmissibleGeometryAut G ≠ 1 := by
  intro h
  have hhom := congrArg (fun a : Aut G => a.hom.hom) h
  exact ambientKernelGeometry_ne_id G.obj G.property hhom

/-- Complete normalization sends the ambient-kernel automorphism to the
identity normalized automorphism. -/
theorem geometryNormalizationFunctor_map_ambientKernelAdmissibleGeometryAut
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (geometryNormalizationFunctor.{u, v} U).mapIso
        (ambientKernelAdmissibleGeometryAut G) = Iso.refl _ := by
  apply Iso.ext
  apply Karoubi.Hom.ext
  apply ObjectProperty.hom_ext
  exact canonicalGeometryNormalization_comp_ambientKernelGeometry
    G.obj G.property

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
