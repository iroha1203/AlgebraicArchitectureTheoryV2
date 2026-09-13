import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationGeometrySection
import ResearchLean.AG.FullGeometryNormalization.ComparisonGroup

/-!
# Automorphism-group section for complete normalization

Normalization-fixed complete-geometry automorphisms are lifted by applying the
Cycle 19 section to both their forward and inverse Karoubi arrows.  The group
laws follow from strict composition and from the fact that the Karoubi identity
is canonical normalization.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport

/-- Lift an automorphism of a normalized complete geometry to an
automorphism of its raw admissible geometry. -/
noncomputable def canonicalNormalizationAutomorphismSection
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) : Aut G where
  hom := ObjectProperty.homMk
    (canonicalNormalizationGeometrySection G.obj G.property a.hom.f.hom)
  inv := ObjectProperty.homMk
    (canonicalNormalizationGeometrySection G.obj G.property a.inv.f.hom)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    change
      (canonicalNormalizationGeometrySection G.obj G.property a.hom.f.hom).comp
          (canonicalNormalizationGeometrySection G.obj G.property a.inv.f.hom) =
        GeometryTotalHom.id G.obj
    rw [← canonicalNormalizationGeometrySection_comp]
    have h := congrArg (fun k => k.f.hom) a.hom_inv_id
    have h' : a.hom.f.hom.comp a.inv.f.hom =
        canonicalGeometryNormalization G.obj G.property := by
      simpa only [normalizedGeometryCategory_comp_f,
        normalizedGeometryCategory_id_f,
        canonicalAdmissibleGeometryNormalization_hom] using h
    rw [h']
    exact canonicalNormalizationGeometrySection_normalization G.obj G.property
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    change
      (canonicalNormalizationGeometrySection G.obj G.property a.inv.f.hom).comp
          (canonicalNormalizationGeometrySection G.obj G.property a.hom.f.hom) =
        GeometryTotalHom.id G.obj
    rw [← canonicalNormalizationGeometrySection_comp]
    have h := congrArg (fun k => k.f.hom) a.inv_hom_id
    have h' : a.inv.f.hom.comp a.hom.f.hom =
        canonicalGeometryNormalization G.obj G.property := by
      simpa only [normalizedGeometryCategory_comp_f,
        normalizedGeometryCategory_id_f,
        canonicalAdmissibleGeometryNormalization_hom] using h
    rw [h']
    exact canonicalNormalizationGeometrySection_normalization G.obj G.property

/-- The lifted raw automorphism has the sectioned forward morphism. -/
@[simp]
theorem canonicalNormalizationAutomorphismSection_hom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    (canonicalNormalizationAutomorphismSection G a).hom.hom =
      canonicalNormalizationGeometrySection G.obj G.property a.hom.f.hom :=
  rfl

/-- The lifted raw automorphism has the sectioned inverse morphism. -/
@[simp]
theorem canonicalNormalizationAutomorphismSection_inv
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    (canonicalNormalizationAutomorphismSection G a).inv.hom =
      canonicalNormalizationGeometrySection G.obj G.property a.inv.f.hom :=
  rfl

/-- The lifted forward automorphism retains the pointed-doctrine morphism of
the normalized arrow. -/
@[simp]
theorem canonicalNormalizationAutomorphismSection_hom_base_base
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    (canonicalNormalizationAutomorphismSection G a).hom.hom.base.base =
      a.hom.f.hom.base.base :=
  rfl

/-- The lifted forward automorphism retains the coefficient homomorphism of
the normalized arrow. -/
@[simp]
theorem canonicalNormalizationAutomorphismSection_hom_coefficientHom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    (canonicalNormalizationAutomorphismSection G a).hom.hom.geometry.coefficientHom =
      a.hom.f.hom.geometry.coefficientHom :=
  rfl

/-- The automorphism lift is a group homomorphism. -/
noncomputable def canonicalNormalizationAutomorphismSectionHom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    Aut ((geometryNormalizationFunctor.{u, v} U).obj G) →* Aut G where
  toFun := canonicalNormalizationAutomorphismSection G
  map_one' := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact canonicalNormalizationGeometrySection_normalization G.obj G.property
  map_mul' a b := by
    apply Iso.ext
    apply ObjectProperty.hom_ext
    change
      canonicalNormalizationGeometrySection G.obj G.property
          (b.hom.f.hom.comp a.hom.f.hom) =
        (canonicalNormalizationGeometrySection G.obj G.property b.hom.f.hom).comp
          (canonicalNormalizationGeometrySection G.obj G.property a.hom.f.hom)
    exact canonicalNormalizationGeometrySection_comp G.obj G.property
      b.hom.f.hom a.hom.f.hom

/-- Normalizing the lifted automorphism recovers the supplied normalized
automorphism. -/
theorem canonicalNormalizationAutomorphismSection_rightInverse
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    RealizationComparisonIdempotents.functorAutomorphismHom
        (geometryNormalizationFunctor.{u, v} U) G
        (canonicalNormalizationAutomorphismSectionHom G a) = a := by
  apply Iso.ext
  apply Karoubi.Hom.ext
  apply ObjectProperty.hom_ext
  change
    (canonicalAdmissibleGeometryNormalization G ≫
        (canonicalNormalizationAutomorphismSection G a).hom).hom =
      a.hom.f.hom
  let lifted : G ⟶ G :=
    (canonicalNormalizationAutomorphismSection G a).hom
  have habsorption :=
    canonicalAdmissibleGeometryNormalization_absorption lifted
  have hfixed :
      canonicalGeometryNormalization G.obj G.property ≫ a.hom.f.hom ≫
          canonicalGeometryNormalization G.obj G.property =
        a.hom.f.hom := by
    exact congrArg (fun k => k.hom) a.hom.comm
  have hretraction := canonicalNormalizationGeometrySection_retraction
    G.obj G.property a.hom.f.hom hfixed
  calc
    (canonicalAdmissibleGeometryNormalization G ≫ lifted).hom =
        (canonicalAdmissibleGeometryNormalization G ≫ lifted ≫
          canonicalAdmissibleGeometryNormalization G).hom :=
      (congrArg (fun k => k.hom) habsorption).symm
    _ = a.hom.f.hom := hretraction

/-- Apply the complete normalization section independently at both
endpoints. -/
noncomputable def canonicalNormalizationEndpointAutomorphismSectionHom
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (Aut ((geometryNormalizationFunctor.{u, v} U).obj G) ×
      Aut ((geometryNormalizationFunctor.{u, v} U).obj H)) →*
        (Aut G × Aut H) :=
  MonoidHom.prodMap
    (canonicalNormalizationAutomorphismSectionHom G)
    (canonicalNormalizationAutomorphismSectionHom H)

/-- Endpoint normalization followed by the endpoint section is the identity. -/
theorem canonicalNormalizationEndpointAutomorphismSection_rightInverse
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (pair : Aut ((geometryNormalizationFunctor.{u, v} U).obj G) ×
      Aut ((geometryNormalizationFunctor.{u, v} U).obj H)) :
    geometryNormalizationEndpointAutomorphismHom G H
        (canonicalNormalizationEndpointAutomorphismSectionHom G H pair) =
      pair := by
  apply Prod.ext
  · exact canonicalNormalizationAutomorphismSection_rightInverse G pair.1
  · exact canonicalNormalizationAutomorphismSection_rightInverse H pair.2

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
