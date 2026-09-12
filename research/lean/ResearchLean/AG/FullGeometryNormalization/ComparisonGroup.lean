import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalization
import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationComparisonGroup

/-!
# Complete-geometry normalization comparison groups

This module completes G-122(A)'s connection from the canonical normalization
of complete geometries to G-119's Karoubi objects, arrows, and comparison-group
construction.

## Implementation notes

The geometry comparison groups use exactly G-119's standard construction:
endpoint automorphism products, the equation preserving the selected arrow,
and restriction of the functor-induced endpoint homomorphism.  Core projection
then gives homomorphisms to G-119's accepted raw and normalized comparison
subgroups.  The final commuting theorem compares the complete endpoint pair,
not only one projection or an equality of carrier sets.
-/

open CategoryTheory
open CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

open AtomFoundation
open GeometryTransport
open RealizationComparisonIdempotents

universe u v

/-! ## Karoubi connection to G-119 -/

/-- Core projection extended to Karoubi objects of admissible complete
geometries. -/
noncomputable def admissibleGeometryCoreKaroubiFunctor
    (U : AtomCarrier.{u}) :
    Karoubi (CanonicalNormalizationAdmissibleGeometry.{u, v} U) ⥤
      Karoubi (CanonicalNormalizationAdmissiblePackage U) :=
  (functorExtension₂ _ _).obj (admissibleGeometryCoreFunctor.{u, v} U)

/-- G-122(A): the Karoubi image of `(G,n_G)` is exactly G-119's
`(G.core,n_G.core)`. -/
@[simp]
theorem admissibleGeometryCoreKaroubiFunctor_normalizedObject
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (admissibleGeometryCoreKaroubiFunctor.{u, v} U).obj
        (normalizedGeometryKaroubiObject G) =
      normalizedPackageKaroubiObject
        ((admissibleGeometryCoreFunctor.{u, v} U).obj G) :=
  rfl

/-- G-122(A): core projection sends every normalized complete-geometry
sandwich arrow to its full underlying G-119 sandwich arrow. -/
@[simp]
theorem admissibleGeometryCoreKaroubiFunctor_normalizedMap
    {U : AtomCarrier.{u}}
    {G H : NormalizedGeometryObject.{u, v} U} (f : G ⟶ H) :
    (admissibleGeometryCoreKaroubiFunctor.{u, v} U).map
        ((normalizedGeometryKaroubiFunctor.{u, v} U).map f) =
      (normalizedPackageKaroubiFunctor U).map
        ((normalizedGeometryCoreFunctor.{u, v} U).map f) :=
  rfl

/-! ## Complete-geometry comparison groups -/

/-- `N_geom` induces a homomorphism on each pair of complete-geometry
endpoint automorphism groups. -/
noncomputable def geometryNormalizationEndpointAutomorphismHom
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (Aut G × Aut H) →*
      (Aut ((geometryNormalizationFunctor.{u, v} U).obj G) ×
        Aut ((geometryNormalizationFunctor.{u, v} U).obj H)) :=
  MonoidHom.prodMap
    (functorAutomorphismHom (geometryNormalizationFunctor.{u, v} U) G)
    (functorAutomorphismHom (geometryNormalizationFunctor.{u, v} U) H)

/-- Raw complete-geometry endpoint pairs preserving the selected comparison
`c`. -/
def rawGeometryNormalizationComparisonSubgroup
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    Subgroup (Aut G × Aut H) where
  carrier pair := pair.1.hom ≫ c = c ≫ pair.2.hom
  one_mem' := by rfl
  mul_mem' := by
    rintro ⟨p₁, b₁⟩ ⟨p₂, b₂⟩ first second
    change (p₂.hom ≫ p₁.hom) ≫ c = c ≫ (b₂.hom ≫ b₁.hom)
    rw [Category.assoc, first, ← Category.assoc, second, Category.assoc]
  inv_mem' := by
    rintro ⟨p, b⟩ relation
    change p.inv ≫ c = c ≫ b.inv
    calc
      p.inv ≫ c = p.inv ≫ ((c ≫ b.hom) ≫ b.inv) := by simp
      _ = p.inv ≫ ((p.hom ≫ c) ≫ b.inv) := by rw [relation]
      _ = c ≫ b.inv := by simp

/-- Membership in the raw geometry comparison group is exactly the endpoint
commuting-square equation. -/
theorem mem_rawGeometryNormalizationComparisonSubgroup
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    {c : G ⟶ H} {pair : Aut G × Aut H} :
    pair ∈ rawGeometryNormalizationComparisonSubgroup c ↔
      pair.1.hom ≫ c = c ≫ pair.2.hom :=
  Iff.rfl

/-- Normalized complete-geometry endpoint pairs preserving `N_geom(c)`. -/
def normalizedGeometryComparisonSubgroup
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    Subgroup
      (Aut ((geometryNormalizationFunctor.{u, v} U).obj G) ×
        Aut ((geometryNormalizationFunctor.{u, v} U).obj H)) where
  carrier pair :=
    pair.1.hom ≫ (geometryNormalizationFunctor.{u, v} U).map c =
      (geometryNormalizationFunctor.{u, v} U).map c ≫ pair.2.hom
  one_mem' := by
    change (𝟙 _ : _ ⟶ _) ≫ _ = _ ≫ (𝟙 _ : _ ⟶ _)
    rw [Category.id_comp, Category.comp_id]
  mul_mem' := by
    rintro ⟨p₁, b₁⟩ ⟨p₂, b₂⟩ first second
    change (p₂.hom ≫ p₁.hom) ≫ _ = _ ≫ (b₂.hom ≫ b₁.hom)
    rw [Category.assoc, first, ← Category.assoc, second, Category.assoc]
  inv_mem' := by
    rintro ⟨p, b⟩ relation
    change p.inv ≫ _ = _ ≫ b.inv
    calc
      p.inv ≫ (geometryNormalizationFunctor.{u, v} U).map c =
          p.inv ≫
            (((geometryNormalizationFunctor.{u, v} U).map c ≫ b.hom) ≫
              b.inv) := by simp
      _ = p.inv ≫
          ((p.hom ≫ (geometryNormalizationFunctor.{u, v} U).map c) ≫
            b.inv) := by rw [relation]
      _ = (geometryNormalizationFunctor.{u, v} U).map c ≫ b.inv := by simp

/-- Functoriality of `N_geom` carries each raw geometry comparison-preserving
pair to a normalized one. -/
theorem geometryNormalizationEndpointAutomorphism_preserves_comparison
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H)
    (pair : Aut G × Aut H)
    (h : pair ∈ rawGeometryNormalizationComparisonSubgroup c) :
    geometryNormalizationEndpointAutomorphismHom G H pair ∈
      normalizedGeometryComparisonSubgroup c := by
  have mapped := congrArg
    (fun k => (geometryNormalizationFunctor.{u, v} U).map k) h
  simpa only [geometryNormalizationEndpointAutomorphismHom,
    functorAutomorphismHom, Functor.map_comp] using mapped

/-- G-122(A)'s restriction of the complete endpoint normalization
homomorphism to comparison-preserving subgroups. -/
noncomputable def geometryNormalizationComparisonSubgroupHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    rawGeometryNormalizationComparisonSubgroup c →*
      normalizedGeometryComparisonSubgroup c where
  toFun pair :=
    ⟨geometryNormalizationEndpointAutomorphismHom G H pair.1,
      geometryNormalizationEndpointAutomorphism_preserves_comparison
        c pair.1 pair.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (geometryNormalizationEndpointAutomorphismHom G H)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (geometryNormalizationEndpointAutomorphismHom G H) a.1 b.1

/-! ## Core projection of the comparison groups -/

/-- Core projection on a pair of raw complete-geometry endpoint
automorphisms. -/
noncomputable def geometryCoreEndpointAutomorphismHom
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (Aut G × Aut H) →*
      (Aut ((admissibleGeometryCoreFunctor.{u, v} U).obj G) ×
        Aut ((admissibleGeometryCoreFunctor.{u, v} U).obj H)) :=
  MonoidHom.prodMap
    (functorAutomorphismHom (admissibleGeometryCoreFunctor.{u, v} U) G)
    (functorAutomorphismHom (admissibleGeometryCoreFunctor.{u, v} U) H)

/-- Core projection sends raw geometry pairs preserving `c` to G-119's raw
comparison subgroup for the projected comparison. -/
theorem geometryCoreEndpointAutomorphism_preserves_comparison
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H)
    (pair : Aut G × Aut H)
    (h : pair ∈ rawGeometryNormalizationComparisonSubgroup c) :
    geometryCoreEndpointAutomorphismHom G H pair ∈
      rawNormalizationComparisonSubgroup
        ((admissibleGeometryCoreFunctor.{u, v} U).map c) := by
  have mapped := congrArg
    (fun k => (admissibleGeometryCoreFunctor.{u, v} U).map k) h
  simpa only [geometryCoreEndpointAutomorphismHom,
    functorAutomorphismHom, Functor.map_comp] using mapped

/-- Restrict raw core projection to the complete-geometry and G-119 raw
comparison subgroups. -/
noncomputable def rawGeometryComparisonCoreHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    rawGeometryNormalizationComparisonSubgroup c →*
      rawNormalizationComparisonSubgroup
        ((admissibleGeometryCoreFunctor.{u, v} U).map c) where
  toFun pair :=
    ⟨geometryCoreEndpointAutomorphismHom G H pair.1,
      geometryCoreEndpointAutomorphism_preserves_comparison c pair.1 pair.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (geometryCoreEndpointAutomorphismHom G H)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (geometryCoreEndpointAutomorphismHom G H) a.1 b.1

/-- Core projection on normalized complete-geometry endpoint
automorphisms. -/
noncomputable def normalizedGeometryCoreEndpointAutomorphismHom
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    (Aut ((geometryNormalizationFunctor.{u, v} U).obj G) ×
      Aut ((geometryNormalizationFunctor.{u, v} U).obj H)) →*
      (Aut ((packageNormalizationFunctor U).obj
          ((admissibleGeometryCoreFunctor.{u, v} U).obj G)) ×
        Aut ((packageNormalizationFunctor U).obj
          ((admissibleGeometryCoreFunctor.{u, v} U).obj H))) :=
  MonoidHom.prodMap
    (functorAutomorphismHom (normalizedGeometryCoreFunctor.{u, v} U)
      ((geometryNormalizationFunctor.{u, v} U).obj G))
    (functorAutomorphismHom (normalizedGeometryCoreFunctor.{u, v} U)
      ((geometryNormalizationFunctor.{u, v} U).obj H))

/-- Core projection sends normalized geometry pairs preserving `N_geom(c)`
to G-119's normalized comparison subgroup. -/
theorem normalizedGeometryCoreEndpointAutomorphism_preserves_comparison
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H)
    (pair : Aut ((geometryNormalizationFunctor.{u, v} U).obj G) ×
      Aut ((geometryNormalizationFunctor.{u, v} U).obj H))
    (h : pair ∈ normalizedGeometryComparisonSubgroup c) :
    normalizedGeometryCoreEndpointAutomorphismHom G H pair ∈
      normalizedComparisonSubgroup
        ((admissibleGeometryCoreFunctor.{u, v} U).map c) := by
  have mapped := congrArg
    (fun k => (normalizedGeometryCoreFunctor.{u, v} U).map k) h
  simpa only [normalizedGeometryCoreEndpointAutomorphismHom,
    functorAutomorphismHom, Functor.map_comp,
    normalizedGeometryCoreFunctor_geometryNormalizationFunctor_map] using mapped

/-- Restrict normalized core projection to the complete-geometry and G-119
normalized comparison subgroups. -/
noncomputable def normalizedGeometryComparisonCoreHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    normalizedGeometryComparisonSubgroup c →*
      normalizedComparisonSubgroup
        ((admissibleGeometryCoreFunctor.{u, v} U).map c) where
  toFun pair :=
    ⟨normalizedGeometryCoreEndpointAutomorphismHom G H pair.1,
      normalizedGeometryCoreEndpointAutomorphism_preserves_comparison
        c pair.1 pair.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (normalizedGeometryCoreEndpointAutomorphismHom G H)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (normalizedGeometryCoreEndpointAutomorphismHom G H) a.1 b.1

/-- G-122(A): normalization of comparison-preserving complete-geometry
endpoint changes commutes with projection to G-119's comparison-group
homomorphism. -/
theorem geometryNormalizationComparisonSubgroupHom_core_commutes
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H)
    (pair : rawGeometryNormalizationComparisonSubgroup c) :
    normalizedGeometryComparisonCoreHom c
        (geometryNormalizationComparisonSubgroupHom c pair) =
      normalizationComparisonSubgroupHom
        ((admissibleGeometryCoreFunctor.{u, v} U).map c)
        (rawGeometryComparisonCoreHom c pair) := by
  rfl

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
