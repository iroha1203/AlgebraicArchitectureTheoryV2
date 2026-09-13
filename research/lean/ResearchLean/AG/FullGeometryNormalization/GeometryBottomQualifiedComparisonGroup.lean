import ResearchLean.AG.FullGeometryNormalization.ComparisonGroup

/-!
# Bottom-qualified complete-geometry comparison groups

This module lifts G-119's bottom qualification from core packages to complete
geometries.  The raw observation forgets geometry and applies `π V`; the
normalized observation forgets normalized geometry and applies `π_N`.  The
accepted identity `π_N N = π V` therefore remains an equality of the actual
bottom maps, rather than a new preservation premise.

Only the generic restriction of the normalization comparison homomorphism is
constructed here.  No section, reflection, selector specialization, or
exactness claim is included.
-/

open CategoryTheory

namespace AAT.AG.FullGeometryNormalization

open AtomFoundation
open RealizationComparisonIdempotents

universe u v

/-! ## Bottom projections and endpoint observations -/

/-- Raw complete geometries are observed at the bottom by forgetting geometry
and applying G-119's `π V`. -/
noncomputable def rawGeometryBottomProjection (U : AtomCarrier.{u}) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U ⥤
      ExtractionInstance U :=
  admissibleGeometryCoreFunctor.{u, v} U ⋙
    canonicalNormalizationCoreInclusion U ⋙ packageProjection U

/-- Normalized complete geometries are observed at the bottom by forgetting
geometry and applying G-119's `π_N`. -/
noncomputable def normalizedGeometryBottomProjection (U : AtomCarrier.{u}) :
    NormalizedGeometryObject.{u, v} U ⥤ ExtractionInstance U :=
  normalizedGeometryCoreFunctor.{u, v} U ⋙ normalizedPackageProjection U

/-- The complete-geometry form of `π_N N = π V`, on every actual morphism. -/
@[simp]
theorem normalizedGeometryBottomProjection_normalization_map
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (f : G ⟶ H) :
    (normalizedGeometryBottomProjection.{u, v} U).map
        ((geometryNormalizationFunctor.{u, v} U).map f) =
      (rawGeometryBottomProjection.{u, v} U).map f := by
  simpa [rawGeometryBottomProjection, normalizedGeometryBottomProjection] using
    normalizedPackageProjection_normalization_map
      ((admissibleGeometryCoreFunctor.{u, v} U).map f)

/-- The complete-geometry functor identity `π_N ∘ N_geom = π V ρ`. -/
theorem normalizedGeometryBottomProjection_normalization_eq
    {U : AtomCarrier.{u}} :
    geometryNormalizationFunctor.{u, v} U ⋙
        normalizedGeometryBottomProjection.{u, v} U =
      rawGeometryBottomProjection.{u, v} U := by
  exact CategoryTheory.Functor.ext
    (fun _ => rfl)
    (fun _ _ f => normalizedGeometryBottomProjection_normalization_map f)

/-- Bottom observation of a raw complete-geometry endpoint automorphism. -/
noncomputable def rawGeometryBottomAutomorphismHom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    Aut G →* Aut ((rawGeometryBottomProjection.{u, v} U).obj G) :=
  functorAutomorphismHom (rawGeometryBottomProjection.{u, v} U) G

/-- Evaluation of raw bottom observation on the underlying automorphism. -/
@[simp]
theorem rawGeometryBottomAutomorphismHom_hom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) (a : Aut G) :
    (rawGeometryBottomAutomorphismHom G a).hom =
      (rawGeometryBottomProjection.{u, v} U).map a.hom :=
  rfl

/-- Bottom observation of a normalized complete-geometry endpoint
automorphism. -/
noncomputable def normalizedGeometryBottomAutomorphismHom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    Aut ((geometryNormalizationFunctor.{u, v} U).obj G) →*
      Aut ((normalizedGeometryBottomProjection.{u, v} U).obj
        ((geometryNormalizationFunctor.{u, v} U).obj G)) :=
  functorAutomorphismHom (normalizedGeometryBottomProjection.{u, v} U)
    ((geometryNormalizationFunctor.{u, v} U).obj G)

/-- Evaluation of normalized bottom observation on the underlying
automorphism. -/
@[simp]
theorem normalizedGeometryBottomAutomorphismHom_hom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    (normalizedGeometryBottomAutomorphismHom G a).hom =
      (normalizedGeometryBottomProjection.{u, v} U).map a.hom :=
  rfl

/-! ## Endpoint and comparison subgroups -/

/-- Raw endpoint automorphisms invisible at the bottom. -/
noncomputable def rawGeometryBottomEndpointSubgroup
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) : Subgroup (Aut G) :=
  (rawGeometryBottomAutomorphismHom G).ker

/-- Membership in the raw bottom endpoint subgroup is bottom identity. -/
theorem mem_rawGeometryBottomEndpointSubgroup
    {U : AtomCarrier.{u}}
    {G : CanonicalNormalizationAdmissibleGeometry.{u, v} U} {a : Aut G} :
    a ∈ rawGeometryBottomEndpointSubgroup G ↔
      rawGeometryBottomAutomorphismHom G a = 1 :=
  Iff.rfl

/-- Normalized endpoint automorphisms invisible at the bottom. -/
noncomputable def normalizedGeometryBottomEndpointSubgroup
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    Subgroup (Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :=
  (normalizedGeometryBottomAutomorphismHom G).ker

/-- Membership in the normalized bottom endpoint subgroup is bottom
identity. -/
theorem mem_normalizedGeometryBottomEndpointSubgroup
    {U : AtomCarrier.{u}}
    {G : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    {a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)} :
    a ∈ normalizedGeometryBottomEndpointSubgroup G ↔
      normalizedGeometryBottomAutomorphismHom G a = 1 :=
  Iff.rfl

/-- Source projection from a raw complete-geometry comparison subgroup. -/
noncomputable def rawGeometryComparisonSourceHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    rawGeometryNormalizationComparisonSubgroup c →* Aut G :=
  (MonoidHom.fst (Aut G) (Aut H)).comp
    (rawGeometryNormalizationComparisonSubgroup c).subtype

/-- Target projection from a raw complete-geometry comparison subgroup. -/
noncomputable def rawGeometryComparisonTargetHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    rawGeometryNormalizationComparisonSubgroup c →* Aut H :=
  (MonoidHom.snd (Aut G) (Aut H)).comp
    (rawGeometryNormalizationComparisonSubgroup c).subtype

/-- Source projection from a normalized complete-geometry comparison
subgroup. -/
noncomputable def normalizedGeometryComparisonSourceHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    normalizedGeometryComparisonSubgroup c →*
      Aut ((geometryNormalizationFunctor.{u, v} U).obj G) :=
  (MonoidHom.fst _ _).comp (normalizedGeometryComparisonSubgroup c).subtype

/-- Target projection from a normalized complete-geometry comparison
subgroup. -/
noncomputable def normalizedGeometryComparisonTargetHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    normalizedGeometryComparisonSubgroup c →*
      Aut ((geometryNormalizationFunctor.{u, v} U).obj H) :=
  (MonoidHom.snd _ _).comp (normalizedGeometryComparisonSubgroup c).subtype

/-- Raw comparison-preserving pairs whose endpoint actions are both invisible
at the bottom. -/
noncomputable def rawGeometryBottomQualifiedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    Subgroup (rawGeometryNormalizationComparisonSubgroup c) :=
  Subgroup.comap (rawGeometryComparisonSourceHom c)
      (rawGeometryBottomAutomorphismHom G).ker ⊓
    Subgroup.comap (rawGeometryComparisonTargetHom c)
      (rawGeometryBottomAutomorphismHom H).ker

/-- Raw bottom qualification is exactly bottom identity at both endpoints. -/
theorem mem_rawGeometryBottomQualifiedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} {c : G ⟶ H}
    {pair : rawGeometryNormalizationComparisonSubgroup c} :
    pair ∈ rawGeometryBottomQualifiedComparisonSubgroup c ↔
      rawGeometryBottomAutomorphismHom G pair.1.1 = 1 ∧
        rawGeometryBottomAutomorphismHom H pair.1.2 = 1 :=
  Iff.rfl

/-- Normalized comparison-preserving pairs whose endpoint actions are both
invisible at the bottom. -/
noncomputable def normalizedGeometryBottomQualifiedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    Subgroup (normalizedGeometryComparisonSubgroup c) :=
  Subgroup.comap (normalizedGeometryComparisonSourceHom c)
      (normalizedGeometryBottomAutomorphismHom G).ker ⊓
    Subgroup.comap (normalizedGeometryComparisonTargetHom c)
      (normalizedGeometryBottomAutomorphismHom H).ker

/-- Normalized bottom qualification is exactly bottom identity at both
endpoints. -/
theorem mem_normalizedGeometryBottomQualifiedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} {c : G ⟶ H}
    {pair : normalizedGeometryComparisonSubgroup c} :
    pair ∈ normalizedGeometryBottomQualifiedComparisonSubgroup c ↔
      normalizedGeometryBottomAutomorphismHom G pair.1.1 = 1 ∧
        normalizedGeometryBottomAutomorphismHom H pair.1.2 = 1 :=
  Iff.rfl

/-! ## Preservation and restricted normalization -/

/-- The identity `π_N N_geom = π V ρ` preserves bottom-trivial endpoint
automorphisms. -/
theorem geometryNormalizationEndpointAutomorphism_preserves_bottom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) (a : Aut G)
    (h : rawGeometryBottomAutomorphismHom G a = 1) :
    normalizedGeometryBottomAutomorphismHom G
        (functorAutomorphismHom (geometryNormalizationFunctor.{u, v} U) G a) =
      1 := by
  apply Iso.ext
  change (normalizedGeometryBottomProjection.{u, v} U).map
      ((geometryNormalizationFunctor.{u, v} U).map a.hom) = 𝟙 _
  rw [normalizedGeometryBottomProjection_normalization_map]
  have bottomIdentity := congrArg Iso.hom h
  exact bottomIdentity

set_option synthInstance.maxHeartbeats 100000 in
/-- Canonical normalization restricted to bottom-qualified complete-geometry
comparison subgroups. -/
noncomputable def geometryNormalizationBottomQualifiedComparisonSubgroupHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    rawGeometryBottomQualifiedComparisonSubgroup c →*
      normalizedGeometryBottomQualifiedComparisonSubgroup c where
  toFun pair := by
    refine ⟨geometryNormalizationComparisonSubgroupHom c pair.1, ?_⟩
    constructor
    · exact geometryNormalizationEndpointAutomorphism_preserves_bottom
        G pair.1.1.1 pair.2.1
    · exact geometryNormalizationEndpointAutomorphism_preserves_bottom
        H pair.1.1.2 pair.2.2
  map_one' := by
    apply Subtype.ext
    exact map_one (geometryNormalizationComparisonSubgroupHom c)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (geometryNormalizationComparisonSubgroupHom c) a.1 b.1

/-- Evaluation of the bottom-qualified restriction retains the underlying
comparison-subgroup normalization value. -/
@[simp]
theorem geometryNormalizationBottomQualifiedComparisonSubgroupHom_val
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H)
    (pair : rawGeometryBottomQualifiedComparisonSubgroup c) :
    (geometryNormalizationBottomQualifiedComparisonSubgroupHom c pair).1 =
      geometryNormalizationComparisonSubgroupHom c pair.1 :=
  rfl

/-! ## Agreement with the core-package APIs -/

/-- Raw geometry bottom observation agrees with first projecting the endpoint
automorphism to G-119's core-package automorphism. -/
theorem rawGeometryBottomAutomorphismHom_core_agrees
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) (a : Aut G) :
    rawGeometryBottomAutomorphismHom G a =
      rawNormalizationBottomAutomorphismHom
        ((admissibleGeometryCoreFunctor.{u, v} U).obj G)
        (functorAutomorphismHom (admissibleGeometryCoreFunctor.{u, v} U) G a) :=
  rfl

/-- Normalized geometry bottom observation agrees with first projecting the
endpoint automorphism to G-119's normalized core-package automorphism. -/
theorem normalizedGeometryBottomAutomorphismHom_core_agrees
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    normalizedGeometryBottomAutomorphismHom G a =
      normalizedBottomAutomorphismHom
        ((admissibleGeometryCoreFunctor.{u, v} U).obj G)
        (functorAutomorphismHom (normalizedGeometryCoreFunctor.{u, v} U)
          ((geometryNormalizationFunctor.{u, v} U).obj G) a) :=
  rfl

/-- The underlying raw endpoint pair of the geometry restriction is exactly
the pair seen by G-119's core comparison API. -/
@[simp]
theorem rawGeometryBottomQualified_core_pair
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} {c : G ⟶ H}
    (pair : rawGeometryBottomQualifiedComparisonSubgroup c) :
    (rawGeometryComparisonCoreHom c pair.1).1 =
      geometryCoreEndpointAutomorphismHom G H pair.1.1 :=
  rfl

/-- The underlying normalized endpoint pair of the geometry restriction is
exactly the pair seen by G-119's normalized core comparison API. -/
@[simp]
theorem normalizedGeometryBottomQualified_core_pair
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} {c : G ⟶ H}
    (pair : normalizedGeometryBottomQualifiedComparisonSubgroup c) :
    (normalizedGeometryComparisonCoreHom c pair.1).1 =
      normalizedGeometryCoreEndpointAutomorphismHom G H pair.1.1 :=
  rfl

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
