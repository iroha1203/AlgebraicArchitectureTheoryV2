import ResearchLean.AG.RealizationComparisonIdempotents.MaximalSubgroupoid
import ResearchLean.AG.CrossStageCoherence.Basic

/-!
# The three-stage AAT projection tower

This file constructs G-119(B1).  Clause A is specialized to the geometry,
core-package, and pointed-extraction categories.  The two existing projections
and their existing composite act on Karoubi objects and comparison objects, and
the comparison naturality for the composite is identified with the two
stagewise components.

## Implementation notes

The composite is the existing `crossStageProjection`; it is not redefined.
The induced Karoubi actions use mathlib's `functorExtension₂`, and comparison
actions use the clause-A `arrowKaroubiMap`.  Field-level evaluation theorems
are recorded so that later qualified-group arguments can read the actual
`.base` and `.base.base` projections without unfolding these functors.  Merely
renaming the generic clause-A constructions was rejected because it would not
fix their action on the AAT projection tower.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation GeometryTransport CrossStageCoherence

universe u v

variable (U : AtomCarrier.{u})

/-- Clause A specialized to the geometry-stage category. -/
noncomputable def geometryKaroubiArrowEquivalence :
    Karoubi (Arrow (GeomReadCategory.{u, v} U)) ≌
      RealizationComparisonCategory (GeomReadCategory.{u, v} U) :=
  karoubiArrowEquivalence

/-- Clause A specialized to the core-package category. -/
noncomputable def packageKaroubiArrowEquivalence :
    Karoubi (Arrow (AATCorePackage U)) ≌
      RealizationComparisonCategory (AATCorePackage U) :=
  karoubiArrowEquivalence

/-- Clause A specialized to the pointed-extraction category. -/
noncomputable def extractionKaroubiArrowEquivalence :
    Karoubi (Arrow (ExtractionInstance U)) ≌
      RealizationComparisonCategory (ExtractionInstance U) :=
  karoubiArrowEquivalence

/-- The geometry projection acting on arbitrary Karoubi objects. -/
noncomputable def geometryKaroubiProjection :
    Karoubi (GeomReadCategory.{u, v} U) ⥤ Karoubi (AATCorePackage U) :=
  (functorExtension₂ _ _).obj (geometryProjection U)

/-- The package projection acting on arbitrary Karoubi objects. -/
noncomputable def packageKaroubiProjection :
    Karoubi (AATCorePackage U) ⥤ Karoubi (ExtractionInstance U) :=
  (functorExtension₂ _ _).obj (packageProjection U)

/-- The composite projection acting on arbitrary Karoubi objects. -/
noncomputable def crossStageKaroubiProjection :
    Karoubi (GeomReadCategory.{u, v} U) ⥤ Karoubi (ExtractionInstance U) :=
  (functorExtension₂ _ _).obj (crossStageProjection U)

/-- The geometry projection acting on comparison objects. -/
noncomputable def geometryComparisonProjection :
    RealizationComparisonCategory (GeomReadCategory.{u, v} U) ⥤
      RealizationComparisonCategory (AATCorePackage U) :=
  arrowKaroubiMap (geometryProjection U)

/-- The package projection acting on comparison objects. -/
noncomputable def packageComparisonProjection :
    RealizationComparisonCategory (AATCorePackage U) ⥤
      RealizationComparisonCategory (ExtractionInstance U) :=
  arrowKaroubiMap (packageProjection U)

/-- The composite projection acting on comparison objects. -/
noncomputable def crossStageComparisonProjection :
    RealizationComparisonCategory (GeomReadCategory.{u, v} U) ⥤
      RealizationComparisonCategory (ExtractionInstance U) :=
  arrowKaroubiMap (crossStageProjection U)

/-- The declared cross-stage projection is the geometry projection followed by the package projection. -/
theorem crossStageProjection_eq_geometry_comp_package :
    crossStageProjection U = geometryProjection U ⋙ packageProjection U :=
  rfl

/-- The two Karoubi-stage projections compose to the declared composite projection. -/
theorem geometryPackageKaroubiProjection_comp :
    geometryKaroubiProjection U ⋙ packageKaroubiProjection U =
      crossStageKaroubiProjection U :=
  rfl

/-- The two comparison-stage projections compose to the declared composite projection. -/
theorem geometryPackageComparisonProjection_comp :
    geometryComparisonProjection U ⋙ packageComparisonProjection U =
      crossStageComparisonProjection U :=
  rfl

/-- Normalization rule: geometry projection retains the underlying core package. -/
@[simp]
theorem geometryKaroubiProjection_obj_X
    (P : Karoubi (GeomReadCategory.{u, v} U)) :
    ((geometryKaroubiProjection U).obj P).X = P.X.core :=
  rfl

/-- Normalization rule: geometry projection sends an idempotent to its core map. -/
@[simp]
theorem geometryKaroubiProjection_obj_p
    (P : Karoubi (GeomReadCategory.{u, v} U)) :
    ((geometryKaroubiProjection U).obj P).p = P.p.base :=
  rfl

/-- Normalization rule: package projection retains the pointed extraction object. -/
@[simp]
theorem packageKaroubiProjection_obj_X (P : Karoubi (AATCorePackage U)) :
    ((packageKaroubiProjection U).obj P).X = packagePoint P.X :=
  rfl

/-- Normalization rule: package projection sends an idempotent to its base map. -/
@[simp]
theorem packageKaroubiProjection_obj_p (P : Karoubi (AATCorePackage U)) :
    ((packageKaroubiProjection U).obj P).p = P.p.base :=
  rfl

/-- Normalization rule: the composite retains the pointed extraction under a geometry object. -/
@[simp]
theorem crossStageKaroubiProjection_obj_X
    (P : Karoubi (GeomReadCategory.{u, v} U)) :
    ((crossStageKaroubiProjection U).obj P).X = packagePoint P.X.core :=
  rfl

/-- Normalization rule: the composite sends an idempotent through both base maps. -/
@[simp]
theorem crossStageKaroubiProjection_obj_p
    (P : Karoubi (GeomReadCategory.{u, v} U)) :
    ((crossStageKaroubiProjection U).obj P).p = P.p.base.base :=
  rfl

/-- Normalization rule: geometry Karoubi projection sends a morphism through its core map. -/
@[simp]
theorem geometryKaroubiProjection_map_f
    {P Q : Karoubi (GeomReadCategory.{u, v} U)} (f : P ⟶ Q) :
    ((geometryKaroubiProjection U).map f).f = f.f.base :=
  rfl

/-- Normalization rule: package Karoubi projection sends a morphism through its base map. -/
@[simp]
theorem packageKaroubiProjection_map_f
    {P Q : Karoubi (AATCorePackage U)} (f : P ⟶ Q) :
    ((packageKaroubiProjection U).map f).f = f.f.base :=
  rfl

/-- Normalization rule: composite Karoubi projection sends a morphism through both base maps. -/
@[simp]
theorem crossStageKaroubiProjection_map_f
    {P Q : Karoubi (GeomReadCategory.{u, v} U)} (f : P ⟶ Q) :
    ((crossStageKaroubiProjection U).map f).f = f.f.base.base :=
  rfl

/-- Normalization rule: geometry comparison projection retains the source core package. -/
@[simp]
theorem geometryComparisonProjection_obj_left_X
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((geometryComparisonProjection U).obj C).left.X = C.left.X.core :=
  rfl

/-- Normalization rule: geometry comparison projection sends the source idempotent to its core map. -/
@[simp]
theorem geometryComparisonProjection_obj_left_p
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((geometryComparisonProjection U).obj C).left.p = C.left.p.base :=
  rfl

/-- Normalization rule: geometry comparison projection retains the target core package. -/
@[simp]
theorem geometryComparisonProjection_obj_right_X
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((geometryComparisonProjection U).obj C).right.X = C.right.X.core :=
  rfl

/-- Normalization rule: geometry comparison projection sends the target idempotent to its core map. -/
@[simp]
theorem geometryComparisonProjection_obj_right_p
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((geometryComparisonProjection U).obj C).right.p = C.right.p.base :=
  rfl

/-- Normalization rule: geometry comparison projection sends the comparison through its core map. -/
@[simp]
theorem geometryComparisonProjection_obj_hom_f
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((geometryComparisonProjection U).obj C).hom.f = C.hom.f.base :=
  rfl

/-- Normalization rule: geometry comparison projection sends a source endpoint map to its core map. -/
@[simp]
theorem geometryComparisonProjection_map_left_f
    {C D : RealizationComparisonCategory (GeomReadCategory.{u, v} U)}
    (f : C ⟶ D) :
    ((geometryComparisonProjection U).map f).left.f = f.left.f.base :=
  rfl

/-- Normalization rule: geometry comparison projection sends a target endpoint map to its core map. -/
@[simp]
theorem geometryComparisonProjection_map_right_f
    {C D : RealizationComparisonCategory (GeomReadCategory.{u, v} U)}
    (f : C ⟶ D) :
    ((geometryComparisonProjection U).map f).right.f = f.right.f.base :=
  rfl

/-- Normalization rule: package comparison projection retains the source pointed extraction. -/
@[simp]
theorem packageComparisonProjection_obj_left_X
    (C : RealizationComparisonCategory (AATCorePackage U)) :
    ((packageComparisonProjection U).obj C).left.X = packagePoint C.left.X :=
  rfl

/-- Normalization rule: package comparison projection sends the source idempotent to its base map. -/
@[simp]
theorem packageComparisonProjection_obj_left_p
    (C : RealizationComparisonCategory (AATCorePackage U)) :
    ((packageComparisonProjection U).obj C).left.p = C.left.p.base :=
  rfl

/-- Normalization rule: package comparison projection retains the target pointed extraction. -/
@[simp]
theorem packageComparisonProjection_obj_right_X
    (C : RealizationComparisonCategory (AATCorePackage U)) :
    ((packageComparisonProjection U).obj C).right.X = packagePoint C.right.X :=
  rfl

/-- Normalization rule: package comparison projection sends the target idempotent to its base map. -/
@[simp]
theorem packageComparisonProjection_obj_right_p
    (C : RealizationComparisonCategory (AATCorePackage U)) :
    ((packageComparisonProjection U).obj C).right.p = C.right.p.base :=
  rfl

/-- Normalization rule: package comparison projection sends the comparison through its base map. -/
@[simp]
theorem packageComparisonProjection_obj_hom_f
    (C : RealizationComparisonCategory (AATCorePackage U)) :
    ((packageComparisonProjection U).obj C).hom.f = C.hom.f.base :=
  rfl

/-- Normalization rule: package comparison projection sends a source endpoint map to its base map. -/
@[simp]
theorem packageComparisonProjection_map_left_f
    {C D : RealizationComparisonCategory (AATCorePackage U)} (f : C ⟶ D) :
    ((packageComparisonProjection U).map f).left.f = f.left.f.base :=
  rfl

/-- Normalization rule: package comparison projection sends a target endpoint map to its base map. -/
@[simp]
theorem packageComparisonProjection_map_right_f
    {C D : RealizationComparisonCategory (AATCorePackage U)} (f : C ⟶ D) :
    ((packageComparisonProjection U).map f).right.f = f.right.f.base :=
  rfl

/-- Normalization rule: the composite retains the source pointed extraction. -/
@[simp]
theorem crossStageComparisonProjection_obj_left_X
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((crossStageComparisonProjection U).obj C).left.X =
      packagePoint C.left.X.core :=
  rfl

/-- Normalization rule: the composite sends the source idempotent through both base maps. -/
@[simp]
theorem crossStageComparisonProjection_obj_left_p
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((crossStageComparisonProjection U).obj C).left.p = C.left.p.base.base :=
  rfl

/-- Normalization rule: the composite retains the target pointed extraction. -/
@[simp]
theorem crossStageComparisonProjection_obj_right_X
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((crossStageComparisonProjection U).obj C).right.X =
      packagePoint C.right.X.core :=
  rfl

/-- Normalization rule: the composite sends the target idempotent through both base maps. -/
@[simp]
theorem crossStageComparisonProjection_obj_right_p
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((crossStageComparisonProjection U).obj C).right.p = C.right.p.base.base :=
  rfl

/-- Normalization rule: the composite sends the comparison through both base maps. -/
@[simp]
theorem crossStageComparisonProjection_obj_hom_f
    (C : RealizationComparisonCategory (GeomReadCategory.{u, v} U)) :
    ((crossStageComparisonProjection U).obj C).hom.f = C.hom.f.base.base :=
  rfl

/-- Normalization rule: composite comparison projection sends a source endpoint through both base maps. -/
@[simp]
theorem crossStageComparisonProjection_map_left_f
    {C D : RealizationComparisonCategory (GeomReadCategory.{u, v} U)}
    (f : C ⟶ D) :
    ((crossStageComparisonProjection U).map f).left.f = f.left.f.base.base :=
  rfl

/-- Normalization rule: composite comparison projection sends a target endpoint through both base maps. -/
@[simp]
theorem crossStageComparisonProjection_map_right_f
    {C D : RealizationComparisonCategory (GeomReadCategory.{u, v} U)}
    (f : C ⟶ D) :
    ((crossStageComparisonProjection U).map f).right.f = f.right.f.base.base :=
  rfl

/-- Clause A naturality specialized to the geometry projection. -/
noncomputable def geometryProjectionKaroubiArrowNaturalityIso :
    karoubiArrowNaturalityLeft (geometryProjection U) ≅
      karoubiArrowNaturalityRight (geometryProjection U) :=
  karoubiArrowNaturalityIso (geometryProjection U)

/-- Clause A naturality specialized to the package projection. -/
noncomputable def packageProjectionKaroubiArrowNaturalityIso :
    karoubiArrowNaturalityLeft (packageProjection U) ≅
      karoubiArrowNaturalityRight (packageProjection U) :=
  karoubiArrowNaturalityIso (packageProjection U)

/-- Clause A naturality specialized to the composite projection. -/
noncomputable def crossStageProjectionKaroubiArrowNaturalityIso :
    karoubiArrowNaturalityLeft (crossStageProjection U) ≅
      karoubiArrowNaturalityRight (crossStageProjection U) :=
  karoubiArrowNaturalityIso (crossStageProjection U)

/-- Normalization rule: composite naturality uses the twice-projected source idempotent. -/
@[simp]
theorem crossStageProjectionKaroubiArrowNaturalityIso_hom_app_left_f
    (P : Karoubi (Arrow (GeomReadCategory.{u, v} U))) :
    ((crossStageProjectionKaroubiArrowNaturalityIso U).hom.app P).left.f =
      P.p.left.base.base :=
  rfl

/-- Normalization rule: composite naturality uses the twice-projected target idempotent. -/
@[simp]
theorem crossStageProjectionKaroubiArrowNaturalityIso_hom_app_right_f
    (P : Karoubi (Arrow (GeomReadCategory.{u, v} U))) :
    ((crossStageProjectionKaroubiArrowNaturalityIso U).hom.app P).right.f =
      P.p.right.base.base :=
  rfl

/-- Normalization rule: inverse composite naturality uses the twice-projected source idempotent. -/
@[simp]
theorem crossStageProjectionKaroubiArrowNaturalityIso_inv_app_left_f
    (P : Karoubi (Arrow (GeomReadCategory.{u, v} U))) :
    ((crossStageProjectionKaroubiArrowNaturalityIso U).inv.app P).left.f =
      P.p.left.base.base :=
  rfl

/-- Normalization rule: inverse composite naturality uses the twice-projected target idempotent. -/
@[simp]
theorem crossStageProjectionKaroubiArrowNaturalityIso_inv_app_right_f
    (P : Karoubi (Arrow (GeomReadCategory.{u, v} U))) :
    ((crossStageProjectionKaroubiArrowNaturalityIso U).inv.app P).right.f =
      P.p.right.base.base :=
  rfl

/-- B1 composition coherence: composite projection naturality is the two stagewise components. -/
theorem crossStageProjectionKaroubiArrowNaturalityIsoApp_comp
    (P : Karoubi (Arrow (GeomReadCategory.{u, v} U))) :
    karoubiArrowNaturalityIsoApp (crossStageProjection U) P =
      (arrowKaroubiMap (packageProjection U)).mapIso
          (karoubiArrowNaturalityIsoApp (geometryProjection U) P) ≪≫
        karoubiArrowNaturalityIsoApp (packageProjection U)
          ((karoubiArrowMap (geometryProjection U)).obj P) := by
  simpa only [crossStageProjection_eq_geometry_comp_package] using
    karoubiArrowNaturalityIsoApp_comp
      (geometryProjection U) (packageProjection U) P

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
