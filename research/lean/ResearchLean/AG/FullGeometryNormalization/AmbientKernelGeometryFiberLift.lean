import ResearchLean.AG.FullGeometryNormalization.AmbientKernelGeometryLift
import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationNaturality

/-!
# Fiber lift of the ambient normalization-kernel automorphism

The complete-geometry ambient-kernel involution lies over the actual pointed
identity.  It therefore determines a vertical endomorphism, and hence an
automorphism, in every geometry fiber whose underlying core is canonically
normalizable.  This construction uses the computed base identity itself; no
completed lift premise is accepted.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

/-- The ambient normalization-kernel involution as a vertical geometry-fiber
endomorphism. -/
noncomputable def ambientKernelGeometryFiberHom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) : G ⟶ G := by
  refine ⟨ambientKernelGeometry G.1 admissible, ?_⟩
  apply CategoryTheory.IsHomLift.of_commsq
    (crossStageProjection.{u, v} U) (𝟙 X)
    (ambientKernelGeometry G.1 admissible) G.2 G.2
  change (ambientKernelGeometry G.1 admissible).base.base ≫ eqToHom G.2 =
    eqToHom G.2 ≫ 𝟙 X
  rw [ambientKernelGeometry_packageBase]
  change (𝟙 (packagePoint G.1.core)) ≫ eqToHom G.2 =
    eqToHom G.2 ≫ 𝟙 X
  simp

/-- The underlying complete-geometry map of the vertical lift is the ambient
kernel map. -/
@[simp]
theorem ambientKernelGeometryFiberHom_val
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    (ambientKernelGeometryFiberHom G admissible).1 =
      ambientKernelGeometry G.1 admissible :=
  rfl

/-- The vertical lift fixes the pointed-doctrine base of its geometry package. -/
@[simp]
theorem ambientKernelGeometryFiberHom_packageBase
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    (ambientKernelGeometryFiberHom G admissible).1.base.base =
      𝟙 (packagePoint G.1.core) :=
  ambientKernelGeometry_packageBase G.1 admissible

/-- The projected base arrow of the vertical lift is the identity. -/
@[simp]
theorem crossStageProjection_map_ambientKernelGeometryFiberHom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    (crossStageProjection.{u, v} U).map
        (ambientKernelGeometryFiberHom G admissible).1 =
      𝟙 (packagePoint G.1.core) :=
  ambientKernelGeometry_packageBase G.1 admissible

/-- The vertical lift fixes coefficients. -/
@[simp]
theorem ambientKernelGeometryFiberHom_coefficientHom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    (ambientKernelGeometryFiberHom G admissible).1.geometry.coefficientHom =
      RingHom.id G.1.Coefficient :=
  ambientKernelGeometry_coefficientHom G.1 admissible

/-- The ambient-kernel vertical endomorphism is nonidentity. -/
theorem ambientKernelGeometryFiberHom_ne_id
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    ambientKernelGeometryFiberHom G admissible ≠ 𝟙 G := by
  intro h
  have hval := congrArg Subtype.val h
  exact ambientKernelGeometry_ne_id G.1 admissible hval

/-- Applying the ambient-kernel vertical endomorphism twice is the identity
fiber morphism. -/
theorem ambientKernelGeometryFiberHom_comp_self
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    ambientKernelGeometryFiberHom G admissible ≫
        ambientKernelGeometryFiberHom G admissible = 𝟙 G := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact ambientKernelGeometry_comp_self G.1 admissible

/-- The ambient normalization-kernel involution as an automorphism internal to
the geometry fiber. -/
noncomputable def ambientKernelGeometryFiberAut
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) : Aut G where
  hom := ambientKernelGeometryFiberHom G admissible
  inv := ambientKernelGeometryFiberHom G admissible
  hom_inv_id := ambientKernelGeometryFiberHom_comp_self G admissible
  inv_hom_id := ambientKernelGeometryFiberHom_comp_self G admissible

/-- The ambient-kernel geometry-fiber automorphism is nontrivial. -/
theorem ambientKernelGeometryFiberAut_ne_one
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    ambientKernelGeometryFiberAut G admissible ≠ 1 := by
  intro h
  have hhom := congrArg (fun a : Aut G => a.hom) h
  exact ambientKernelGeometryFiberHom_ne_id G admissible hhom

/-- Canonical fiber normalization absorbs the ambient-kernel vertical lift on
the right. -/
theorem canonicalGeometryFiberNormalization_comp_ambientKernelGeometryFiberHom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    canonicalGeometryFiberNormalization G admissible ≫
        ambientKernelGeometryFiberHom G admissible =
      canonicalGeometryFiberNormalization G admissible := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact canonicalGeometryNormalization_comp_ambientKernelGeometry
    G.1 admissible

/-- Canonical fiber normalization absorbs the ambient-kernel vertical lift on
the left. -/
theorem ambientKernelGeometryFiberHom_comp_canonicalGeometryFiberNormalization
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    ambientKernelGeometryFiberHom G admissible ≫
        canonicalGeometryFiberNormalization G admissible =
      canonicalGeometryFiberNormalization G admissible := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact ambientKernelGeometry_comp_canonicalGeometryNormalization
    G.1 admissible

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
