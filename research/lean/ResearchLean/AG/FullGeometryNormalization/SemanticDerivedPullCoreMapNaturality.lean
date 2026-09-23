import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedCoreEndpointProjection

/-! # Naturality of semantic geometry/core pull projection -/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The selected geometry pull functor projects to the canonical core inverse
pull functor on vertical morphisms. -/
theorem semanticDerivedPullCoreMap_eq
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (arrow : ExtInstHom X Y) {G H : GeomFiber.{u, v} Y}
    (f : G ⟶ H) :
    (geometryFiberProjection X).map
      ((semanticGeometryPullFunctor arrow).map f) =
    (semanticCoreInverseReindexFunctor arrow).map
      ((geometryFiberProjection Y).map f) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCartesian arrow
      (semanticCoreInverseLift arrow
        ((geometryFiberProjection Y).obj H)).hom :=
    (semanticCoreInverseLift arrow
      ((geometryFiberProjection Y).obj H)).isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) arrow
    (semanticCoreInverseLift arrow
      ((geometryFiberProjection Y).obj H)).hom (𝟙 X)
  have hgeometry := congrArg (geometryProjection U).map
    (semanticGeometryPullMap_fac arrow f)
  simp only [Functor.map_comp] at hgeometry
  have hcore := (semanticCoreInverseCleavage arrow).reindexFunctor_map_fac
    ((geometryFiberProjection Y).map f)
  change
    ((semanticCoreInverseReindexFunctor arrow).map
      ((geometryFiberProjection Y).map f)).1 ≫
      (semanticCoreInverseLift arrow
        ((geometryFiberProjection Y).obj H)).hom =
    (semanticCoreInverseLift arrow
      ((geometryFiberProjection Y).obj G)).hom ≫
      ((geometryFiberProjection Y).map f).1 at hcore
  change
    ((geometryFiberProjection X).map
      ((semanticGeometryPullFunctor arrow).map f)).1 ≫
      (semanticCoreInverseLift arrow
        ((geometryFiberProjection Y).obj H)).hom =
    ((semanticCoreInverseReindexFunctor arrow).map
      ((geometryFiberProjection Y).map f)).1 ≫
      (semanticCoreInverseLift arrow
        ((geometryFiberProjection Y).obj H)).hom
  rw [hcore]
  simpa only [semanticDerivedPullCoreLift_eq] using hgeometry

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
