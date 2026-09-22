import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.SemanticExactGeometryPull

/-!
# Canonical normalization along semantic exact geometry pullback

The complete-geometry exact pull lift and its fiber functor preserve canonical
normalization for every exact extraction-instance arrow.  Admissibility at the
source is generated from the target through the actual inverse-core package.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- Equal base and component maps determine heterogeneous equality of geometry
reading morphisms. -/
private theorem semanticGeometryReadHom_heq_of_base_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {f g : PackageTotalHom G.core H.core}
    (F : GeomReadHom G H f) (T : GeomReadHom G H g)
    (hbase : f = g)
    (hcoefficient : F.coefficientHom = T.coefficientHom)
    (hsupport : HEq F.supportComp T.supportComp)
    (haxis : HEq F.axisComp T.axisComp)
    (hobservable : HEq F.observableComp T.observableComp) : HEq F T := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

/-- Semantic exact complete-geometry pullback preserves canonical normalization
admissibility, generated from the target core and the pulled inverse package. -/
theorem canonicalGeometryNormalizationAdmissible_semanticExactPull
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y)
    (admissible : CanonicalObjectNormalizationAdmissible target.1.core) :
    CanonicalObjectNormalizationAdmissible
      ((semanticGeometryPullFunctor input).obj target).1.core := by
  change CanonicalObjectNormalizationAdmissible
    (semanticGeometryPull input target).1.core
  rw [semanticGeometryPull_core]
  exact canonicalObjectNormalizationAdmissible_inverseCorePackage
    target.1.core admissible (semanticGeometryPullBaseHom input target)

/-- Canonical complete-geometry normalization commutes with the exact pull
lift over an arbitrary extraction-instance arrow. -/
theorem semanticGeometryPullLift_normalization_natural
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y)
    (admissible : CanonicalObjectNormalizationAdmissible target.1.core) :
    canonicalGeometryNormalization (semanticGeometryPull input target).1
          (canonicalGeometryNormalizationAdmissible_semanticExactPull
            input target admissible) ≫
        semanticGeometryPullLift input target =
      semanticGeometryPullLift input target ≫
        canonicalGeometryNormalization target.1 admissible := by
  have hbase :
      (canonicalGeometryNormalization (semanticGeometryPull input target).1
            (canonicalGeometryNormalizationAdmissible_semanticExactPull
              input target admissible) ≫
          semanticGeometryPullLift input target).base =
        (semanticGeometryPullLift input target ≫
          canonicalGeometryNormalization target.1 admissible).base := by
    simpa [semanticGeometryPull, semanticGeometryPullObject,
      semanticGeometryPullLift, UpperGeometryCleavage.generatedExactGeometryHom_base,
      UpperGeometryCleavage.exactBaseHom] using
        (inverseCorePackageHom_normalization_natural target.1.core
          admissible (semanticGeometryPullBaseHom input target)).symm
  apply GeometryTotalHom.ext hbase
  apply semanticGeometryReadHom_heq_of_base_eq _ _ hbase <;> rfl

/-- The semantic exact pull functor maps canonical normalization to the
internally generated normalization at the source. -/
theorem semanticGeometryPullFunctor_map_normalization
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y)
    (admissible : CanonicalObjectNormalizationAdmissible target.1.core) :
    (semanticGeometryPullFunctor input).map
        (canonicalGeometryFiberNormalization target admissible) =
      canonicalGeometryFiberNormalization
        ((semanticGeometryPullFunctor input).obj target)
        (canonicalGeometryNormalizationAdmissible_semanticExactPull
          input target admissible) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input (semanticGeometryPullLift input target) :=
    semanticGeometryPullLift_crossStageStronglyCartesian input target
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (crossStageProjection.{u, v} U) input
    (semanticGeometryPullLift input target) (𝟙 X)
  calc
    ((semanticGeometryPullFunctor input).map
          (canonicalGeometryFiberNormalization target admissible)).1 ≫
        semanticGeometryPullLift input target =
      semanticGeometryPullLift input target ≫
        (canonicalGeometryFiberNormalization target admissible).1 := by
      simpa only [semanticGeometryPullFunctor] using
        semanticGeometryPullMap_fac input
          (canonicalGeometryFiberNormalization target admissible)
    _ = (canonicalGeometryFiberNormalization
          ((semanticGeometryPullFunctor input).obj target)
          (canonicalGeometryNormalizationAdmissible_semanticExactPull
            input target admissible)).1 ≫
        semanticGeometryPullLift input target := by
      simpa [canonicalGeometryFiberNormalization,
        semanticGeometryPullFunctor] using
          (semanticGeometryPullLift_normalization_natural
            input target admissible).symm

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
