import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationNaturality
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCleavage
import ResearchLean.AG.DoctrineFiberProduct.ExactBottomCoverageSchema
import ResearchLean.AG.DoctrineFiberProduct.ExactBottomGlobalLiftCoherence

/-!
# Canonical core normalization along semantic exact arrows

The canonical core transport and the explicit inverse-package Cartesian
cleavage are defined for every pointed exact arrow.  Their generated lifts
commute with canonical normalization, and the resulting fiber functors map
normalization to normalization by the universal properties of those lifts.
-/

namespace AAT.AG.FullGeometryNormalization

universe u

open CategoryTheory AtomFoundation CrossStageCoherence DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- Canonical core normalization as a vertical endomorphism. -/
noncomputable def canonicalCoreFiberNormalization
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : CoreFiber X)
    (admissible : CanonicalObjectNormalizationAdmissible P.1) : P ⟶ P := by
  refine ⟨canonicalObjectNormalizationTotal P.1 admissible, ?_⟩
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U) (𝟙 X)
    (canonicalObjectNormalizationTotal P.1 admissible) P.2 P.2
  change (𝟙 (packagePoint P.1)) ≫ eqToHom P.2 =
    eqToHom P.2 ≫ 𝟙 X
  simp

/-- Semantic core transport generates admissibility at its target. -/
theorem canonicalCoreNormalizationAdmissible_semanticTransport
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (source : CoreFiber X)
    (admissible : CanonicalObjectNormalizationAdmissible source.1) :
    CanonicalObjectNormalizationAdmissible
      ((coreFiberTransportFunctor input).obj source).1 := by
  change CanonicalObjectNormalizationAdmissible
    (transportAlong source.1 (coreFiberBaseHom input source).doctrineHom)
  exact canonicalObjectNormalizationAdmissible_transportAlong source.1
    admissible (coreFiberBaseHom input source).doctrineHom

/-- Normalization commutes with the generated core cocartesian lift. -/
theorem semanticCoreFiberLift_normalization_natural
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (source : CoreFiber X)
    (admissible : CanonicalObjectNormalizationAdmissible source.1) :
    canonicalObjectNormalizationTotal source.1 admissible ≫
        coreFiberLift input source =
      coreFiberLift input source ≫
        canonicalObjectNormalizationTotal
          ((coreFiberTransportFunctor input).obj source).1
          (canonicalCoreNormalizationAdmissible_semanticTransport
            input source admissible) := by
  simpa [coreFiberLift, coreFiberTransportFunctor, coreFiberTransportObj,
    coreFiberTransportObject] using
      (transportAlongHom_normalization_natural source.1 admissible
        (coreFiberBaseHom input source).doctrineHom).symm

/-- Semantic core transport maps normalization to generated normalization. -/
theorem semanticCoreFiberTransportFunctor_map_normalization
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (source : CoreFiber X)
    (admissible : CanonicalObjectNormalizationAdmissible source.1) :
    (coreFiberTransportFunctor input).map
        (canonicalCoreFiberNormalization source admissible) =
      canonicalCoreFiberNormalization
        ((coreFiberTransportFunctor input).obj source)
        (canonicalCoreNormalizationAdmissible_semanticTransport
          input source admissible) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian
      input (coreFiberLift input source) :=
    coreFiberLift_isStronglyCocartesian input source
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) input (coreFiberLift input source) (𝟙 Y)
  calc
    coreFiberLift input source ≫
        ((coreFiberTransportFunctor input).map
          (canonicalCoreFiberNormalization source admissible)).1 =
      (canonicalCoreFiberNormalization source admissible).1 ≫
        coreFiberLift input source := by
      simpa only [coreFiberTransportFunctor] using
        coreFiberTransportMap_fac input
          (canonicalCoreFiberNormalization source admissible)
    _ = coreFiberLift input source ≫
        (canonicalCoreFiberNormalization
          ((coreFiberTransportFunctor input).obj source)
          (canonicalCoreNormalizationAdmissible_semanticTransport
            input source admissible)).1 := by
      change canonicalObjectNormalizationTotal source.1 admissible ≫
          coreFiberLift input source =
        coreFiberLift input source ≫
          canonicalObjectNormalizationTotal
            ((coreFiberTransportFunctor input).obj source).1
            (canonicalCoreNormalizationAdmissible_semanticTransport
              input source admissible)
      exact semanticCoreFiberLift_normalization_natural
        input source admissible

/-- The explicit inverse-package cleavage for any semantic exact arrow. -/
noncomputable def semanticCoreInverseCleavage
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    CoreFiberCartesianCleavage (cartSemanticInputOfHom input) where
  lift := strongCartesianLiftOfTarget (cartSemanticInputOfHom input)

/-- Canonical semantic core reindexing, with no finite presentation. -/
noncomputable def semanticCoreInverseReindexFunctor
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) : CoreFiber Y ⥤ CoreFiber X :=
  (semanticCoreInverseCleavage input).reindexFunctor

/-- The selected canonical inverse-package lift at a target core. -/
noncomputable def semanticCoreInverseLift
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (target : CoreFiber Y) :
    StrongCartesianLift (cartSemanticInputOfHom input) target :=
  (semanticCoreInverseCleavage input).lift target

/-- The canonical inverse-package reindexing generates source admissibility. -/
theorem canonicalCoreNormalizationAdmissible_semanticPull
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (target : CoreFiber Y)
    (admissible : CanonicalObjectNormalizationAdmissible target.1) :
    CanonicalObjectNormalizationAdmissible
      ((semanticCoreInverseReindexFunctor input).obj target).1 := by
  change CanonicalObjectNormalizationAdmissible
    (inverseCorePackage target.1
      (input ≫ eqToHom target.2.symm))
  exact canonicalObjectNormalizationAdmissible_inverseCorePackage
    target.1 admissible (input ≫ eqToHom target.2.symm)

/-- Normalization commutes with the generated core Cartesian lift. -/
theorem semanticCoreInverseLift_normalization_natural
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (target : CoreFiber Y)
    (admissible : CanonicalObjectNormalizationAdmissible target.1) :
    canonicalObjectNormalizationTotal
        ((semanticCoreInverseReindexFunctor input).obj target).1
        (canonicalCoreNormalizationAdmissible_semanticPull
          input target admissible) ≫
      (semanticCoreInverseLift input target).hom =
    (semanticCoreInverseLift input target).hom ≫
      canonicalObjectNormalizationTotal target.1 admissible := by
  simpa [semanticCoreInverseReindexFunctor, semanticCoreInverseLift,
    semanticCoreInverseCleavage, CoreFiberCartesianCleavage.reindexFunctor,
    CoreFiberCartesianCleavage.reindexObject,
    strongCartesianLiftOfTarget] using
      (inverseCorePackageHom_normalization_natural target.1 admissible
        (input ≫ eqToHom target.2.symm)).symm

/-- The semantic core pull functor maps normalization to generated
normalization by uniqueness of the Cartesian factor. -/
theorem semanticCoreInverseReindexFunctor_map_normalization
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (target : CoreFiber Y)
    (admissible : CanonicalObjectNormalizationAdmissible target.1) :
    (semanticCoreInverseReindexFunctor input).map
        (canonicalCoreFiberNormalization target admissible) =
      canonicalCoreFiberNormalization
        ((semanticCoreInverseReindexFunctor input).obj target)
        (canonicalCoreNormalizationAdmissible_semanticPull
          input target admissible) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCartesian
      input (semanticCoreInverseLift input target).hom :=
    (semanticCoreInverseLift input target).isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input (semanticCoreInverseLift input target).hom
    (𝟙 X)
  calc
    ((semanticCoreInverseReindexFunctor input).map
        (canonicalCoreFiberNormalization target admissible)).1 ≫
      (semanticCoreInverseLift input target).hom =
      (semanticCoreInverseLift input target).hom ≫
        (canonicalCoreFiberNormalization target admissible).1 := by
      exact (semanticCoreInverseCleavage input).reindexFunctor_map_fac
        (canonicalCoreFiberNormalization target admissible)
    _ = (canonicalCoreFiberNormalization
          ((semanticCoreInverseReindexFunctor input).obj target)
          (canonicalCoreNormalizationAdmissible_semanticPull
            input target admissible)).1 ≫
        (semanticCoreInverseLift input target).hom := by
      exact (semanticCoreInverseLift_normalization_natural
        input target admissible).symm

/-- The explicit inverse-package pullback is canonically equivalent to the
previous semantic-global cleavage choice. -/
noncomputable def semanticCoreInverseReindexToGlobalIso
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    semanticCoreInverseReindexFunctor input ≅
      exact_bottom_semantic_global_reindex_functor input :=
  CoreFiberCartesianCleavage.comparison
    (semanticCoreInverseCleavage input)
    (exact_bottom_semantic_global_cartesian_cleavage input)

/-- Each component of the semantic-global comparison preserves the selected
lift into its target, so the two pull functors read the same base arrow. -/
theorem semanticCoreInverseReindexToGlobalIso_hom_fac
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) (target : CoreFiber Y) :
    ((semanticCoreInverseReindexToGlobalIso input).hom.app target).1 ≫
        (exact_bottom_semantic_global_selected_lift input target).hom =
      (semanticCoreInverseLift input target).hom :=
  CoreFiberCartesianCleavage.comparisonApp_hom_fac
    (semanticCoreInverseCleavage input)
    (exact_bottom_semantic_global_cartesian_cleavage input) target

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
