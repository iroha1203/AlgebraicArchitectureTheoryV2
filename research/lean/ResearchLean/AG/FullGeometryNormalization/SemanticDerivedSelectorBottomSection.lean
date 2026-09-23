import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorBottomReflection
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorComparisonSection

/-!
# Bottom-fixed section of the semantic selector comparison

The literal bottom predicates on the semantic fiber endpoints hold for every
endpoint automorphism. The selector comparison section therefore restricts to
the bottom-fixed raw and Karoubi comparison subgroups.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option maxHeartbeats 3000000

section

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) =
    input.square.southwest)
variable (square_isPullback : IsPullback input.square.left input.square.top
  input.square.bottom input.square.right)

/-- Literal bottom-fixed Karoubi comparison changes. -/
noncomputable def SemanticExactBottomKaroubiComparisonSubgroup :
    Subgroup (SemanticExactKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback) where
  carrier pair :=
    pair.1.1.hom.f.1.base.base =
        𝟙 (packagePoint
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1.core) ∧
      pair.1.2.hom.f.1.base.base =
        𝟙 (packagePoint
          (semanticDerivedViaBaseGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1.core)
  one_mem' := ⟨semanticGeometryFiberMorphism_packageBase_identity _,
    semanticGeometryFiberMorphism_packageBase_identity _⟩
  mul_mem' := by
    intros
    exact ⟨semanticGeometryFiberMorphism_packageBase_identity _,
      semanticGeometryFiberMorphism_packageBase_identity _⟩
  inv_mem' := by
    intros
    exact ⟨semanticGeometryFiberMorphism_packageBase_identity _,
      semanticGeometryFiberMorphism_packageBase_identity _⟩

/-- Actual Karoubi endpoint changes automatically satisfy bottom fixity. -/
theorem SemanticExactBottomKaroubiComparisonSubgroup_eq_top :
    SemanticExactBottomKaroubiComparisonSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback = ⊤ := by
  apply top_unique
  intro pair _
  exact ⟨semanticGeometryFiberMorphism_packageBase_identity pair.1.1.hom.f,
    semanticGeometryFiberMorphism_packageBase_identity pair.1.2.hom.f⟩

/-- The selector restriction on the typed bottom-fixed groups. -/
noncomputable def semanticExactBottomCompatibleRestrictionHom :
    SemanticExactBottomRawComparisonSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback →*
      SemanticExactBottomKaroubiComparisonSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback :=
  ((semanticExactCompatibleRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback).comp
    (Subgroup.inclusion (show
      SemanticExactBottomRawComparisonSubgroup input interpretation z omega k g
          endpoint_eq square_isPullback ≤
        SemanticExactCentralizingRawComparisonSubgroup input interpretation z
          omega k g endpoint_eq square_isPullback from by
      intro pair hpair
      exact hpair.2))).codRestrict
    (SemanticExactBottomKaroubiComparisonSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback)
    (by
      intro pair
      exact ⟨semanticGeometryFiberMorphism_packageBase_identity _,
        semanticGeometryFiberMorphism_packageBase_identity _⟩)

/-- The actual semantic selector section in bottom-fixed endpoint groups. -/
noncomputable def semanticExactBottomComparisonSectionHom :
    SemanticExactBottomKaroubiComparisonSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback →*
      SemanticExactBottomRawComparisonSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback where
  toFun pair := by
    let lifted := semanticExactComparisonSectionHom input interpretation z
      omega k g endpoint_eq square_isPullback pair.1
    exact ⟨lifted.1,
      ⟨semanticExactCentralizingPairBottom_all input interpretation z omega k g
        endpoint_eq square_isPullback lifted.1, lifted.2⟩⟩
  map_one' := by
    apply Subtype.ext
    change
      (semanticExactComparisonSectionHom input interpretation z omega k g
        endpoint_eq square_isPullback 1).1 = 1
    exact congrArg Subtype.val (map_one
      (semanticExactComparisonSectionHom input interpretation z omega k g
        endpoint_eq square_isPullback))
  map_mul' first second := by
    apply Subtype.ext
    change
      (semanticExactComparisonSectionHom input interpretation z omega k g
        endpoint_eq square_isPullback (first.1 * second.1)).1 =
        (semanticExactComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback first.1).1 *
          (semanticExactComparisonSectionHom input interpretation z omega k g
            endpoint_eq square_isPullback second.1).1
    exact congrArg Subtype.val
      (map_mul (semanticExactComparisonSectionHom input interpretation z omega
        k g endpoint_eq square_isPullback) first.1 second.1)

/-- The bottom-fixed selector section is a right inverse to restriction. -/
theorem semanticExactBottomComparisonSection_rightInverse
    (pair : SemanticExactBottomKaroubiComparisonSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback) :
    semanticExactBottomCompatibleRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback
        (semanticExactBottomComparisonSectionHom input interpretation z omega k
          g endpoint_eq square_isPullback pair) = pair := by
  apply Subtype.ext
  change
    semanticExactCompatibleRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback
        (semanticExactComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback pair.1) = pair.1
  exact semanticExactComparisonSection_rightInverse input interpretation z
    omega k g endpoint_eq square_isPullback pair.1

/-- Every bottom-fixed image comparison has a bottom-fixed raw compatible
lift supplied by the actual semantic section. -/
theorem semanticExactBottomCompatibleRestrictionHom_surjective :
    Function.Surjective
      (semanticExactBottomCompatibleRestrictionHom input interpretation z omega
        k g endpoint_eq square_isPullback) := by
  intro pair
  exact ⟨semanticExactBottomComparisonSectionHom input interpretation z omega k
    g endpoint_eq square_isPullback pair,
    semanticExactBottomComparisonSection_rightInverse input interpretation z
      omega k g endpoint_eq square_isPullback pair⟩

end

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
