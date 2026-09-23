import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorGlobalBottomBridge
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorGlobalSection

/-!
# Bottom-fixed automorphisms of the unrestricted semantic image comparison

The image-side bottom group is measured by the actual Karoubi extension of
the complete-geometry projection.  This allows the bottom-fixed comparison
to be treated as a restriction of the unrestricted comparison homomorphism.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss
open RealizationComparisonIdempotents

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 3000000

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

/-- Observe the two image endpoint automorphisms in the Karoubi category of
pointed doctrines. -/
noncomputable def semanticExactGlobalImageBottomEndpointHom :
    SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback →*
      (Aut (((functorExtension₂ _ _).obj (crossStageProjection.{u, v} U)).obj
        (SemanticExactGlobalSourceImage input interpretation z omega k g
          endpoint_eq square_isPullback)) ×
       Aut (((functorExtension₂ _ _).obj (crossStageProjection.{u, v} U)).obj
        (SemanticExactGlobalTargetImage input interpretation z omega k g
          endpoint_eq))) :=
  (MonoidHom.prodMap
      (functorAutomorphismHom
        ((functorExtension₂ _ _).obj (crossStageProjection.{u, v} U)) _)
      (functorAutomorphismHom
        ((functorExtension₂ _ _).obj (crossStageProjection.{u, v} U)) _)).comp
    (Subgroup.subtype _)

/-- The bottom-fixed image comparison is the kernel of actual Karoubi
bottom projection. -/
noncomputable abbrev SemanticExactGlobalBottomImageComparison :=
  (semanticExactGlobalImageBottomEndpointHom input interpretation z omega k g
    endpoint_eq square_isPullback).ker

/-- A precise endpoint test for bottom-fixed image automorphisms. -/
theorem mem_SemanticExactGlobalBottomImageComparison
    (pair : SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback) :
    pair ∈ SemanticExactGlobalBottomImageComparison input interpretation z
        omega k g endpoint_eq square_isPullback ↔
      pair.1.1.hom.f.base.base =
        (SemanticExactGlobalSourceImage input interpretation z omega k g
          endpoint_eq square_isPullback).p.base.base ∧
      pair.1.2.hom.f.base.base =
        (SemanticExactGlobalTargetImage input interpretation z omega k g
          endpoint_eq).p.base.base := by
  change semanticExactGlobalImageBottomEndpointHom input interpretation z omega
      k g endpoint_eq square_isPullback pair = 1 ↔ _
  constructor
  · intro h
    have h₁ := congrArg (fun p => p.1.hom.f) h
    have h₂ := congrArg (fun p => p.2.hom.f) h
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext
    · apply Iso.ext
      apply Karoubi.Hom.ext
      exact h₁
    · apply Iso.ext
      apply Karoubi.Hom.ext
      exact h₂

/-- The selected source image idempotent is identity at the pointed-doctrine
bottom. -/
theorem semanticExactGlobalSourceImage_bottomProjector_eq_id :
    (SemanticExactGlobalSourceImage input interpretation z omega k g
      endpoint_eq square_isPullback).p.base.base =
        𝟙 (packagePoint (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1.core) := by
  exact semanticGeometryFiberMorphism_packageBase_identity
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)

/-- The selected target image idempotent is identity at the bottom. -/
theorem semanticExactGlobalTargetImage_bottomProjector_eq_id :
    (SemanticExactGlobalTargetImage input interpretation z omega k g
      endpoint_eq).p.base.base =
        𝟙 (packagePoint (semanticDerivedViaBaseGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1.core) := by
  exact semanticGeometryFiberMorphism_packageBase_identity
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)

/-- Restriction of a full bottom-fixed pair remains bottom-fixed on both
Karoubi image endpoints whenever it preserves the image comparison. -/
theorem semanticExactGlobalRestriction_mem_bottomImage
    (pair : SemanticExactGlobalBottomH input interpretation z omega k g
      endpoint_eq square_isPullback)
    (hcompat : semanticExactGlobalRestrictionHom input interpretation z omega
      k g endpoint_eq square_isPullback pair.1 ∈
      SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback) :
    (⟨semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback pair.1, hcompat⟩ :
      SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback) ∈
      SemanticExactGlobalBottomImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback := by
  rw [mem_SemanticExactGlobalBottomImageComparison]
  obtain ⟨hsource, htarget⟩ :=
    (mem_SemanticExactGlobalBottomH input interpretation z omega k g
      endpoint_eq square_isPullback pair.1).1 pair.2
  constructor
  · simp only [semanticExactGlobalRestrictionHom,
      idempotentEndpointRestrictionHom_fst_hom_f]
    change
      ((semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback ≫ pair.1.1.1.hom ≫
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback).base.base) =
        (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback).base.base
    change (crossStageProjection.{u, v} U).map
      (semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback ≫ pair.1.1.1.hom ≫
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback) =
      (crossStageProjection.{u, v} U).map
        (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback)
    rw [Functor.map_comp, Functor.map_comp]
    rw [show (crossStageProjection.{u, v} U).map pair.1.1.1.hom =
      𝟙 _ from hsource]
    simp only [Category.id_comp]
    have hE := semanticExactGlobalSourceImage_bottomProjector_eq_id input
      interpretation z omega k g endpoint_eq square_isPullback
    have hE' : (crossStageProjection.{u, v} U).map
        (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback) = 𝟙 _ := hE
    rw [hE']
    simp
  · simp only [semanticExactGlobalRestrictionHom,
      idempotentEndpointRestrictionHom_snd_hom_f]
    change
      ((semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
        pair.1.1.2.hom ≫
        semanticExactGlobalD input interpretation z omega k g
          endpoint_eq).base.base) =
        (semanticExactGlobalD input interpretation z omega k g
          endpoint_eq).base.base
    change (crossStageProjection.{u, v} U).map
      (semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
        pair.1.1.2.hom ≫
        semanticExactGlobalD input interpretation z omega k g endpoint_eq) =
      (crossStageProjection.{u, v} U).map
        (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
    rw [Functor.map_comp, Functor.map_comp]
    rw [show (crossStageProjection.{u, v} U).map pair.1.1.2.hom =
      𝟙 _ from htarget]
    simp only [Category.id_comp]
    have hD := semanticExactGlobalTargetImage_bottomProjector_eq_id input
      interpretation z omega k g endpoint_eq
    have hD' : (crossStageProjection.{u, v} U).map
        (semanticExactGlobalD input interpretation z omega k g endpoint_eq) =
          𝟙 _ := hD
    rw [hD']
    simp

/-- Raw-compatible full endpoint pairs whose underlying complete geometries
fix both package bottoms. -/
noncomputable abbrev SemanticExactGlobalBottomRawComparison :=
  (SemanticExactGlobalBottomH input interpretation z omega k g endpoint_eq
    square_isPullback).subgroupOf
      (SemanticExactGlobalRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback)

/-- Restriction between the genuine bottom-fixed raw and image comparison
subgroups. -/
noncomputable def semanticExactGlobalBottomCompatibleRestrictionHom :
    SemanticExactGlobalBottomRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback →*
      SemanticExactGlobalBottomImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback where
  toFun pair := by
    let raw : SemanticExactGlobalRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback := pair.1
    let image := semanticExactGlobalCompatibleRestrictionHom input interpretation
      z omega k g endpoint_eq square_isPullback raw
    refine ⟨image, ?_⟩
    exact semanticExactGlobalRestriction_mem_bottomImage input interpretation z
      omega k g endpoint_eq square_isPullback ⟨raw.1, pair.2⟩ image.2
  map_one' := by
    apply Subtype.ext
    exact map_one (semanticExactGlobalCompatibleRestrictionHom input
      interpretation z omega k g endpoint_eq square_isPullback)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (semanticExactGlobalCompatibleRestrictionHom input
      interpretation z omega k g endpoint_eq square_isPullback) a.1 b.1

/-- Restrict the full comparison section to the actual bottom kernels. -/
noncomputable def semanticExactGlobalBottomComparisonSectionHom :
    SemanticExactGlobalBottomImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback →*
      SemanticExactGlobalBottomRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback where
  toFun pair := by
    let raw := semanticExactGlobalComparisonSectionHom input interpretation z
      omega k g endpoint_eq square_isPullback pair.1
    refine ⟨raw, ?_⟩
    apply (mem_SemanticExactGlobalBottomH input interpretation z omega k g
      endpoint_eq square_isPullback raw.1).2
    have himage := (mem_SemanticExactGlobalBottomImageComparison input
      interpretation z omega k g endpoint_eq square_isPullback pair.1).1
      pair.2
    constructor
    · rw [semanticExactGlobalComparisonSection_source_base input interpretation
        z omega k g endpoint_eq square_isPullback pair.1, himage.1,
        semanticExactGlobalSourceImage_bottomProjector_eq_id]
    · rw [semanticExactGlobalComparisonSection_target_base input interpretation
        z omega k g endpoint_eq square_isPullback pair.1, himage.2,
        semanticExactGlobalTargetImage_bottomProjector_eq_id]
  map_one' := by
    apply Subtype.ext
    exact map_one (semanticExactGlobalComparisonSectionHom input interpretation z
      omega k g endpoint_eq square_isPullback)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (semanticExactGlobalComparisonSectionHom input interpretation z
      omega k g endpoint_eq square_isPullback) a.1 b.1

/-- The bottom-fixed section is a right inverse of actual bottom-fixed
restriction. -/
theorem semanticExactGlobalBottomComparisonSection_rightInverse
    (pair : SemanticExactGlobalBottomImageComparison input interpretation z
      omega k g endpoint_eq square_isPullback) :
    semanticExactGlobalBottomCompatibleRestrictionHom input interpretation z
      omega k g endpoint_eq square_isPullback
      (semanticExactGlobalBottomComparisonSectionHom input interpretation z
        omega k g endpoint_eq square_isPullback pair) = pair := by
  apply Subtype.ext
  exact semanticExactGlobalComparisonSection_rightInverse input interpretation z
    omega k g endpoint_eq square_isPullback pair.1

end

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
