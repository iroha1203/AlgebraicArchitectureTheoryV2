import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedCanonicalComparisonExactness
import ResearchLean.AG.FullGeometryNormalization.GeometryBottomQualifiedComparisonGroup
import ResearchLean.AG.FullGeometryNormalization.AmbientKernelComparisonWitness

/-!
# Canonical comparison groups of a fixed semantic source

The direct and via-base endpoints are generated from one southwest complete
geometry. A single admissibility proof for that source propagates through
the semantic exact pull and transport functors. The resulting actual alpha
isomorphism supports the canonical comparison section and its bottom-fixed
restriction. An internally generated ambient kernel pair witnesses failure
of reflection, including inside the bottom-fixed endpoint groups.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 3000000

/-! ## Isomorphism comparison in the bottom-fixed endpoint groups -/

/-- The normalization comparison section of an admissible geometry
isomorphism preserves the literal bottom identity at both endpoints. -/
noncomputable def canonicalNormalizationIsoBottomComparisonSectionHom
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) :
    normalizedGeometryBottomQualifiedComparisonSubgroup c.hom →*
      rawGeometryBottomQualifiedComparisonSubgroup c.hom where
  toFun pair := by
    let lifted := canonicalNormalizationIsoComparisonSectionHom c pair.1
    refine ⟨lifted, ?_⟩
    rw [mem_rawGeometryBottomQualifiedComparisonSubgroup]
    constructor
    · apply Iso.ext
      change lifted.1.1.hom.hom.base.base = ExtInstHom.id _
      rw [canonicalNormalizationIsoComparisonSection_fst_hom_base_base]
      exact congrArg Iso.hom pair.2.1
    · apply Iso.ext
      change lifted.1.2.hom.hom.base.base = ExtInstHom.id _
      rw [canonicalNormalizationIsoComparisonSection_snd_hom_base_base]
      exact congrArg Iso.hom pair.2.2
  map_one' := by
    apply Subtype.ext
    exact map_one (canonicalNormalizationIsoComparisonSectionHom c)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (canonicalNormalizationIsoComparisonSectionHom c) first.1 second.1

/-- The bottom-fixed isomorphism comparison section is a right inverse of
normalization on every bottom-fixed normalized comparison pair. -/
theorem canonicalNormalizationIsoBottomComparisonSection_rightInverse
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H)
    (pair : normalizedGeometryBottomQualifiedComparisonSubgroup c.hom) :
    geometryNormalizationBottomQualifiedComparisonSubgroupHom c.hom
      (canonicalNormalizationIsoBottomComparisonSectionHom c pair) = pair := by
  apply Subtype.ext
  change geometryNormalizationComparisonSubgroupHom c.hom
      (canonicalNormalizationIsoComparisonSectionHom c pair.1) = pair.1
  exact canonicalNormalizationIsoComparisonSection_rightInverse c pair.1

/-- The internally generated ambient normalization-kernel pair fixes the
bottom at both raw endpoints of every admissible isomorphism. -/
theorem ambientKernelComparisonPair_raw_bottom
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    rawGeometryBottomAutomorphismHom G (ambientKernelComparisonPair G H).1 = 1 ∧
      rawGeometryBottomAutomorphismHom H (ambientKernelComparisonPair G H).2 = 1 := by
  constructor <;> apply Iso.ext <;> rfl

/-- Canonical normalization fails to reflect raw comparison compatibility
even after both ambient endpoints are restricted to bottom-fixing changes. -/
theorem canonicalNormalizationIsoBottomComparison_preimage_ne_raw
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) :
    {pair : Aut G × Aut H |
      rawGeometryBottomAutomorphismHom G pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H pair.2 = 1 ∧
      geometryNormalizationEndpointAutomorphismHom G H pair ∈
        normalizedGeometryComparisonSubgroup c.hom} ≠
    {pair : Aut G × Aut H |
      rawGeometryBottomAutomorphismHom G pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H pair.2 = 1 ∧
      pair ∈ rawGeometryNormalizationComparisonSubgroup c.hom} := by
  intro hsets
  let witness := ambientKernelComparisonPair G H
  have hbottom := ambientKernelComparisonPair_raw_bottom G H
  have hnormalized := ambientKernelComparisonPair_normalized_mem c
  have hleft : witness ∈ {pair : Aut G × Aut H |
      rawGeometryBottomAutomorphismHom G pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H pair.2 = 1 ∧
      geometryNormalizationEndpointAutomorphismHom G H pair ∈
        normalizedGeometryComparisonSubgroup c.hom} :=
    ⟨hbottom.1, hbottom.2, hnormalized⟩
  have hright := (Set.ext_iff.mp hsets witness).mp hleft
  exact ambientKernelComparisonPair_not_raw_mem c hright.2.2

/-! ## The fixed semantic square and one source geometry -/

/-- Bottom-fixed raw comparison changes of the actual semantic `barAlpha`. -/
noncomputable abbrev SemanticDerivedCanonicalRawBottomComparisonSubgroup
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :=
  rawGeometryBottomQualifiedComparisonSubgroup
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom

/-- Bottom-fixed normalized comparison changes of the same actual
semantic `barAlpha`. -/
noncomputable abbrev SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :=
  normalizedGeometryBottomQualifiedComparisonSubgroup
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom

/-- The bottom-fixed section for the generated semantic comparison. -/
noncomputable def semanticDerivedCanonicalBottomComparisonSectionHom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
        input Q k g endpoint_eq square_isPullback admissible →*
      SemanticDerivedCanonicalRawBottomComparisonSubgroup
        input Q k g endpoint_eq square_isPullback admissible :=
  canonicalNormalizationIsoBottomComparisonSectionHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible)

/-- The actual bottom-fixed semantic section is a right inverse. -/
theorem semanticDerivedCanonicalBottomComparisonSection_rightInverse
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (pair : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    geometryNormalizationBottomQualifiedComparisonSubgroupHom
        (semanticDerivedBarAlphaAdmissibleIsoAt
          input Q k g endpoint_eq square_isPullback admissible).hom
        (semanticDerivedCanonicalBottomComparisonSectionHom
          input Q k g endpoint_eq square_isPullback admissible pair) = pair :=
  canonicalNormalizationIsoBottomComparisonSection_rightInverse
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible) pair

/-- Canonical normalization does not reflect compatibility of the generated
semantic `barAlpha`, even among bottom-fixing endpoint changes. The witness
is the internally constructed normalization-kernel involution. -/
theorem semanticDerivedCanonicalBottomComparison_preimage_ne_raw
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    let G := semanticDerivedDirectAdmissibleGeometryAt
      input Q k g endpoint_eq admissible
    let H := semanticDerivedViaBaseAdmissibleGeometryAt
      input Q k g endpoint_eq admissible
    let c := semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible
    {pair : Aut G × Aut H |
      rawGeometryBottomAutomorphismHom G pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H pair.2 = 1 ∧
      geometryNormalizationEndpointAutomorphismHom G H pair ∈
        normalizedGeometryComparisonSubgroup c.hom} ≠
    {pair : Aut G × Aut H |
      rawGeometryBottomAutomorphismHom G pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H pair.2 = 1 ∧
      pair ∈ rawGeometryNormalizationComparisonSubgroup c.hom} := by
  exact canonicalNormalizationIsoBottomComparison_preimage_ne_raw
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible)

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
