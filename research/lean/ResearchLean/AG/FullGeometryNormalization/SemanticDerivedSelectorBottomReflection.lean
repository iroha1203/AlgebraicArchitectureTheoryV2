import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorComparisonGroup

/-!
# Bottom-fixed reflection of the semantic selector comparison

All endpoints of the fixed semantic comparison are objects of the same
geometry fiber. The literal package-bottom identity therefore follows from
the fiber lift law. This file retains that predicate in the comparison sets
and proves the selector reflection criterion there.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option maxHeartbeats 3000000

/-- Every endomorphism in a geometry fiber fixes its package bottom. -/
theorem semanticGeometryFiberMorphism_packageBase_identity
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P : GeomFiber.{u, v} X} (f : P ⟶ P) :
    f.1.base.base = 𝟙 (packagePoint P.1.core) := by
  letI := f.2
  have h := CategoryTheory.IsHomLift.fac'
    (crossStageProjection.{u, v} U) (𝟙 X) f.1
  rw [crossStageProjection_map] at h
  simpa using h

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

/-- Literal bottom equations on an ambient centralizing endpoint pair. -/
def semanticExactCentralizingPairBottom
    (pair : SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) : Prop :=
  pair.1.1.hom.1.base.base =
      𝟙 (packagePoint
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1.core) ∧
    pair.1.2.hom.1.base.base =
      𝟙 (packagePoint
        (semanticDerivedViaBaseGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1.core)

/-- Bottom fixity is automatic for both actual fiber endpoints. -/
theorem semanticExactCentralizingPairBottom_all
    (pair : SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :
    semanticExactCentralizingPairBottom input interpretation z omega k g
      endpoint_eq square_isPullback pair := by
  exact ⟨semanticGeometryFiberMorphism_packageBase_identity pair.1.1.hom,
    semanticGeometryFiberMorphism_packageBase_identity pair.1.2.hom⟩

/-- Both Karoubi endpoints of the actual restriction also fix the package
bottom, including on the selected branch. -/
theorem semanticExactEndpointRestriction_bottom
    (pair : SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :
    (semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair).1.hom.f.1.base.base =
        𝟙 (packagePoint
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1.core) ∧
      (semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair).2.hom.f.1.base.base =
        𝟙 (packagePoint
          (semanticDerivedViaBaseGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1.core) := by
  exact ⟨semanticGeometryFiberMorphism_packageBase_identity
      (semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair).1.hom.f,
    semanticGeometryFiberMorphism_packageBase_identity
      (semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair).2.hom.f⟩

/-- The ambient semantic centralizer with the literal bottom equations. -/
noncomputable def SemanticExactBottomCentralizingEndpointSubgroup :
    Subgroup (SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) where
  carrier := semanticExactCentralizingPairBottom input interpretation z omega k g
    endpoint_eq square_isPullback
  one_mem' := semanticExactCentralizingPairBottom_all input interpretation z
    omega k g endpoint_eq square_isPullback 1
  mul_mem' := by
    intros
    apply semanticExactCentralizingPairBottom_all
  inv_mem' := by
    intros
    apply semanticExactCentralizingPairBottom_all

/-- Bottom-fixed ambient pairs preserving the raw reversible comparison. -/
noncomputable def SemanticExactBottomRawComparisonSubgroup :
    Subgroup (SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :=
  SemanticExactBottomCentralizingEndpointSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback ⊓
    SemanticExactCentralizingRawComparisonSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback

/-- Bottom-fixed ambient pairs whose restrictions preserve the image
comparison. -/
noncomputable def SemanticExactBottomRestrictionPreimageSubgroup :
    Subgroup (SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :=
  SemanticExactBottomCentralizingEndpointSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback ⊓
    (SemanticExactKaroubiComparisonSubgroup input interpretation z omega k g
      endpoint_eq square_isPullback).comap
      (semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback)

/-- Raw compatibility among pairs that literally fix both package bottoms. -/
def semanticExactBottomRawComparisonSet :
    Set (SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :=
  {pair | semanticExactCentralizingPairBottom input interpretation z omega k g
      endpoint_eq square_isPullback pair ∧
    pair ∈ SemanticExactCentralizingRawComparisonSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback}

/-- Image compatibility under restriction among pairs that fix both bottoms. -/
def semanticExactBottomRestrictionPreimageSet :
    Set (SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :=
  {pair | semanticExactCentralizingPairBottom input interpretation z omega k g
      endpoint_eq square_isPullback pair ∧
    semanticExactEndpointRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback pair ∈
      SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback}

/-- The selected ambient-kernel pair fixes both package bottoms. -/
theorem semanticExactSelectedAmbientKernelCentralizingPair_bottom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactCentralizingPairBottom input interpretation z omega k g
      endpoint_eq square_isPullback
      (semanticExactSelectedAmbientKernelCentralizingPair
        input interpretation z omega k g endpoint_eq square_isPullback
        selected) :=
  semanticExactCentralizingPairBottom_all input interpretation z omega k g
    endpoint_eq square_isPullback _

/-- The semantic comparison reflects raw compatibility among bottom-fixed
pairs exactly off the diagnostic selector. -/
theorem semanticExactBottomRestrictionPreimage_eq_raw_iff_not_selected :
    semanticExactBottomRestrictionPreimageSet input interpretation z omega k g
        endpoint_eq square_isPullback =
      semanticExactBottomRawComparisonSet input interpretation z omega k g
        endpoint_eq square_isPullback ↔
      ¬ semanticExactBarSelectedAt input interpretation z omega := by
  constructor
  · intro h selected
    have hmem :
        semanticExactSelectedAmbientKernelCentralizingPair
            input interpretation z omega k g endpoint_eq square_isPullback
            selected ∈
          semanticExactBottomRestrictionPreimageSet input interpretation z
            omega k g endpoint_eq square_isPullback := by
      exact ⟨semanticExactSelectedAmbientKernelCentralizingPair_bottom
        input interpretation z omega k g endpoint_eq square_isPullback
        selected,
        semanticExactSelectedAmbientKernelCentralizingPair_mem_preimage
          input interpretation z omega k g endpoint_eq square_isPullback
          selected⟩
    have hraw := (Set.ext_iff.mp h _).mp hmem
    exact semanticExactSelectedAmbientKernelCentralizingPair_not_mem_raw
      input interpretation z omega k g endpoint_eq square_isPullback
      selected hraw.2
  · intro notSelected
    have hreflection := semanticExactEndpointRestriction_preimage_eq_raw_of_not_selected
      input interpretation z omega k g endpoint_eq square_isPullback
      notSelected
    ext pair
    change
      (semanticExactCentralizingPairBottom input interpretation z omega k g
          endpoint_eq square_isPullback pair ∧
        pair ∈ (SemanticExactKaroubiComparisonSubgroup input interpretation z
          omega k g endpoint_eq square_isPullback).comap
          (semanticExactEndpointRestrictionHom input interpretation z omega k g
            endpoint_eq square_isPullback)) ↔
      (semanticExactCentralizingPairBottom input interpretation z omega k g
          endpoint_eq square_isPullback pair ∧
        pair ∈ SemanticExactCentralizingRawComparisonSubgroup input
          interpretation z omega k g endpoint_eq square_isPullback)
    rw [hreflection]

/-- The same bottom-fixed classification in the actual subgroup lattice. -/
theorem semanticExactBottomRestrictionPreimageSubgroup_eq_raw_iff_not_selected :
    SemanticExactBottomRestrictionPreimageSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback =
      SemanticExactBottomRawComparisonSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback ↔
      ¬ semanticExactBarSelectedAt input interpretation z omega := by
  have hsets := semanticExactBottomRestrictionPreimage_eq_raw_iff_not_selected
    input interpretation z omega k g endpoint_eq square_isPullback
  constructor
  · intro h
    apply hsets.mp
    ext pair
    have hpair := (Subgroup.ext_iff.mp h pair)
    simpa [semanticExactBottomRestrictionPreimageSet,
      semanticExactBottomRawComparisonSet,
      SemanticExactBottomRestrictionPreimageSubgroup,
      SemanticExactBottomRawComparisonSubgroup,
      SemanticExactBottomCentralizingEndpointSubgroup] using hpair
  · intro h
    apply Subgroup.ext
    intro pair
    have hpair := (Set.ext_iff.mp (hsets.mpr h) pair)
    simpa [semanticExactBottomRestrictionPreimageSet,
      semanticExactBottomRawComparisonSet,
      SemanticExactBottomRestrictionPreimageSubgroup,
      SemanticExactBottomRawComparisonSubgroup,
      SemanticExactBottomCentralizingEndpointSubgroup] using hpair

end

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
