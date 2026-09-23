import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorGlobalImageBottom

/-!
# Reflection on the genuine bottom kernel of the full geometry group

The diagnostic selector controls reflection even after restricting the
unrestricted complete-geometry centralizer to the kernel of its actual
pointed-doctrine endpoint projection.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

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

/-- The selected ambient-kernel involution fixes both actual package
bottoms, so it belongs to the genuine bottom kernel of the full group. -/
theorem semanticExactGlobalSelectedKernelPair_mem_bottom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactGlobalSelectedKernelPair input interpretation z omega k g
        endpoint_eq square_isPullback selected ∈
      SemanticExactGlobalBottomH input interpretation z omega k g endpoint_eq
        square_isPullback := by
  apply (mem_SemanticExactGlobalBottomH input interpretation z omega k g
    endpoint_eq square_isPullback _).2
  constructor
  · change (ambientKernelGeometry
      (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g
        endpoint_eq).1
      (semanticExactDirectGeometryAt_admissible input interpretation z k g
        endpoint_eq selected.2)).base.base =
      ExtInstHom.id (packagePoint (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g
        endpoint_eq).1.core)
    exact ambientKernelGeometry_packageBase _ _
  · rfl

/-- Full image-compatible pairs, restricted to the actual bottom kernel. -/
noncomputable abbrev SemanticExactGlobalBottomRestrictionPreimage :=
  ((SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback).comap
      (semanticExactGlobalRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback)).comap
    (Subgroup.subtype (SemanticExactGlobalBottomH input interpretation z omega k
      g endpoint_eq square_isPullback))

/-- Raw alpha-compatible pairs, restricted to the actual bottom kernel. -/
noncomputable abbrev SemanticExactGlobalBottomRawInH :=
  (SemanticExactGlobalRawComparison input interpretation z omega k g
    endpoint_eq square_isPullback).comap
    (Subgroup.subtype (SemanticExactGlobalBottomH input interpretation z omega k
      g endpoint_eq square_isPullback))

/-- On a genuinely bottom-fixed pair, membership in the image preimage
already carries the actual Karoubi image-bottom condition. -/
theorem mem_SemanticExactGlobalBottomRestrictionPreimage_iff_imageBottom
    (pair : SemanticExactGlobalBottomH input interpretation z omega k g
      endpoint_eq square_isPullback) :
    pair ∈ SemanticExactGlobalBottomRestrictionPreimage input interpretation z
        omega k g endpoint_eq square_isPullback ↔
      ∃ hcompat : semanticExactGlobalRestrictionHom input interpretation z
          omega k g endpoint_eq square_isPullback pair.1 ∈
          SemanticExactGlobalImageComparison input interpretation z omega k g
            endpoint_eq square_isPullback,
        (⟨semanticExactGlobalRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback pair.1, hcompat⟩ :
          SemanticExactGlobalImageComparison input interpretation z omega k g
            endpoint_eq square_isPullback) ∈
          SemanticExactGlobalBottomImageComparison input interpretation z omega
            k g endpoint_eq square_isPullback := by
  constructor
  · intro h
    refine ⟨h, ?_⟩
    exact semanticExactGlobalRestriction_mem_bottomImage input interpretation z
      omega k g endpoint_eq square_isPullback pair h
  · rintro ⟨hcompat, _⟩
    exact hcompat

/-- The selected kernel witness lies in the bottom-fixed image preimage. -/
theorem semanticExactGlobalSelectedKernelPair_mem_bottomPreimage
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    (⟨semanticExactGlobalSelectedKernelPair input interpretation z omega k g
      endpoint_eq square_isPullback selected,
      semanticExactGlobalSelectedKernelPair_mem_bottom input interpretation z
        omega k g endpoint_eq square_isPullback selected⟩ :
      SemanticExactGlobalBottomH input interpretation z omega k g endpoint_eq
        square_isPullback) ∈
      SemanticExactGlobalBottomRestrictionPreimage input interpretation z omega
        k g endpoint_eq square_isPullback := by
  change semanticExactGlobalRestrictionHom input interpretation z omega k g
    endpoint_eq square_isPullback
      (semanticExactGlobalSelectedKernelPair input interpretation z omega k g
        endpoint_eq square_isPullback selected) ∈
    SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback
  rw [semanticExactGlobalSelectedKernelPair_restriction]
  exact Subgroup.one_mem _

/-- The same bottom-fixed witness does not preserve the raw reversible
comparison. -/
theorem semanticExactGlobalSelectedKernelPair_not_mem_bottomRaw
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    (⟨semanticExactGlobalSelectedKernelPair input interpretation z omega k g
      endpoint_eq square_isPullback selected,
      semanticExactGlobalSelectedKernelPair_mem_bottom input interpretation z
        omega k g endpoint_eq square_isPullback selected⟩ :
      SemanticExactGlobalBottomH input interpretation z omega k g endpoint_eq
        square_isPullback) ∉
      SemanticExactGlobalBottomRawInH input interpretation z omega k g
        endpoint_eq square_isPullback := by
  exact semanticExactGlobalSelectedKernelPair_not_raw input interpretation z
    omega k g endpoint_eq square_isPullback selected

/-- Corollary 7.22 reflection criterion in the *actual* full-geometry bottom
kernel: image compatibility reflects raw alpha compatibility exactly when the
diagnostic selector is false. -/
theorem semanticExactGlobalBottomRestriction_preimage_eq_raw_iff_not_selected :
    (SemanticExactGlobalBottomRestrictionPreimage input interpretation z omega
        k g endpoint_eq square_isPullback =
      SemanticExactGlobalBottomRawInH input interpretation z omega k g
        endpoint_eq square_isPullback) ↔
      ¬ semanticExactBarSelectedAt input interpretation z omega := by
  constructor
  · intro hEq selected
    have hmem := semanticExactGlobalSelectedKernelPair_mem_bottomPreimage
      input interpretation z omega k g endpoint_eq square_isPullback selected
    rw [hEq] at hmem
    exact semanticExactGlobalSelectedKernelPair_not_mem_bottomRaw input
      interpretation z omega k g endpoint_eq square_isPullback selected hmem
  · intro notSelected
    apply Subgroup.ext
    intro pair
    have hfull := semanticExactGlobalRestriction_preimage_eq_raw_of_not_selected
      input interpretation z omega k g endpoint_eq square_isPullback
      notSelected
    exact (Subgroup.ext_iff.mp hfull pair.1)

end

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
