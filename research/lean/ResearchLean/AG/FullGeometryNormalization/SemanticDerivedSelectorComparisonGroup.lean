import ResearchLean.AG.FullGeometryNormalization.SemanticExactBarBetaClassification
import ResearchLean.AG.FullGeometryNormalization.AmbientKernelGeometryFiberLift
import ResearchLean.AG.ComparisonInformationLoss.KaroubiRestriction

/-!
# Comparison groups of the generated semantic selector

The source and target projectors, reversible comparison, and Karoubi image
are constructed from one semantic square, a diagnostic interpretation of its
same diagram, and a fixed southwest geometry. This module instantiates the
generic centralizer and sandwich restriction APIs on those actual objects.
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

/-- Ambient pairs that commute with both actual endpoint projectors. -/
noncomputable abbrev SemanticExactCentralizingEndpointSubgroup :=
  centralizingEndpointSubgroup
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)

/-- Centralizing pairs preserving the reversible raw semantic comparison. -/
noncomputable abbrev SemanticExactCentralizingRawComparisonSubgroup :=
  centralizingCompatibleSubgroup
    (semanticDerivedBarAlphaIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
      square_isPullback).hom
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)

/-- Automorphism pairs preserving the actual Karoubi image comparison. -/
noncomputable abbrev SemanticExactKaroubiComparisonSubgroup :=
  comparisonAutomorphismSubgroup
    (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g
      endpoint_eq square_isPullback).hom

/-- The source and target projectors intertwine the generated reversible
comparison. -/
theorem semanticExactBarAlphaAt_projector_comm :
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      (semanticDerivedBarAlphaIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
        square_isPullback).hom =
    (semanticDerivedBarAlphaIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
        square_isPullback).hom ≫
      semanticExactBarDAt input interpretation z omega k g endpoint_eq := by
  simp [semanticExactBarEAt, Category.assoc]

/-- The generic idempotent-image comparison is the literal semantic
`barBeta` Karoubi arrow. -/
theorem semanticExactIdempotentImageComparison_eq_barBeta :
    idempotentImageComparison
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          square_isPullback).hom
        (semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
        (semanticExactBarEAt_idem input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq)
        (semanticExactBarAlphaAt_projector_comm input interpretation z omega k g
          endpoint_eq square_isPullback) =
      (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g
        endpoint_eq square_isPullback).hom := by
  apply Karoubi.Hom.ext
  change
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          square_isPullback).hom ≫
        semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback
  have h := congrArg
    (fun f => f ≫ semanticExactBarDAt input interpretation z omega k g
      endpoint_eq)
    (semanticExactBarAlphaAt_projector_comm input interpretation z omega k g
      endpoint_eq square_isPullback)
  simpa only [Category.assoc, semanticExactBarDAt_idem,
    semanticExactBarBetaAt] using h

/-- The actual endpoint sandwich on semantic comparison changes. -/
noncomputable def semanticExactEndpointRestrictionHom :
    SemanticExactCentralizingEndpointSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback →*
      (Aut (semanticExactBarESourceKaroubiAt input interpretation z omega k g
          endpoint_eq square_isPullback) ×
        Aut (semanticExactBarDTargetKaroubiAt input interpretation z omega k g
          endpoint_eq)) :=
  idempotentEndpointRestrictionHom
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
    (semanticExactBarEAt_idem input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq)

/-- The source component of the actual semantic sandwich is `e ≫ u ≫ e`. -/
@[simp] theorem semanticExactEndpointRestrictionHom_fst_hom_f
    (pair : SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :
    (semanticExactEndpointRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback pair).1.hom.f =
      semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback ≫ pair.1.1.hom ≫
        semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback :=
  idempotentEndpointRestrictionHom_fst_hom_f _ _ _ _ _ _ pair

/-- The target component of the actual semantic sandwich is `d ≫ v ≫ d`. -/
@[simp] theorem semanticExactEndpointRestrictionHom_snd_hom_f
    (pair : SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :
    (semanticExactEndpointRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback pair).2.hom.f =
      semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
        pair.1.2.hom ≫
        semanticExactBarDAt input interpretation z omega k g endpoint_eq :=
  idempotentEndpointRestrictionHom_snd_hom_f _ _ _ _ _ _ pair

/-- Restriction of a raw compatible pair preserves the actual semantic image
comparison. -/
theorem semanticExactEndpointRestriction_preserves_comparison
    (pair : SemanticExactCentralizingRawComparisonSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback) :
    semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair.1 ∈
      SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback := by
  have h := idempotentEndpointRestriction_preserves_comparison
    (semanticDerivedBarAlphaIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
      square_isPullback).hom
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
    (semanticExactBarEAt_idem input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq)
    (semanticExactBarAlphaAt_projector_comm input interpretation z omega k g
      endpoint_eq square_isPullback) pair
  simpa only [semanticExactIdempotentImageComparison_eq_barBeta] using h

/-- The actual semantic sandwich sends raw-compatible centralizing changes
into the Karoubi comparison group. -/
theorem semanticExactEndpointRestriction_map_le :
    Subgroup.map
        (semanticExactEndpointRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback)
        (SemanticExactCentralizingRawComparisonSubgroup
          input interpretation z omega k g endpoint_eq square_isPullback) ≤
      SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback := by
  rintro image ⟨pair, hpair, rfl⟩
  exact semanticExactEndpointRestriction_preserves_comparison
    input interpretation z omega k g endpoint_eq square_isPullback
    ⟨pair, hpair⟩

/-- Restriction of the actual endpoint sandwich to raw-compatible semantic
comparison pairs. -/
noncomputable def semanticExactCompatibleRestrictionHom :
    SemanticExactCentralizingRawComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback →*
      SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback :=
  restrictedSubgroupHom
    (semanticExactEndpointRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback)
    (SemanticExactCentralizingRawComparisonSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback)
    (SemanticExactKaroubiComparisonSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback)
    (semanticExactEndpointRestriction_map_le input interpretation z omega k g
      endpoint_eq square_isPullback)

/-- Off the diagnostic selector the two projectors are identities, so the
actual Karoubi-image condition reflects the raw semantic comparison. -/
theorem semanticExactEndpointRestriction_preimage_eq_raw_of_not_selected
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    (SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback).comap
        (semanticExactEndpointRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      SemanticExactCentralizingRawComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback := by
  have hprojectors := semanticExactBarProjectorsAt_eq_id
    input interpretation z omega k g endpoint_eq square_isPullback notSelected
  have hbeta : semanticExactBarBetaAt input interpretation z omega k g
      endpoint_eq square_isPullback =
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          square_isPullback).hom := by
    simp [semanticExactBarBetaAt, hprojectors.2]
  ext pair
  change
    (semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair).1.hom ≫
      (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g
        endpoint_eq square_isPullback).hom =
    (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g
        endpoint_eq square_isPullback).hom ≫
      (semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair).2.hom ↔
    pair.1.1.hom ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          square_isPullback).hom =
      (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          square_isPullback).hom ≫ pair.1.2.hom
  constructor
  · intro h
    have hf := congrArg Karoubi.Hom.f h
    simpa [semanticExactEndpointRestrictionHom_fst_hom_f,
      semanticExactEndpointRestrictionHom_snd_hom_f,
      semanticExactBarBetaKaroubiIsoAt, hprojectors.1, hprojectors.2,
      hbeta] using hf
  · intro h
    apply Karoubi.Hom.ext
    simpa [semanticExactEndpointRestrictionHom_fst_hom_f,
      semanticExactEndpointRestrictionHom_snd_hom_f,
      semanticExactBarBetaKaroubiIsoAt, hprojectors.1, hprojectors.2,
      hbeta] using h

/-- On the selected branch the internally generated ambient normalization
kernel involution and the target identity centralize both projectors. -/
noncomputable def semanticExactSelectedAmbientKernelCentralizingPair
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    SemanticExactCentralizingEndpointSubgroup
      input interpretation z omega k g endpoint_eq square_isPullback := by
  refine ⟨(ambientKernelGeometryFiberAut
      (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
      (semanticExactDirectGeometryAt_admissible input interpretation z k g
        endpoint_eq selected.2), 1), ?_⟩
  constructor
  · rw [semanticExactBarEAt_eq_endpoint_normalization
      input interpretation z omega k g endpoint_eq square_isPullback selected]
    exact (ambientKernelGeometryFiberHom_comp_canonicalGeometryFiberNormalization
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2)).trans
      (canonicalGeometryFiberNormalization_comp_ambientKernelGeometryFiberHom
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2)).symm
  · simp

/-- The selected ambient pair has the nontrivial source involution. -/
@[simp] theorem semanticExactSelectedAmbientKernelCentralizingPair_fst
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    (semanticExactSelectedAmbientKernelCentralizingPair input interpretation z
      omega k g endpoint_eq square_isPullback selected).1.1 =
      ambientKernelGeometryFiberAut
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2) :=
  rfl

/-- The selected ambient pair has identity target component. -/
@[simp] theorem semanticExactSelectedAmbientKernelCentralizingPair_snd
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    (semanticExactSelectedAmbientKernelCentralizingPair input interpretation z
      omega k g endpoint_eq square_isPullback selected).1.2 = 1 :=
  rfl

/-- The ambient restriction erases the selected source involution. -/
@[simp] theorem semanticExactSelectedAmbientKernelCentralizingPair_restriction_fst
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    (semanticExactEndpointRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
      (semanticExactSelectedAmbientKernelCentralizingPair input interpretation z
        omega k g endpoint_eq square_isPullback selected)).1 = 1 := by
  apply Iso.ext
  apply Karoubi.Hom.ext
  rw [semanticExactEndpointRestrictionHom_fst_hom_f,
    semanticExactSelectedAmbientKernelCentralizingPair_fst]
  rw [semanticExactBarEAt_eq_endpoint_normalization
    input interpretation z omega k g endpoint_eq square_isPullback selected]
  change
    canonicalGeometryFiberNormalization
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2) ≫
      ambientKernelGeometryFiberHom
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2) ≫
      canonicalGeometryFiberNormalization
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2) = _
  calc
    _ = canonicalGeometryFiberNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2) ≫
        canonicalGeometryFiberNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2) := by
          rw [← Category.assoc,
            canonicalGeometryFiberNormalization_comp_ambientKernelGeometryFiberHom]
    _ = canonicalGeometryFiberNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2) := by
          rw [← semanticExactBarEAt_eq_endpoint_normalization
            input interpretation z omega k g endpoint_eq square_isPullback selected]
          exact semanticExactBarEAt_idem input interpretation z omega k g
            endpoint_eq square_isPullback
    _ = semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback :=
        (semanticExactBarEAt_eq_endpoint_normalization
          input interpretation z omega k g endpoint_eq square_isPullback selected).symm
    _ = _ := rfl

/-- The ambient endpoint restriction erases the complete selected pair. -/
@[simp] theorem semanticExactSelectedAmbientKernelCentralizingPair_restriction
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactEndpointRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
      (semanticExactSelectedAmbientKernelCentralizingPair input interpretation z
        omega k g endpoint_eq square_isPullback selected) = 1 := by
  apply Prod.ext
  · exact semanticExactSelectedAmbientKernelCentralizingPair_restriction_fst
      input interpretation z omega k g endpoint_eq square_isPullback selected
  · apply Iso.ext
    apply Karoubi.Hom.ext
    rw [semanticExactEndpointRestrictionHom_snd_hom_f,
      semanticExactSelectedAmbientKernelCentralizingPair_snd]
    exact semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq

/-- The selected witness lies in the ambient preimage of the semantic image
comparison. This is the ambient kernel, not the restricted raw-domain kernel. -/
theorem semanticExactSelectedAmbientKernelCentralizingPair_mem_preimage
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactSelectedAmbientKernelCentralizingPair input interpretation z
      omega k g endpoint_eq square_isPullback selected ∈
      (SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback).comap
        (semanticExactEndpointRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) := by
  apply Subgroup.mem_comap.mpr
  rw [semanticExactSelectedAmbientKernelCentralizingPair_restriction]
  exact Subgroup.one_mem _

/-- The same selected pair does not preserve the reversible raw semantic
comparison; invertibility would force its nontrivial source involution to be
the identity. -/
theorem semanticExactSelectedAmbientKernelCentralizingPair_not_mem_raw
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactSelectedAmbientKernelCentralizingPair input interpretation z
      omega k g endpoint_eq square_isPullback selected ∉
      SemanticExactCentralizingRawComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback := by
  intro hmem
  change
    (ambientKernelGeometryFiberAut
      (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
      (semanticExactDirectGeometryAt_admissible input interpretation z k g
        endpoint_eq selected.2)).hom ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          square_isPullback).hom =
      (semanticDerivedBarAlphaIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
        square_isPullback).hom ≫ 𝟙 _ at hmem
  rw [Category.comp_id] at hmem
  have hhom :
      (ambientKernelGeometryFiberAut
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2)).hom = 𝟙 _ := by
    apply (cancel_mono (semanticDerivedBarAlphaIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
      square_isPullback).hom).1
    simpa using hmem
  apply ambientKernelGeometryFiberAut_ne_one
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
    (semanticExactDirectGeometryAt_admissible input interpretation z k g
      endpoint_eq selected.2)
  apply Iso.ext
  exact hhom

/-- Selected normalization fails to reflect compatibility with the
reversible raw comparison in the actual semantic centralizer. -/
theorem semanticExactEndpointRestriction_preimage_ne_raw_of_selected
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    (SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback).comap
        (semanticExactEndpointRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) ≠
      SemanticExactCentralizingRawComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback := by
  intro hEq
  have hmem := semanticExactSelectedAmbientKernelCentralizingPair_mem_preimage
    input interpretation z omega k g endpoint_eq square_isPullback selected
  rw [hEq] at hmem
  exact semanticExactSelectedAmbientKernelCentralizingPair_not_mem_raw
    input interpretation z omega k g endpoint_eq square_isPullback selected hmem

/-- Exact reflection classification for the actual semantic selector. -/
theorem semanticExactEndpointRestriction_preimage_eq_raw_iff_not_selected :
    ((SemanticExactKaroubiComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback).comap
        (semanticExactEndpointRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      SemanticExactCentralizingRawComparisonSubgroup
        input interpretation z omega k g endpoint_eq square_isPullback) ↔
      ¬ semanticExactBarSelectedAt input interpretation z omega := by
  constructor
  · intro hEq selected
    exact semanticExactEndpointRestriction_preimage_ne_raw_of_selected
      input interpretation z omega k g endpoint_eq square_isPullback selected hEq
  · intro notSelected
    exact semanticExactEndpointRestriction_preimage_eq_raw_of_not_selected
      input interpretation z omega k g endpoint_eq square_isPullback notSelected

end

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
