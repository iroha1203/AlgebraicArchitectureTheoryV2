import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorComparisonGroup
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorComparisonSection

/-!
# Unrestricted complete-geometry endpoint comparison

The ambient category here is `GeomReadCategory`, so its automorphisms may
move the pointed doctrine.  The previously constructed fiber comparison is
the bottom-fixed part of this larger comparison.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option maxHeartbeats 3000000


/-- For centralizing endpoint changes, compatibility on the Karoubi image
is exactly compatibility with the underlying selected comparison. -/
theorem global_idempotent_restriction_preimage_eq_beta
    {E : Type*} [Category E] {X Y : E} (c : X ⟶ Y)
    (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d)
    (hedc : e ≫ c = c ≫ d) :
    (comparisonAutomorphismSubgroup
        (idempotentImageComparison c e d he hd hedc)).comap
        (idempotentEndpointRestrictionHom X Y e d he hd) =
      centralizingCompatibleSubgroup (e ≫ c ≫ d) e d := by
  ext pair
  change
    (idempotentEndpointRestrictionHom X Y e d he hd pair).1.hom ≫
        idempotentImageComparison c e d he hd hedc =
      idempotentImageComparison c e d he hd hedc ≫
        (idempotentEndpointRestrictionHom X Y e d he hd pair).2.hom ↔
      pair.1.1.hom ≫ (e ≫ c ≫ d) =
        (e ≫ c ≫ d) ≫ pair.1.2.hom
  have left_absorb : e ≫ (e ≫ c ≫ d) = e ≫ c ≫ d := by
    simp only [← Category.assoc, he]
  have right_absorb : (e ≫ c ≫ d) ≫ d = e ≫ c ≫ d := by
    simp only [Category.assoc, hd]
  have hsource : e ≫ pair.1.1.hom = pair.1.1.hom ≫ e :=
    pair.2.1.symm
  have htarget : d ≫ pair.1.2.hom = pair.1.2.hom ≫ d :=
    pair.2.2.symm
  have hl : (e ≫ pair.1.1.hom ≫ e) ≫ (e ≫ c ≫ d) =
      pair.1.1.hom ≫ (e ≫ c ≫ d) := by
    rw [idempotentCentralizerAutSubgroup_hom_sandwich X e he
      ⟨pair.1.1, pair.2.1⟩]
    rw [Category.assoc, left_absorb]
  have hr : (e ≫ c ≫ d) ≫ (d ≫ pair.1.2.hom ≫ d) =
      (e ≫ c ≫ d) ≫ pair.1.2.hom := by
    rw [idempotentCentralizerAutSubgroup_hom_sandwich Y d hd
      ⟨pair.1.2, pair.2.2⟩]
    rw [← htarget, ← Category.assoc, right_absorb]
  constructor
  · intro h
    have hf := congrArg Karoubi.Hom.f h
    simp only [Karoubi.comp_f,
      idempotentEndpointRestrictionHom_fst_hom_f,
      idempotentEndpointRestrictionHom_snd_hom_f] at hf
    change (e ≫ pair.1.1.hom ≫ e) ≫ (e ≫ c ≫ d) =
      (e ≫ c ≫ d) ≫ (d ≫ pair.1.2.hom ≫ d) at hf
    simpa only [hl, hr] using hf
  · intro h
    apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f,
      idempotentEndpointRestrictionHom_fst_hom_f,
      idempotentEndpointRestrictionHom_snd_hom_f]
    change (e ≫ pair.1.1.hom ≫ e) ≫ (e ≫ c ≫ d) =
      (e ≫ c ≫ d) ≫ (d ≫ pair.1.2.hom ≫ d)
    simpa only [hl, hr] using h

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

/-- Inclusion of a fixed pointed-doctrine fiber in all complete geometries. -/
noncomputable abbrev semanticExactGlobalInclusion :
    GeomFiber.{u, v} input.square.northeast ⥤ GeomReadCategory.{u, v} U :=
  CategoryTheory.Functor.Fiber.fiberInclusion

/-- The raw semantic comparison in the unrestricted complete-geometry category. -/
noncomputable def semanticExactGlobalAlphaIso :
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 ≅
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 :=
  (semanticExactGlobalInclusion input).mapIso
    (semanticDerivedBarAlphaIsoAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
      square_isPullback)

/-- Selected source idempotent on the complete geometry, allowing all endpoint
automorphisms in the ambient category. -/
noncomputable def semanticExactGlobalE :
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 ⟶
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 :=
  (semanticExactGlobalInclusion input).map
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)

/-- Selected target idempotent in the unrestricted complete-geometry category. -/
noncomputable def semanticExactGlobalD :
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 ⟶
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 :=
  (semanticExactGlobalInclusion input).map
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)

theorem semanticExactGlobalE_idem :
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback =
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback := by
  exact (Functor.map_comp _ _ _).symm.trans
    (congrArg (semanticExactGlobalInclusion input).map
      (semanticExactBarEAt_idem input interpretation z omega k g endpoint_eq
        square_isPullback))

theorem semanticExactGlobalD_idem :
    semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
      semanticExactGlobalD input interpretation z omega k g endpoint_eq =
      semanticExactGlobalD input interpretation z omega k g endpoint_eq := by
  exact (Functor.map_comp _ _ _).symm.trans
    (congrArg (semanticExactGlobalInclusion input).map
      (semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq))

theorem semanticExactGlobalAlpha_projector_comm :
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
        square_isPullback).hom =
    (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
        square_isPullback).hom ≫
      semanticExactGlobalD input interpretation z omega k g endpoint_eq := by
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg (semanticExactGlobalInclusion input).map
      (semanticExactBarAlphaAt_projector_comm input interpretation z omega k g
        endpoint_eq square_isPullback)).trans (Functor.map_comp _ _ _))

/-- The actual complete-geometry group H of endpoint automorphism pairs
centralizing the two selected projectors. -/
noncomputable abbrev SemanticExactGlobalH :=
  centralizingEndpointSubgroup
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1
    (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD input interpretation z omega k g endpoint_eq)

/-- Raw alpha-preserving pairs inside the full complete-geometry centralizer. -/
noncomputable abbrev SemanticExactGlobalRawComparison :=
  centralizingCompatibleSubgroup
    (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
      square_isPullback).hom
    (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD input interpretation z omega k g endpoint_eq)

/-- Source and target Karoubi images in the unrestricted complete category. -/
noncomputable abbrev SemanticExactGlobalSourceImage :=
  idempotentKaroubiObject
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1
    (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalE_idem input interpretation z omega k g endpoint_eq
      square_isPullback)

noncomputable abbrev SemanticExactGlobalTargetImage :=
  idempotentKaroubiObject
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1
    (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
    (semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq)

/-- The complete-geometry image arrow induced by the selected semantic beta. -/
noncomputable def semanticExactGlobalBetaImage :
    SemanticExactGlobalSourceImage input interpretation z omega k g
        endpoint_eq square_isPullback ⟶
      SemanticExactGlobalTargetImage input interpretation z omega k g
        endpoint_eq :=
  idempotentImageComparison
    (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
      square_isPullback).hom
    (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
    (semanticExactGlobalE_idem input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq)
    (semanticExactGlobalAlpha_projector_comm input interpretation z omega k g
      endpoint_eq square_isPullback)

noncomputable abbrev SemanticExactGlobalImageComparison :=
  comparisonAutomorphismSubgroup
    (semanticExactGlobalBetaImage input interpretation z omega k g endpoint_eq
      square_isPullback)

/-- Restrict every complete-geometry centralizing pair by the actual two
idempotents. -/
noncomputable def semanticExactGlobalRestrictionHom :
    SemanticExactGlobalH input interpretation z omega k g endpoint_eq
        square_isPullback →*
      (Aut (SemanticExactGlobalSourceImage input interpretation z omega k g
          endpoint_eq square_isPullback) ×
        Aut (SemanticExactGlobalTargetImage input interpretation z omega k g
          endpoint_eq)) :=
  idempotentEndpointRestrictionHom _ _
    (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
    (semanticExactGlobalE_idem input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq)

/-- The full-category beta before passage to its Karoubi image. -/
noncomputable def semanticExactGlobalBeta :
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 ⟶
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 :=
  semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback ≫
    (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
      square_isPullback).hom ≫
    semanticExactGlobalD input interpretation z omega k g endpoint_eq

/-- Equation (7.36) for unrestricted complete-geometry endpoint
automorphisms: the image comparison remembers precisely beta compatibility
inside the full centralizer. -/
theorem semanticExactGlobalRestriction_preimage_eq_beta :
    (SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback).comap
        (semanticExactGlobalRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      centralizingCompatibleSubgroup
        (semanticExactGlobalBeta input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalD input interpretation z omega k g endpoint_eq) :=
  global_idempotent_restriction_preimage_eq_beta
    (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
      square_isPullback).hom
    (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
    (semanticExactGlobalE_idem input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq)
    (semanticExactGlobalAlpha_projector_comm input interpretation z omega k g
      endpoint_eq square_isPullback)

/-- Outside the selector, both complete-geometry idempotents are identities. -/
theorem semanticExactGlobalProjectors_eq_id
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback = 𝟙 _ ∧
      semanticExactGlobalD input interpretation z omega k g endpoint_eq =
        𝟙 _ := by
  have h := semanticExactBarProjectorsAt_eq_id input interpretation z omega
    k g endpoint_eq square_isPullback notSelected
  constructor
  · simpa only [semanticExactGlobalE, ← Functor.map_id] using
      congrArg (semanticExactGlobalInclusion input).map h.1
  · simpa only [semanticExactGlobalD, ← Functor.map_id] using
      congrArg (semanticExactGlobalInclusion input).map h.2

/-- Off the selector, the full-category beta equals the reversible alpha. -/
theorem semanticExactGlobalBeta_eq_alpha_of_not_selected
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactGlobalBeta input interpretation z omega k g endpoint_eq
        square_isPullback =
      (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
        square_isPullback).hom := by
  obtain ⟨he, hd⟩ := semanticExactGlobalProjectors_eq_id input
    interpretation z omega k g endpoint_eq square_isPullback notSelected
  simp [semanticExactGlobalBeta, he, hd]

/-- Raw alpha compatibility reflects from the full image comparison when the
diagnostic selector is false. -/
theorem semanticExactGlobalRestriction_preimage_eq_raw_of_not_selected
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    (SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback).comap
        (semanticExactGlobalRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      SemanticExactGlobalRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback := by
  rw [semanticExactGlobalRestriction_preimage_eq_beta,
    semanticExactGlobalBeta_eq_alpha_of_not_selected input interpretation z
      omega k g endpoint_eq square_isPullback notSelected]

/-- In the selected branch, the source projector is the canonical
normalization of the actual complete geometry. -/
theorem semanticExactGlobalE_eq_normalization
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback =
      canonicalGeometryNormalization
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1
        (semanticExactDirectGeometryAt_admissible input interpretation z
          k g endpoint_eq selected.2) := by
  have h := semanticExactBarEAt_eq_endpoint_normalization input
    interpretation z omega k g endpoint_eq square_isPullback selected
  exact congrArg (semanticExactGlobalInclusion input).map h

/-- The nontrivial ambient-kernel involution, together with the target
identity, is a pair in the *full* complete-geometry centralizer. -/
noncomputable def semanticExactGlobalSelectedKernelPair
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    SemanticExactGlobalH input interpretation z omega k g endpoint_eq
      square_isPullback := by
  refine ⟨(ambientKernelGeometryAut
      (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g
        endpoint_eq).1
      (semanticExactDirectGeometryAt_admissible input interpretation z k g
        endpoint_eq selected.2), 1), ?_⟩
  constructor
  · rw [semanticExactGlobalE_eq_normalization input interpretation z omega k g
      endpoint_eq square_isPullback selected]
    exact (ambientKernelGeometry_comp_canonicalGeometryNormalization
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2)).trans
      (canonicalGeometryNormalization_comp_ambientKernelGeometry
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2)).symm
  · simp

/-- The full-category selected kernel pair vanishes under the image
restriction. -/
theorem semanticExactGlobalSelectedKernelPair_restriction
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (semanticExactGlobalSelectedKernelPair input interpretation z omega k g
          endpoint_eq square_isPullback selected) = 1 := by
  apply Prod.ext
  · apply Iso.ext
    apply Karoubi.Hom.ext
    change
      (idempotentEndpointRestrictionHom _ _
        (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
        (semanticExactGlobalE_idem input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq)
        (semanticExactGlobalSelectedKernelPair input interpretation z omega k g
          endpoint_eq square_isPullback selected)).1.hom.f = _
    rw [idempotentEndpointRestrictionHom_fst_hom_f]
    change
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback ≫
        (ambientKernelGeometryAut
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2)).hom ≫
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback = _
    change
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback ≫
        ambientKernelGeometry _ _ ≫
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback =
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback
    rw [semanticExactGlobalE_eq_normalization input interpretation z omega k g
      endpoint_eq square_isPullback selected]
    rw [← Category.assoc,
      canonicalGeometryNormalization_comp_ambientKernelGeometry]
    exact canonicalGeometryNormalization_idem _ _
  · apply Iso.ext
    apply Karoubi.Hom.ext
    change
      (idempotentEndpointRestrictionHom _ _
        (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
        (semanticExactGlobalE_idem input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq)
        (semanticExactGlobalSelectedKernelPair input interpretation z omega k g
          endpoint_eq square_isPullback selected)).2.hom.f = _
    rw [idempotentEndpointRestrictionHom_snd_hom_f]
    change semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
      (𝟙 _) ≫ semanticExactGlobalD input interpretation z omega k g
        endpoint_eq = semanticExactGlobalD input interpretation z omega k g
          endpoint_eq
    simpa only [Category.comp_id, Category.id_comp] using
      semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq

/-- The same complete-geometry pair fails compatibility with the original
reversible comparison. -/
theorem semanticExactGlobalSelectedKernelPair_not_raw
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactGlobalSelectedKernelPair input interpretation z omega k g
        endpoint_eq square_isPullback selected ∉
      SemanticExactGlobalRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback := by
  intro h
  have h' :
      (ambientKernelGeometryAut
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2)).hom ≫
          (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
            square_isPullback).hom =
        (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
          square_isPullback).hom := by
    change
      (ambientKernelGeometryAut
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq).1
        (semanticExactDirectGeometryAt_admissible input interpretation z k g
          endpoint_eq selected.2)).hom ≫
        (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
          square_isPullback).hom =
      (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
        square_isPullback).hom ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h
  have hid : (ambientKernelGeometryAut
      (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g
        endpoint_eq).1
      (semanticExactDirectGeometryAt_admissible input interpretation z k g
        endpoint_eq selected.2)).hom = 𝟙 _ := by
    apply (cancel_mono (semanticExactGlobalAlphaIso input interpretation z k g
      endpoint_eq square_isPullback).hom).1
    simpa using h'
  apply ambientKernelGeometryAut_ne_one
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1
    (semanticExactDirectGeometryAt_admissible input interpretation z k g
      endpoint_eq selected.2)
  apply Iso.ext
  exact hid

/-- Selected normalization fails to reflect raw alpha compatibility among
all complete-geometry endpoint automorphisms. -/
theorem semanticExactGlobalRestriction_preimage_ne_raw_of_selected
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    (SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback).comap
        (semanticExactGlobalRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) ≠
      SemanticExactGlobalRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback := by
  intro hEq
  have hmem :
      semanticExactGlobalSelectedKernelPair input interpretation z omega k g
          endpoint_eq square_isPullback selected ∈
        (SemanticExactGlobalImageComparison input interpretation z omega k g
          endpoint_eq square_isPullback).comap
          (semanticExactGlobalRestrictionHom input interpretation z omega k g
            endpoint_eq square_isPullback) := by
    apply Subgroup.mem_comap.mpr
    rw [semanticExactGlobalSelectedKernelPair_restriction]
    exact Subgroup.one_mem _
  rw [hEq] at hmem
  exact semanticExactGlobalSelectedKernelPair_not_raw input interpretation z
    omega k g endpoint_eq square_isPullback selected hmem

/-- Full complete-geometry comparison reflects alpha compatibility exactly
on the off-selector branch. -/
theorem semanticExactGlobalRestriction_preimage_eq_raw_iff_not_selected :
    ((SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback).comap
        (semanticExactGlobalRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      SemanticExactGlobalRawComparison input interpretation z omega k g
        endpoint_eq square_isPullback) ↔
      ¬ semanticExactBarSelectedAt input interpretation z omega := by
  constructor
  · intro h selected
    exact semanticExactGlobalRestriction_preimage_ne_raw_of_selected input
      interpretation z omega k g endpoint_eq square_isPullback selected h
  · intro notSelected
    exact semanticExactGlobalRestriction_preimage_eq_raw_of_not_selected input
      interpretation z omega k g endpoint_eq square_isPullback notSelected

end

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
