import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorBottomExactness

/-!
# Exact barBeta preimage for the semantic selector

The image comparison condition under endpoint restriction is precisely the
ambient `barBeta` equation on centralizing pairs. This identifies the full
preimage and its bottom-qualified part without choosing a selector branch.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

/-- For a generic idempotent square, the sandwich image preserves the
Karoubi comparison exactly when the original centralizing pair preserves the
ambient sandwich arrow. -/
private theorem idempotentEndpointRestriction_mem_image_iff_mem_sandwich
    {E : Type u} [Category.{v} E] {X Y : E}
    (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (pair : centralizingEndpointSubgroup X Y e d) :
    idempotentEndpointRestrictionHom X Y e d he hd pair ∈
        comparisonAutomorphismSubgroup
          (idempotentImageComparison c e d he hd hedc) ↔
      pair.1.1.hom ≫ (e ≫ c ≫ d) =
        (e ≫ c ≫ d) ≫ pair.1.2.hom := by
  have hsource : e ≫ (e ≫ c ≫ d) = e ≫ c ≫ d := by
    simp only [← Category.assoc, he]
  have htarget : (e ≫ c ≫ d) ≫ d = e ≫ c ≫ d := by
    simp only [Category.assoc, hd]
  have sourceSandwich :
      (e ≫ pair.1.1.hom ≫ e) ≫ (e ≫ c ≫ d) =
        pair.1.1.hom ≫ (e ≫ c ≫ d) := by
    calc
      (e ≫ pair.1.1.hom ≫ e) ≫ (e ≫ c ≫ d) =
          e ≫ pair.1.1.hom ≫ (e ≫ (e ≫ c ≫ d)) := by
            simp only [Category.assoc]
      _ = e ≫ pair.1.1.hom ≫ (e ≫ c ≫ d) := by rw [hsource]
      _ = (e ≫ pair.1.1.hom) ≫ (e ≫ c ≫ d) :=
        (Category.assoc _ _ _).symm
      _ = (pair.1.1.hom ≫ e) ≫ (e ≫ c ≫ d) := by
        rw [pair.property.1]
      _ = pair.1.1.hom ≫ (e ≫ (e ≫ c ≫ d)) :=
        Category.assoc _ _ _
      _ = pair.1.1.hom ≫ (e ≫ c ≫ d) := by rw [hsource]
  have targetSandwich :
      (e ≫ c ≫ d) ≫ (d ≫ pair.1.2.hom ≫ d) =
        (e ≫ c ≫ d) ≫ pair.1.2.hom := by
    calc
      (e ≫ c ≫ d) ≫ (d ≫ pair.1.2.hom ≫ d) =
          ((e ≫ c ≫ d) ≫ d) ≫ pair.1.2.hom ≫ d := by
            simp only [Category.assoc]
      _ = (e ≫ c ≫ d) ≫ pair.1.2.hom ≫ d := by rw [htarget]
      _ = (e ≫ c ≫ d) ≫ (pair.1.2.hom ≫ d) :=
        rfl
      _ = (e ≫ c ≫ d) ≫ (d ≫ pair.1.2.hom) := by
        rw [pair.property.2]
      _ = ((e ≫ c ≫ d) ≫ d) ≫ pair.1.2.hom :=
        (Category.assoc _ _ _).symm
      _ = (e ≫ c ≫ d) ≫ pair.1.2.hom := by rw [htarget]
  constructor
  · intro h
    have hUnderlying :
      (e ≫ pair.1.1.hom ≫ e) ≫ (e ≫ c ≫ d) =
        (e ≫ c ≫ d) ≫ (d ≫ pair.1.2.hom ≫ d) := by
      simpa only [Karoubi.comp_f,
        idempotentEndpointRestrictionHom_fst_hom_f,
        idempotentEndpointRestrictionHom_snd_hom_f,
        idempotentImageComparison_f] using congrArg Karoubi.Hom.f h
    exact sourceSandwich.symm.trans (hUnderlying.trans targetSandwich)
  · intro h
    change
      (idempotentEndpointRestrictionHom X Y e d he hd pair).1.hom ≫
          idempotentImageComparison c e d he hd hedc =
        idempotentImageComparison c e d he hd hedc ≫
          (idempotentEndpointRestrictionHom X Y e d he hd pair).2.hom
    apply Karoubi.Hom.ext
    simpa only [Karoubi.comp_f,
      idempotentEndpointRestrictionHom_fst_hom_f,
      idempotentEndpointRestrictionHom_snd_hom_f,
      idempotentImageComparison_f] using
        sourceSandwich.trans (h.trans targetSandwich.symm)

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

/-- The actual semantic image comparison condition is the ambient `barBeta`
equation on the centralizer. -/
theorem semanticExactEndpointRestriction_mem_image_iff_mem_barBeta
    (pair : SemanticExactCentralizingEndpointSubgroup input interpretation z
      omega k g endpoint_eq square_isPullback) :
    semanticExactEndpointRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback pair ∈
      SemanticExactKaroubiComparisonSubgroup input interpretation z omega k g
        endpoint_eq square_isPullback ↔
      pair.1.1.hom ≫ semanticExactBarBetaAt input interpretation z omega k g
        endpoint_eq square_isPullback =
      semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫ pair.1.2.hom := by
  have generic := idempotentEndpointRestriction_mem_image_iff_mem_sandwich
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
  have hfactor :
      semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          square_isPullback).hom ≫
        semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback := by
    have h := congrArg
      (fun f => f ≫ semanticExactBarDAt input interpretation z omega k g
        endpoint_eq)
      (semanticExactBarAlphaAt_projector_comm input interpretation z omega k g
        endpoint_eq square_isPullback)
    simpa only [Category.assoc, semanticExactBarDAt_idem,
      semanticExactBarBetaAt] using h
  simpa only [semanticExactIdempotentImageComparison_eq_barBeta,
    hfactor] using generic

/-- Semantic form of (7.36), inside the generated centralizer `H`. -/
theorem semanticExactEndpointRestriction_preimage_eq_barBeta :
    (SemanticExactKaroubiComparisonSubgroup input interpretation z omega k g
      endpoint_eq square_isPullback).comap
        (semanticExactEndpointRestrictionHom input interpretation z omega k g
          endpoint_eq square_isPullback) =
      centralizingCompatibleSubgroup
        (semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactBarEAt input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactBarDAt input interpretation z omega k g endpoint_eq) := by
  ext pair
  exact semanticExactEndpointRestriction_mem_image_iff_mem_barBeta input
    interpretation z omega k g endpoint_eq square_isPullback pair

/-- The ambient form of (7.36): the preimage is `H ∩ Γ_barBeta`. -/
theorem semanticExactEndpointRestriction_preimage_map_eq_inf_barBeta :
    Subgroup.map
        (SemanticExactCentralizingEndpointSubgroup input interpretation z omega
          k g endpoint_eq square_isPullback).subtype
        ((SemanticExactKaroubiComparisonSubgroup input interpretation z omega k g
          endpoint_eq square_isPullback).comap
          (semanticExactEndpointRestrictionHom input interpretation z omega k g
            endpoint_eq square_isPullback)) =
      SemanticExactCentralizingEndpointSubgroup input interpretation z omega k g
          endpoint_eq square_isPullback ⊓
        comparisonAutomorphismSubgroup
          (semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
            square_isPullback) := by
  rw [semanticExactEndpointRestriction_preimage_eq_barBeta]
  exact centralizingCompatibleSubgroup_map_eq_inf
    (semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)

/-- Equation (7.36) with literal package-bottom fixity retained. -/
theorem semanticExactBottomRestrictionPreimage_eq_barBeta :
    SemanticExactBottomRestrictionPreimageSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback =
      SemanticExactBottomCentralizingEndpointSubgroup input interpretation z
          omega k g endpoint_eq square_isPullback ⊓
        centralizingCompatibleSubgroup
          (semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
            square_isPullback)
          (semanticExactBarEAt input interpretation z omega k g endpoint_eq
            square_isPullback)
          (semanticExactBarDAt input interpretation z omega k g endpoint_eq) := by
  unfold SemanticExactBottomRestrictionPreimageSubgroup
  rw [semanticExactEndpointRestriction_preimage_eq_barBeta]

end

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
