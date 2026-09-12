import ResearchLean.AG.ComparisonInformationLoss.KaroubiRestriction
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaClassification

/-!
# Comparison groups of the exact complete-geometry image

This module begins G-122(D) on the same exact comparison constructed in
G-122(B)--(C).  It specializes G-120's centralizer sandwich homomorphism to
`barE`, `barD`, and the reversible raw comparison `barAlpha`, then identifies
the ambient preimage of the actual Karoubi comparison group with the
centralizing pairs that preserve the same `barBeta`.

## Implementation notes

The groups and homomorphisms are direct specializations of G-120's accepted
`Subgroup.comap`, centralizer, and sandwich APIs.  A duplicate automorphism
structure was rejected because it would obscure both the raw `barAlpha`
equation and the actual Karoubi arrow.  The preimage theorem is stated with
literal `authoredExactBarBetaAt`, rather than only the generic sandwich
presentation, so it cannot be mistaken for reflection of the reversible raw
comparison.  No section or reflection conclusion is included here; those
require the separate endpoint-lift and kernel constructions fixed by D.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation CrossStageCoherence DoctrineFiberProduct
open GeometryTransport TransportCoherence
open ComparisonInformationLoss

set_option maxHeartbeats 3000000

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

/-- The exact projectors intertwine the reversible raw comparison. -/
theorem authoredExactBarAlphaAt_projector_comm
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarEAt A z omega k g ≫
        (authoredExactBarAlphaIsoAt A z k g).hom =
      (authoredExactBarAlphaIsoAt A z k g).hom ≫
        authoredExactBarDAt A z omega k g := by
  simp [authoredExactBarEAt, Category.assoc]

/-- The generic sandwich presentation of the image comparison is the literal
exact `barBeta`. -/
theorem authoredExactBarESandwichAlphaD_eq_barBeta
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarEAt A z omega k g ≫
          (authoredExactBarAlphaIsoAt A z k g).hom ≫
      authoredExactBarDAt A z omega k g =
      authoredExactBarBetaAt A z omega k g := by
  simpa only [authoredExactBarBetaAt_factor] using
    authoredExactBarBetaAt_source_factorization A z omega k g

/-- The complete-geometry centralizer product `H^cent` for `barE,barD`. -/
noncomputable abbrev AuthoredExactCentralizingEndpointSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :=
  centralizingEndpointSubgroup
    (authoredExactDirectGeometryAt A z k g)
    (authoredExactViaBaseGeometryAt A z k g)
    (authoredExactBarEAt A z omega k g)
    (authoredExactBarDAt A z omega k g)

/-- The subgroup `Gamma_c^cent` for the reversible comparison `barAlpha`. -/
noncomputable abbrev AuthoredExactCentralizingRawComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :=
  centralizingCompatibleSubgroup
    (authoredExactBarAlphaIsoAt A z k g).hom
    (authoredExactBarEAt A z omega k g)
    (authoredExactBarDAt A z omega k g)

/-- The comparison group `Gamma_a` of the actual Karoubi isomorphism. -/
noncomputable abbrev AuthoredExactKaroubiComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :=
  comparisonAutomorphismSubgroup
    (authoredExactBarBetaKaroubiIsoAt A z omega k g).hom

/-- The generic idempotent-image comparison is the actual `barBeta` Karoubi
arrow, including its full underlying complete-geometry morphism. -/
theorem authoredExactIdempotentImageComparison_eq_barBeta
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    idempotentImageComparison
        (authoredExactBarAlphaIsoAt A z k g).hom
        (authoredExactBarEAt A z omega k g)
        (authoredExactBarDAt A z omega k g)
        (authoredExactBarEAt_idem A z omega k g)
        (authoredExactBarDAt_idem A z omega k g)
        (authoredExactBarAlphaAt_projector_comm A z omega k g) =
      (authoredExactBarBetaKaroubiIsoAt A z omega k g).hom := by
  apply Karoubi.Hom.ext
  exact authoredExactBarESandwichAlphaD_eq_barBeta A z omega k g

/-- G-122(D)'s ambient sandwich homomorphism `r` on the actual exact
complete-geometry endpoints. -/
noncomputable def authoredExactEndpointRestrictionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactCentralizingEndpointSubgroup A z omega k g →*
      (Aut (authoredExactBarESourceKaroubiAt A z omega k g) ×
        Aut (authoredExactBarDTargetKaroubiAt A z omega k g)) :=
  idempotentEndpointRestrictionHom
    (authoredExactDirectGeometryAt A z k g)
    (authoredExactViaBaseGeometryAt A z k g)
    (authoredExactBarEAt A z omega k g)
    (authoredExactBarDAt A z omega k g)
    (authoredExactBarEAt_idem A z omega k g)
    (authoredExactBarDAt_idem A z omega k g)

/-- The exact ambient restriction has source component `barE u barE`. -/
@[simp] theorem authoredExactEndpointRestrictionHom_fst_hom_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactCentralizingEndpointSubgroup A z omega k g) :
    (authoredExactEndpointRestrictionHom A z omega k g pair).1.hom.f =
      authoredExactBarEAt A z omega k g ≫ pair.1.1.hom ≫
        authoredExactBarEAt A z omega k g :=
  idempotentEndpointRestrictionHom_fst_hom_f _ _ _ _ _ _ pair

/-- The exact ambient restriction has target component `barD v barD`. -/
@[simp] theorem authoredExactEndpointRestrictionHom_snd_hom_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactCentralizingEndpointSubgroup A z omega k g) :
    (authoredExactEndpointRestrictionHom A z omega k g pair).2.hom.f =
      authoredExactBarDAt A z omega k g ≫ pair.1.2.hom ≫
        authoredExactBarDAt A z omega k g :=
  idempotentEndpointRestrictionHom_snd_hom_f _ _ _ _ _ _ pair

/-- The ambient exact sandwich sends every `barAlpha`-compatible centralizing
pair to a pair preserving the actual Karoubi comparison `barBeta`. -/
theorem authoredExactEndpointRestriction_preserves_comparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactCentralizingRawComparisonSubgroup A z omega k g) :
    authoredExactEndpointRestrictionHom A z omega k g pair.1 ∈
      AuthoredExactKaroubiComparisonSubgroup A z omega k g := by
  have h := idempotentEndpointRestriction_preserves_comparison
      (authoredExactBarAlphaIsoAt A z k g).hom
      (authoredExactBarEAt A z omega k g)
      (authoredExactBarDAt A z omega k g)
      (authoredExactBarEAt_idem A z omega k g)
      (authoredExactBarDAt_idem A z omega k g)
      (authoredExactBarAlphaAt_projector_comm A z omega k g) pair
  simpa only [authoredExactIdempotentImageComparison_eq_barBeta] using h

/-- The subgroup-image inclusion used to restrict `r` to `bar r`. -/
theorem authoredExactEndpointRestriction_map_le
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Subgroup.map (authoredExactEndpointRestrictionHom A z omega k g)
        (AuthoredExactCentralizingRawComparisonSubgroup A z omega k g) ≤
      AuthoredExactKaroubiComparisonSubgroup A z omega k g := by
  rintro image ⟨pair, hpair, rfl⟩
  exact authoredExactEndpointRestriction_preserves_comparison
    A z omega k g ⟨pair, hpair⟩

/-- G-122(D)'s restricted homomorphism
`bar r : Gamma_c^cent → Gamma_a`. -/
noncomputable def authoredExactCompatibleRestrictionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactCentralizingRawComparisonSubgroup A z omega k g →*
      AuthoredExactKaroubiComparisonSubgroup A z omega k g :=
  restrictedSubgroupHom (authoredExactEndpointRestrictionHom A z omega k g)
    (AuthoredExactCentralizingRawComparisonSubgroup A z omega k g)
    (AuthoredExactKaroubiComparisonSubgroup A z omega k g)
    (authoredExactEndpointRestriction_map_le A z omega k g)

/-- Evaluation of `bar r` retains the actual ambient sandwich pair. -/
@[simp] theorem authoredExactCompatibleRestrictionHom_coe
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactCentralizingRawComparisonSubgroup A z omega k g) :
    ((authoredExactCompatibleRestrictionHom A z omega k g pair :
        AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
      Aut (authoredExactBarESourceKaroubiAt A z omega k g) ×
        Aut (authoredExactBarDTargetKaroubiAt A z omega k g)) =
      authoredExactEndpointRestrictionHom A z omega k g pair.1 :=
  rfl

/-- On centralizing endpoint pairs, preserving the actual image comparison
after sandwiching is equivalent to preserving the same ambient `barBeta`. -/
theorem authoredExactEndpointRestriction_mem_image_iff_mem_barBeta
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactCentralizingEndpointSubgroup A z omega k g) :
    authoredExactEndpointRestrictionHom A z omega k g pair ∈
        AuthoredExactKaroubiComparisonSubgroup A z omega k g ↔
      pair.1.1.hom ≫ authoredExactBarBetaAt A z omega k g =
        authoredExactBarBetaAt A z omega k g ≫ pair.1.2.hom := by
  have generic := idempotentEndpointRestriction_mem_image_iff_mem_sandwich
    (authoredExactBarAlphaIsoAt A z k g).hom
    (authoredExactBarEAt A z omega k g)
    (authoredExactBarDAt A z omega k g)
    (authoredExactBarEAt_idem A z omega k g)
    (authoredExactBarDAt_idem A z omega k g)
    (authoredExactBarAlphaAt_projector_comm A z omega k g) pair
  simpa only [authoredExactIdempotentImageComparison_eq_barBeta,
    authoredExactBarESandwichAlphaD_eq_barBeta] using generic

/-- G-122(D)'s exact preimage identity: `r⁻¹(Gamma_a)` consists precisely
of centralizing pairs that preserve the same ambient `barBeta`. -/
theorem authoredExactEndpointRestriction_preimage_eq_barBeta
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (AuthoredExactKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactEndpointRestrictionHom A z omega k g) =
      centralizingCompatibleSubgroup
        (authoredExactBarBetaAt A z omega k g)
        (authoredExactBarEAt A z omega k g)
        (authoredExactBarDAt A z omega k g) := by
  ext pair
  exact authoredExactEndpointRestriction_mem_image_iff_mem_barBeta
    A z omega k g pair

/-- Ambient presentation of the exact preimage as
`H^cent ∩ Gamma_barBeta`. -/
theorem authoredExactEndpointRestriction_preimage_map_eq_inf_barBeta
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Subgroup.map
        (AuthoredExactCentralizingEndpointSubgroup A z omega k g).subtype
        ((AuthoredExactKaroubiComparisonSubgroup A z omega k g).comap
          (authoredExactEndpointRestrictionHom A z omega k g)) =
      AuthoredExactCentralizingEndpointSubgroup A z omega k g ⊓
        comparisonAutomorphismSubgroup
          (authoredExactBarBetaAt A z omega k g) := by
  rw [authoredExactEndpointRestriction_preimage_eq_barBeta]
  exact centralizingCompatibleSubgroup_map_eq_inf
    (authoredExactBarBetaAt A z omega k g)
    (authoredExactBarEAt A z omega k g)
    (authoredExactBarDAt A z omega k g)

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
