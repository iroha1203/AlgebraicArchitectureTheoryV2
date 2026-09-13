import ResearchLean.AG.FullGeometryNormalization.AmbientKernelGeometryFiberLift
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaComparisonGroup
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaClassification

/-!
# Reflection of the exact raw comparison group

For the actual exact `barAlpha`/`barBeta` comparison, the ambient preimage of
the Karoubi comparison group reflects the raw centralizing comparison group
exactly off the selector.  On the selected branch the canonical normalization
kernel involution at the source is an explicit counterexample.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence
open ComparisonInformationLoss

set_option maxHeartbeats 3000000

/-- On the selected branch, the source ambient-kernel involution paired with
the target identity is an endpoint-centralizing pair. -/
noncomputable def authoredExactSelectedAmbientKernelCentralizingPair
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    AuthoredExactCentralizingEndpointSubgroup A z omega k g := by
  refine ⟨(ambientKernelGeometryFiberAut
      (authoredExactDirectGeometryAt A z k g)
      (authoredExactDirectGeometryAt_admissible A z k g selected.2), 1), ?_⟩
  constructor
  · rw [authoredExactBarEAt_eq_endpoint_normalization A z omega k g selected]
    exact (ambientKernelGeometryFiberHom_comp_canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2)).trans
        (canonicalGeometryFiberNormalization_comp_ambientKernelGeometryFiberHom
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2)).symm
  · simp

/-- The selected witness has the ambient-kernel involution as its source. -/
@[simp] theorem authoredExactSelectedAmbientKernelCentralizingPair_fst
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactSelectedAmbientKernelCentralizingPair
      A z omega k g selected).1.1 =
      ambientKernelGeometryFiberAut
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g selected.2) :=
  rfl

/-- The selected witness has the identity as its target. -/
@[simp] theorem authoredExactSelectedAmbientKernelCentralizingPair_snd
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactSelectedAmbientKernelCentralizingPair
      A z omega k g selected).1.2 = 1 :=
  rfl

/-- The selected witness preserves the ambient `barBeta`, hence its endpoint
restriction belongs to the actual Karoubi comparison subgroup. -/
theorem authoredExactSelectedAmbientKernelCentralizingPair_mem_preimage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactSelectedAmbientKernelCentralizingPair A z omega k g selected ∈
      (AuthoredExactKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactEndpointRestrictionHom A z omega k g) := by
  rw [authoredExactEndpointRestriction_preimage_eq_barBeta]
  change
    (ambientKernelGeometryFiberAut
      (authoredExactDirectGeometryAt A z k g)
      (authoredExactDirectGeometryAt_admissible A z k g selected.2)).hom ≫
        authoredExactBarBetaAt A z omega k g =
      authoredExactBarBetaAt A z omega k g ≫ 𝟙 _
  rw [Category.comp_id]
  calc
    _ = (ambientKernelGeometryFiberAut
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2)).hom ≫
        (authoredExactBarEAt A z omega k g ≫
          authoredExactBarBetaAt A z omega k g) := by
            rw [authoredExactBarBetaAt_source_factorization]
    _ = ((ambientKernelGeometryFiberAut
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2)).hom ≫
        authoredExactBarEAt A z omega k g) ≫
          authoredExactBarBetaAt A z omega k g := by simp only [Category.assoc]
    _ = authoredExactBarEAt A z omega k g ≫
          authoredExactBarBetaAt A z omega k g := by
            rw [authoredExactBarEAt_eq_endpoint_normalization
              A z omega k g selected]
            change
              (ambientKernelGeometryFiberHom
                  (authoredExactDirectGeometryAt A z k g)
                  (authoredExactDirectGeometryAt_admissible
                    A z k g selected.2) ≫
                canonicalGeometryFiberNormalization
                  (authoredExactDirectGeometryAt A z k g)
                  (authoredExactDirectGeometryAt_admissible
                    A z k g selected.2)) ≫
                  authoredExactBarBetaAt A z omega k g =
                canonicalGeometryFiberNormalization
                  (authoredExactDirectGeometryAt A z k g)
                  (authoredExactDirectGeometryAt_admissible
                    A z k g selected.2) ≫
                  authoredExactBarBetaAt A z omega k g
            rw [ambientKernelGeometryFiberHom_comp_canonicalGeometryFiberNormalization]
    _ = _ := authoredExactBarBetaAt_source_factorization A z omega k g

/-- The same selected witness does not preserve the reversible raw
five-factor comparison `barAlpha`. -/
theorem authoredExactSelectedAmbientKernelCentralizingPair_not_mem_raw
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactSelectedAmbientKernelCentralizingPair A z omega k g selected ∉
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g := by
  intro h
  change
    (ambientKernelGeometryFiberAut
      (authoredExactDirectGeometryAt A z k g)
      (authoredExactDirectGeometryAt_admissible A z k g selected.2)).hom ≫
        (authoredExactBarAlphaIsoAt A z k g).hom =
      (authoredExactBarAlphaIsoAt A z k g).hom ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  have htrivial :
      (ambientKernelGeometryFiberAut
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g selected.2)).hom =
          𝟙 _ := by
    apply (cancel_mono (authoredExactBarAlphaIsoAt A z k g).hom).1
    simpa using h
  apply ambientKernelGeometryFiberAut_ne_one
    (authoredExactDirectGeometryAt A z k g)
    (authoredExactDirectGeometryAt_admissible A z k g selected.2)
  apply Iso.ext
  exact htrivial

/-- On the selected branch, the actual Karoubi comparison preimage is not the
raw centralizing comparison subgroup. -/
theorem authoredExactEndpointRestriction_preimage_ne_raw_of_selected
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (AuthoredExactKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactEndpointRestrictionHom A z omega k g) ≠
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g := by
  intro hEq
  have hmem := authoredExactSelectedAmbientKernelCentralizingPair_mem_preimage
    A z omega k g selected
  rw [hEq] at hmem
  exact authoredExactSelectedAmbientKernelCentralizingPair_not_mem_raw
    A z omega k g selected hmem

/-- Off the selector, `barE`, `barD` and the sandwich comparison introduce no
loss: the actual Karoubi comparison preimage is the raw comparison subgroup. -/
theorem authoredExactEndpointRestriction_preimage_eq_raw_of_not_selected
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (notSelected : ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))) :
    (AuthoredExactKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactEndpointRestrictionHom A z omega k g) =
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g := by
  have hbeta : authoredExactBarBetaAt A z omega k g =
      (authoredExactBarAlphaIsoAt A z k g).hom := by
    rw [authoredExactBarBetaAt_factor,
      authoredExactBarDAt_eq_id A z omega k g notSelected]
    simp
  rw [authoredExactEndpointRestriction_preimage_eq_barBeta]
  ext pair
  change
    pair.1.1.hom ≫ authoredExactBarBetaAt A z omega k g =
        authoredExactBarBetaAt A z omega k g ≫ pair.1.2.hom ↔
      pair.1.1.hom ≫ (authoredExactBarAlphaIsoAt A z k g).hom =
        (authoredExactBarAlphaIsoAt A z k g).hom ≫ pair.1.2.hom
  rw [hbeta]

/-- G-122(D)'s selector reflection theorem for the actual exact comparison. -/
theorem authoredExactEndpointRestriction_preimage_eq_raw_iff_not_selected
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    ((AuthoredExactKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactEndpointRestrictionHom A z omega k g) =
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g) ↔
      ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)) := by
  constructor
  · intro hEq selected
    exact authoredExactEndpointRestriction_preimage_ne_raw_of_selected
      A z omega k g selected hEq
  · intro notSelected
    exact authoredExactEndpointRestriction_preimage_eq_raw_of_not_selected
      (A := A) (z := z) (omega := omega) (k := k) (g := g) notSelected

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
