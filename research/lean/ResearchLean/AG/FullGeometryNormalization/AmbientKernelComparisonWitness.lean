import ResearchLean.AG.FullGeometryNormalization.AmbientKernelGeometryLift
import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonSection

/-!
# Ambient comparison-kernel witness

The ambient normalization-kernel involution at the source endpoint, paired
with the identity at the target, becomes the identity endpoint pair after
normalization.  Along an isomorphism it cannot preserve the raw comparison:
cancellation would make the source involution trivial.  Thus the ambient
preimage of the normalized comparison subgroup is strictly larger than the
raw comparison subgroup, including for the actual exact `barAlpha`.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct

/-- The ambient kernel witness at the source endpoint, with trivial target. -/
noncomputable def ambientKernelComparisonPair
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    Aut G × Aut H :=
  (ambientKernelAdmissibleGeometryAut G, 1)

/-- Endpoint normalization erases the ambient comparison witness completely. -/
theorem geometryNormalizationEndpointAutomorphismHom_ambientKernelComparisonPair
    {U : AtomCarrier.{u}}
    (G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    geometryNormalizationEndpointAutomorphismHom G H
        (ambientKernelComparisonPair G H) = 1 := by
  apply Prod.ext
  · exact geometryNormalizationFunctor_map_ambientKernelAdmissibleGeometryAut G
  · change (geometryNormalizationFunctor.{u, v} U).mapIso (Iso.refl H) = Iso.refl _
    simp

/-- The normalized image of the ambient pair preserves every normalized
comparison. -/
theorem ambientKernelComparisonPair_normalized_mem
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) :
    geometryNormalizationEndpointAutomorphismHom G H
        (ambientKernelComparisonPair G H) ∈
      normalizedGeometryComparisonSubgroup c.hom := by
  rw [geometryNormalizationEndpointAutomorphismHom_ambientKernelComparisonPair]
  exact Subgroup.one_mem _

/-- Along an isomorphism, the ambient source involution paired with the
identity target does not preserve the raw comparison. -/
theorem ambientKernelComparisonPair_not_raw_mem
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) :
    ambientKernelComparisonPair G H ∉
      rawGeometryNormalizationComparisonSubgroup c.hom := by
  intro hmem
  have h := (mem_rawGeometryNormalizationComparisonSubgroup).mp hmem
  change (ambientKernelAdmissibleGeometryAut G).hom ≫ c.hom =
    c.hom ≫ (𝟙 H) at h
  have hhom : (ambientKernelAdmissibleGeometryAut G).hom = 𝟙 G := by
    rw [Category.comp_id] at h
    simpa using congrArg (fun f => f ≫ c.inv) h
  apply ambientKernelAdmissibleGeometryAut_ne_one G
  apply Iso.ext
  exact hhom

/-- The ambient preimage of the normalized comparison subgroup is not the raw
comparison subgroup.  This is the carrier-set form of
`r_N⁻¹(Γ_N(c)) ≠ Γ_c`. -/
theorem geometryNormalizationEndpoint_preimage_normalized_ne_raw
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U}
    (c : G ≅ H) :
    (geometryNormalizationEndpointAutomorphismHom G H) ⁻¹'
        (normalizedGeometryComparisonSubgroup c.hom : Set _) ≠
      (rawGeometryNormalizationComparisonSubgroup c.hom : Set _) := by
  intro hsets
  have hpre : ambientKernelComparisonPair G H ∈
      (geometryNormalizationEndpointAutomorphismHom G H) ⁻¹'
        (normalizedGeometryComparisonSubgroup c.hom : Set _) :=
    ambientKernelComparisonPair_normalized_mem c
  have hraw : ambientKernelComparisonPair G H ∈
      rawGeometryNormalizationComparisonSubgroup c.hom := by
    exact (Set.ext_iff.mp hsets (ambientKernelComparisonPair G H)).mp hpre
  exact ambientKernelComparisonPair_not_raw_mem c hraw

/-! ## Actual exact `barAlpha` specialization -/

/-- The ambient source-kernel pair for the actual exact `barAlpha` endpoints. -/
noncomputable def authoredExactAmbientKernelComparisonPair
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    Aut (authoredExactDirectAdmissibleGeometryAt A z k g admissible) ×
      Aut (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible) :=
  ambientKernelComparisonPair _ _

/-- The actual witness normalizes to the identity endpoint pair. -/
theorem authoredExactAmbientKernelComparisonPair_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    geometryNormalizationEndpointAutomorphismHom
        (authoredExactDirectAdmissibleGeometryAt A z k g admissible)
        (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible) = 1 :=
  geometryNormalizationEndpointAutomorphismHom_ambientKernelComparisonPair _ _

/-- The actual witness lies over the normalized comparison subgroup of the
actual five-factor `barAlpha`. -/
theorem authoredExactAmbientKernelComparisonPair_normalized_mem
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    geometryNormalizationEndpointAutomorphismHom
        (authoredExactDirectAdmissibleGeometryAt A z k g admissible)
        (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible) ∈
      normalizedGeometryComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom :=
  ambientKernelComparisonPair_normalized_mem
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible)

/-- The actual witness does not preserve the raw five-factor `barAlpha`. -/
theorem authoredExactAmbientKernelComparisonPair_not_raw_mem
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactAmbientKernelComparisonPair A z k g admissible ∉
      rawGeometryNormalizationComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom :=
  ambientKernelComparisonPair_not_raw_mem
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible)

/-- For the actual five-factor `barAlpha`, the ambient preimage of the
normalized comparison subgroup differs from the raw comparison subgroup. -/
theorem authoredExactGeometryNormalizationEndpoint_preimage_normalized_ne_raw
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (geometryNormalizationEndpointAutomorphismHom
        (authoredExactDirectAdmissibleGeometryAt A z k g admissible)
        (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible)) ⁻¹'
        (normalizedGeometryComparisonSubgroup
          (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom : Set _) ≠
      (rawGeometryNormalizationComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom : Set _) :=
  geometryNormalizationEndpoint_preimage_normalized_ne_raw
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible)

/-- The source component of the actual witness fixes the pointed doctrine. -/
@[simp]
theorem authoredExactAmbientKernelComparisonPair_fst_hom_base_base
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactAmbientKernelComparisonPair A z k g admissible).1.hom.hom.base.base =
      ExtInstHom.id (packagePoint
        (authoredExactDirectAdmissibleGeometryAt A z k g admissible).obj.core) :=
  rfl

/-- The source component of the actual witness fixes coefficients. -/
@[simp]
theorem authoredExactAmbientKernelComparisonPair_fst_hom_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactAmbientKernelComparisonPair A z k g admissible).1.hom.hom.geometry.coefficientHom =
      RingHom.id k :=
  rfl

/-- The target identity component of the actual witness fixes the pointed
doctrine. -/
@[simp]
theorem authoredExactAmbientKernelComparisonPair_snd_hom_base_base
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactAmbientKernelComparisonPair A z k g admissible).2.hom.hom.base.base =
      ExtInstHom.id (packagePoint
        (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible).obj.core) :=
  rfl

/-- The target identity component of the actual witness fixes coefficients. -/
@[simp]
theorem authoredExactAmbientKernelComparisonPair_snd_hom_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactAmbientKernelComparisonPair A z k g admissible).2.hom.hom.geometry.coefficientHom =
      RingHom.id k :=
  rfl

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
