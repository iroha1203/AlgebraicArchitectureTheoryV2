import ResearchLean.AG.FullGeometryNormalization.GeometryBottomQualifiedComparisonGroup
import ResearchLean.AG.FullGeometryNormalization.AmbientKernelComparisonWitness

/-!
# Bottom-qualified canonical comparison for the actual exact barAlpha

The canonical normalization section for the generated five-factor `barAlpha`
retains the endpoint bottom maps and coefficient maps.  It therefore restricts
to the two-ended bottom-qualified comparison groups.  The actual ambient
normalization-kernel involution is itself bottom-trivial at both endpoints, but
normalization erases it; this gives the required bottom-qualified failure of
reflection without adding a premise to the authored exact input.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

set_option synthInstance.maxHeartbeats 100000

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct

/-! ## Actual bottom-qualified comparison groups and section -/

/-- Bottom-qualified raw comparison-preserving changes for the actual
five-factor `barAlpha`. -/
noncomputable abbrev AuthoredExactCanonicalRawBottomComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :=
  rawGeometryBottomQualifiedComparisonSubgroup
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom

/-- Bottom-qualified normalized comparison-preserving changes for the actual
five-factor `barAlpha`. -/
noncomputable abbrev AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :=
  normalizedGeometryBottomQualifiedComparisonSubgroup
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom

set_option synthInstance.maxHeartbeats 100000 in
/-- The actual canonical comparison section restricts to endpoint changes
which are trivial under both bottom projections. -/
noncomputable def authoredExactCanonicalBottomComparisonSectionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
        A z k g admissible →*
      AuthoredExactCanonicalRawBottomComparisonSubgroup A z k g admissible where
  toFun pair := by
    let lifted := authoredExactCanonicalComparisonSectionHom
      A z k g admissible pair.1
    refine ⟨lifted, ?_⟩
    rw [mem_rawGeometryBottomQualifiedComparisonSubgroup]
    constructor
    · apply Iso.ext
      change lifted.1.1.hom.hom.base.base = ExtInstHom.id _
      rw [authoredExactCanonicalComparisonSection_fst_hom_base_base]
      have h := congrArg Iso.hom pair.2.1
      exact h
    · apply Iso.ext
      change lifted.1.2.hom.hom.base.base = ExtInstHom.id _
      rw [authoredExactCanonicalComparisonSection_snd_hom_base_base]
      have h := congrArg Iso.hom pair.2.2
      exact h
  map_one' := by
    apply Subtype.ext
    exact map_one (authoredExactCanonicalComparisonSectionHom
      A z k g admissible)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (authoredExactCanonicalComparisonSectionHom
      A z k g admissible) first.1 second.1

/-- Forgetting bottom qualification recovers the existing actual canonical
comparison section. -/
@[simp]
theorem authoredExactCanonicalBottomComparisonSectionHom_val
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    (authoredExactCanonicalBottomComparisonSectionHom
        A z k g admissible pair).1 =
      authoredExactCanonicalComparisonSectionHom
        A z k g admissible pair.1 :=
  rfl

/-- Bottom-qualified normalization of the restricted section is the supplied
normalized compatible pair. -/
theorem authoredExactCanonicalBottomComparisonSection_rightInverse
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    geometryNormalizationBottomQualifiedComparisonSubgroupHom
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
        (authoredExactCanonicalBottomComparisonSectionHom
          A z k g admissible pair) = pair := by
  apply Subtype.ext
  change geometryNormalizationComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
      (authoredExactCanonicalComparisonSectionHom
        A z k g admissible pair.1) = pair.1
  exact authoredExactCanonicalComparisonSection_rightInverse A z k g admissible pair.1

/-! ## Explicit endpoint retention -/

@[simp]
theorem authoredExactCanonicalBottomComparisonSection_fst_hom_base_base
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    (authoredExactCanonicalBottomComparisonSectionHom
        A z k g admissible pair).1.1.1.hom.hom.base.base =
      pair.1.1.1.hom.f.hom.base.base := by
  change (authoredExactCanonicalComparisonSectionHom
      A z k g admissible pair.1).1.1.hom.hom.base.base = _
  exact authoredExactCanonicalComparisonSection_fst_hom_base_base
    A z k g admissible pair.1

@[simp]
theorem authoredExactCanonicalBottomComparisonSection_fst_hom_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    (authoredExactCanonicalBottomComparisonSectionHom
        A z k g admissible pair).1.1.1.hom.hom.geometry.coefficientHom =
      pair.1.1.1.hom.f.hom.geometry.coefficientHom := by
  change (authoredExactCanonicalComparisonSectionHom
      A z k g admissible pair.1).1.1.hom.hom.geometry.coefficientHom = _
  exact authoredExactCanonicalComparisonSection_fst_hom_coefficientHom
    A z k g admissible pair.1

@[simp]
theorem authoredExactCanonicalBottomComparisonSection_snd_hom_base_base
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    (authoredExactCanonicalBottomComparisonSectionHom
        A z k g admissible pair).1.1.2.hom.hom.base.base =
      pair.1.1.2.hom.f.hom.base.base := by
  change (authoredExactCanonicalComparisonSectionHom
      A z k g admissible pair.1).1.2.hom.hom.base.base = _
  exact authoredExactCanonicalComparisonSection_snd_hom_base_base
    A z k g admissible pair.1

@[simp]
theorem authoredExactCanonicalBottomComparisonSection_snd_hom_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    (authoredExactCanonicalBottomComparisonSectionHom
        A z k g admissible pair).1.1.2.hom.hom.geometry.coefficientHom =
      pair.1.1.2.hom.f.hom.geometry.coefficientHom := by
  change (authoredExactCanonicalComparisonSectionHom
      A z k g admissible pair.1).1.2.hom.hom.geometry.coefficientHom = _
  exact authoredExactCanonicalComparisonSection_snd_hom_coefficientHom
    A z k g admissible pair.1

/-! ## Bottom-qualified ambient witness and failure of reflection -/

/-- The actual ambient source-kernel pair is bottom-trivial at both raw
endpoints. -/
theorem authoredExactAmbientKernelComparisonPair_raw_bottom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    rawGeometryBottomAutomorphismHom
        (authoredExactDirectAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible).1 = 1 ∧
      rawGeometryBottomAutomorphismHom
        (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible).2 = 1 := by
  constructor <;> apply Iso.ext <;> rfl

/-- The source component of the bottom-qualified ambient witness is genuinely
nonidentity before canonical normalization. -/
theorem authoredExactAmbientKernelComparisonPair_source_ne_one
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (authoredExactAmbientKernelComparisonPair A z k g admissible).1 ≠ 1 :=
  ambientKernelAdmissibleGeometryAut_ne_one _

/-- The actual nontrivial witness simultaneously fixes the bottom and
coefficient maps at both endpoints. -/
theorem authoredExactAmbientKernelComparisonPair_bottom_coefficient_packet
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    rawGeometryBottomAutomorphismHom
        (authoredExactDirectAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible).1 = 1 ∧
      (authoredExactAmbientKernelComparisonPair
          A z k g admissible).1.hom.hom.geometry.coefficientHom = RingHom.id k ∧
      rawGeometryBottomAutomorphismHom
        (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible).2 = 1 ∧
      (authoredExactAmbientKernelComparisonPair
          A z k g admissible).2.hom.hom.geometry.coefficientHom = RingHom.id k := by
  exact ⟨(authoredExactAmbientKernelComparisonPair_raw_bottom
      A z k g admissible).1,
    authoredExactAmbientKernelComparisonPair_fst_hom_coefficientHom
      A z k g admissible,
    (authoredExactAmbientKernelComparisonPair_raw_bottom
      A z k g admissible).2,
    authoredExactAmbientKernelComparisonPair_snd_hom_coefficientHom
      A z k g admissible⟩

/-- After normalization the actual bottom-trivial ambient pair lies in the
bottom-qualified normalized comparison group. -/
theorem authoredExactAmbientKernelComparisonPair_normalized_bottom_mem
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    let normalizedPair : normalizedGeometryComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom :=
      ⟨geometryNormalizationEndpointAutomorphismHom
          (authoredExactDirectAdmissibleGeometryAt A z k g admissible)
          (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible)
          (authoredExactAmbientKernelComparisonPair A z k g admissible),
        authoredExactAmbientKernelComparisonPair_normalized_mem
          A z k g admissible⟩
    normalizedPair ∈ normalizedGeometryBottomQualifiedComparisonSubgroup
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom := by
  dsimp only
  rw [mem_normalizedGeometryBottomQualifiedComparisonSubgroup]
  have hbottom := authoredExactAmbientKernelComparisonPair_raw_bottom
    A z k g admissible
  exact ⟨geometryNormalizationEndpointAutomorphism_preserves_bottom _ _ hbottom.1,
    geometryNormalizationEndpointAutomorphism_preserves_bottom _ _ hbottom.2⟩

/-- Before normalization the same bottom-trivial ambient pair does not
preserve the actual raw `barAlpha`.  It is therefore an ambient qualified
witness, not an element of the restricted lift-fiber kernel. -/
theorem authoredExactAmbientKernelComparisonPair_not_raw_bottom_comparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (rawGeometryBottomAutomorphismHom
        (authoredExactDirectAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible).1 = 1 ∧
      rawGeometryBottomAutomorphismHom
        (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible)
        (authoredExactAmbientKernelComparisonPair A z k g admissible).2 = 1) ∧
      authoredExactAmbientKernelComparisonPair A z k g admissible ∉
        rawGeometryNormalizationComparisonSubgroup
          (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom :=
  ⟨authoredExactAmbientKernelComparisonPair_raw_bottom A z k g admissible,
    authoredExactAmbientKernelComparisonPair_not_raw_mem A z k g admissible⟩

/-- Inside the ambient bottom-trivial endpoint group, the preimage of the
normalized comparison condition is not the raw comparison condition. -/
theorem authoredExactCanonicalBottomComparison_preimage_ne_raw
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    {pair : Aut (authoredExactDirectAdmissibleGeometryAt A z k g admissible) ×
        Aut (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible) |
      rawGeometryBottomAutomorphismHom _ pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom _ pair.2 = 1 ∧
      geometryNormalizationEndpointAutomorphismHom _ _ pair ∈
        normalizedGeometryComparisonSubgroup
          (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom} ≠
    {pair : Aut (authoredExactDirectAdmissibleGeometryAt A z k g admissible) ×
        Aut (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible) |
      rawGeometryBottomAutomorphismHom _ pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom _ pair.2 = 1 ∧
      pair ∈ rawGeometryNormalizationComparisonSubgroup
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom} := by
  intro hsets
  let witness := authoredExactAmbientKernelComparisonPair A z k g admissible
  have hbottom := authoredExactAmbientKernelComparisonPair_raw_bottom
    A z k g admissible
  have hnormalized := authoredExactAmbientKernelComparisonPair_normalized_mem
    A z k g admissible
  have hleft : witness ∈ {pair : Aut
      (authoredExactDirectAdmissibleGeometryAt A z k g admissible) × Aut
      (authoredExactViaBaseAdmissibleGeometryAt A z k g admissible) |
      rawGeometryBottomAutomorphismHom _ pair.1 = 1 ∧
      rawGeometryBottomAutomorphismHom _ pair.2 = 1 ∧
      geometryNormalizationEndpointAutomorphismHom _ _ pair ∈
        normalizedGeometryComparisonSubgroup
          (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom} :=
    ⟨hbottom.1, hbottom.2, hnormalized⟩
  have hright := (Set.ext_iff.mp hsets witness).mp hleft
  exact authoredExactAmbientKernelComparisonPair_not_raw_mem
    A z k g admissible hright.2.2

/-- The canonical bottom-qualified comparison map is split-surjective. -/
theorem authoredExactCanonicalBottomComparisonHom_surjective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    Function.Surjective
      (geometryNormalizationBottomQualifiedComparisonSubgroupHom
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom) := by
  intro pair
  exact ⟨authoredExactCanonicalBottomComparisonSectionHom
      A z k g admissible pair,
    authoredExactCanonicalBottomComparisonSection_rightInverse
      A z k g admissible pair⟩

/-! ## Split exactness and bottom-qualified lift fibers -/

/-- The kernel inclusion followed by bottom-qualified canonical normalization
is a split short exact sequence. -/
theorem authoredExactCanonicalBottomComparison_shortExact
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    ComparisonInformationLoss.IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
  exact ⟨Subtype.val_injective,
    by
      rw [MonoidHom.mulExact_iff]
      exact p.ker.range_subtype.symm,
    authoredExactCanonicalBottomComparisonHom_surjective A z k g admissible⟩

/-- The fiber of bottom-qualified raw comparison lifts over a fixed
bottom-qualified normalized change. -/
noncomputable abbrev AuthoredExactCanonicalBottomComparisonLiftFiber
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :=
  {a : AuthoredExactCanonicalRawBottomComparisonSubgroup A z k g admissible //
    geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom a = t}

/-- Right multiplication by the restricted bottom-qualified kernel acts on
each lift fiber. -/
noncomputable instance authoredExactCanonicalBottomComparisonLiftFiberSMul
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    SMul p.kerᵐᵒᵖ
      (AuthoredExactCanonicalBottomComparisonLiftFiber A z k g admissible t) := by
  dsimp
  let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
    (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- The bottom-qualified right-kernel action satisfies the group action laws. -/
noncomputable instance authoredExactCanonicalBottomComparisonLiftFiberMulAction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    MulAction p.kerᵐᵒᵖ
      (AuthoredExactCanonicalBottomComparisonLiftFiber A z k g admissible t) := by
  dsimp
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 * (((MulOpposite.unop second).1 :
        AuthoredExactCanonicalRawBottomComparisonSubgroup A z k g admissible) *
      ((MulOpposite.unop first).1 :
        AuthoredExactCanonicalRawBottomComparisonSubgroup A z k g admissible)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : AuthoredExactCanonicalRawBottomComparisonSubgroup
        A z k g admissible) = lift.1
    simp

/-- The restricted bottom-qualified kernel action is free on every lift
fiber. -/
theorem authoredExactCanonicalBottomComparisonLiftFiber_action_free
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible)
    (lift : AuthoredExactCanonicalBottomComparisonLiftFiber
      A z k g admissible t) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    Function.Injective (fun kernelValue : p.kerᵐᵒᵖ => kernelValue • lift) := by
  dsimp
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have underlying := congrArg
    (fun value : AuthoredExactCanonicalBottomComparisonLiftFiber
      A z k g admissible t => value.1) equality
  exact mul_left_cancel underlying

/-- The restricted bottom-qualified kernel action is transitive on every lift
fiber. -/
theorem authoredExactCanonicalBottomComparisonLiftFiber_action_transitive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible)
    (first second : AuthoredExactCanonicalBottomComparisonLiftFiber
      A z k g admissible t) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    ∃ kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  let displacement : AuthoredExactCanonicalRawBottomComparisonSubgroup
      A z k g admissible := first.1⁻¹ * second.1
  have inKernel : displacement ∈
      (geometryNormalizationBottomQualifiedComparisonSubgroupHom
        (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, first.property, second.property,
      inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, inKernel⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- Every two bottom-qualified lifts have a unique right-kernel displacement. -/
theorem authoredExactCanonicalBottomComparisonLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (t : AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
      A z k g admissible)
    (first second : AuthoredExactCanonicalBottomComparisonLiftFiber
      A z k g admissible t) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (authoredExactBarAlphaAdmissibleIsoAt A z k g admissible).hom
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases authoredExactCanonicalBottomComparisonLiftFiber_action_transitive
      A z k g admissible t first second with ⟨kernelValue, equality⟩
  exact ⟨kernelValue, equality, fun other otherEquality =>
    authoredExactCanonicalBottomComparisonLiftFiber_action_free
      A z k g admissible t first (otherEquality.trans equality.symm)⟩

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
