import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedCanonicalBottomComparison

/-!
# Theorem 7.21: generated comparison identification

For every normalized change, the canonical section gives the compatible
change and the internally constructed source involution gives an incompatible
change with exactly the same normalized value. The construction also respects
both bottom identities.
-/

open CategoryTheory

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open ComparisonInformationLoss

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

/-- The two explicit endpoint changes of (7.35) for every generated semantic
comparison and every normalized compatible change. -/
theorem semanticDerivedCanonicalComparison_identification
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    let G := semanticDerivedDirectAdmissibleGeometryAt input Q k g endpoint_eq admissible
    let H := semanticDerivedViaBaseAdmissibleGeometryAt input Q k g endpoint_eq admissible
    let c := semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible
    let q_plus : Aut G × Aut H :=
      (semanticDerivedCanonicalComparisonSectionHom
        input Q k g endpoint_eq square_isPullback admissible δ).1
    let q_minus := ambientKernelComparisonPair G H
    let q_bad := q_plus * q_minus
    q_plus ∈ rawGeometryNormalizationComparisonSubgroup c.hom ∧
      q_bad ∉ rawGeometryNormalizationComparisonSubgroup c.hom ∧
      geometryNormalizationEndpointAutomorphismHom G H q_plus = δ.1 ∧
      geometryNormalizationEndpointAutomorphismHom G H q_bad = δ.1 := by
  dsimp
  let G := semanticDerivedDirectAdmissibleGeometryAt input Q k g endpoint_eq admissible
  let H := semanticDerivedViaBaseAdmissibleGeometryAt input Q k g endpoint_eq admissible
  let c := semanticDerivedBarAlphaAdmissibleIsoAt
    input Q k g endpoint_eq square_isPullback admissible
  let s := semanticDerivedCanonicalComparisonSectionHom
    input Q k g endpoint_eq square_isPullback admissible
  let q_minus := ambientKernelComparisonPair G H
  have hs : (s δ).1 ∈ rawGeometryNormalizationComparisonSubgroup c.hom := (s δ).2
  have hm : q_minus ∉ rawGeometryNormalizationComparisonSubgroup c.hom :=
    ambientKernelComparisonPair_not_raw_mem c
  have hnorm : geometryNormalizationEndpointAutomorphismHom G H (s δ).1 = δ.1 := by
    exact congrArg Subtype.val
      (semanticDerivedCanonicalComparisonSection_rightInverse
        input Q k g endpoint_eq square_isPullback admissible δ)
  refine ⟨hs, ?_, hnorm, ?_⟩
  · intro hbad
    have : (s δ).1⁻¹ * ((s δ).1 * q_minus) ∈
        rawGeometryNormalizationComparisonSubgroup c.hom :=
      (rawGeometryNormalizationComparisonSubgroup c.hom).mul_mem
        ((rawGeometryNormalizationComparisonSubgroup c.hom).inv_mem hs) hbad
    exact hm (by simpa using this)
  · rw [map_mul, hnorm,
      geometryNormalizationEndpointAutomorphismHom_ambientKernelComparisonPair,
      mul_one]

/-- The bottom-qualified restricted normalization map is split exact. -/
theorem semanticDerivedCanonicalBottomComparison_shortExact
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · rw [MonoidHom.mulExact_iff]
    exact p.ker.range_subtype.symm
  · intro δ
    exact ⟨semanticDerivedCanonicalBottomComparisonSectionHom
      input Q k g endpoint_eq square_isPullback admissible δ,
      semanticDerivedCanonicalBottomComparisonSection_rightInverse
        input Q k g endpoint_eq square_isPullback admissible δ⟩

/-- The same explicit pair from (7.35) in both bottom-fixing ambient endpoint
groups. The bad change retains the normalization of the section value. -/
theorem semanticDerivedCanonicalBottomComparison_identification
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    let G := semanticDerivedDirectAdmissibleGeometryAt input Q k g endpoint_eq admissible
    let H := semanticDerivedViaBaseAdmissibleGeometryAt input Q k g endpoint_eq admissible
    let c := semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible
    let q_plus : Aut G × Aut H :=
      (semanticDerivedCanonicalBottomComparisonSectionHom
        input Q k g endpoint_eq square_isPullback admissible δ).1.1
    let q_minus := ambientKernelComparisonPair G H
    let q_bad := q_plus * q_minus
    q_plus ∈ rawGeometryNormalizationComparisonSubgroup c.hom ∧
      q_bad ∉ rawGeometryNormalizationComparisonSubgroup c.hom ∧
      rawGeometryBottomAutomorphismHom G q_plus.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H q_plus.2 = 1 ∧
      rawGeometryBottomAutomorphismHom G q_bad.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H q_bad.2 = 1 ∧
      geometryNormalizationEndpointAutomorphismHom G H q_plus = δ.1.1 ∧
      geometryNormalizationEndpointAutomorphismHom G H q_bad = δ.1.1 := by
  dsimp
  let G := semanticDerivedDirectAdmissibleGeometryAt input Q k g endpoint_eq admissible
  let H := semanticDerivedViaBaseAdmissibleGeometryAt input Q k g endpoint_eq admissible
  let c := semanticDerivedBarAlphaAdmissibleIsoAt
    input Q k g endpoint_eq square_isPullback admissible
  let s := semanticDerivedCanonicalBottomComparisonSectionHom
    input Q k g endpoint_eq square_isPullback admissible
  let q_minus := ambientKernelComparisonPair G H
  have hs : (s δ).1.1 ∈ rawGeometryNormalizationComparisonSubgroup c.hom := (s δ).1.2
  have hm : q_minus ∉ rawGeometryNormalizationComparisonSubgroup c.hom :=
    ambientKernelComparisonPair_not_raw_mem c
  have hbottom : rawGeometryBottomAutomorphismHom G (s δ).1.1.1 = 1 ∧
      rawGeometryBottomAutomorphismHom H (s δ).1.1.2 = 1 := (s δ).2
  have hminus := ambientKernelComparisonPair_raw_bottom G H
  have hnorm : geometryNormalizationEndpointAutomorphismHom G H (s δ).1.1 = δ.1.1 := by
    have h := semanticDerivedCanonicalBottomComparisonSection_rightInverse
      input Q k g endpoint_eq square_isPullback admissible δ
    exact congrArg (fun pair => pair.1.1) h
  refine ⟨hs, ?_, hbottom.1, hbottom.2, ?_, ?_, hnorm, ?_⟩
  · intro hbad
    have : (s δ).1.1⁻¹ * ((s δ).1.1 * q_minus) ∈
        rawGeometryNormalizationComparisonSubgroup c.hom :=
      (rawGeometryNormalizationComparisonSubgroup c.hom).mul_mem
        ((rawGeometryNormalizationComparisonSubgroup c.hom).inv_mem hs) hbad
    exact hm (by simpa using this)
  · rw [map_mul, hbottom.1, hminus.1, one_mul]
  · rw [map_mul, hbottom.2, hminus.2, one_mul]
  · rw [map_mul, hnorm,
      geometryNormalizationEndpointAutomorphismHom_ambientKernelComparisonPair,
      mul_one]

/-- Bottom-fixed compatible lifts over one normalized compatible change. -/
noncomputable abbrev SemanticDerivedCanonicalBottomComparisonLiftFiber
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :=
  {a : SemanticDerivedCanonicalRawBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible //
    geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom a = δ}

/-- Every bottom-fixed normalized comparison change has a compatible lift. -/
theorem semanticDerivedCanonicalBottomComparisonLiftFiber_nonempty
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    Nonempty (SemanticDerivedCanonicalBottomComparisonLiftFiber
      input Q k g endpoint_eq square_isPullback admissible δ) :=
  ⟨⟨semanticDerivedCanonicalBottomComparisonSectionHom
      input Q k g endpoint_eq square_isPullback admissible δ,
    semanticDerivedCanonicalBottomComparisonSection_rightInverse
      input Q k g endpoint_eq square_isPullback admissible δ⟩⟩

/-- Each pair of bottom-fixed lifts differs by a unique right kernel factor. -/
theorem semanticDerivedCanonicalBottomComparisonLiftFiber_unique_rightKernel
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible)
    (first second : SemanticDerivedCanonicalBottomComparisonLiftFiber
      input Q k g endpoint_eq square_isPullback admissible δ) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    ∃! kernelValue : p.ker,
      first.1 * (kernelValue : SemanticDerivedCanonicalRawBottomComparisonSubgroup
        input Q k g endpoint_eq square_isPullback admissible) = second.1 := by
  dsimp
  let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom
  let displacement : SemanticDerivedCanonicalRawBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible :=
    first.1⁻¹ * second.1
  have inKernel : displacement ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      first.property, second.property, inv_mul_cancel]
  refine ⟨⟨displacement, inKernel⟩, ?_, ?_⟩
  · simp [displacement]
  · intro other otherEquality
    apply Subtype.ext
    exact mul_left_cancel (otherEquality.trans (by simp [displacement] :
      second.1 = first.1 * displacement))

/-- Right multiplication by the bottom-fixed restricted kernel. -/
noncomputable instance semanticDerivedCanonicalBottomComparisonLiftFiberSMul
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    SMul p.kerᵐᵒᵖ
      (SemanticDerivedCanonicalBottomComparisonLiftFiber
        input Q k g endpoint_eq square_isPullback admissible δ) := by
  dsimp
  let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- The opposite kernel gives the bottom-fixed fiber a genuine right action. -/
noncomputable instance semanticDerivedCanonicalBottomComparisonLiftFiberMulAction
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    MulAction p.kerᵐᵒᵖ
      (SemanticDerivedCanonicalBottomComparisonLiftFiber
        input Q k g endpoint_eq square_isPullback admissible δ) := by
  dsimp
  letI := semanticDerivedCanonicalBottomComparisonLiftFiberSMul
    input Q k g endpoint_eq square_isPullback admissible δ
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 *
        (((MulOpposite.unop second).1 :
          SemanticDerivedCanonicalRawBottomComparisonSubgroup
            input Q k g endpoint_eq square_isPullback admissible) *
          ((MulOpposite.unop first).1 :
            SemanticDerivedCanonicalRawBottomComparisonSubgroup
              input Q k g endpoint_eq square_isPullback admissible)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : SemanticDerivedCanonicalRawBottomComparisonSubgroup
        input Q k g endpoint_eq square_isPullback admissible) = lift.1
    simp

/-- The bottom-fixed lift fiber is a right torsor for the restricted kernel. -/
theorem semanticDerivedCanonicalBottomComparisonLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (δ : SemanticDerivedCanonicalNormalizedBottomComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible)
    (first second : SemanticDerivedCanonicalBottomComparisonLiftFiber
      input Q k g endpoint_eq square_isPullback admissible δ) :
    let p := geometryNormalizationBottomQualifiedComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases semanticDerivedCanonicalBottomComparisonLiftFiber_unique_rightKernel
      input Q k g endpoint_eq square_isPullback admissible δ first second with
    ⟨displacement, hdisplacement, hunique⟩
  refine ⟨MulOpposite.op displacement, ?_, ?_⟩
  · apply Subtype.ext
    exact hdisplacement
  · intro other hother
    apply MulOpposite.unop_injective
    apply hunique
    have hvalue := congrArg
      (fun lift : SemanticDerivedCanonicalBottomComparisonLiftFiber
        input Q k g endpoint_eq square_isPullback admissible δ => lift.1)
      hother
    exact hvalue

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
