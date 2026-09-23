import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedEndpointBridge
import ResearchLean.AG.FullGeometryNormalization.SemanticExactNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationIsoComparisonSection
import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction

/-!
# Canonical comparison groups for the generated semantic square

The literal direct and via-base geometries are generated from one southwest
geometry. Its Ad property propagates through the exact pull and transport
operations. The resulting generated comparison iso then yields a section,
split group short exact sequence, and right kernel torsors on lift fibers.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct ComparisonInformationLoss

set_option maxHeartbeats 3000000

noncomputable local instance semanticDerivedCanonicalAtomDecidableEq
    (U : AtomCarrier.{u}) : DecidableEq U.Atom := Classical.decEq _

/-- Ad is preserved by transport along any pointed exact semantic arrow. -/
theorem canonicalGeometryNormalizationAdmissible_semanticTransport
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (input : ExtInstHom X Y)
    (source : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    CanonicalObjectNormalizationAdmissible
      ((geomFiberTransportFunctor input).obj source).1.core := by
  change CanonicalObjectNormalizationAdmissible
    (transportAlong source.1.core
      (geomFiberBaseHom input source).doctrineHom)
  exact canonicalObjectNormalizationAdmissible_transportAlong
    source.1.core admissible
      (geomFiberBaseHom input source).doctrineHom

/-- Ad at the southwest source gives Ad at the generated direct endpoint. -/
theorem semanticDerivedDirectGeometryAt_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedDirectGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticTransport input.square.top
    (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)
    (canonicalGeometryNormalizationAdmissible_semanticExactPull
      input.square.left
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
      admissible)

/-- Ad at the southwest source gives Ad at the generated via-base endpoint. -/
theorem semanticDerivedViaBaseGeometryAt_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull input.square.right
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    (canonicalGeometryNormalizationAdmissible_semanticTransport
      input.square.bottom
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
      admissible)

/-- The generated direct geometry as an admissible complete geometry. -/
noncomputable def semanticDerivedDirectAdmissibleGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U :=
  ⟨(semanticDerivedDirectGeometryAt input Q k g endpoint_eq).1,
    semanticDerivedDirectGeometryAt_admissible
      input Q k g endpoint_eq admissible⟩

/-- The generated via-base geometry as an admissible complete geometry. -/
noncomputable def semanticDerivedViaBaseAdmissibleGeometryAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalNormalizationAdmissibleGeometry.{u, v} U :=
  ⟨(semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq).1,
    semanticDerivedViaBaseGeometryAt_admissible
      input Q k g endpoint_eq admissible⟩

/-- The generated semantic `barAlpha` in the admissible geometry category. -/
noncomputable def semanticDerivedBarAlphaAdmissibleIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    semanticDerivedDirectAdmissibleGeometryAt
        input Q k g endpoint_eq admissible ≅
      semanticDerivedViaBaseAdmissibleGeometryAt
        input Q k g endpoint_eq admissible where
  hom := ObjectProperty.homMk
    (semanticDerivedBarAlphaIsoAt
      input Q k g endpoint_eq square_isPullback).hom.1
  inv := ObjectProperty.homMk
    (semanticDerivedBarAlphaIsoAt
      input Q k g endpoint_eq square_isPullback).inv.1
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.1)
      (semanticDerivedBarAlphaIsoAt
        input Q k g endpoint_eq square_isPullback).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.1)
      (semanticDerivedBarAlphaIsoAt
        input Q k g endpoint_eq square_isPullback).inv_hom_id

/-- The generated admissible comparison retains the literal `barAlpha`. -/
@[simp] theorem semanticDerivedBarAlphaAdmissibleIsoAt_hom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom.hom =
      (semanticDerivedBarAlphaIsoAt
        input Q k g endpoint_eq square_isPullback).hom.1 :=
  rfl

/-- Section of the actual restricted normalization comparison. -/
noncomputable def semanticDerivedCanonicalComparisonSectionHom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    normalizedGeometryComparisonSubgroup
        (semanticDerivedBarAlphaAdmissibleIsoAt
          input Q k g endpoint_eq square_isPullback admissible).hom →*
      rawGeometryNormalizationComparisonSubgroup
        (semanticDerivedBarAlphaAdmissibleIsoAt
          input Q k g endpoint_eq square_isPullback admissible).hom :=
  canonicalNormalizationIsoComparisonSectionHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible)

/-- Normalization after the generated section is the identity. -/
theorem semanticDerivedCanonicalComparisonSection_rightInverse
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (pair : normalizedGeometryComparisonSubgroup
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom) :
    geometryNormalizationComparisonSubgroupHom
        (semanticDerivedBarAlphaAdmissibleIsoAt
          input Q k g endpoint_eq square_isPullback admissible).hom
        (semanticDerivedCanonicalComparisonSectionHom
          input Q k g endpoint_eq square_isPullback admissible pair) = pair :=
  canonicalNormalizationIsoComparisonSection_rightInverse
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible) pair

/-- The restricted normalization comparison is surjective. -/
theorem semanticDerivedCanonicalComparisonHom_surjective
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    Function.Surjective
      (geometryNormalizationComparisonSubgroupHom
        (semanticDerivedBarAlphaAdmissibleIsoAt
          input Q k g endpoint_eq square_isPullback admissible).hom) := by
  intro pair
  exact ⟨semanticDerivedCanonicalComparisonSectionHom
      input Q k g endpoint_eq square_isPullback admissible pair,
    semanticDerivedCanonicalComparisonSection_rightInverse
      input Q k g endpoint_eq square_isPullback admissible pair⟩

/-- Kernel inclusion and restricted normalization form a split group short
exact sequence. -/
theorem semanticDerivedCanonicalComparison_shortExact
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    let p := geometryNormalizationComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    IsGroupShortExact p.ker.subtype p := by
  dsimp
  let p := geometryNormalizationComparisonSubgroupHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom
  exact ⟨Subtype.val_injective,
    by
      rw [MonoidHom.mulExact_iff]
      exact p.ker.range_subtype.symm,
    semanticDerivedCanonicalComparisonHom_surjective
      input Q k g endpoint_eq square_isPullback admissible⟩

/-- The literal raw comparison group for the generated semantic `barAlpha`. -/
noncomputable abbrev SemanticDerivedCanonicalRawComparisonSubgroup
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :=
  rawGeometryNormalizationComparisonSubgroup
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom

/-- The literal normalized comparison group for the generated semantic `barAlpha`. -/
noncomputable abbrev SemanticDerivedCanonicalNormalizedComparisonSubgroup
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :=
  normalizedGeometryComparisonSubgroup
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom

/-- The fiber of raw compatible changes over one normalized compatible change. -/
noncomputable abbrev SemanticDerivedCanonicalComparisonLiftFiber
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (t : SemanticDerivedCanonicalNormalizedComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :=
  {a : SemanticDerivedCanonicalRawComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible //
    geometryNormalizationComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom a = t}

/-- Right multiplication by the restricted kernel on each generated lift fiber. -/
noncomputable instance semanticDerivedCanonicalComparisonLiftFiberSMul
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (t : SemanticDerivedCanonicalNormalizedComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    let p := geometryNormalizationComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    SMul p.kerᵐᵒᵖ
      (SemanticDerivedCanonicalComparisonLiftFiber
        input Q k g endpoint_eq square_isPullback admissible t) := by
  dsimp
  let p := geometryNormalizationComparisonSubgroupHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom
  exact ⟨fun kernelValue lift =>
    ⟨lift.1 * (MulOpposite.unop kernelValue).1, by
      rw [map_mul, lift.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelValue).property,
        mul_one]⟩⟩

/-- Opposite-kernel multiplication satisfies the right action laws. -/
noncomputable instance semanticDerivedCanonicalComparisonLiftFiberMulAction
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (t : SemanticDerivedCanonicalNormalizedComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    let p := geometryNormalizationComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    MulAction p.kerᵐᵒᵖ
      (SemanticDerivedCanonicalComparisonLiftFiber
        input Q k g endpoint_eq square_isPullback admissible t) := by
  dsimp
  refine { one_smul := ?_, mul_smul := ?_ }
  · intro first second lift
    apply Subtype.ext
    change lift.1 *
        (((MulOpposite.unop second).1 :
          SemanticDerivedCanonicalRawComparisonSubgroup
            input Q k g endpoint_eq square_isPullback admissible) *
          ((MulOpposite.unop first).1 :
            SemanticDerivedCanonicalRawComparisonSubgroup
              input Q k g endpoint_eq square_isPullback admissible)) =
      (lift.1 * (MulOpposite.unop second).1) *
        (MulOpposite.unop first).1
    simp [mul_assoc]
  · intro lift
    apply Subtype.ext
    change lift.1 *
      (1 : SemanticDerivedCanonicalRawComparisonSubgroup
        input Q k g endpoint_eq square_isPullback admissible) = lift.1
    simp

/-- Every normalized compatible change has an actual raw compatible lift. -/
theorem semanticDerivedCanonicalComparisonLiftFiber_nonempty
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (t : SemanticDerivedCanonicalNormalizedComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible) :
    Nonempty (SemanticDerivedCanonicalComparisonLiftFiber
      input Q k g endpoint_eq square_isPullback admissible t) :=
  ⟨⟨semanticDerivedCanonicalComparisonSectionHom
      input Q k g endpoint_eq square_isPullback admissible t,
    semanticDerivedCanonicalComparisonSection_rightInverse
      input Q k g endpoint_eq square_isPullback admissible t⟩⟩

/-- Every two lifts differ by a unique right factor in the restricted kernel. -/
theorem semanticDerivedCanonicalComparisonLiftFiber_unique_rightKernel
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (t : SemanticDerivedCanonicalNormalizedComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible)
    (first second : SemanticDerivedCanonicalComparisonLiftFiber
      input Q k g endpoint_eq square_isPullback admissible t) :
    let p := geometryNormalizationComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    ∃! kernelValue : p.ker,
      first.1 * (kernelValue : SemanticDerivedCanonicalRawComparisonSubgroup
        input Q k g endpoint_eq square_isPullback admissible) = second.1 := by
  dsimp
  let p := geometryNormalizationComparisonSubgroupHom
    (semanticDerivedBarAlphaAdmissibleIsoAt
      input Q k g endpoint_eq square_isPullback admissible).hom
  let displacement : SemanticDerivedCanonicalRawComparisonSubgroup
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

/-- The generated lift fiber is a right torsor for the restricted kernel. -/
theorem semanticDerivedCanonicalComparisonLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (t : SemanticDerivedCanonicalNormalizedComparisonSubgroup
      input Q k g endpoint_eq square_isPullback admissible)
    (first second : SemanticDerivedCanonicalComparisonLiftFiber
      input Q k g endpoint_eq square_isPullback admissible t) :
    let p := geometryNormalizationComparisonSubgroupHom
      (semanticDerivedBarAlphaAdmissibleIsoAt
        input Q k g endpoint_eq square_isPullback admissible).hom
    ∃! kernelValue : p.kerᵐᵒᵖ, kernelValue • first = second := by
  dsimp
  rcases semanticDerivedCanonicalComparisonLiftFiber_unique_rightKernel
      input Q k g endpoint_eq square_isPullback admissible t first second with
    ⟨displacement, hdisplacement, hunique⟩
  refine ⟨MulOpposite.op displacement, ?_, ?_⟩
  · apply Subtype.ext
    exact hdisplacement
  · intro other hother
    apply MulOpposite.unop_injective
    apply hunique
    have hvalue := congrArg
      (fun lift : SemanticDerivedCanonicalComparisonLiftFiber
        input Q k g endpoint_eq square_isPullback admissible t => lift.1)
      hother
    exact hvalue

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
