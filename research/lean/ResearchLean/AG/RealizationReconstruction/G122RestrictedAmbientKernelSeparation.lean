import ResearchLean.AG.RealizationReconstruction.CSAATRestrictionKernelFiberTransport
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldAmbientKernelComparison
import Formal.Util.AssertStandardAxioms

/-!
# Restricted and ambient normalization kernels are different objects

For a homomorphism restricted to source and target subgroups, its kernel maps
canonically and injectively to the ambient kernel.  The image consists exactly
of the ambient-kernel elements that satisfy the source subgroup predicate.

Applied to G-122 normalization, the source predicate is preservation of the
original raw comparison.  The mandated finite-axis-fold ambient involution is
in the ambient endpoint kernel but does not preserve that comparison.  Hence
the restricted comparison kernel is strictly smaller than the ambient kernel.
This all-elements image characterization keeps the two kernels separate; it
does not replace either one by the other or by a selected witness.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open FullGeometryNormalization
open AtomFoundation DoctrineFiberProduct GeometryTransport TransportCoherence

universe u v

noncomputable section

namespace RestrictedAmbientKernel

variable {G H : Type*} [Group G] [Group H]

/-- The kernel of a subgroup restriction embeds in the ambient kernel when
the square commutes on underlying values. -/
def inclusion
    (ambient : G →* H) (source : Subgroup G) (target : Subgroup H)
    (restricted : source →* target)
    (commutes : ∀ value, (restricted value).1 = ambient value.1) :
    MonoidHom.ker restricted →* MonoidHom.ker ambient where
  toFun value := ⟨value.1.1, by
    rw [MonoidHom.mem_ker]
    calc
      ambient value.1.1 = (restricted value.1).1 := (commutes value.1).symm
      _ = (1 : target).1 := congrArg Subtype.val
        (MonoidHom.mem_ker.mp value.property)
      _ = 1 := rfl⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply Subtype.ext
    rfl

/-- The restricted-kernel inclusion is injective. -/
theorem inclusion_injective
    (ambient : G →* H) (source : Subgroup G) (target : Subgroup H)
    (restricted : source →* target)
    (commutes : ∀ value, (restricted value).1 = ambient value.1) :
    Function.Injective (inclusion ambient source target restricted commutes) := by
  intro first second equality
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun value : MonoidHom.ker ambient => value.1) equality

/-- Exact all-elements image characterization: an ambient-kernel value comes
from the restricted kernel precisely when its underlying source value obeys
the source subgroup predicate. -/
theorem mem_range_inclusion_iff
    (ambient : G →* H) (source : Subgroup G) (target : Subgroup H)
    (restricted : source →* target)
    (commutes : ∀ value, (restricted value).1 = ambient value.1)
    (value : MonoidHom.ker ambient) :
    value ∈ MonoidHom.range
        (inclusion ambient source target restricted commutes) ↔
      value.1 ∈ source := by
  constructor
  · rintro ⟨preimage, equality⟩
    have underlying : preimage.1.1 = value.1 :=
      congrArg (fun result : MonoidHom.ker ambient => result.1) equality
    rw [← underlying]
    exact preimage.1.property
  · intro membership
    let sourceValue : source := ⟨value.1, membership⟩
    have restrictedKernel : restricted sourceValue = 1 := by
      apply Subtype.ext
      calc
        (restricted sourceValue).1 = ambient sourceValue.1 := commutes sourceValue
        _ = 1 := MonoidHom.mem_ker.mp value.property
        _ = (1 : target).1 := rfl
    let preimage : MonoidHom.ker restricted :=
      ⟨sourceValue, MonoidHom.mem_ker.mpr restrictedKernel⟩
    refine ⟨preimage, ?_⟩
    apply Subtype.ext
    rfl

end RestrictedAmbientKernel

/-! ## G-122 normalization specialization -/

/-- The actual restricted comparison kernel embeds into the ambient endpoint
normalization kernel. -/
noncomputable def geometryComparisonRestrictedKernelToAmbientKernel
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    MonoidHom.ker (geometryNormalizationComparisonSubgroupHom c) →*
      MonoidHom.ker (geometryNormalizationEndpointAutomorphismHom G H) :=
  RestrictedAmbientKernel.inclusion
    (geometryNormalizationEndpointAutomorphismHom G H)
    (rawGeometryNormalizationComparisonSubgroup c)
    (normalizedGeometryComparisonSubgroup c)
    (geometryNormalizationComparisonSubgroupHom c)
    (fun _ => rfl)

/-- The actual restricted-to-ambient kernel map is injective. -/
theorem geometryComparisonRestrictedKernelToAmbientKernel_injective
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H) :
    Function.Injective (geometryComparisonRestrictedKernelToAmbientKernel c) :=
  RestrictedAmbientKernel.inclusion_injective
    (geometryNormalizationEndpointAutomorphismHom G H)
    (rawGeometryNormalizationComparisonSubgroup c)
    (normalizedGeometryComparisonSubgroup c)
    (geometryNormalizationComparisonSubgroupHom c)
    (fun _ => rfl)

/-- Inside the ambient endpoint kernel, the restricted-kernel image is
exactly the locus that preserves the original raw comparison. -/
theorem mem_geometryComparisonRestrictedKernelToAmbientKernel_range_iff
    {U : AtomCarrier.{u}}
    {G H : CanonicalNormalizationAdmissibleGeometry.{u, v} U} (c : G ⟶ H)
    (value : MonoidHom.ker
      (geometryNormalizationEndpointAutomorphismHom G H)) :
    value ∈ MonoidHom.range
        (geometryComparisonRestrictedKernelToAmbientKernel c) ↔
      value.1 ∈ rawGeometryNormalizationComparisonSubgroup c :=
  RestrictedAmbientKernel.mem_range_inclusion_iff
    (geometryNormalizationEndpointAutomorphismHom G H)
    (rawGeometryNormalizationComparisonSubgroup c)
    (normalizedGeometryComparisonSubgroup c)
    (geometryNormalizationComparisonSubgroupHom c)
    (fun _ => rfl) value

/-! ## Fixed finite-axis-fold strict separation -/

namespace FiniteAxisFoldRestrictedAmbientKernel

local instance finiteAxisFoldRestrictedAmbientKernelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

noncomputable abbrev DirectEndpoint :=
  authoredExactDirectAdmissibleGeometryAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

noncomputable abbrev ViaBaseEndpoint :=
  authoredExactViaBaseAdmissibleGeometryAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

noncomputable abbrev comparisonIso :=
  authoredExactBarAlphaAdmissibleIsoAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The mandated ambient involution as an element of the complete endpoint
normalization kernel. -/
noncomputable def ambientElement :
    MonoidHom.ker
      (geometryNormalizationEndpointAutomorphismHom
        DirectEndpoint ViaBaseEndpoint) :=
  ⟨finiteAxisFoldDisplayedAmbientKernelComparisonPair,
    finiteAxisFoldDisplayedAmbientKernelComparisonPair_normalization⟩

/-- The mandated ambient element lies outside the whole restricted-kernel
image because it does not preserve the original comparison. -/
theorem ambientElement_not_mem_restrictedKernel_range :
    ambientElement ∉ MonoidHom.range
      (geometryComparisonRestrictedKernelToAmbientKernel comparisonIso.hom) := by
  rw [mem_geometryComparisonRestrictedKernelToAmbientKernel_range_iff]
  exact finiteAxisFoldDisplayedAmbientKernelComparisonPair_not_raw_mem

/-- Therefore the restricted comparison kernel does not exhaust the ambient
endpoint normalization kernel on the fixed original G-122 input. -/
theorem restrictedKernel_inclusion_not_surjective :
    ¬ Function.Surjective
      (geometryComparisonRestrictedKernelToAmbientKernel comparisonIso.hom) := by
  intro surjective
  rcases surjective ambientElement with ⟨preimage, equality⟩
  exact ambientElement_not_mem_restrictedKernel_range ⟨preimage, equality⟩

/-- The separating ambient element fixes the bottom and coefficient
components at both endpoints, so the distinction survives those evaluations. -/
theorem ambientElement_bottom_coefficient_packet :
    finiteAxisFoldDisplayedAmbientKernelComparisonPair.1.hom.hom.base.base =
        ExtInstHom.id (packagePoint DirectEndpoint.obj.core) ∧
      finiteAxisFoldDisplayedAmbientKernelComparisonPair.1.hom.hom.geometry.coefficientHom =
        RingHom.id Int ∧
      finiteAxisFoldDisplayedAmbientKernelComparisonPair.2.hom.hom.base.base =
        ExtInstHom.id (packagePoint ViaBaseEndpoint.obj.core) ∧
      finiteAxisFoldDisplayedAmbientKernelComparisonPair.2.hom.hom.geometry.coefficientHom =
        RingHom.id Int :=
  finiteAxisFoldDisplayedAmbientKernelComparisonPair_component_packet

end FiniteAxisFoldRestrictedAmbientKernel

end


#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
