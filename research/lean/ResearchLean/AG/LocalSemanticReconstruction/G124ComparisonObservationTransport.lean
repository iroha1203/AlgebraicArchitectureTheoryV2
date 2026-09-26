import ResearchLean.AG.LocalSemanticReconstruction.G124PrimitiveNormalization
import ResearchLean.AG.RealizationReconstruction.CSAATRestrictionKernelFiberTransport
import ResearchLean.AG.ComparisonInformationLoss.ObservationTransport
import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction
import Formal.Util.AssertStandardAxioms

/-! G-120 observation-diagram transport for every G-124 comparison arrow. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ComparisonObservationTransport

open CategoryTheory IndependentAATPrimitiveReconstruction
open RealizationReconstruction RealizationComparisonIdempotents
open ComparisonInformationLoss G124ProjectionGlobal G124ProjectionGroupSquare

universe u v

/-- The comparison source observation diagram is transported by the whole
main-reader comparison group, and the bottom-qualified subgroup is identified
by the direct primitive projection square. -/
noncomputable def bottomObservationEquiv (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    ObservationEquiv
      (generatedArrowComparisonSourceHom c)
      (nativeBottomFixedComparison parameter c)
      (generatedArrowComparisonSourceHom ((reading parameter).map c))
      (localBottomFixedComparison parameter ((reading parameter).map c)) where
  changeEquiv := G124ComparisonTransport.comparisonMulEquiv parameter c
  observationEquiv := fullyFaithfulEndpointAutMulEquiv
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor X
  observation_comm := G124ComparisonTransport.source_compatibility parameter c
  compatible_map := by
    apply SetLike.ext
    intro pair
    constructor
    · rintro ⟨native, hnative, rfl⟩
      exact (bottom_comparison_mem_iff parameter c native).mp hnative
    · intro hlocal
      let E := G124ComparisonTransport.comparisonMulEquiv parameter c
      refine ⟨E.symm pair, ?_, by simp [E]⟩
      apply (bottom_comparison_mem_iff parameter c (E.symm pair)).mpr
      simpa [E] using hlocal

/-- G-120 kernel transport now applies to the actual bottom-qualified
comparison diagram for any arrow, without an invertibility assumption. -/
noncomputable def bottomObservationKernelEquiv (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :=
  (bottomObservationEquiv parameter c).kernelEquiv

noncomputable def bottomObservationCompatibleKernelEquiv
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :=
  (bottomObservationEquiv parameter c).compatibleKernelEquiv

noncomputable def bottomObservationFiberEquiv (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :=
  (bottomObservationEquiv parameter c).fiberEquiv pair

noncomputable def bottomObservationCompatibleFiberEquiv
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :=
  (bottomObservationEquiv parameter c).compatibleFiberEquiv pair

noncomputable def bottomObservationQuotientEquiv
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :=
  (bottomObservationEquiv parameter c).quotientEquiv

/-- The source-restriction kernel uses the same full comparison-group
equivalence and the same native/local source projection. -/
noncomputable def sourceRestrictionKernelEquiv
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :=
  generatedArrowComparisonSourceKernelMulEquiv
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor c

/-- Every lift in a source-restriction fiber, not only a chosen element, is
transported to and from the common local comparison group. -/
noncomputable def sourceRestrictionFiberEquiv
    (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) (a : Aut X) :=
  generatedArrowComparisonSourceFiberEquiv
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor c a

/-- The actual source projection sends every bottom-fixed comparison pair to
a bottom-fixed source automorphism. -/
theorem nativeBottomSource_preserves (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    (nativeBottomFixedComparison parameter c).map
        (generatedArrowComparisonSourceHom c) ≤ nativeBottomFixed parameter X := by
  rintro a ⟨pair, hpair, rfl⟩
  exact hpair.1

theorem localBottomSource_preserves (parameter : Parameter.{u, v})
    {X Y : LocalCategory parameter} (c : X ⟶ Y) :
    (localBottomFixedComparison parameter c).map
        (generatedArrowComparisonSourceHom c) ≤ localBottomFixed parameter X := by
  rintro a ⟨pair, hpair, rfl⟩
  exact hpair.1

/-- G-120's exact reflection criterion on the native qualified source
restriction.  No surjectivity is imposed on an arbitrary comparison. -/
theorem nativeBottomSource_reflection_iff (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    (nativeBottomFixed parameter X).comap
        (generatedArrowComparisonSourceHom c) =
      nativeBottomFixedComparison parameter c ↔
    (generatedArrowComparisonSourceHom c).ker ≤
        nativeBottomFixedComparison parameter c ∧
      (nativeBottomFixedComparison parameter c).map
          (generatedArrowComparisonSourceHom c) =
        nativeBottomFixed parameter X ⊓
          (generatedArrowComparisonSourceHom c).range :=
  comap_eq_iff_ker_le_and_map_eq_inf_range _ _ _

theorem localBottomSource_reflection_iff (parameter : Parameter.{u, v})
    {X Y : LocalCategory parameter} (c : X ⟶ Y) :
    (localBottomFixed parameter X).comap
        (generatedArrowComparisonSourceHom c) =
      localBottomFixedComparison parameter c ↔
    (generatedArrowComparisonSourceHom c).ker ≤
        localBottomFixedComparison parameter c ∧
      (localBottomFixedComparison parameter c).map
          (generatedArrowComparisonSourceHom c) =
        localBottomFixed parameter X ⊓
          (generatedArrowComparisonSourceHom c).range :=
  comap_eq_iff_ker_le_and_map_eq_inf_range _ _ _

/-- The restriction is formed only after the preservation square has been
proved; its source and target are the actual qualified subgroups. -/
noncomputable def nativeBottomSourceRestriction (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    nativeBottomFixedComparison parameter c →*
      nativeBottomFixed parameter X :=
  restrictedSubgroupHom _ _ _ (nativeBottomSource_preserves parameter c)

noncomputable def localBottomSourceRestriction (parameter : Parameter.{u, v})
    {X Y : LocalCategory parameter} (c : X ⟶ Y) :
    localBottomFixedComparison parameter c →*
      localBottomFixed parameter X :=
  restrictedSubgroupHom _ _ _ (localBottomSource_preserves parameter c)

/-- The bottom-fixed endpoint subgroup is transported by the original
fully-faithful automorphism equivalence, with membership proved from the
III-1 projection naturality square. -/
noncomputable def bottomFixedEndpointEquiv (parameter : Parameter.{u, v})
    (X : NativeCategory parameter) :
    nativeBottomFixed parameter X ≃*
      localBottomFixed parameter ((reading parameter).obj X) where
  toFun a := ⟨fullyFaithfulEndpointAutMulEquiv
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor X a,
    (bottom_fixed_iff parameter X a).mp a.property⟩
  invFun a := ⟨(fullyFaithfulEndpointAutMulEquiv
    (reading parameter) (equivalence parameter).fullyFaithfulFunctor X).symm a,
    (bottom_fixed_iff parameter X _).mpr (by simpa using a.property)⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (map_mul _ a.1 b.1)

noncomputable def bottomFixedComparisonEquiv (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    nativeBottomFixedComparison parameter c ≃*
      localBottomFixedComparison parameter ((reading parameter).map c) where
  toFun pair := ⟨G124ComparisonTransport.comparisonMulEquiv parameter c pair,
    (bottom_comparison_mem_iff parameter c pair).mp pair.property⟩
  invFun pair := ⟨(G124ComparisonTransport.comparisonMulEquiv parameter c).symm pair,
    (bottom_comparison_mem_iff parameter c _).mpr (by simpa using pair.property)⟩
  left_inv pair := Subtype.ext (by simp)
  right_inv pair := Subtype.ext (by simp)
  map_mul' first second := Subtype.ext (map_mul _ first.1 second.1)

/-- G-120's restricted source square on the actual qualified subgroups. -/
theorem bottomSourceRestriction_square (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : nativeBottomFixedComparison parameter c) :
    localBottomSourceRestriction parameter ((reading parameter).map c)
        (bottomFixedComparisonEquiv parameter c pair) =
      bottomFixedEndpointEquiv parameter X
        (nativeBottomSourceRestriction parameter c pair) := by
  apply Subtype.ext
  exact G124ComparisonTransport.source_compatibility parameter c pair.1

/-- The literal kernel of the qualified restriction is transported; it is
kept distinct from the ambient two-endpoint normalization kernel. -/
noncomputable def bottomRestrictedKernelEquiv (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    (nativeBottomSourceRestriction parameter c).ker ≃*
      (localBottomSourceRestriction parameter ((reading parameter).map c)).ker :=
  RestrictionKernelFiberTransport.kernelMulEquiv
    (nativeBottomSourceRestriction parameter c)
    (localBottomSourceRestriction parameter ((reading parameter).map c))
    (bottomFixedComparisonEquiv parameter c)
    (bottomFixedEndpointEquiv parameter X)
    (bottomSourceRestriction_square parameter c)

/-- Every qualified lift fiber is transported, with the same source element
and the same actual comparison group. -/
noncomputable def bottomRestrictedFiberEquiv (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (a : nativeBottomFixed parameter X) :
    RestrictionKernelFiberTransport.Fiber
        (nativeBottomSourceRestriction parameter c) a ≃
      RestrictionKernelFiberTransport.Fiber
        (localBottomSourceRestriction parameter ((reading parameter).map c))
        (bottomFixedEndpointEquiv parameter X a) :=
  RestrictionKernelFiberTransport.fiberEquiv
    (nativeBottomSourceRestriction parameter c)
    (localBottomSourceRestriction parameter ((reading parameter).map c))
    (bottomFixedComparisonEquiv parameter c)
    (bottomFixedEndpointEquiv parameter X)
    (bottomSourceRestriction_square parameter c) a

theorem bottomRestrictedFiberEquiv_smul (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (a : nativeBottomFixed parameter X)
    (kernelElement : ((nativeBottomSourceRestriction parameter c).ker)ᵐᵒᵖ)
    (point : RestrictionKernelFiberTransport.Fiber
      (nativeBottomSourceRestriction parameter c) a) :
    bottomRestrictedFiberEquiv parameter c a
        (RestrictionKernelFiberTransport.rightKernelAction
          (nativeBottomSourceRestriction parameter c) a kernelElement point) =
      RestrictionKernelFiberTransport.rightKernelAction
        (localBottomSourceRestriction parameter ((reading parameter).map c))
        (bottomFixedEndpointEquiv parameter X a)
        (MulOpposite.op
          (bottomRestrictedKernelEquiv parameter c
            (MulOpposite.unop kernelElement)))
        (bottomRestrictedFiberEquiv parameter c a point) :=
  RestrictionKernelFiberTransport.fiberEquiv_smul
    (nativeBottomSourceRestriction parameter c)
    (localBottomSourceRestriction parameter ((reading parameter).map c))
    (bottomFixedComparisonEquiv parameter c)
    (bottomFixedEndpointEquiv parameter X)
    (bottomSourceRestriction_square parameter c) a kernelElement point

/-- Existence of lifts for all qualified source automorphisms is invariant
under the fixed reader; no surjectivity is asserted for an arbitrary `c`. -/
theorem bottomRestricted_surjective_iff (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    Function.Surjective (nativeBottomSourceRestriction parameter c) ↔
      Function.Surjective
        (localBottomSourceRestriction parameter ((reading parameter).map c)) := by
  constructor
  · intro h nativeTarget
    let original := (bottomFixedEndpointEquiv parameter X).symm nativeTarget
    obtain ⟨originalPair, hp⟩ := h original
    refine ⟨bottomFixedComparisonEquiv parameter c originalPair, ?_⟩
    rw [bottomSourceRestriction_square parameter c originalPair, hp]
    exact (bottomFixedEndpointEquiv parameter X).apply_symm_apply nativeTarget
  · intro h originalTarget
    obtain ⟨localPair, hp⟩ := h
      (bottomFixedEndpointEquiv parameter X originalTarget)
    refine ⟨(bottomFixedComparisonEquiv parameter c).symm localPair, ?_⟩
    apply (bottomFixedEndpointEquiv parameter X).injective
    rw [← bottomSourceRestriction_square parameter c
      ((bottomFixedComparisonEquiv parameter c).symm localPair)]
    simpa using hp

theorem nativeBottomSource_lift_iff (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (a : nativeBottomFixed parameter X) :
    Nonempty (RestrictedFiber (generatedArrowComparisonSourceHom c)
      (nativeBottomFixedComparison parameter c)
      (nativeBottomFixed parameter X)
      (nativeBottomSource_preserves parameter c) a) ↔
      (a : Aut X) ∈
        (nativeBottomFixedComparison parameter c).map
          (generatedArrowComparisonSourceHom c) :=
  nonempty_restrictedFiber_iff_mem_map _ _ _ _ _

theorem localBottomSource_lift_iff (parameter : Parameter.{u, v})
    {X Y : LocalCategory parameter} (c : X ⟶ Y)
    (a : localBottomFixed parameter X) :
    Nonempty (RestrictedFiber (generatedArrowComparisonSourceHom c)
      (localBottomFixedComparison parameter c)
      (localBottomFixed parameter X)
      (localBottomSource_preserves parameter c) a) ↔
      (a : Aut X) ∈
        (localBottomFixedComparison parameter c).map
          (generatedArrowComparisonSourceHom c) :=
  nonempty_restrictedFiber_iff_mem_map _ _ _ _ _

theorem nativeBottomSource_shortExact_iff (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    IsGroupShortExact
        (restrictedKernelInclusion (generatedArrowComparisonSourceHom c)
          (nativeBottomFixedComparison parameter c)
          (nativeBottomFixed parameter X)
          (nativeBottomSource_preserves parameter c))
        (nativeBottomSourceRestriction parameter c) ↔
      (nativeBottomFixedComparison parameter c).map
          (generatedArrowComparisonSourceHom c) =
        nativeBottomFixed parameter X :=
  restrictedSubgroupHom_shortExact_iff_map_eq _ _ _ _

theorem localBottomSource_shortExact_iff (parameter : Parameter.{u, v})
    {X Y : LocalCategory parameter} (c : X ⟶ Y) :
    IsGroupShortExact
        (restrictedKernelInclusion (generatedArrowComparisonSourceHom c)
          (localBottomFixedComparison parameter c)
          (localBottomFixed parameter X)
          (localBottomSource_preserves parameter c))
        (localBottomSourceRestriction parameter c) ↔
      (localBottomFixedComparison parameter c).map
          (generatedArrowComparisonSourceHom c) =
        localBottomFixed parameter X :=
  restrictedSubgroupHom_shortExact_iff_map_eq _ _ _ _

/-- The G-120 short exact condition has the same truth value on both sides
of the main reader.  Its condition is surjectivity of the qualified source
restriction, not an assumption on all comparison arrows. -/
theorem bottomRestricted_shortExact_iff (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    IsGroupShortExact
        (restrictedKernelInclusion (generatedArrowComparisonSourceHom c)
          (nativeBottomFixedComparison parameter c)
          (nativeBottomFixed parameter X)
          (nativeBottomSource_preserves parameter c))
        (nativeBottomSourceRestriction parameter c) ↔
      IsGroupShortExact
        (restrictedKernelInclusion
          (generatedArrowComparisonSourceHom ((reading parameter).map c))
          (localBottomFixedComparison parameter ((reading parameter).map c))
          (localBottomFixed parameter ((reading parameter).obj X))
          (localBottomSource_preserves parameter ((reading parameter).map c)))
        (localBottomSourceRestriction parameter ((reading parameter).map c)) := by
  rw [nativeBottomSource_shortExact_iff, localBottomSource_shortExact_iff]
  exact (restrictedSubgroupHom_surjective_iff_map_eq _ _ _
      (nativeBottomSource_preserves parameter c)).symm.trans
    ((bottomRestricted_surjective_iff parameter c).trans
      (restrictedSubgroupHom_surjective_iff_map_eq _ _ _
        (localBottomSource_preserves parameter ((reading parameter).map c))))

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ComparisonObservationTransport

end AAT.AG.LocalSemanticReconstruction.G124ComparisonObservationTransport
