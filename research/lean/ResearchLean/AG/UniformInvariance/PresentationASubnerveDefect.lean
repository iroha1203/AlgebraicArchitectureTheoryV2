import ResearchLean.AG.UniformInvariance.ExecutableRationalRank
import ResearchLean.AG.UniformInvariance.FiniteComparisonPresentation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Formal.Util.AssertStandardAxioms

/-!
# Executable defects for finite A-subnerve presentations

This module connects the finite comparison presentation of Cycle 6 and the
executable rational matrix rank of Cycle 7 to the actual quotient-`H¹` defect
from Cycle 5.  Its main API will compute a defect for every finite target
subset directly from raw support and incidence tables, then prove equality with
the canonical A-subnerve comparison defect.

## Position and premises

The module discharges the presentation-to-semantics bridge inside claim (ii);
it does not define the all-subset uniformity checker.  Its only ambient input is
`FiniteComparisonPresentation`, whose finite reading, cell, incidence, support,
and partial-morphism data were fixed in Cycle 6.  No rank, basis, cohomology,
defect, or uniformity result is added to that structure.

## Implementation notes

For a cochain map `f : K ⟶ L`, the induced quotient-`H¹` rank is recovered from
the block map

```text
(z, x) ↦ (K.d1 z, f.f1 z - L.d0 x).
```

Two finite-dimensional exact sequences identify its range with the sum of the
image of cycles and target boundaries.  This route was chosen because it keeps
the literal `ker d1 / range d0` semantics visible.  Replacing `H¹(f)` by `f1`
was rejected because boundaries can change the rank.  Supplying cycle bases,
boundary bases, matrices, ranks, or the final defect was rejected because those
would move the conclusion into certificates.  Semantic `Module.finrank` is
used only in correctness theorems; the later executable definitions use the
Cycle 7 evaluator on matrices generated from raw tables.
-/

namespace AAT.AG.TwoPhase

namespace ThreeCochainComplex

namespace Hom

variable {K L : ThreeCochainComplex ℚ}

/-- API construction for the presentation defect theorem: the block map whose
range records source coboundary failure together with the target class of the
degree-one comparison.  Its premises are exactly the existing cochain map and
finite complexes; it stores no rank data. -/
def h1RankBlockLinearMap (f : Hom K L) :
    (K.C1 × L.C0) →ₗ[ℚ] (K.C2 × L.C1) :=
  (K.d1.comp (LinearMap.fst ℚ K.C1 L.C0)).prod
    ((f.f1.comp (LinearMap.fst ℚ K.C1 L.C0)) -
      (L.d0.comp (LinearMap.snd ℚ K.C1 L.C0)))

/-- Evaluation API for `h1RankBlockLinearMap`; the displayed block expression
is the normal form used by the subsequent exact-sequence proof. -/
@[simp]
theorem h1RankBlockLinearMap_apply (f : Hom K L) (z : K.C1) (x : L.C0) :
    f.h1RankBlockLinearMap (z, x) = (K.d1 z, f.f1 z - L.d0 x) :=
  rfl

/-- Internal image-plus-boundary subspace used to compare the block range with
the literal target quotient.  Both summands are derived from `f`, not supplied
certificates. -/
private def h1CycleRangeSum (f : Hom K L) :
    Submodule ℚ (LinearMap.ker L.d1) :=
  LinearMap.range f.cyclesMap ⊔
    LinearMap.range L.boundaryToCycles

/-- Restrict the target quotient map to the sum of mapped cycles and target
boundaries.  This proof-only map exposes the first exact sequence used by the
public block-rank theorem. -/
private def h1CycleRangeQuotientMap (f : Hom K L) :
    h1CycleRangeSum f →ₗ[ℚ] L.H1 :=
  (LinearMap.range L.boundaryToCycles).mkQ.domRestrict
    (h1CycleRangeSum f)

/-- The restricted quotient map has exactly the range of the induced `H¹`
map; adjoining target boundaries does not change quotient classes. -/
private theorem range_h1CycleRangeQuotientMap (f : Hom K L) :
    LinearMap.range (h1CycleRangeQuotientMap f) =
      LinearMap.range f.h1Map := by
  rw [h1CycleRangeQuotientMap, LinearMap.range_domRestrict,
    h1CycleRangeSum, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  exact f.range_h1Map.symm

/-- The kernel of the restricted quotient is precisely the target-boundary
subspace viewed inside the image-plus-boundary sum. -/
private theorem ker_h1CycleRangeQuotientMap (f : Hom K L) :
    LinearMap.ker (h1CycleRangeQuotientMap f) =
      (LinearMap.range L.boundaryToCycles).comap
        (h1CycleRangeSum f).subtype := by
  rw [h1CycleRangeQuotientMap, LinearMap.ker_domRestrict,
    Submodule.ker_mkQ]

/-- First exact-sequence dimension identity: the rank of the induced `H¹`
map plus the target-boundary rank is the dimension of mapped cycles together
with target boundaries. -/
private theorem finrank_h1Map_add_boundary_eq_cycleRangeSum (f : Hom K L) :
    Module.finrank ℚ (LinearMap.range f.h1Map) +
        Module.finrank ℚ (LinearMap.range L.boundaryToCycles) =
      Module.finrank ℚ (h1CycleRangeSum f) := by
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker
      (h1CycleRangeQuotientMap f)
  have hkernel :
      Module.finrank ℚ
          (LinearMap.ker (h1CycleRangeQuotientMap f)) =
        Module.finrank ℚ (LinearMap.range L.boundaryToCycles) := by
    rw [ker_h1CycleRangeQuotientMap]
    exact (Submodule.comapSubtypeEquivOfLe
      (show LinearMap.range L.boundaryToCycles ≤ h1CycleRangeSum f from
        le_sup_right)).finrank_eq
  rw [range_h1CycleRangeQuotientMap, hkernel] at hrankNullity
  exact hrankNullity

/-- API helper for the block-rank theorem: viewing target boundaries inside
target cycles preserves their rank, so their dimension is the rank of `L.d0`.
-/
private theorem finrank_range_boundaryToCycles_eq_d0 (L : ThreeCochainComplex ℚ) :
    Module.finrank ℚ (LinearMap.range L.boundaryToCycles) =
      Module.finrank ℚ (LinearMap.range L.d0) := by
  have hcomp :
      (LinearMap.ker L.d1).subtype.comp L.boundaryToCycles = L.d0 := by
    ext x
    rfl
  calc
    Module.finrank ℚ (LinearMap.range L.boundaryToCycles) =
        Module.finrank ℚ
          ((LinearMap.range L.boundaryToCycles).map
            (LinearMap.ker L.d1).subtype) :=
      (Submodule.finrank_map_subtype_eq
        (LinearMap.ker L.d1)
        (LinearMap.range L.boundaryToCycles)).symm
    _ = Module.finrank ℚ (LinearMap.range L.d0) := by
      rw [← LinearMap.range_comp, hcomp]

/-- Project the range of the block map to its first component.  This is the
surjection in the second exact sequence used by the block-rank theorem. -/
private def h1RankBlockFirstOnRange (f : Hom K L) :
    LinearMap.range f.h1RankBlockLinearMap →ₗ[ℚ] K.C2 :=
  (LinearMap.fst ℚ K.C2 L.C1).comp
    (LinearMap.range f.h1RankBlockLinearMap).subtype

/-- The first projection of the block range is exactly the range of `K.d1`.
-/
private theorem range_h1RankBlockFirstOnRange (f : Hom K L) :
    LinearMap.range (h1RankBlockFirstOnRange f) =
      LinearMap.range K.d1 := by
  apply le_antisymm
  · rintro _ ⟨blockValue, rfl⟩
    obtain ⟨input, hinput⟩ := blockValue.2
    refine ⟨input.1, ?_⟩
    change K.d1 input.1 = blockValue.1.1
    exact congrArg Prod.fst hinput
  · rintro _ ⟨z, rfl⟩
    let blockValue := f.h1RankBlockLinearMap (z, 0)
    have hblockValue : blockValue ∈
        LinearMap.range f.h1RankBlockLinearMap :=
      LinearMap.mem_range_self f.h1RankBlockLinearMap (z, 0)
    refine ⟨⟨blockValue, hblockValue⟩, ?_⟩
    rfl

/-- The second component identifies the kernel of the first block projection
with mapped source cycles together with target boundaries. -/
private noncomputable def h1RankBlockKernelSecond (f : Hom K L) :
    LinearMap.ker (h1RankBlockFirstOnRange f) →ₗ[ℚ]
      h1CycleRangeSum f where
  toFun blockKernel := by
    let input := Classical.choose blockKernel.1.2
    have hinput := Classical.choose_spec blockKernel.1.2
    have hfirst : K.d1 input.1 = 0 := by
      have hzero := blockKernel.2
      change blockKernel.1.1.1 = 0 at hzero
      exact (congrArg Prod.fst hinput).trans hzero
    have hcycle :
        L.d1 (f.f1 input.1 - L.d0 input.2) = 0 := by
      rw [map_sub, ← f.comm1, hfirst, map_zero, L.d1_comp_d0, sub_zero]
    have hsecond :
        f.f1 input.1 - L.d0 input.2 = blockKernel.1.1.2 :=
      congrArg Prod.snd hinput
    have hblockCycle : L.d1 blockKernel.1.1.2 = 0 := by
      rw [← hsecond]
      exact hcycle
    refine ⟨⟨blockKernel.1.1.2, hblockCycle⟩, ?_⟩
    · have himage : f.cyclesMap ⟨input.1, hfirst⟩ ∈
          h1CycleRangeSum f :=
        (show LinearMap.range f.cyclesMap ≤ h1CycleRangeSum f from
          le_sup_left)
          (LinearMap.mem_range_self f.cyclesMap ⟨input.1, hfirst⟩)
      have hboundary : L.boundaryToCycles input.2 ∈
          h1CycleRangeSum f :=
        (show LinearMap.range L.boundaryToCycles ≤ h1CycleRangeSum f from
          le_sup_right)
          (LinearMap.mem_range_self L.boundaryToCycles input.2)
      have hsub := (h1CycleRangeSum f).sub_mem himage hboundary
      have hvalue :
          f.cyclesMap ⟨input.1, hfirst⟩ -
              L.boundaryToCycles input.2 =
            (⟨blockKernel.1.1.2, hblockCycle⟩ : LinearMap.ker L.d1) := by
        apply Subtype.ext
        exact hsecond
      rw [← hvalue]
      exact hsub
  map_add' left right := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' scalar blockKernel := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Coercing the block-kernel identification remembers only the second block
component; the noncomputable range witness is proof-only. -/
@[simp]
private theorem h1RankBlockKernelSecond_coe (f : Hom K L)
    (blockKernel : LinearMap.ker (h1RankBlockFirstOnRange f)) :
    ((h1RankBlockKernelSecond f blockKernel).1.1 : L.C1) =
      blockKernel.1.1.2 := by
  rfl

/-- The second-component map on the block kernel is injective. -/
private theorem h1RankBlockKernelSecond_injective (f : Hom K L) :
    Function.Injective (h1RankBlockKernelSecond f) := by
  intro left right hsecond
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hleft := left.2
    have hright := right.2
    change left.1.1.1 = 0 at hleft
    change right.1.1.1 = 0 at hright
    exact hleft.trans hright.symm
  · simpa using congrArg
      (fun value : h1CycleRangeSum f => (value.1 : L.C1)) hsecond

/-- The second-component map on the block kernel is surjective. -/
private theorem h1RankBlockKernelSecond_surjective (f : Hom K L) :
    Function.Surjective (h1RankBlockKernelSecond f) := by
  intro cycleSum
  obtain ⟨mapped, hmapped, boundary, hboundary, hsum⟩ :=
    (Submodule.mem_sup.mp cycleSum.2)
  obtain ⟨sourceCycle, hsourceCycle⟩ := hmapped
  obtain ⟨primitive, hprimitive⟩ := hboundary
  subst mapped
  subst boundary
  let blockValue := f.h1RankBlockLinearMap (sourceCycle.1, -primitive)
  have hblockValue : blockValue ∈
      LinearMap.range f.h1RankBlockLinearMap :=
    LinearMap.mem_range_self f.h1RankBlockLinearMap
      (sourceCycle.1, -primitive)
  let blockRange : LinearMap.range f.h1RankBlockLinearMap :=
    ⟨blockValue, hblockValue⟩
  have hfirst : h1RankBlockFirstOnRange f blockRange = 0 := by
    change K.d1 sourceCycle.1 = 0
    exact sourceCycle.2
  let blockKernel : LinearMap.ker (h1RankBlockFirstOnRange f) :=
    ⟨blockRange, hfirst⟩
  refine ⟨blockKernel, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((h1RankBlockKernelSecond f blockKernel).1.1 : L.C1) =
    cycleSum.1.1
  rw [h1RankBlockKernelSecond_coe]
  change f.f1 sourceCycle.1 - L.d0 (-primitive) = cycleSum.1.1
  rw [map_neg, sub_neg_eq_add]
  exact congrArg Subtype.val hsum

/-- The block-kernel identification preserves dimension. -/
private theorem finrank_ker_h1RankBlockFirstOnRange_eq_cycleRangeSum
    (f : Hom K L) :
    Module.finrank ℚ (LinearMap.ker (h1RankBlockFirstOnRange f)) =
      Module.finrank ℚ (h1CycleRangeSum f) :=
  (LinearEquiv.ofBijective (h1RankBlockKernelSecond f)
    ⟨h1RankBlockKernelSecond_injective f,
      h1RankBlockKernelSecond_surjective f⟩).finrank_eq

/-- Second exact-sequence dimension identity: the block rank is the source
`d1` rank plus the dimension of mapped cycles and target boundaries. -/
private theorem finrank_h1RankBlock_eq_d1_add_cycleRangeSum (f : Hom K L) :
    Module.finrank ℚ (LinearMap.range f.h1RankBlockLinearMap) =
      Module.finrank ℚ (LinearMap.range K.d1) +
        Module.finrank ℚ (h1CycleRangeSum f) := by
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker
      (h1RankBlockFirstOnRange f)
  rw [range_h1RankBlockFirstOnRange,
    finrank_ker_h1RankBlockFirstOnRange_eq_cycleRangeSum] at hrankNullity
  exact hrankNullity.symm

/-- The literal quotient-`H¹` rank is recovered from the block rank after
removing the source `d1` and target `d0` contributions.  This is the semantic
correctness theorem used by the executable presentation defect; the block map
itself contains no quotient or dimension operation. -/
theorem finrank_range_h1Map_eq_h1RankBlock (f : Hom K L) :
    Module.finrank ℚ (LinearMap.range f.h1Map) =
      Module.finrank ℚ (LinearMap.range f.h1RankBlockLinearMap) -
        Module.finrank ℚ (LinearMap.range K.d1) -
          Module.finrank ℚ (LinearMap.range L.d0) := by
  have hquotient := finrank_h1Map_add_boundary_eq_cycleRangeSum f
  have hboundary := finrank_range_boundaryToCycles_eq_d0 L
  have hblock := finrank_h1RankBlock_eq_d1_add_cycleRangeSum f
  omega

end Hom

/-- The dimension of literal `H¹ = ker d1 / range d0` is the degree-one
dimension minus the two differential ranks. -/
theorem finrank_h1_eq_c1_sub_d1_sub_d0 (K : ThreeCochainComplex ℚ) :
    Module.finrank ℚ K.H1 =
      Module.finrank ℚ K.C1 -
        Module.finrank ℚ (LinearMap.range K.d1) -
          Module.finrank ℚ (LinearMap.range K.d0) := by
  have hquotient :
      Module.finrank ℚ K.H1 +
          Module.finrank ℚ (LinearMap.range K.boundaryToCycles) =
        Module.finrank ℚ (LinearMap.ker K.d1) :=
    Submodule.finrank_quotient_add_finrank
      (LinearMap.range K.boundaryToCycles)
  have hboundary := Hom.finrank_range_boundaryToCycles_eq_d0 K
  rw [hboundary] at hquotient
  have hrankNullity :
      Module.finrank ℚ (LinearMap.range K.d1) +
          Module.finrank ℚ (LinearMap.ker K.d1) =
        Module.finrank ℚ K.C1 :=
    LinearMap.finrank_range_add_finrank_ker K.d1
  omega

end ThreeCochainComplex

end AAT.AG.TwoPhase

#assert_standard_axioms_only AAT.AG.TwoPhase.ThreeCochainComplex

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

universe u

namespace FiniteComparisonPresentation

open ExecutableRationalLinearAlgebra

/-! ## Raw finite A-subnerve cells -/

/-- Raw K1 support of a coarse edge, computed as the intersection of its two
endpoint chart-support tables. -/
def coarseEdgeSupportFinset (P : FiniteComparisonPresentation)
    (edge : P.CoarseEdge) : Finset P.CoarseTarget :=
  P.coarseChartSupport (P.coarseEdgeLeft edge) ∩
    P.coarseChartSupport (P.coarseEdgeRight edge)

/-- Raw K1 support of a coarse face, computed as the intersection of its
three boundary-edge supports. -/
def coarseFaceSupportFinset (P : FiniteComparisonPresentation)
    (face : P.CoarseFace) : Finset P.CoarseTarget :=
  P.coarseEdgeSupportFinset (P.coarseFaceEdge0 face) ∩
    P.coarseEdgeSupportFinset (P.coarseFaceEdge1 face) ∩
      P.coarseEdgeSupportFinset (P.coarseFaceEdge2 face)

/-- Raw K1 support of a fine edge, computed as the intersection of its two
endpoint chart-support tables. -/
def fineEdgeSupportFinset (P : FiniteComparisonPresentation)
    (edge : P.FineEdge) : Finset P.FineTarget :=
  P.fineChartSupport (P.fineEdgeLeft edge) ∩
    P.fineChartSupport (P.fineEdgeRight edge)

/-- Raw K1 support of a fine face, computed as the intersection of its three
boundary-edge supports. -/
def fineFaceSupportFinset (P : FiniteComparisonPresentation)
    (face : P.FineFace) : Finset P.FineTarget :=
  P.fineEdgeSupportFinset (P.fineFaceEdge0 face) ∩
    P.fineEdgeSupportFinset (P.fineFaceEdge1 face) ∩
      P.fineEdgeSupportFinset (P.fineFaceEdge2 face)

/-- Executable preimage of a coarse target subset under the computed reading
factor.  It uses only the finite target enumeration and the Cycle 6 search
factor, not the canonical choice-based semantic factor. -/
def finePreimageFinset (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineTarget :=
  Finset.univ.filter fun target => P.computedFactor target ∈ A

/-- Membership in the executable fine preimage is evaluation of the computed
factor against the coarse target subset.  This public Cycle 15 owner API lets
fixture clients normalize preimage membership without unfolding the search
definition; all data come from `computedFactor` and `A`. -/
theorem mem_finePreimageFinset_iff (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (target : P.FineTarget) :
    target ∈ P.finePreimageFinset A ↔ P.computedFactor target ∈ A := by
  simp only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership in a raw coarse edge support is simultaneous membership at
its two endpoint charts.  This public Cycle 15 owner API exposes the support
normal form for clients and derives solely from raw endpoint incidence. -/
theorem mem_coarseEdgeSupportFinset_iff_raw
    (P : FiniteComparisonPresentation) (edge : P.CoarseEdge)
    (target : P.CoarseTarget) :
    target ∈ P.coarseEdgeSupportFinset edge ↔
      target ∈ P.coarseChartSupport (P.coarseEdgeLeft edge) ∧
        target ∈ P.coarseChartSupport (P.coarseEdgeRight edge) := by
  simp only [coarseEdgeSupportFinset, Finset.mem_inter]

/-- Membership in a raw fine edge support is simultaneous membership at its
two endpoint charts.  This public Cycle 15 owner API exposes the support
normal form for clients and derives solely from raw endpoint incidence. -/
theorem mem_fineEdgeSupportFinset_iff_raw
    (P : FiniteComparisonPresentation) (edge : P.FineEdge)
    (target : P.FineTarget) :
    target ∈ P.fineEdgeSupportFinset edge ↔
      target ∈ P.fineChartSupport (P.fineEdgeLeft edge) ∧
        target ∈ P.fineChartSupport (P.fineEdgeRight edge) := by
  simp only [fineEdgeSupportFinset, Finset.mem_inter]

/-- Membership in a raw coarse face support is simultaneous membership in
the supports of its three boundary edges.  This public Cycle 15 owner API
exposes the support normal form from raw face incidence and adds no filling
premise. -/
theorem mem_coarseFaceSupportFinset_iff_raw
    (P : FiniteComparisonPresentation) (face : P.CoarseFace)
    (target : P.CoarseTarget) :
    target ∈ P.coarseFaceSupportFinset face ↔
      (target ∈ P.coarseEdgeSupportFinset (P.coarseFaceEdge0 face) ∧
        target ∈ P.coarseEdgeSupportFinset (P.coarseFaceEdge1 face)) ∧
          target ∈ P.coarseEdgeSupportFinset (P.coarseFaceEdge2 face) := by
  simp only [coarseFaceSupportFinset, Finset.mem_inter]

/-- Membership in a raw fine face support is simultaneous membership in the
supports of its three boundary edges.  This public Cycle 15 owner API exposes
the support normal form from raw face incidence and adds no filling premise. -/
theorem mem_fineFaceSupportFinset_iff_raw
    (P : FiniteComparisonPresentation) (face : P.FineFace)
    (target : P.FineTarget) :
    target ∈ P.fineFaceSupportFinset face ↔
      (target ∈ P.fineEdgeSupportFinset (P.fineFaceEdge0 face) ∧
        target ∈ P.fineEdgeSupportFinset (P.fineFaceEdge1 face)) ∧
          target ∈ P.fineEdgeSupportFinset (P.fineFaceEdge2 face) := by
  simp only [fineFaceSupportFinset, Finset.mem_inter]

/-- Coarse charts whose raw support meets `A`. -/
def coarseChartsIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.CoarseChart :=
  Finset.univ.filter fun chart =>
    (P.coarseChartSupport chart ∩ A).Nonempty

/-- Coarse edges whose raw K1 support meets `A`. -/
def coarseEdgesIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.CoarseEdge :=
  Finset.univ.filter fun edge =>
    (P.coarseEdgeSupportFinset edge ∩ A).Nonempty

/-- Coarse faces whose raw K1 support meets `A`. -/
def coarseFacesIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.CoarseFace :=
  Finset.univ.filter fun face =>
    (P.coarseFaceSupportFinset face ∩ A).Nonempty

/-- Fine charts whose raw support meets the computed preimage of `A`. -/
def fineChartsIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineChart :=
  Finset.univ.filter fun chart =>
    (P.fineChartSupport chart ∩ P.finePreimageFinset A).Nonempty

/-- Fine edges whose raw K1 support meets the computed preimage of `A`. -/
def fineEdgesIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineEdge :=
  Finset.univ.filter fun edge =>
    (P.fineEdgeSupportFinset edge ∩ P.finePreimageFinset A).Nonempty

/-- Fine faces whose raw K1 support meets the computed preimage of `A`. -/
def fineFacesIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Finset P.FineFace :=
  Finset.univ.filter fun face =>
    (P.fineFaceSupportFinset face ∩ P.finePreimageFinset A).Nonempty

/-- Raw coarse-chart selection is witnessed by a target in both the chart
support and the selected coarse subset.  This public Cycle 15 owner API is the
no-unfold characterization used by fixture clients; its witnesses come from
raw support and `A`. -/
theorem mem_coarseChartsIn_iff_raw (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (chart : P.CoarseChart) :
    chart ∈ P.coarseChartsIn A ↔
      ∃ target, target ∈ P.coarseChartSupport chart ∧ target ∈ A := by
  rw [coarseChartsIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    exact ⟨target, (Finset.mem_inter.mp htarget).1,
      (Finset.mem_inter.mp htarget).2⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr ⟨hsupport, hA⟩⟩

/-- Raw coarse-edge selection is witnessed by a target in both the generated
edge support and the selected coarse subset.  This public Cycle 15 owner API is
the no-unfold characterization used by fixture clients; it introduces no
selected-edge certificate. -/
theorem mem_coarseEdgesIn_iff_raw (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.CoarseEdge) :
    edge ∈ P.coarseEdgesIn A ↔
      ∃ target, target ∈ P.coarseEdgeSupportFinset edge ∧ target ∈ A := by
  rw [coarseEdgesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    exact ⟨target, (Finset.mem_inter.mp htarget).1,
      (Finset.mem_inter.mp htarget).2⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr ⟨hsupport, hA⟩⟩

/-- Raw coarse-face selection is witnessed by a target in both the generated
face support and the selected coarse subset.  This public Cycle 15 owner API is
the no-unfold characterization used by fixture clients; it introduces no
selected-face or filling certificate. -/
theorem mem_coarseFacesIn_iff_raw (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFace) :
    face ∈ P.coarseFacesIn A ↔
      ∃ target, target ∈ P.coarseFaceSupportFinset face ∧ target ∈ A := by
  rw [coarseFacesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    exact ⟨target, (Finset.mem_inter.mp htarget).1,
      (Finset.mem_inter.mp htarget).2⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr ⟨hsupport, hA⟩⟩

/-- Raw fine-chart selection is witnessed by a supported fine target whose
computed factor lies in the selected coarse subset.  This public Cycle 15
owner API exposes the executable-preimage selection rule and uses only raw
support plus the computed factor. -/
theorem mem_fineChartsIn_iff_raw (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (chart : P.FineChart) :
    chart ∈ P.fineChartsIn A ↔
      ∃ target, target ∈ P.fineChartSupport chart ∧
        P.computedFactor target ∈ A := by
  rw [fineChartsIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
    exact ⟨target, hsupport,
      (P.mem_finePreimageFinset_iff A target).1 hpreimage⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr ⟨hsupport,
      (P.mem_finePreimageFinset_iff A target).2 hA⟩⟩

/-- Raw fine-edge selection is witnessed by a supported fine target whose
computed factor lies in the selected coarse subset.  This public Cycle 15
owner API exposes the executable-preimage selection rule and uses only raw
support plus the computed factor. -/
theorem mem_fineEdgesIn_iff_raw (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdge) :
    edge ∈ P.fineEdgesIn A ↔
      ∃ target, target ∈ P.fineEdgeSupportFinset edge ∧
        P.computedFactor target ∈ A := by
  rw [fineEdgesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
    exact ⟨target, hsupport,
      (P.mem_finePreimageFinset_iff A target).1 hpreimage⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr ⟨hsupport,
      (P.mem_finePreimageFinset_iff A target).2 hA⟩⟩

/-- Raw fine-face selection is witnessed by a supported fine target whose
computed factor lies in the selected coarse subset.  This public Cycle 15
owner API exposes the executable-preimage selection rule and uses only raw
support plus the computed factor. -/
theorem mem_fineFacesIn_iff_raw (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFace) :
    face ∈ P.fineFacesIn A ↔
      ∃ target, target ∈ P.fineFaceSupportFinset face ∧
        P.computedFactor target ∈ A := by
  rw [fineFacesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
    exact ⟨target, hsupport,
      (P.mem_finePreimageFinset_iff A target).1 hpreimage⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr ⟨hsupport,
      (P.mem_finePreimageFinset_iff A target).2 hA⟩⟩

/-- Executable coarse chart index type for the `A`-subnerve. -/
abbrev CoarseChartIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) := {chart // chart ∈ P.coarseChartsIn A}

/-- Executable coarse edge index type for the `A`-subnerve. -/
abbrev CoarseEdgeIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) := {edge // edge ∈ P.coarseEdgesIn A}

/-- Executable coarse face index type for the `A`-subnerve. -/
abbrev CoarseFaceIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) := {face // face ∈ P.coarseFacesIn A}

/-- Executable fine chart index type for the computed preimage subnerve. -/
abbrev FineChartIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) := {chart // chart ∈ P.fineChartsIn A}

/-- Executable fine edge index type for the computed preimage subnerve. -/
abbrev FineEdgeIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) := {edge // edge ∈ P.fineEdgesIn A}

/-- Executable fine face index type for the computed preimage subnerve. -/
abbrev FineFaceIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) := {face // face ∈ P.fineFacesIn A}

/-! ## Raw selected incidence and comparison tables -/

/-- Raw chart-support compatibility for the computed factor.  The source
representative is used only to discharge membership; the returned target is
the executable `computedFactor`. -/
theorem computedFactor_mem_coarseChartSupport
    (P : FiniteComparisonPresentation) (chart : P.FineChart)
    (target : P.FineTarget)
    (htarget : target ∈ P.fineChartSupport chart) :
    P.computedFactor target ∈ P.coarseChartSupport (P.chartMap chart) := by
  exact P.chartSupport_compatible_source chart
    (P.computedRepresentative target) (by
      simpa only [P.fineRead_computedRepresentative target] using htarget)

/-- Left endpoint in the raw coarse selected cells. -/
def coarseEdgeLeftIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.CoarseEdgeIn A) :
    P.CoarseChartIn A := by
  refine ⟨P.coarseEdgeLeft edge.1, ?_⟩
  simp only [coarseChartsIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hedge : (P.coarseEdgeSupportFinset edge.1 ∩ A).Nonempty := by
    simpa only [coarseEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using edge.2
  obtain ⟨target, htarget⟩ := hedge
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hsupport).1, hA⟩⟩

/-- Right endpoint in the raw coarse selected cells. -/
def coarseEdgeRightIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.CoarseEdgeIn A) :
    P.CoarseChartIn A := by
  refine ⟨P.coarseEdgeRight edge.1, ?_⟩
  simp only [coarseChartsIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hedge : (P.coarseEdgeSupportFinset edge.1 ∩ A).Nonempty := by
    simpa only [coarseEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using edge.2
  obtain ⟨target, htarget⟩ := hedge
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hsupport).2, hA⟩⟩

/-- Boundary edge zero in the raw coarse selected cells. -/
def coarseFaceEdge0In (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFaceIn A) :
    P.CoarseEdgeIn A := by
  refine ⟨P.coarseFaceEdge0 face.1, ?_⟩
  simp only [coarseEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hface : (P.coarseFaceSupportFinset face.1 ∩ A).Nonempty := by
    simpa only [coarseFacesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using face.2
  obtain ⟨target, htarget⟩ := hface
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hsupport).1).1, hA⟩⟩

/-- Boundary edge one in the raw coarse selected cells. -/
def coarseFaceEdge1In (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFaceIn A) :
    P.CoarseEdgeIn A := by
  refine ⟨P.coarseFaceEdge1 face.1, ?_⟩
  simp only [coarseEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hface : (P.coarseFaceSupportFinset face.1 ∩ A).Nonempty := by
    simpa only [coarseFacesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using face.2
  obtain ⟨target, htarget⟩ := hface
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hsupport).1).2, hA⟩⟩

/-- Boundary edge two in the raw coarse selected cells. -/
def coarseFaceEdge2In (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFaceIn A) :
    P.CoarseEdgeIn A := by
  refine ⟨P.coarseFaceEdge2 face.1, ?_⟩
  simp only [coarseEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hface : (P.coarseFaceSupportFinset face.1 ∩ A).Nonempty := by
    simpa only [coarseFacesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using face.2
  obtain ⟨target, htarget⟩ := hface
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hsupport).2, hA⟩⟩

/-- Left endpoint in the raw fine selected cells. -/
def fineEdgeLeftIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    P.FineChartIn A := by
  refine ⟨P.fineEdgeLeft edge.1, ?_⟩
  simp only [fineChartsIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hedge :
      (P.fineEdgeSupportFinset edge.1 ∩ P.finePreimageFinset A).Nonempty := by
    simpa only [fineEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using edge.2
  obtain ⟨target, htarget⟩ := hedge
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hsupport).1, hA⟩⟩

/-- The raw selected fine left endpoint exposes the underlying incidence-table
endpoint.  This definition-owner rule keeps downstream finite fixtures from
expanding the selection proof carried by `fineEdgeLeftIn`. -/
@[simp]
theorem fineEdgeLeftIn_coe (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    (P.fineEdgeLeftIn A edge).1 = P.fineEdgeLeft edge.1 :=
  rfl

/-- Right endpoint in the raw fine selected cells. -/
def fineEdgeRightIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    P.FineChartIn A := by
  refine ⟨P.fineEdgeRight edge.1, ?_⟩
  simp only [fineChartsIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hedge :
      (P.fineEdgeSupportFinset edge.1 ∩ P.finePreimageFinset A).Nonempty := by
    simpa only [fineEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using edge.2
  obtain ⟨target, htarget⟩ := hedge
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hsupport).2, hA⟩⟩

/-- The raw selected fine right endpoint exposes the underlying incidence-table
endpoint.  This companion definition-owner rule hides the selection proof. -/
@[simp]
theorem fineEdgeRightIn_coe (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    (P.fineEdgeRightIn A edge).1 = P.fineEdgeRight edge.1 :=
  rfl

/-- Boundary edge zero in the raw fine selected cells. -/
def fineFaceEdge0In (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFaceIn A) :
    P.FineEdgeIn A := by
  refine ⟨P.fineFaceEdge0 face.1, ?_⟩
  simp only [fineEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hface :
      (P.fineFaceSupportFinset face.1 ∩ P.finePreimageFinset A).Nonempty := by
    simpa only [fineFacesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using face.2
  obtain ⟨target, htarget⟩ := hface
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hsupport).1).1, hA⟩⟩

/-- Boundary edge one in the raw fine selected cells. -/
def fineFaceEdge1In (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFaceIn A) :
    P.FineEdgeIn A := by
  refine ⟨P.fineFaceEdge1 face.1, ?_⟩
  simp only [fineEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hface :
      (P.fineFaceSupportFinset face.1 ∩ P.finePreimageFinset A).Nonempty := by
    simpa only [fineFacesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using face.2
  obtain ⟨target, htarget⟩ := hface
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hsupport).1).2, hA⟩⟩

/-- Boundary edge two in the raw fine selected cells. -/
def fineFaceEdge2In (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFaceIn A) :
    P.FineEdgeIn A := by
  refine ⟨P.fineFaceEdge2 face.1, ?_⟩
  simp only [fineEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hface :
      (P.fineFaceSupportFinset face.1 ∩ P.finePreimageFinset A).Nonempty := by
    simpa only [fineFacesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using face.2
  obtain ⟨target, htarget⟩ := hface
  obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
  exact ⟨target, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hsupport).2, hA⟩⟩

/-- The raw chart comparison sends every selected fine chart to a selected
coarse chart using computed-factor support compatibility. -/
def chartMapIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (chart : P.FineChartIn A) :
    P.CoarseChartIn A := by
  refine ⟨P.chartMap chart.1, ?_⟩
  simp only [coarseChartsIn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hchart :
      (P.fineChartSupport chart.1 ∩ P.finePreimageFinset A).Nonempty := by
    simpa only [fineChartsIn, Finset.mem_filter, Finset.mem_univ, true_and]
      using chart.2
  obtain ⟨target, htarget⟩ := hchart
  obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
  refine ⟨P.computedFactor target, Finset.mem_inter.mpr ⟨
    P.computedFactor_mem_coarseChartSupport chart.1 target hsupport, ?_⟩⟩
  simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] using hpreimage

/-- The raw selected chart map exposes the underlying chart-map table.  This
definition-owner rule records that selection changes only the proof field. -/
@[simp]
theorem chartMapIn_coe (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (chart : P.FineChartIn A) :
    (P.chartMapIn A chart).1 = P.chartMap chart.1 :=
  rfl

/-- The raw partial edge comparison restricted to selected cells.  A
nondegenerate raw edge maps to a selected coarse edge; `none` remains the zero
branch used by cochain pullback. -/
def edgeMapOptionIn (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    Option (P.CoarseEdgeIn A) := by
  match hmap : P.edgeMap edge.1 with
  | none => exact none
  | some coarseEdge =>
      refine some ⟨coarseEdge, ?_⟩
      simp only [coarseEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      have hedge :
          (P.fineEdgeSupportFinset edge.1 ∩
            P.finePreimageFinset A).Nonempty := by
        simpa only [fineEdgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
          using edge.2
      obtain ⟨target, htarget⟩ := hedge
      obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
      have hleftFine : target ∈ P.fineChartSupport (P.fineEdgeLeft edge.1) :=
        (Finset.mem_inter.mp hsupport).1
      have hrightFine : target ∈ P.fineChartSupport (P.fineEdgeRight edge.1) :=
        (Finset.mem_inter.mp hsupport).2
      have hleft := P.computedFactor_mem_coarseChartSupport
        (P.fineEdgeLeft edge.1) target hleftFine
      have hright := P.computedFactor_mem_coarseChartSupport
        (P.fineEdgeRight edge.1) target hrightFine
      rw [P.edge_some_left edge.1 coarseEdge hmap] at hleft
      rw [P.edge_some_right edge.1 coarseEdge hmap] at hright
      refine ⟨P.computedFactor target, Finset.mem_inter.mpr ⟨
        Finset.mem_inter.mpr ⟨hleft, hright⟩, ?_⟩⟩
      simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpreimage

/-- Forgetting selected-cell proofs from the restricted raw partial edge map
recovers the presentation's original edge table. -/
@[simp]
theorem edgeMapOptionIn_map_val (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    (P.edgeMapOptionIn A edge).map (fun mapped => mapped.1) =
      P.edgeMap edge.1 := by
  unfold edgeMapOptionIn
  split <;> simp_all

/-- A raw degenerate edge stays degenerate after selected-cell restriction. -/
theorem edgeMapOptionIn_eq_none (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A)
    (hmap : P.edgeMap edge.1 = none) :
    P.edgeMapOptionIn A edge = none := by
  unfold edgeMapOptionIn
  split <;> simp_all

/-- A selected fine edge maps to a specified selected coarse edge exactly
when their underlying raw edge-table entry is the corresponding `some`.  This
public Cycle 15 owner API lets comparison clients reason about the restricted
partial map from raw table data, without unfolding its dependent construction. -/
theorem edgeMapOptionIn_eq_some_iff (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A)
    (coarseEdge : P.CoarseEdgeIn A) :
    P.edgeMapOptionIn A edge = some coarseEdge ↔
      P.edgeMap edge.1 = some coarseEdge.1 := by
  unfold edgeMapOptionIn
  split <;> simp_all [Subtype.ext_iff]

/-! ## Executable cochain maps and matrices -/

/-- Raw coarse degree-zero differential on the selected finite cell types. -/
def coarseD0LinearMap (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.CoarseChartIn A → ℚ) →ₗ[ℚ] (P.CoarseEdgeIn A → ℚ) where
  toFun cochain edge :=
    cochain (P.coarseEdgeRightIn A edge) -
      cochain (P.coarseEdgeLeftIn A edge)
  map_add' left right := by
    ext edge
    simp
    ring
  map_smul' scalar cochain := by
    ext edge
    simp
    ring

/-- Public evaluation API for `coarseD0LinearMap`: it exposes the endpoint
incidence formula used by downstream cochain arguments without unfolding the
executable definition.  Its only data are the raw coarse endpoints stored in
the presentation, so it adds no mathematical premise. -/
theorem coarseD0LinearMap_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (cochain : P.CoarseChartIn A → ℚ)
    (edge : P.CoarseEdgeIn A) :
    P.coarseD0LinearMap A cochain edge =
      cochain (P.coarseEdgeRightIn A edge) -
        cochain (P.coarseEdgeLeftIn A edge) :=
  rfl

/-- Raw coarse degree-one differential on the selected finite cell types. -/
def coarseD1LinearMap (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.CoarseEdgeIn A → ℚ) →ₗ[ℚ] (P.CoarseFaceIn A → ℚ) where
  toFun cochain face :=
    cochain (P.coarseFaceEdge0In A face) -
      cochain (P.coarseFaceEdge1In A face) +
        cochain (P.coarseFaceEdge2In A face)
  map_add' left right := by
    ext face
    simp
    ring
  map_smul' scalar cochain := by
    ext face
    simp
    ring

/-- Public evaluation API for `coarseD1LinearMap`: it exposes the oriented
three-edge boundary formula used by downstream cochain arguments.  The formula
is generated only from the presentation's raw coarse face-incidence table. -/
theorem coarseD1LinearMap_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (cochain : P.CoarseEdgeIn A → ℚ)
    (face : P.CoarseFaceIn A) :
    P.coarseD1LinearMap A cochain face =
      cochain (P.coarseFaceEdge0In A face) -
          cochain (P.coarseFaceEdge1In A face) +
        cochain (P.coarseFaceEdge2In A face) :=
  rfl

/-- Raw fine degree-zero differential on the computed-preimage cells. -/
def fineD0LinearMap (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.FineChartIn A → ℚ) →ₗ[ℚ] (P.FineEdgeIn A → ℚ) where
  toFun cochain edge :=
    cochain (P.fineEdgeRightIn A edge) -
      cochain (P.fineEdgeLeftIn A edge)
  map_add' left right := by
    ext edge
    simp
    ring
  map_smul' scalar cochain := by
    ext edge
    simp
    ring

/-- Public evaluation API for `fineD0LinearMap`: it exposes the endpoint
incidence formula on the computed-preimage cells for downstream clients.  The
formula depends only on raw fine endpoints and the selected-cell input. -/
theorem fineD0LinearMap_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (cochain : P.FineChartIn A → ℚ)
    (edge : P.FineEdgeIn A) :
    P.fineD0LinearMap A cochain edge =
      cochain (P.fineEdgeRightIn A edge) -
        cochain (P.fineEdgeLeftIn A edge) :=
  rfl

/-- Raw fine degree-one differential on the computed-preimage cells. -/
def fineD1LinearMap (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.FineEdgeIn A → ℚ) →ₗ[ℚ] (P.FineFaceIn A → ℚ) where
  toFun cochain face :=
    cochain (P.fineFaceEdge0In A face) -
      cochain (P.fineFaceEdge1In A face) +
        cochain (P.fineFaceEdge2In A face)
  map_add' left right := by
    ext face
    simp
    ring
  map_smul' scalar cochain := by
    ext face
    simp
    ring

/-- Public evaluation API for `fineD1LinearMap`: it exposes the oriented
three-edge boundary formula on computed-preimage cells.  The formula is
generated from raw fine face incidence and introduces no certificate input. -/
theorem fineD1LinearMap_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (cochain : P.FineEdgeIn A → ℚ)
    (face : P.FineFaceIn A) :
    P.fineD1LinearMap A cochain face =
      cochain (P.fineFaceEdge0In A face) -
          cochain (P.fineFaceEdge1In A face) +
        cochain (P.fineFaceEdge2In A face) :=
  rfl

/-- Raw degree-one comparison pullback, extended by zero on a degenerate fine
edge.  Its only branching datum is the presentation's partial edge table. -/
def edgePullback1LinearMap (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.CoarseEdgeIn A → ℚ) →ₗ[ℚ] (P.FineEdgeIn A → ℚ) where
  toFun cochain edge := (P.edgeMapOptionIn A edge).elim 0 cochain
  map_add' left right := by
    ext edge
    cases hmap : P.edgeMapOptionIn A edge <;> simp [hmap]
  map_smul' scalar cochain := by
    ext edge
    cases hmap : P.edgeMapOptionIn A edge <;> simp [hmap]

/-- Public evaluation API for `edgePullback1LinearMap`: downstream comparison
proofs may evaluate the partial-map branch without unfolding the linear-map
constructor.  The branch is the computed selected edge table, not a supplied
comparison certificate. -/
theorem edgePullback1LinearMap_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (cochain : P.CoarseEdgeIn A → ℚ)
    (edge : P.FineEdgeIn A) :
    P.edgePullback1LinearMap A cochain edge =
      (P.edgeMapOptionIn A edge).elim 0 cochain :=
  rfl

/-- Raw H¹-rank block map on sum-indexed coordinate functions.  The two row
blocks are exactly `[d1_K, 0]` and `[f1, -d0_L]`. -/
def h1RankBlockLinearMap (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.CoarseEdgeIn A ⊕ P.FineChartIn A → ℚ) →ₗ[ℚ]
      (P.CoarseFaceIn A ⊕ P.FineEdgeIn A → ℚ) where
  toFun cochain
    | Sum.inl face =>
        P.coarseD1LinearMap A (fun edge => cochain (Sum.inl edge)) face
    | Sum.inr edge =>
        P.edgePullback1LinearMap A
            (fun coarseEdge => cochain (Sum.inl coarseEdge)) edge -
          P.fineD0LinearMap A
            (fun chart => cochain (Sum.inr chart)) edge
  map_add' left right := by
    ext index
    cases index with
    | inl face =>
        simp [coarseD1LinearMap]
        ring
    | inr edge =>
        cases hmap : P.edgeMapOptionIn A edge <;>
          simp [edgePullback1LinearMap, fineD0LinearMap, hmap] <;>
            ring
  map_smul' scalar cochain := by
    ext index
    cases index with
    | inl face =>
        simp [coarseD1LinearMap]
        ring
    | inr edge =>
        cases hmap : P.edgeMapOptionIn A edge <;>
          simp [edgePullback1LinearMap, fineD0LinearMap, hmap] <;>
            ring

/-- Public left-row evaluation API for `h1RankBlockLinearMap`.  It identifies
the coarse-face block with the raw coarse `d1`, allowing rank and fixture
clients to use the generated incidence map rather than its implementation. -/
theorem h1RankBlockLinearMap_apply_inl (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (cochain : P.CoarseEdgeIn A ⊕ P.FineChartIn A → ℚ)
    (face : P.CoarseFaceIn A) :
    P.h1RankBlockLinearMap A cochain (Sum.inl face) =
      P.coarseD1LinearMap A (fun edge => cochain (Sum.inl edge)) face :=
  rfl

/-- Public right-row evaluation API for `h1RankBlockLinearMap`.  It identifies
the fine-edge block with raw edge pullback minus fine `d0`; both terms are
computed from presentation tables and no rank or H¹ value is supplied. -/
theorem h1RankBlockLinearMap_apply_inr (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (cochain : P.CoarseEdgeIn A ⊕ P.FineChartIn A → ℚ)
    (edge : P.FineEdgeIn A) :
    P.h1RankBlockLinearMap A cochain (Sum.inr edge) =
      P.edgePullback1LinearMap A
          (fun coarseEdge => cochain (Sum.inl coarseEdge)) edge -
        P.fineD0LinearMap A
          (fun chart => cochain (Sum.inr chart)) edge :=
  rfl

/-- Executable matrix of the raw coarse degree-zero differential. -/
def coarseD0Matrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    Matrix (P.CoarseEdgeIn A) (P.CoarseChartIn A) ℚ :=
  LinearMap.toMatrix' (P.coarseD0LinearMap A)

/-- Executable matrix of the raw coarse degree-one differential. -/
def coarseD1Matrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    Matrix (P.CoarseFaceIn A) (P.CoarseEdgeIn A) ℚ :=
  LinearMap.toMatrix' (P.coarseD1LinearMap A)

/-- Executable matrix of the raw fine degree-zero differential. -/
def fineD0Matrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    Matrix (P.FineEdgeIn A) (P.FineChartIn A) ℚ :=
  LinearMap.toMatrix' (P.fineD0LinearMap A)

/-- Executable matrix of the raw fine degree-one differential. -/
def fineD1Matrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    Matrix (P.FineFaceIn A) (P.FineEdgeIn A) ℚ :=
  LinearMap.toMatrix' (P.fineD1LinearMap A)

/-- Executable matrix of the raw degree-one comparison pullback. -/
def edgePullback1Matrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    Matrix (P.FineEdgeIn A) (P.CoarseEdgeIn A) ℚ :=
  LinearMap.toMatrix' (P.edgePullback1LinearMap A)

/-- Executable H¹-rank block matrix generated from the raw incidence and
partial comparison tables. -/
def h1RankBlockMatrix (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    Matrix (P.CoarseFaceIn A ⊕ P.FineEdgeIn A)
      (P.CoarseEdgeIn A ⊕ P.FineChartIn A) ℚ :=
  LinearMap.toMatrix' (P.h1RankBlockLinearMap A)

/-! The following matrix-entry APIs keep downstream executable fixtures on the
public linear-map surface.  They expose `toMatrix'` evaluation but do not add
matrix, rank, defect, or result data to `FiniteComparisonPresentation`. -/

/-- Public entry API for the coarse degree-zero matrix.  It positions the
matrix as the coordinate presentation of the raw `coarseD0LinearMap`; the
standard basis vector is generated by `LinearMap.toMatrix'`. -/
theorem coarseD0Matrix_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.CoarseEdgeIn A)
    (chart : P.CoarseChartIn A) :
    P.coarseD0Matrix A edge chart =
      P.coarseD0LinearMap A (Pi.single chart 1) edge := by
  rw [coarseD0Matrix, LinearMap.toMatrix'_apply]

/-- Public entry API for the coarse degree-one matrix.  It connects executable
matrix entries to `coarseD1LinearMap` on the generated standard basis, with no
additional incidence or rank premise. -/
theorem coarseD1Matrix_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFaceIn A)
    (edge : P.CoarseEdgeIn A) :
    P.coarseD1Matrix A face edge =
      P.coarseD1LinearMap A (Pi.single edge 1) face := by
  rw [coarseD1Matrix, LinearMap.toMatrix'_apply]

/-- Public entry API for the fine degree-zero matrix.  It connects executable
matrix entries to `fineD0LinearMap` on the generated standard basis and uses
only the computed-preimage cell types. -/
theorem fineD0Matrix_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A)
    (chart : P.FineChartIn A) :
    P.fineD0Matrix A edge chart =
      P.fineD0LinearMap A (Pi.single chart 1) edge := by
  rw [fineD0Matrix, LinearMap.toMatrix'_apply]

/-- Public entry API for the fine degree-one matrix.  It connects executable
matrix entries to `fineD1LinearMap` on the generated standard basis and adds
no face-boundary certificate. -/
theorem fineD1Matrix_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFaceIn A)
    (edge : P.FineEdgeIn A) :
    P.fineD1Matrix A face edge =
      P.fineD1LinearMap A (Pi.single edge 1) face := by
  rw [fineD1Matrix, LinearMap.toMatrix'_apply]

/-- Public entry API for the degree-one comparison matrix.  It evaluates the
raw `edgePullback1LinearMap` on a generated standard basis, so clients need not
unfold either the matrix or partial comparison linear map. -/
theorem edgePullback1Matrix_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (fineEdge : P.FineEdgeIn A)
    (coarseEdge : P.CoarseEdgeIn A) :
    P.edgePullback1Matrix A fineEdge coarseEdge =
      P.edgePullback1LinearMap A (Pi.single coarseEdge 1) fineEdge := by
  rw [edgePullback1Matrix, LinearMap.toMatrix'_apply]

/-- Public entry API for the executable H¹ block matrix.  It positions each
entry as evaluation of the generic raw block map on a standard basis; rank and
defect remain downstream computations rather than presentation fields. -/
theorem h1RankBlockMatrix_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (row : P.CoarseFaceIn A ⊕ P.FineEdgeIn A)
    (column : P.CoarseEdgeIn A ⊕ P.FineChartIn A) :
    P.h1RankBlockMatrix A row column =
      P.h1RankBlockLinearMap A (Pi.single column 1) row := by
  rw [h1RankBlockMatrix, LinearMap.toMatrix'_apply]

/-- Rank of the induced H¹ comparison computed from the raw block matrix and
the two exact-sequence correction ranks. -/
def computedASubnerveH1Rank (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : ℕ :=
  rationalMatrixRank (P.h1RankBlockMatrix A) -
    rationalMatrixRank (P.coarseD1Matrix A) -
      rationalMatrixRank (P.fineD0Matrix A)

/-- Main executable Cycle 8 API: compute the kernel/cokernel defect of the
actual A-subnerve H¹ comparison using only finite raw tables and exact rational
matrix rank. -/
def computedASubnerveDefect (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : ℕ × ℕ :=
  (Fintype.card (P.CoarseEdgeIn A) -
      rationalMatrixRank (P.coarseD1Matrix A) -
        rationalMatrixRank (P.coarseD0Matrix A) -
          P.computedASubnerveH1Rank A,
    Fintype.card (P.FineEdgeIn A) -
      rationalMatrixRank (P.fineD1Matrix A) -
        rationalMatrixRank (P.fineD0Matrix A) -
          P.computedASubnerveH1Rank A)

/-! ## Raw cells versus the canonical semantic A-subnerve -/

/-- Canonical semantic fine preimage corresponding to the raw computed
preimage.  This abbreviation occurs only in correctness statements. -/
abbrev canonicalFinePreimage (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : Set P.FineTarget :=
  comparisonFactor P.coarseReading P.fineReading P.coarserThan ⁻¹'
    (↑A : Set P.CoarseTarget)

/-- Raw coarse edge support has exactly the generated semantic K1 support. -/
@[simp]
theorem mem_coarseEdgeSupportFinset_iff
    (P : FiniteComparisonPresentation) (edge : P.CoarseEdge)
    (target : P.CoarseTarget) :
    target ∈ P.coarseEdgeSupportFinset edge ↔
      target ∈ P.coarseSupportedNerve.edgeSupport edge := by
  rw [P.coarseSupportedNerve.mem_edgeSupport_iff]
  simp only [coarseEdgeSupportFinset, Finset.mem_inter,
    P.mem_coarseSupportedNerve_chartSupport,
    P.coarseSupportedNerve_edgeLeft, P.coarseSupportedNerve_edgeRight]

/-- Raw fine edge support has exactly the generated semantic K1 support. -/
@[simp]
theorem mem_fineEdgeSupportFinset_iff
    (P : FiniteComparisonPresentation) (edge : P.FineEdge)
    (target : P.FineTarget) :
    target ∈ P.fineEdgeSupportFinset edge ↔
      target ∈ P.fineSupportedNerve.edgeSupport edge := by
  rw [P.fineSupportedNerve.mem_edgeSupport_iff]
  simp only [fineEdgeSupportFinset, Finset.mem_inter,
    P.mem_fineSupportedNerve_chartSupport,
    P.fineSupportedNerve_edgeLeft, P.fineSupportedNerve_edgeRight]

/-- Raw coarse face support has exactly the generated semantic K1 support. -/
@[simp]
theorem mem_coarseFaceSupportFinset_iff
    (P : FiniteComparisonPresentation) (face : P.CoarseFace)
    (target : P.CoarseTarget) :
    target ∈ P.coarseFaceSupportFinset face ↔
      target ∈ P.coarseSupportedNerve.faceSupport face := by
  rw [P.coarseSupportedNerve.mem_faceSupport_iff]
  simp only [coarseFaceSupportFinset, Finset.mem_inter,
    mem_coarseEdgeSupportFinset_iff]
  tauto

/-- Raw fine face support has exactly the generated semantic K1 support. -/
@[simp]
theorem mem_fineFaceSupportFinset_iff
    (P : FiniteComparisonPresentation) (face : P.FineFace)
    (target : P.FineTarget) :
    target ∈ P.fineFaceSupportFinset face ↔
      target ∈ P.fineSupportedNerve.faceSupport face := by
  rw [P.fineSupportedNerve.mem_faceSupport_iff]
  simp only [fineFaceSupportFinset, Finset.mem_inter,
    mem_fineEdgeSupportFinset_iff]
  tauto

/-- Raw coarse chart selection is the semantic chart-subset predicate.  This
public Cycle 15 owner API connects executable selected cells to the actual
A-subnerve; the only inputs are `P`, `A`, and a raw chart. -/
theorem mem_coarseChartsIn_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (chart : P.CoarseChart) :
    chart ∈ P.coarseChartsIn A ↔
      ∃ target, target ∈ P.coarseSupportedNerve.chartSupport chart ∧
        target ∈ (↑A : Set P.CoarseTarget) := by
  rw [coarseChartsIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
    exact ⟨target, hsupport, hA⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr ⟨hsupport, hA⟩⟩

/-- Raw coarse edge selection is the semantic edge-subset predicate.  This
public Cycle 15 owner API connects executable selected cells to the actual
A-subnerve from raw support, with no comparison certificate. -/
theorem mem_coarseEdgesIn_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (edge : P.CoarseEdge) :
    edge ∈ P.coarseEdgesIn A ↔
      ∃ target, target ∈ P.coarseSupportedNerve.edgeSupport edge ∧
        target ∈ (↑A : Set P.CoarseTarget) := by
  rw [coarseEdgesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
    exact ⟨target, (P.mem_coarseEdgeSupportFinset_iff edge target).1 hsupport,
      hA⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr
      ⟨(P.mem_coarseEdgeSupportFinset_iff edge target).2 hsupport, hA⟩⟩

/-- Raw coarse face selection is the semantic face-subset predicate.  This
public Cycle 15 owner API connects executable selected cells to the actual
A-subnerve from raw support, with no filling certificate. -/
theorem mem_coarseFacesIn_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (face : P.CoarseFace) :
    face ∈ P.coarseFacesIn A ↔
      ∃ target, target ∈ P.coarseSupportedNerve.faceSupport face ∧
        target ∈ (↑A : Set P.CoarseTarget) := by
  rw [coarseFacesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hA⟩ := Finset.mem_inter.mp htarget
    exact ⟨target, (P.mem_coarseFaceSupportFinset_iff face target).1 hsupport,
      hA⟩
  · rintro ⟨target, hsupport, hA⟩
    exact ⟨target, Finset.mem_inter.mpr
      ⟨(P.mem_coarseFaceSupportFinset_iff face target).2 hsupport, hA⟩⟩

/-- Raw fine chart selection is the canonical semantic preimage predicate.
This public Cycle 15 owner API connects computed-factor selection to the
canonical comparison preimage using the proved factor equality. -/
theorem mem_fineChartsIn_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (chart : P.FineChart) :
    chart ∈ P.fineChartsIn A ↔
      ∃ target, target ∈ P.fineSupportedNerve.chartSupport chart ∧
        target ∈ P.canonicalFinePreimage A := by
  rw [fineChartsIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
    have hA : P.computedFactor target ∈ A := by
      simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpreimage
    refine ⟨target, hsupport, ?_⟩
    change comparisonFactor P.coarseReading P.fineReading P.coarserThan target ∈ A
    rw [← congrFun P.computedFactor_eq_comparisonFactor target]
    exact hA
  · rintro ⟨target, hsupport, hpreimage⟩
    have hA : P.computedFactor target ∈ A := by
      change comparisonFactor P.coarseReading P.fineReading P.coarserThan target ∈ A
        at hpreimage
      rw [← congrFun P.computedFactor_eq_comparisonFactor target] at hpreimage
      exact hpreimage
    refine ⟨target, Finset.mem_inter.mpr ⟨hsupport, ?_⟩⟩
    simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA

/-- Raw fine edge selection is the canonical semantic preimage predicate.
This public Cycle 15 owner API connects computed-factor selection to the
canonical comparison preimage using raw support and factor equality. -/
theorem mem_fineEdgesIn_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (edge : P.FineEdge) :
    edge ∈ P.fineEdgesIn A ↔
      ∃ target, target ∈ P.fineSupportedNerve.edgeSupport edge ∧
        target ∈ P.canonicalFinePreimage A := by
  rw [fineEdgesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
    have hA : P.computedFactor target ∈ A := by
      simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpreimage
    refine ⟨target, (P.mem_fineEdgeSupportFinset_iff edge target).1 hsupport, ?_⟩
    change comparisonFactor P.coarseReading P.fineReading P.coarserThan target ∈ A
    rw [← congrFun P.computedFactor_eq_comparisonFactor target]
    exact hA
  · rintro ⟨target, hsupport, hpreimage⟩
    have hA : P.computedFactor target ∈ A := by
      change comparisonFactor P.coarseReading P.fineReading P.coarserThan target ∈ A
        at hpreimage
      rw [← congrFun P.computedFactor_eq_comparisonFactor target] at hpreimage
      exact hpreimage
    refine ⟨target, Finset.mem_inter.mpr
      ⟨(P.mem_fineEdgeSupportFinset_iff edge target).2 hsupport, ?_⟩⟩
    simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA

/-- Raw fine face selection is the canonical semantic preimage predicate.
This public Cycle 15 owner API connects computed-factor selection to the
canonical comparison preimage using raw support and factor equality. -/
theorem mem_fineFacesIn_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (face : P.FineFace) :
    face ∈ P.fineFacesIn A ↔
      ∃ target, target ∈ P.fineSupportedNerve.faceSupport face ∧
        target ∈ P.canonicalFinePreimage A := by
  rw [fineFacesIn, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨target, htarget⟩
    obtain ⟨hsupport, hpreimage⟩ := Finset.mem_inter.mp htarget
    have hA : P.computedFactor target ∈ A := by
      simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpreimage
    refine ⟨target, (P.mem_fineFaceSupportFinset_iff face target).1 hsupport, ?_⟩
    change comparisonFactor P.coarseReading P.fineReading P.coarserThan target ∈ A
    rw [← congrFun P.computedFactor_eq_comparisonFactor target]
    exact hA
  · rintro ⟨target, hsupport, hpreimage⟩
    have hA : P.computedFactor target ∈ A := by
      change comparisonFactor P.coarseReading P.fineReading P.coarserThan target ∈ A
        at hpreimage
      rw [← congrFun P.computedFactor_eq_comparisonFactor target] at hpreimage
      exact hpreimage
    refine ⟨target, Finset.mem_inter.mpr
      ⟨(P.mem_fineFaceSupportFinset_iff face target).2 hsupport, ?_⟩⟩
    simpa only [finePreimageFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA

/-- Raw coarse selected charts are canonically the actual semantic
`A`-subnerve charts. -/
def coarseChartEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    P.CoarseChartIn A ≃
      P.coarseSupportedNerve.ChartInTargetSubset
        (↑A : Set P.CoarseTarget) where
  toFun chart := ⟨chart.1, (P.mem_coarseChartsIn_iff A chart.1).1 chart.2⟩
  invFun chart := ⟨chart.1, (P.mem_coarseChartsIn_iff A chart.1).2 chart.2⟩
  left_inv chart := by apply Subtype.ext; rfl
  right_inv chart := by apply Subtype.ext; rfl

/-- Raw coarse selected edges are canonically the actual semantic
`A`-subnerve edges. -/
def coarseEdgeEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    P.CoarseEdgeIn A ≃
      P.coarseSupportedNerve.EdgeInTargetSubset
        (↑A : Set P.CoarseTarget) where
  toFun edge := ⟨edge.1, (P.mem_coarseEdgesIn_iff A edge.1).1 edge.2⟩
  invFun edge := ⟨edge.1, (P.mem_coarseEdgesIn_iff A edge.1).2 edge.2⟩
  left_inv edge := by apply Subtype.ext; rfl
  right_inv edge := by apply Subtype.ext; rfl

/-- Raw coarse selected faces are canonically the actual semantic
`A`-subnerve faces. -/
def coarseFaceEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    P.CoarseFaceIn A ≃
      P.coarseSupportedNerve.FaceInTargetSubset
        (↑A : Set P.CoarseTarget) where
  toFun face := ⟨face.1, (P.mem_coarseFacesIn_iff A face.1).1 face.2⟩
  invFun face := ⟨face.1, (P.mem_coarseFacesIn_iff A face.1).2 face.2⟩
  left_inv face := by apply Subtype.ext; rfl
  right_inv face := by apply Subtype.ext; rfl

/-- Raw fine selected charts are canonically the actual semantic charts over
the canonical factor preimage of `A`. -/
def fineChartEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    P.FineChartIn A ≃
      P.fineSupportedNerve.ChartInTargetSubset
        (P.canonicalFinePreimage A) where
  toFun chart := ⟨chart.1, (P.mem_fineChartsIn_iff A chart.1).1 chart.2⟩
  invFun chart := ⟨chart.1, (P.mem_fineChartsIn_iff A chart.1).2 chart.2⟩
  left_inv chart := by apply Subtype.ext; rfl
  right_inv chart := by apply Subtype.ext; rfl

/-- Raw fine selected edges are canonically the actual semantic edges over
the canonical factor preimage of `A`. -/
def fineEdgeEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    P.FineEdgeIn A ≃
      P.fineSupportedNerve.EdgeInTargetSubset
        (P.canonicalFinePreimage A) where
  toFun edge := ⟨edge.1, (P.mem_fineEdgesIn_iff A edge.1).1 edge.2⟩
  invFun edge := ⟨edge.1, (P.mem_fineEdgesIn_iff A edge.1).2 edge.2⟩
  left_inv edge := by apply Subtype.ext; rfl
  right_inv edge := by apply Subtype.ext; rfl

/-- Raw fine selected faces are canonically the actual semantic faces over
the canonical factor preimage of `A`. -/
def fineFaceEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    P.FineFaceIn A ≃
      P.fineSupportedNerve.FaceInTargetSubset
        (P.canonicalFinePreimage A) where
  toFun face := ⟨face.1, (P.mem_fineFacesIn_iff A face.1).1 face.2⟩
  invFun face := ⟨face.1, (P.mem_fineFacesIn_iff A face.1).2 face.2⟩
  left_inv face := by apply Subtype.ext; rfl
  right_inv face := by apply Subtype.ext; rfl

/-! ## Incidence correspondence -/

/-- Coarse left-endpoint transport commutes with the raw/semantic cell
equivalences. -/
theorem coarseEquiv_edgeLeft (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.CoarseEdgeIn A) :
    P.coarseChartEquiv A (P.coarseEdgeLeftIn A edge) =
      P.coarseSupportedNerve.targetSubsetEdgeLeft (↑A : Set P.CoarseTarget)
        (P.coarseEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Coarse right-endpoint transport commutes with the raw/semantic cell
equivalences. -/
theorem coarseEquiv_edgeRight (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.CoarseEdgeIn A) :
    P.coarseChartEquiv A (P.coarseEdgeRightIn A edge) =
      P.coarseSupportedNerve.targetSubsetEdgeRight (↑A : Set P.CoarseTarget)
        (P.coarseEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Coarse face-edge zero transport commutes with the raw/semantic cell
equivalences. -/
theorem coarseEquiv_faceEdge0 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFaceIn A) :
    P.coarseEdgeEquiv A (P.coarseFaceEdge0In A face) =
      P.coarseSupportedNerve.targetSubsetFaceEdge0 (↑A : Set P.CoarseTarget)
        (P.coarseFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Coarse face-edge one transport commutes with the raw/semantic cell
equivalences. -/
theorem coarseEquiv_faceEdge1 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFaceIn A) :
    P.coarseEdgeEquiv A (P.coarseFaceEdge1In A face) =
      P.coarseSupportedNerve.targetSubsetFaceEdge1 (↑A : Set P.CoarseTarget)
        (P.coarseFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Coarse face-edge two transport commutes with the raw/semantic cell
equivalences. -/
theorem coarseEquiv_faceEdge2 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFaceIn A) :
    P.coarseEdgeEquiv A (P.coarseFaceEdge2In A face) =
      P.coarseSupportedNerve.targetSubsetFaceEdge2 (↑A : Set P.CoarseTarget)
        (P.coarseFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Fine left-endpoint transport commutes with the raw/semantic cell
equivalences. -/
theorem fineEquiv_edgeLeft (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    P.fineChartEquiv A (P.fineEdgeLeftIn A edge) =
      P.fineSupportedNerve.targetSubsetEdgeLeft (P.canonicalFinePreimage A)
        (P.fineEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Fine right-endpoint transport commutes with the raw/semantic cell
equivalences. -/
theorem fineEquiv_edgeRight (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (edge : P.FineEdgeIn A) :
    P.fineChartEquiv A (P.fineEdgeRightIn A edge) =
      P.fineSupportedNerve.targetSubsetEdgeRight (P.canonicalFinePreimage A)
        (P.fineEdgeEquiv A edge) := by
  apply Subtype.ext
  rfl

/-- Fine face-edge zero transport commutes with the raw/semantic cell
equivalences. -/
theorem fineEquiv_faceEdge0 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFaceIn A) :
    P.fineEdgeEquiv A (P.fineFaceEdge0In A face) =
      P.fineSupportedNerve.targetSubsetFaceEdge0 (P.canonicalFinePreimage A)
        (P.fineFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Fine face-edge one transport commutes with the raw/semantic cell
equivalences. -/
theorem fineEquiv_faceEdge1 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFaceIn A) :
    P.fineEdgeEquiv A (P.fineFaceEdge1In A face) =
      P.fineSupportedNerve.targetSubsetFaceEdge1 (P.canonicalFinePreimage A)
        (P.fineFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-- Fine face-edge two transport commutes with the raw/semantic cell
equivalences. -/
theorem fineEquiv_faceEdge2 (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFaceIn A) :
    P.fineEdgeEquiv A (P.fineFaceEdge2In A face) =
      P.fineSupportedNerve.targetSubsetFaceEdge2 (P.canonicalFinePreimage A)
        (P.fineFaceEquiv A face) := by
  apply Subtype.ext
  rfl

/-! ## Cochain reindexing and differential correspondence -/

/-- Reindex semantic coarse chart cochains onto raw chart indices. -/
def coarseChartCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.coarseSupportedNerve.ChartInTargetSubset
        (↑A : Set P.CoarseTarget) → ℚ) ≃ₗ[ℚ]
      (P.CoarseChartIn A → ℚ) :=
  cochainEquivOfIndexEquiv (P.coarseChartEquiv A)

/-- Reindex semantic coarse edge cochains onto raw edge indices. -/
def coarseEdgeCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.coarseSupportedNerve.EdgeInTargetSubset
        (↑A : Set P.CoarseTarget) → ℚ) ≃ₗ[ℚ]
      (P.CoarseEdgeIn A → ℚ) :=
  cochainEquivOfIndexEquiv (P.coarseEdgeEquiv A)

/-- Reindex semantic coarse face cochains onto raw face indices. -/
def coarseFaceCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.coarseSupportedNerve.FaceInTargetSubset
        (↑A : Set P.CoarseTarget) → ℚ) ≃ₗ[ℚ]
      (P.CoarseFaceIn A → ℚ) :=
  cochainEquivOfIndexEquiv (P.coarseFaceEquiv A)

/-- Reindex semantic fine chart cochains onto raw chart indices. -/
def fineChartCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.fineSupportedNerve.ChartInTargetSubset
        (P.canonicalFinePreimage A) → ℚ) ≃ₗ[ℚ]
      (P.FineChartIn A → ℚ) :=
  cochainEquivOfIndexEquiv (P.fineChartEquiv A)

/-- Reindex semantic fine edge cochains onto raw edge indices. -/
def fineEdgeCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.fineSupportedNerve.EdgeInTargetSubset
        (P.canonicalFinePreimage A) → ℚ) ≃ₗ[ℚ]
      (P.FineEdgeIn A → ℚ) :=
  cochainEquivOfIndexEquiv (P.fineEdgeEquiv A)

/-- Reindex semantic fine face cochains onto raw face indices. -/
def fineFaceCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    (P.fineSupportedNerve.FaceInTargetSubset
        (P.canonicalFinePreimage A) → ℚ) ≃ₗ[ℚ]
      (P.FineFaceIn A → ℚ) :=
  cochainEquivOfIndexEquiv (P.fineFaceEquiv A)

/-- Coarse raw `d0` is the actual semantic A-subnerve `d0` after canonical
cell reindexing. -/
theorem coarseD0_commutes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (cochain : P.coarseSupportedNerve.ChartInTargetSubset
      (↑A : Set P.CoarseTarget) → ℚ) :
    P.coarseD0LinearMap A (P.coarseChartCochainEquiv A cochain) =
      P.coarseEdgeCochainEquiv A
        (P.coarseSupportedNerve.targetSubsetD0
          (↑A : Set P.CoarseTarget) cochain) := by
  ext edge
  change cochain (P.coarseChartEquiv A (P.coarseEdgeRightIn A edge)) -
      cochain (P.coarseChartEquiv A (P.coarseEdgeLeftIn A edge)) =
    cochain (P.coarseSupportedNerve.targetSubsetEdgeRight
        (↑A : Set P.CoarseTarget) (P.coarseEdgeEquiv A edge)) -
      cochain (P.coarseSupportedNerve.targetSubsetEdgeLeft
        (↑A : Set P.CoarseTarget) (P.coarseEdgeEquiv A edge))
  rw [P.coarseEquiv_edgeRight A edge, P.coarseEquiv_edgeLeft A edge]

/-- Coarse raw `d1` is the actual semantic A-subnerve `d1` after canonical
cell reindexing. -/
theorem coarseD1_commutes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (cochain : P.coarseSupportedNerve.EdgeInTargetSubset
      (↑A : Set P.CoarseTarget) → ℚ) :
    P.coarseD1LinearMap A (P.coarseEdgeCochainEquiv A cochain) =
      P.coarseFaceCochainEquiv A
        (P.coarseSupportedNerve.targetSubsetD1
          (↑A : Set P.CoarseTarget) cochain) := by
  ext face
  change cochain (P.coarseEdgeEquiv A (P.coarseFaceEdge0In A face)) -
        cochain (P.coarseEdgeEquiv A (P.coarseFaceEdge1In A face)) +
          cochain (P.coarseEdgeEquiv A (P.coarseFaceEdge2In A face)) =
    cochain (P.coarseSupportedNerve.targetSubsetFaceEdge0
        (↑A : Set P.CoarseTarget) (P.coarseFaceEquiv A face)) -
      cochain (P.coarseSupportedNerve.targetSubsetFaceEdge1
        (↑A : Set P.CoarseTarget) (P.coarseFaceEquiv A face)) +
        cochain (P.coarseSupportedNerve.targetSubsetFaceEdge2
          (↑A : Set P.CoarseTarget) (P.coarseFaceEquiv A face))
  rw [P.coarseEquiv_faceEdge0 A face, P.coarseEquiv_faceEdge1 A face,
    P.coarseEquiv_faceEdge2 A face]

/-- Fine raw `d0` is the actual semantic preimage-subnerve `d0` after
canonical cell reindexing. -/
theorem fineD0_commutes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (cochain : P.fineSupportedNerve.ChartInTargetSubset
      (P.canonicalFinePreimage A) → ℚ) :
    P.fineD0LinearMap A (P.fineChartCochainEquiv A cochain) =
      P.fineEdgeCochainEquiv A
        (P.fineSupportedNerve.targetSubsetD0
          (P.canonicalFinePreimage A) cochain) := by
  ext edge
  change cochain (P.fineChartEquiv A (P.fineEdgeRightIn A edge)) -
      cochain (P.fineChartEquiv A (P.fineEdgeLeftIn A edge)) =
    cochain (P.fineSupportedNerve.targetSubsetEdgeRight
        (P.canonicalFinePreimage A) (P.fineEdgeEquiv A edge)) -
      cochain (P.fineSupportedNerve.targetSubsetEdgeLeft
        (P.canonicalFinePreimage A) (P.fineEdgeEquiv A edge))
  rw [P.fineEquiv_edgeRight A edge, P.fineEquiv_edgeLeft A edge]

/-- Fine raw `d1` is the actual semantic preimage-subnerve `d1` after
canonical cell reindexing. -/
theorem fineD1_commutes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (cochain : P.fineSupportedNerve.EdgeInTargetSubset
      (P.canonicalFinePreimage A) → ℚ) :
    P.fineD1LinearMap A (P.fineEdgeCochainEquiv A cochain) =
      P.fineFaceCochainEquiv A
        (P.fineSupportedNerve.targetSubsetD1
          (P.canonicalFinePreimage A) cochain) := by
  ext face
  change cochain (P.fineEdgeEquiv A (P.fineFaceEdge0In A face)) -
        cochain (P.fineEdgeEquiv A (P.fineFaceEdge1In A face)) +
          cochain (P.fineEdgeEquiv A (P.fineFaceEdge2In A face)) =
    cochain (P.fineSupportedNerve.targetSubsetFaceEdge0
        (P.canonicalFinePreimage A) (P.fineFaceEquiv A face)) -
      cochain (P.fineSupportedNerve.targetSubsetFaceEdge1
        (P.canonicalFinePreimage A) (P.fineFaceEquiv A face)) +
        cochain (P.fineSupportedNerve.targetSubsetFaceEdge2
          (P.canonicalFinePreimage A) (P.fineFaceEquiv A face))
  rw [P.fineEquiv_faceEdge0 A face, P.fineEquiv_faceEdge1 A face,
    P.fineEquiv_faceEdge2 A face]

/-- The raw degree-one pullback is the actual canonical A-subnerve comparison
`f1` after cell reindexing.  In particular, the raw partial edge table—not a
supplied comparison matrix—determines the map used in the H¹ block. -/
theorem edgePullback1_commutes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (cochain : P.coarseSupportedNerve.EdgeInTargetSubset
      (↑A : Set P.CoarseTarget) → ℚ) :
    P.edgePullback1LinearMap A (P.coarseEdgeCochainEquiv A cochain) =
      P.fineEdgeCochainEquiv A
        ((P.toGeometry.aSubnerveComparisonHom
          (↑A : Set P.CoarseTarget)).f1 cochain) := by
  ext edge
  change (P.edgeMapOptionIn A edge).elim 0
      (fun rawEdge => cochain (P.coarseEdgeEquiv A rawEdge)) =
    (P.toGeometry.targetSubsetEdgeMapOption
      (↑A : Set P.CoarseTarget) (P.canonicalFinePreimage A)
      (fun _ htarget => htarget) (P.fineEdgeEquiv A edge)).elim 0 cochain
  cases hmap : P.edgeMap edge.1 with
  | none =>
      have hsemantic :
          P.toGeometry.edgeMap (P.fineEdgeEquiv A edge).1 = none := by
        simpa only [P.toGeometry_edgeMap] using hmap
      rw [P.toGeometry.targetSubsetEdgeMapOption_eq_none
        (↑A : Set P.CoarseTarget) (P.canonicalFinePreimage A)
        (fun _ htarget => htarget) (P.fineEdgeEquiv A edge) hsemantic]
      rw [P.edgeMapOptionIn_eq_none A edge hmap]
      rfl
  | some coarseEdge =>
      have hsemantic :
          P.toGeometry.edgeMap (P.fineEdgeEquiv A edge).1 =
            some coarseEdge := by
        simpa only [P.toGeometry_edgeMap] using hmap
      rw [P.toGeometry.targetSubsetEdgeMapOption_eq_some
        (↑A : Set P.CoarseTarget) (P.canonicalFinePreimage A)
        (fun _ htarget => htarget) (P.fineEdgeEquiv A edge)
        coarseEdge hsemantic]
      simp only [Option.elim_some]
      cases hraw : P.edgeMapOptionIn A edge with
      | none =>
          have hval := P.edgeMapOptionIn_map_val A edge
          rw [hraw, hmap] at hval
          simp at hval
      | some rawEdge =>
          simp only [Option.elim_some]
          apply congrArg cochain
          apply Subtype.ext
          have hval := P.edgeMapOptionIn_map_val A edge
          rw [hraw, hmap] at hval
          simpa using Option.some.inj hval

/-! ## Rank transport through the canonical reindexings -/

/-- Range dimension is invariant under commuting linear equivalences on the
domain and codomain. -/
private theorem finrank_range_eq_of_equiv_commutes
    {V W V' W' : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    [AddCommGroup V'] [Module ℚ V']
    [AddCommGroup W'] [Module ℚ W']
    (semantic : V →ₗ[ℚ] W) (raw : V' →ₗ[ℚ] W')
    (domainEquiv : V ≃ₗ[ℚ] V') (codomainEquiv : W ≃ₗ[ℚ] W')
    (hcommutes : ∀ input, raw (domainEquiv input) =
      codomainEquiv (semantic input)) :
    Module.finrank ℚ (LinearMap.range raw) =
      Module.finrank ℚ (LinearMap.range semantic) := by
  have hmaps : raw.comp domainEquiv.toLinearMap =
      codomainEquiv.toLinearMap.comp semantic := by
    ext input
    exact hcommutes input
  calc
    Module.finrank ℚ (LinearMap.range raw) =
        Module.finrank ℚ
          (LinearMap.range (raw.comp domainEquiv.toLinearMap)) := by
      rw [LinearMap.range_comp_of_range_eq_top raw domainEquiv.range]
    _ = Module.finrank ℚ
          (LinearMap.range (codomainEquiv.toLinearMap.comp semantic)) := by
      rw [hmaps]
    _ = Module.finrank ℚ
          ((LinearMap.range semantic).map codomainEquiv.toLinearMap) := by
      rw [LinearMap.range_comp]
    _ = Module.finrank ℚ (LinearMap.range semantic) :=
      LinearEquiv.finrank_map_eq codomainEquiv (LinearMap.range semantic)

/-- Cycle 7 rank of a standard coordinate matrix is the range dimension of
the linear map used to generate that matrix. -/
private theorem rationalMatrixRank_toMatrix'_eq_finrank_range
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (linearMap : (n → ℚ) →ₗ[ℚ] (m → ℚ)) :
    rationalMatrixRank (LinearMap.toMatrix' linearMap) =
      Module.finrank ℚ (LinearMap.range linearMap) := by
  classical
  rw [rationalMatrixRank_eq_finrank_range]
  have hlinear :
      (LinearMap.toMatrix' linearMap).mulVecLin = linearMap := by
    apply LinearMap.ext
    intro input
    funext index
    simpa only [Matrix.mulVecLin_apply] using
      congrFun (LinearMap.toMatrix'_mulVec linearMap input) index
  rw [hlinear]

/-- Reindex the product domain of the semantic H¹-rank block onto the raw
sum-indexed coordinate type. -/
def h1RankBlockDomainCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    ((P.coarseSupportedNerve.EdgeInTargetSubset
          (↑A : Set P.CoarseTarget) → ℚ) ×
        (P.fineSupportedNerve.ChartInTargetSubset
          (P.canonicalFinePreimage A) → ℚ)) ≃ₗ[ℚ]
      (P.CoarseEdgeIn A ⊕ P.FineChartIn A → ℚ) :=
  ((P.coarseEdgeCochainEquiv A).prodCongr
      (P.fineChartCochainEquiv A)).trans
    (LinearEquiv.sumArrowLequivProdArrow
      (P.CoarseEdgeIn A) (P.FineChartIn A) ℚ ℚ).symm

/-- Reindex the product codomain of the semantic H¹-rank block onto the raw
sum-indexed coordinate type. -/
def h1RankBlockCodomainCochainEquiv (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    ((P.coarseSupportedNerve.FaceInTargetSubset
          (↑A : Set P.CoarseTarget) → ℚ) ×
        (P.fineSupportedNerve.EdgeInTargetSubset
          (P.canonicalFinePreimage A) → ℚ)) ≃ₗ[ℚ]
      (P.CoarseFaceIn A ⊕ P.FineEdgeIn A → ℚ) :=
  ((P.coarseFaceCochainEquiv A).prodCongr
      (P.fineEdgeCochainEquiv A)).trans
    (LinearEquiv.sumArrowLequivProdArrow
      (P.CoarseFaceIn A) (P.FineEdgeIn A) ℚ ℚ).symm

/-- The raw sum-indexed block map is the actual semantic H¹-rank block after
the canonical product/sum reindexings. -/
theorem h1RankBlock_commutes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget)
    (input :
      (P.coarseSupportedNerve.EdgeInTargetSubset
          (↑A : Set P.CoarseTarget) → ℚ) ×
        (P.fineSupportedNerve.ChartInTargetSubset
          (P.canonicalFinePreimage A) → ℚ)) :
    P.h1RankBlockLinearMap A
        (P.h1RankBlockDomainCochainEquiv A input) =
      P.h1RankBlockCodomainCochainEquiv A
        ((P.toGeometry.aSubnerveComparisonHom
          (↑A : Set P.CoarseTarget)).h1RankBlockLinearMap input) := by
  ext index
  cases index with
  | inl face =>
      change P.coarseD1LinearMap A
          (P.coarseEdgeCochainEquiv A input.1) face =
        P.coarseFaceCochainEquiv A
          (P.coarseSupportedNerve.targetSubsetD1
            (↑A : Set P.CoarseTarget) input.1) face
      exact congrFun (P.coarseD1_commutes A input.1) face
  | inr edge =>
      change P.edgePullback1LinearMap A
            (P.coarseEdgeCochainEquiv A input.1) edge -
          P.fineD0LinearMap A
            (P.fineChartCochainEquiv A input.2) edge =
        P.fineEdgeCochainEquiv A
            ((P.toGeometry.aSubnerveComparisonHom
              (↑A : Set P.CoarseTarget)).f1 input.1) edge -
          P.fineEdgeCochainEquiv A
            (P.fineSupportedNerve.targetSubsetD0
              (P.canonicalFinePreimage A) input.2) edge
      rw [congrFun (P.edgePullback1_commutes A input.1) edge,
        congrFun (P.fineD0_commutes A input.2) edge]

/-- The executable coarse `d0` matrix rank is the rank of the actual semantic
A-subnerve differential. -/
theorem rationalMatrixRank_coarseD0Matrix_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    rationalMatrixRank (P.coarseD0Matrix A) =
      Module.finrank ℚ (LinearMap.range
        (P.coarseSupportedNerve.targetSubsetD0
          (↑A : Set P.CoarseTarget))) := by
  rw [coarseD0Matrix,
    rationalMatrixRank_toMatrix'_eq_finrank_range]
  exact finrank_range_eq_of_equiv_commutes
    (P.coarseSupportedNerve.targetSubsetD0 (↑A : Set P.CoarseTarget))
    (P.coarseD0LinearMap A) (P.coarseChartCochainEquiv A)
    (P.coarseEdgeCochainEquiv A) (P.coarseD0_commutes A)

/-- The executable coarse `d1` matrix rank is the rank of the actual semantic
A-subnerve differential. -/
theorem rationalMatrixRank_coarseD1Matrix_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    rationalMatrixRank (P.coarseD1Matrix A) =
      Module.finrank ℚ (LinearMap.range
        (P.coarseSupportedNerve.targetSubsetD1
          (↑A : Set P.CoarseTarget))) := by
  rw [coarseD1Matrix,
    rationalMatrixRank_toMatrix'_eq_finrank_range]
  exact finrank_range_eq_of_equiv_commutes
    (P.coarseSupportedNerve.targetSubsetD1 (↑A : Set P.CoarseTarget))
    (P.coarseD1LinearMap A) (P.coarseEdgeCochainEquiv A)
    (P.coarseFaceCochainEquiv A) (P.coarseD1_commutes A)

/-- The executable fine `d0` matrix rank is the rank of the actual semantic
preimage-subnerve differential. -/
theorem rationalMatrixRank_fineD0Matrix_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    rationalMatrixRank (P.fineD0Matrix A) =
      Module.finrank ℚ (LinearMap.range
        (P.fineSupportedNerve.targetSubsetD0
          (P.canonicalFinePreimage A))) := by
  rw [fineD0Matrix,
    rationalMatrixRank_toMatrix'_eq_finrank_range]
  exact finrank_range_eq_of_equiv_commutes
    (P.fineSupportedNerve.targetSubsetD0 (P.canonicalFinePreimage A))
    (P.fineD0LinearMap A) (P.fineChartCochainEquiv A)
    (P.fineEdgeCochainEquiv A) (P.fineD0_commutes A)

/-- The executable fine `d1` matrix rank is the rank of the actual semantic
preimage-subnerve differential. -/
theorem rationalMatrixRank_fineD1Matrix_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    rationalMatrixRank (P.fineD1Matrix A) =
      Module.finrank ℚ (LinearMap.range
        (P.fineSupportedNerve.targetSubsetD1
          (P.canonicalFinePreimage A))) := by
  rw [fineD1Matrix,
    rationalMatrixRank_toMatrix'_eq_finrank_range]
  exact finrank_range_eq_of_equiv_commutes
    (P.fineSupportedNerve.targetSubsetD1 (P.canonicalFinePreimage A))
    (P.fineD1LinearMap A) (P.fineEdgeCochainEquiv A)
    (P.fineFaceCochainEquiv A) (P.fineD1_commutes A)

/-- The executable raw edge-pullback matrix rank is the rank of the actual
canonical comparison `f1`. -/
theorem rationalMatrixRank_edgePullback1Matrix_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    rationalMatrixRank (P.edgePullback1Matrix A) =
      Module.finrank ℚ (LinearMap.range
        (P.toGeometry.aSubnerveComparisonHom
          (↑A : Set P.CoarseTarget)).f1) := by
  rw [edgePullback1Matrix,
    rationalMatrixRank_toMatrix'_eq_finrank_range]
  exact finrank_range_eq_of_equiv_commutes
    (P.toGeometry.aSubnerveComparisonHom
      (↑A : Set P.CoarseTarget)).f1
    (P.edgePullback1LinearMap A) (P.coarseEdgeCochainEquiv A)
    (P.fineEdgeCochainEquiv A) (P.edgePullback1_commutes A)

/-- The executable raw H¹ block-matrix rank is the range dimension of the
actual semantic block map. -/
theorem rationalMatrixRank_h1RankBlockMatrix_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    rationalMatrixRank (P.h1RankBlockMatrix A) =
      Module.finrank ℚ (LinearMap.range
        (P.toGeometry.aSubnerveComparisonHom
          (↑A : Set P.CoarseTarget)).h1RankBlockLinearMap) := by
  rw [h1RankBlockMatrix,
    rationalMatrixRank_toMatrix'_eq_finrank_range]
  exact finrank_range_eq_of_equiv_commutes
    (P.toGeometry.aSubnerveComparisonHom
      (↑A : Set P.CoarseTarget)).h1RankBlockLinearMap
    (P.h1RankBlockLinearMap A) (P.h1RankBlockDomainCochainEquiv A)
    (P.h1RankBlockCodomainCochainEquiv A) (P.h1RankBlock_commutes A)

/-- The computed block-corrected rank is exactly the range dimension of the
literal quotient-`H¹` map. -/
theorem computedASubnerveH1Rank_eq_finrank_range_h1Map
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    P.computedASubnerveH1Rank A =
      Module.finrank ℚ (LinearMap.range
        (P.toGeometry.aSubnerveComparisonHom
          (↑A : Set P.CoarseTarget)).h1Map) := by
  rw [computedASubnerveH1Rank,
    P.rationalMatrixRank_h1RankBlockMatrix_eq A,
    P.rationalMatrixRank_coarseD1Matrix_eq A,
    P.rationalMatrixRank_fineD0Matrix_eq A]
  exact (P.toGeometry.aSubnerveComparisonHom
    (↑A : Set P.CoarseTarget)).finrank_range_h1Map_eq_h1RankBlock.symm

/-- Main Cycle 8 correctness theorem: for every finite coarse target subset,
including the empty subset, the defect computed from raw presentation tables
is the literal kernel/cokernel defect of the actual canonical A-subnerve H¹
comparison. -/
theorem computedASubnerveDefect_eq_aSubnerveDefect
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    P.computedASubnerveDefect A =
      P.toGeometry.aSubnerveDefect (↑A : Set P.CoarseTarget) := by
  classical
  let comparison := P.toGeometry.aSubnerveComparisonHom
    (↑A : Set P.CoarseTarget)
  have hcoarseC1 :
      Module.finrank ℚ
          (P.coarseSupportedNerve.targetSubsetComplex
            (↑A : Set P.CoarseTarget)).C1 =
        Fintype.card (P.CoarseEdgeIn A) := by
    change Module.finrank ℚ
        (P.coarseSupportedNerve.EdgeInTargetSubset
          (↑A : Set P.CoarseTarget) → ℚ) =
      Fintype.card (P.CoarseEdgeIn A)
    calc
      Module.finrank ℚ
          (P.coarseSupportedNerve.EdgeInTargetSubset
            (↑A : Set P.CoarseTarget) → ℚ) =
          Fintype.card
            (P.coarseSupportedNerve.EdgeInTargetSubset
              (↑A : Set P.CoarseTarget)) := by simp
      _ = Fintype.card (P.CoarseEdgeIn A) :=
        (Fintype.card_congr (P.coarseEdgeEquiv A)).symm
  have hfineC1 :
      Module.finrank ℚ
          (P.fineSupportedNerve.targetSubsetComplex
            (P.canonicalFinePreimage A)).C1 =
        Fintype.card (P.FineEdgeIn A) := by
    change Module.finrank ℚ
        (P.fineSupportedNerve.EdgeInTargetSubset
          (P.canonicalFinePreimage A) → ℚ) =
      Fintype.card (P.FineEdgeIn A)
    calc
      Module.finrank ℚ
          (P.fineSupportedNerve.EdgeInTargetSubset
            (P.canonicalFinePreimage A) → ℚ) =
          Fintype.card
            (P.fineSupportedNerve.EdgeInTargetSubset
              (P.canonicalFinePreimage A)) := by simp
      _ = Fintype.card (P.FineEdgeIn A) :=
        (Fintype.card_congr (P.fineEdgeEquiv A)).symm
  have hcoarseH1 :=
    ThreeCochainComplex.finrank_h1_eq_c1_sub_d1_sub_d0
      (P.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set P.CoarseTarget))
  have hfineH1 :=
    ThreeCochainComplex.finrank_h1_eq_c1_sub_d1_sub_d0
      (P.fineSupportedNerve.targetSubsetComplex
        (P.canonicalFinePreimage A))
  rw [hcoarseC1] at hcoarseH1
  rw [hfineC1] at hfineH1
  change Module.finrank ℚ
      (P.coarseSupportedNerve.targetSubsetComplex
        (↑A : Set P.CoarseTarget)).H1 =
      Fintype.card (P.CoarseEdgeIn A) -
        Module.finrank ℚ (LinearMap.range
          (P.coarseSupportedNerve.targetSubsetD1
            (↑A : Set P.CoarseTarget))) -
          Module.finrank ℚ (LinearMap.range
            (P.coarseSupportedNerve.targetSubsetD0
              (↑A : Set P.CoarseTarget))) at hcoarseH1
  change Module.finrank ℚ
      (P.fineSupportedNerve.targetSubsetComplex
        (P.canonicalFinePreimage A)).H1 =
      Fintype.card (P.FineEdgeIn A) -
        Module.finrank ℚ (LinearMap.range
          (P.fineSupportedNerve.targetSubsetD1
            (P.canonicalFinePreimage A))) -
          Module.finrank ℚ (LinearMap.range
            (P.fineSupportedNerve.targetSubsetD0
              (P.canonicalFinePreimage A))) at hfineH1
  rw [computedASubnerveDefect,
    P.rationalMatrixRank_coarseD1Matrix_eq A,
    P.rationalMatrixRank_coarseD0Matrix_eq A,
    P.rationalMatrixRank_fineD1Matrix_eq A,
    P.rationalMatrixRank_fineD0Matrix_eq A,
    P.computedASubnerveH1Rank_eq_finrank_range_h1Map A]
  change _ = blockDefect comparison.h1Map
  rw [blockDefect_eq_finrank_sub_range comparison.h1Map]
  apply Prod.ext
  · dsimp only
    rw [hcoarseH1]
  · dsimp only
    rw [hfineH1]

end FiniteComparisonPresentation

/-! ## Boundary-sensitive regression fixture -/

namespace BoundaryShortcutCounterexample

/-- Source fixture with zero differentials and one-dimensional `H¹`. -/
def sourceComplex : ThreeCochainComplex ℚ where
  C0 := ℚ
  C1 := ℚ
  C2 := ℚ
  d0 := 0
  d1 := 0
  d1_comp_d0 := by simp

/-- Target fixture whose identity `d0` makes `H¹` vanish. -/
def targetComplex : ThreeCochainComplex ℚ where
  C0 := ℚ
  C1 := ℚ
  C2 := ℚ
  d0 := LinearMap.id
  d1 := 0
  d1_comp_d0 := by simp

/-- The comparison has identity degree-one map even though the target class
of every cocycle is a boundary. -/
def comparison : ThreeCochainComplex.Hom sourceComplex targetComplex where
  f0 := 0
  f1 := LinearMap.id
  f2 := 0
  comm0 := by
    intro cochain
    change (0 : ℚ) = 0
    rfl
  comm1 := by
    intro cochain
    change (0 : ℚ) = 0
    rfl

/-- The source fixture has one-dimensional literal quotient-`H¹`. -/
theorem source_h1_finrank : Module.finrank ℚ sourceComplex.H1 = 1 := by
  rw [ThreeCochainComplex.finrank_h1_eq_c1_sub_d1_sub_d0]
  simp only [sourceComplex]
  rw [LinearMap.range_zero]
  simp

/-- The target fixture has zero-dimensional literal quotient-`H¹` because
the identity `d0` makes every degree-one cocycle a boundary. -/
theorem target_h1_finrank : Module.finrank ℚ targetComplex.H1 = 0 := by
  rw [ThreeCochainComplex.finrank_h1_eq_c1_sub_d1_sub_d0]
  simp only [targetComplex]
  rw [LinearMap.range_zero, LinearMap.range_id]
  simp

/-- The underlying degree-one identity has rank one. -/
theorem f1_range_finrank :
    Module.finrank ℚ (LinearMap.range comparison.f1) = 1 := by
  change Module.finrank ℚ
      (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) = 1
  rw [LinearMap.range_id]
  simp

/-- The induced quotient-`H¹` map has rank zero. -/
theorem h1Map_range_finrank :
    Module.finrank ℚ (LinearMap.range comparison.h1Map) = 0 := by
  have hle := (LinearMap.range comparison.h1Map).finrank_le
  rw [target_h1_finrank] at hle
  omega

/-- Regression guard: the rank of `f1` cannot replace the rank of the induced
quotient-`H¹` map in the executable defect. -/
theorem f1_rank_ne_h1Map_rank :
    Module.finrank ℚ (LinearMap.range comparison.f1) ≠
      Module.finrank ℚ (LinearMap.range comparison.h1Map) := by
  rw [f1_range_finrank, h1Map_range_finrank]
  decide

end BoundaryShortcutCounterexample

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
