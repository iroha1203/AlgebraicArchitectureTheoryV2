import ResearchLean.AG.ResolutionInvariance.LawValueBlockDecomposition
import Mathlib.LinearAlgebra.Quotient.Pi
import Formal.Util.AssertStandardAxioms

/-!
# Cohomology of the finite law-value block decomposition

This module lifts the coordinate-level decomposition from Cycle 10 of
`G-104-aat-resolution-invariance` to the actual quotient definition of `H^1`
reviewed in G-102.  The componentwise block differentials form an aggregate
finite direct-sum complex.  Its cycle space is canonically the product of the
block cycle spaces, and its boundary subspace is exactly the product of the
block boundary subspaces.

Consequently, the `H^1` of the original law-generated complex is canonically
linearly equivalent to the finite direct sum of the `H^1` spaces of the exact
source-generated `(law, value)` blocks.  The construction uses no basis,
complement, dimension count, or supplied quotient equivalence.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution DirectSum TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerve

variable {q : Reading Source}

/-! ## The aggregate finite direct-sum complex -/

/-- Component formula for the aggregate degree-zero block differential. -/
@[simp]
theorem lawValueBlockDirectSumD0_component [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (cochain : ⨁ label : LawValueLabel laws,
      D.ChartBlockCoordinate laws hadequate label → ℚ)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
      (D.lawValueBlockDirectSumD0 laws hadequate cochain)) label =
      D.lawValueBlockD0 laws hadequate label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => D.ChartBlockCoordinate laws hadequate current → ℚ)
          cochain) label) := by
  rfl

/-- Component formula for the aggregate degree-one block differential. -/
@[simp]
theorem lawValueBlockDirectSumD1_component [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (cochain : ⨁ label : LawValueLabel laws,
      D.EdgeBlockCoordinate laws hadequate label → ℚ)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.FaceBlockCoordinate laws hadequate current → ℚ)
      (D.lawValueBlockDirectSumD1 laws hadequate cochain)) label =
      D.lawValueBlockD1 laws hadequate label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
          cochain) label) := by
  rfl

/-- The aggregate block differentials compose to zero componentwise. -/
theorem lawValueBlockDirectSum_d1_comp_d0 [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (cochain : ⨁ label : LawValueLabel laws,
      D.ChartBlockCoordinate laws hadequate label → ℚ) :
    D.lawValueBlockDirectSumD1 laws hadequate
        (D.lawValueBlockDirectSumD0 laws hadequate cochain) = 0 := by
  apply (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
    (fun label => D.FaceBlockCoordinate laws hadequate label → ℚ)).injective
  funext label
  rw [D.lawValueBlockDirectSumD1_component,
    D.lawValueBlockDirectSumD0_component]
  exact D.lawValueBlock_d1_comp_d0 laws hadequate label _

/--
The finite direct sum of the exact law-value block complexes, with the
componentwise differentials generated in Cycle 10.
-/
def lawValueBlockDirectSumComplex [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) : ThreeCochainComplex ℚ where
  C0 := ⨁ label : LawValueLabel laws,
    D.ChartBlockCoordinate laws hadequate label → ℚ
  C1 := ⨁ label : LawValueLabel laws,
    D.EdgeBlockCoordinate laws hadequate label → ℚ
  C2 := ⨁ label : LawValueLabel laws,
    D.FaceBlockCoordinate laws hadequate label → ℚ
  d0 := D.lawValueBlockDirectSumD0 laws hadequate
  d1 := D.lawValueBlockDirectSumD1 laws hadequate
  d1_comp_d0 := D.lawValueBlockDirectSum_d1_comp_d0 laws hadequate

/-! ## Cycles and boundaries under the aggregate decomposition -/

/--
The global cycle space is canonically equivalent to the cycle space of the
aggregate block complex.  The proof uses the degree-one differential
intertwining theorem, rather than a dimension argument.
-/
def lawGeneratedAggregateCyclesEquiv [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    LinearMap.ker (D.lawGeneratedComplex laws hadequate).d1 ≃ₗ[ℚ]
      LinearMap.ker (D.lawValueBlockDirectSumComplex laws hadequate).d1 where
  toFun cycle := by
    refine ⟨D.edgeCochainBlockEquiv laws hadequate cycle.1, ?_⟩
    change D.lawValueBlockDirectSumD1 laws hadequate
        (D.edgeCochainBlockEquiv laws hadequate cycle.1) = 0
    have hcycle := cycle.2
    change D.lawGeneratedD1 laws hadequate cycle.1 = 0 at hcycle
    rw [D.lawGeneratedD1_block_intertwining, hcycle, map_zero]
  invFun cycle := by
    refine ⟨(D.edgeCochainBlockEquiv laws hadequate).symm cycle.1, ?_⟩
    change D.lawGeneratedD1 laws hadequate
        ((D.edgeCochainBlockEquiv laws hadequate).symm cycle.1) = 0
    apply (D.faceCochainBlockEquiv laws hadequate).injective
    have hcycle := cycle.2
    change D.lawValueBlockDirectSumD1 laws hadequate cycle.1 = 0 at hcycle
    rw [← D.lawGeneratedD1_block_intertwining,
      (D.edgeCochainBlockEquiv laws hadequate).apply_symm_apply,
      hcycle, map_zero]
  left_inv cycle := by
    apply Subtype.ext
    exact (D.edgeCochainBlockEquiv laws hadequate).symm_apply_apply cycle.1
  right_inv cycle := by
    apply Subtype.ext
    exact (D.edgeCochainBlockEquiv laws hadequate).apply_symm_apply cycle.1
  map_add' left right := by
    apply Subtype.ext
    simp
  map_smul' scalar cycle := by
    apply Subtype.ext
    simp

/-- The global boundary subspace maps exactly onto the aggregate one. -/
theorem lawGeneratedBoundaryRange_map_aggregate [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    (LinearMap.range (D.lawGeneratedComplex laws hadequate).boundaryToCycles).map
        (D.lawGeneratedAggregateCyclesEquiv laws hadequate).toLinearMap =
      LinearMap.range
        (D.lawValueBlockDirectSumComplex laws hadequate).boundaryToCycles := by
  apply le_antisymm
  · rintro _ ⟨cycle, ⟨cochain, hcochain⟩, rfl⟩
    subst cycle
    refine ⟨D.chartCochainBlockEquiv laws hadequate cochain, ?_⟩
    apply Subtype.ext
    exact D.lawGeneratedD0_block_intertwining laws hadequate cochain
  · rintro _ ⟨cochain, rfl⟩
    let globalCochain :=
      (D.chartCochainBlockEquiv laws hadequate).symm cochain
    refine ⟨(D.lawGeneratedComplex laws hadequate).boundaryToCycles
        globalCochain, ⟨globalCochain, rfl⟩, ?_⟩
    apply Subtype.ext
    change D.edgeCochainBlockEquiv laws hadequate
        (D.lawGeneratedD0 laws hadequate globalCochain) =
      D.lawValueBlockDirectSumD0 laws hadequate cochain
    rw [← D.lawGeneratedD0_block_intertwining]
    exact congrArg (D.lawValueBlockDirectSumD0 laws hadequate)
      ((D.chartCochainBlockEquiv laws hadequate).apply_symm_apply cochain)

/--
Cycles of the aggregate finite direct-sum complex are canonically the product
of the cycle spaces of the individual block complexes.
-/
def lawValueBlockCyclesEquiv [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    LinearMap.ker (D.lawValueBlockDirectSumComplex laws hadequate).d1 ≃ₗ[ℚ]
      ((label : LawValueLabel laws) →
        LinearMap.ker (D.lawValueBlockComplex laws hadequate label).d1) where
  toFun cycle label := by
    refine ⟨(DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
      cycle.1) label, ?_⟩
    have hcycle := cycle.2
    change D.lawValueBlockDirectSumD1 laws hadequate cycle.1 = 0 at hcycle
    change D.lawValueBlockD1 laws hadequate label
      ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
        cycle.1) label) = 0
    rw [← D.lawValueBlockDirectSumD1_component]
    rw [hcycle]
    rfl
  invFun cycles := by
    let cochain :=
      (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun label => D.EdgeBlockCoordinate laws hadequate label → ℚ)).symm
        (fun label => (cycles label).1)
    refine ⟨cochain, ?_⟩
    change D.lawValueBlockDirectSumD1 laws hadequate cochain = 0
    apply (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label => D.FaceBlockCoordinate laws hadequate label → ℚ)).injective
    funext label
    rw [D.lawValueBlockDirectSumD1_component]
    change D.lawValueBlockD1 laws hadequate label
      ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
        cochain) label) = 0
    rw [show (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
        cochain) = (fun current => (cycles current).1) by
      exact (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current =>
          D.EdgeBlockCoordinate laws hadequate current → ℚ)).apply_symm_apply _]
    exact (cycles label).2
  left_inv cycle := by
    apply Subtype.ext
    exact (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label => D.EdgeBlockCoordinate laws hadequate label → ℚ)).symm_apply_apply
        cycle.1
  right_inv cycles := by
    funext label
    apply Subtype.ext
    change (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
      ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current =>
          D.EdgeBlockCoordinate laws hadequate current → ℚ)).symm
        (fun current => (cycles current).1))) label = (cycles label).1
    rw [(DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current =>
        D.EdgeBlockCoordinate laws hadequate current → ℚ)).apply_symm_apply]
  map_add' left right := by
    funext label
    apply Subtype.ext
    change
      (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
        (left.1 + right.1)) label =
      (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
        left.1) label +
      (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
        right.1) label
    rw [map_add]
    rfl
  map_smul' scalar cycle := by
    funext label
    apply Subtype.ext
    change
      (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
        (scalar • cycle.1)) label =
      scalar •
        (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => D.EdgeBlockCoordinate laws hadequate current → ℚ)
          cycle.1) label
    rw [map_smul]
    rfl

/-- The aggregate boundary subspace is exactly the product of block boundaries. -/
theorem lawValueBlockBoundaryRange_map_cyclesEquiv [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    (LinearMap.range
        (D.lawValueBlockDirectSumComplex laws hadequate).boundaryToCycles).map
        (D.lawValueBlockCyclesEquiv laws hadequate).toLinearMap =
      Submodule.pi Set.univ (fun label : LawValueLabel laws =>
        LinearMap.range
          (D.lawValueBlockComplex laws hadequate label).boundaryToCycles) := by
  apply le_antisymm
  · rintro _ ⟨cycle, ⟨cochain, hcochain⟩, rfl⟩
    subst cycle
    rw [Submodule.mem_pi]
    intro label _hlabel
    refine ⟨(DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun current => D.ChartBlockCoordinate laws hadequate current → ℚ)
      cochain) label, ?_⟩
    apply Subtype.ext
    rfl
  · intro cycles hcycles
    choose cochain hcochain using fun label =>
      (Submodule.mem_pi.mp hcycles) label (Set.mem_univ label)
    let aggregateCochain :=
      (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun label => D.ChartBlockCoordinate laws hadequate label → ℚ)).symm
        cochain
    refine ⟨(D.lawValueBlockDirectSumComplex laws hadequate).boundaryToCycles
      aggregateCochain, ⟨aggregateCochain, rfl⟩, ?_⟩
    funext label
    apply Subtype.ext
    change D.lawValueBlockD0 laws hadequate label
        ((DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
          (fun current => D.ChartBlockCoordinate laws hadequate current → ℚ)
          aggregateCochain) label) = (cycles label).1
    rw [show (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current => D.ChartBlockCoordinate laws hadequate current → ℚ)
        aggregateCochain) = cochain by
      exact (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current =>
          D.ChartBlockCoordinate laws hadequate current → ℚ)).apply_symm_apply _]
    exact congrArg Subtype.val (hcochain label)

/-! ## The quotient-level finite direct-sum theorem -/

/-- Global cycles are canonically the product of the exact block cycles. -/
def lawGeneratedBlockCyclesEquiv [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    LinearMap.ker (D.lawGeneratedComplex laws hadequate).d1 ≃ₗ[ℚ]
      ((label : LawValueLabel laws) →
        LinearMap.ker (D.lawValueBlockComplex laws hadequate label).d1) :=
  (D.lawGeneratedAggregateCyclesEquiv laws hadequate).trans
    (D.lawValueBlockCyclesEquiv laws hadequate)

/-- The global boundary subspace maps exactly to the product of block boundaries. -/
theorem lawGeneratedBoundaryRange_map_blocks [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    (LinearMap.range (D.lawGeneratedComplex laws hadequate).boundaryToCycles).map
        (D.lawGeneratedBlockCyclesEquiv laws hadequate).toLinearMap =
      Submodule.pi Set.univ (fun label : LawValueLabel laws =>
        LinearMap.range
          (D.lawValueBlockComplex laws hadequate label).boundaryToCycles) := by
  change
    (LinearMap.range (D.lawGeneratedComplex laws hadequate).boundaryToCycles).map
        ((D.lawValueBlockCyclesEquiv laws hadequate).toLinearMap.comp
          (D.lawGeneratedAggregateCyclesEquiv laws hadequate).toLinearMap) = _
  rw [Submodule.map_comp, D.lawGeneratedBoundaryRange_map_aggregate,
    D.lawValueBlockBoundaryRange_map_cyclesEquiv]

/--
The actual G-102 `H^1` quotient of the law-generated complex is canonically the
finite direct sum of the actual G-102 `H^1` quotients of its law-value blocks.
-/
def lawGeneratedH1BlockEquiv [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q) :
    (D.lawGeneratedComplex laws hadequate).H1 ≃ₗ[ℚ]
      ⨁ label : LawValueLabel laws,
        (D.lawValueBlockComplex laws hadequate label).H1 := by
  classical
  exact Submodule.Quotient.equiv
      (LinearMap.range
        (D.lawGeneratedComplex laws hadequate).boundaryToCycles)
      (Submodule.pi Set.univ (fun label : LawValueLabel laws =>
        LinearMap.range
          (D.lawValueBlockComplex laws hadequate label).boundaryToCycles))
      (D.lawGeneratedBlockCyclesEquiv laws hadequate)
      (D.lawGeneratedBoundaryRange_map_blocks laws hadequate) ≪≫ₗ
    Submodule.quotientPi (R := ℚ) (fun label : LawValueLabel laws =>
      LinearMap.range
        (D.lawValueBlockComplex laws hadequate label).boundaryToCycles) ≪≫ₗ
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun label =>
        (D.lawValueBlockComplex laws hadequate label).H1)).symm

/--
On a quotient representative, the component at one label is represented by
the corresponding canonically transported block cycle.
-/
@[simp]
theorem lawGeneratedH1BlockEquiv_mk_component [Fintype Source]
    (D : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (hadequate : laws.Adequate q)
    (cycle : LinearMap.ker (D.lawGeneratedComplex laws hadequate).d1)
    (label : LawValueLabel laws) :
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
        (fun current =>
          (D.lawValueBlockComplex laws hadequate current).H1)
      (D.lawGeneratedH1BlockEquiv laws hadequate
        ((LinearMap.range
          (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ cycle))) label =
      (LinearMap.range
        (D.lawValueBlockComplex laws hadequate label).boundaryToCycles).mkQ
        ((D.lawGeneratedBlockCyclesEquiv laws hadequate cycle) label) := by
  classical
  rfl

end TargetSupportedNerve

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
