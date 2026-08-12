import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# Executed positive and negative uniform-presentation instances

This module fires the Cycle 9 checker on two nonvacuous raw finite comparison
presentations.  Both presentations have one target, one chart, one coarse
self-loop edge, and no faces.  The positive presentation has one fine
self-loop, while the negative presentation has two parallel fine self-loops,
both mapping to the unique coarse edge.

The same generic checker reads both raw tables.  Neither fixture stores a
matrix, rank, defect, uniformity proof, or expected Boolean result.  The rank
one firing theorems below certify that the comparison map is not being tested
only on zero cohomology.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology
open ExecutableRationalLinearAlgebra

namespace UniformPresentationInstancePairs

/-- Executable enumeration carried by the generic self-loop fixture helpers.

Position: private §1.4 certificate structure for the positive/negative checker
fixtures.  It supplies only a complete finite edge list; it carries no matrix,
rank, defect, or expected checker result. -/
private class SelfLoopEntries (α : Type) where
  entries : List α
  complete : ∀ value, value ∈ entries

/-- The singleton self-loop fixture uses its unique unit entry.

Position: positive §1.4 instance for `SelfLoopEntries`; the complete list is
computed from `PUnit`, not from the positive checker's expected result. -/
private instance : SelfLoopEntries PUnit where
  entries := [PUnit.unit]
  complete := by intro value; cases value; simp

/-- The two-edge self-loop fixture explicitly enumerates both Boolean edges.

Position: second finite §1.4 instance used by the negative raw fixture; the list
comes from `Bool` and supplies no rank, defect, or checker certificate. -/
private instance : SelfLoopEntries Bool where
  entries := [false, true]
  complete := by intro value; cases value <;> simp

/-- Publicly audited negative §1.4 theorem for the private fixture-enumeration
certificate: no finite list can cover `Nat`.  Infinitude, rather than any checker
result or presentation-specific conclusion, supplies the obstruction. -/
theorem not_nonempty_selfLoopEntries_nat :
    ¬ Nonempty (SelfLoopEntries Nat) := by
  rintro ⟨certificate⟩
  obtain ⟨value, hvalue⟩ :=
    Infinite.exists_notMem_finset certificate.entries.toFinset
  exact hvalue (by simpa using certificate.complete value)

/-- Raw singleton-target comparison data with a caller-specified finite type
of parallel fine self-loop edges.

Position: private raw-presentation constructor supporting the positive and
negative uniformity checker instances.  `SelfLoopEntries` supplies only complete
cell coverage; all maps and ranks are computed from the self-loop tables. -/
private def selfLoopPresentation (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    FiniteComparisonPresentation where
  Source := PUnit
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := PUnit.unit
  sourceEntries := [PUnit.unit]
  source_mem_sourceEntries := by
    intro source
    cases source
    simp
  CoarseTarget := PUnit
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [PUnit.unit]
  coarseTarget_mem_coarseTargetEntries := by
    intro target
    cases target
    simp
  FineTarget := PUnit
  fineTargetFintype := inferInstance
  fineTargetDecidableEq := inferInstance
  coarseRead := fun _ => PUnit.unit
  fineRead := fun _ => PUnit.unit
  coarseRead_surjective := by
    intro target
    cases target
    exact ⟨PUnit.unit, rfl⟩
  fineRead_surjective := by
    intro target
    cases target
    exact ⟨PUnit.unit, rfl⟩
  rawCoarserThan := by
    intro left right hequal
    rfl
  CoarseChart := PUnit
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  coarseChartEntries := [PUnit.unit]
  coarseChart_mem_coarseChartEntries := by intro chart; cases chart; simp
  CoarseEdge := PUnit
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  coarseEdgeEntries := [PUnit.unit]
  coarseEdge_mem_coarseEdgeEntries := by intro edge; cases edge; simp
  CoarseFace := PEmpty
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseFaceEntries := []
  coarseFace_mem_coarseFaceEntries := by intro face; exact nomatch face
  coarseEdgeLeft := fun _ => PUnit.unit
  coarseEdgeRight := fun _ => PUnit.unit
  coarseFaceEdge0 := fun face => nomatch face
  coarseFaceEdge1 := fun face => nomatch face
  coarseFaceEdge2 := fun face => nomatch face
  coarseFaceEdge0_left := by
    intro face
    exact nomatch face
  coarseFaceEdge0_right := by
    intro face
    exact nomatch face
  coarseFaceEdge1_right := by
    intro face
    exact nomatch face
  coarseChartSupport := fun _ => Finset.univ
  coarseChartSupport_nonempty := by
    intro chart
    exact ⟨PUnit.unit, Finset.mem_univ _⟩
  FineChart := PUnit
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  fineChartEntries := [PUnit.unit]
  fineChart_mem_fineChartEntries := by intro chart; cases chart; simp
  FineEdge := FineEdge
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  fineEdgeEntries := SelfLoopEntries.entries
  fineEdge_mem_fineEdgeEntries := SelfLoopEntries.complete
  FineFace := PEmpty
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineFaceEntries := []
  fineFace_mem_fineFaceEntries := by intro face; exact nomatch face
  fineEdgeLeft := fun _ => PUnit.unit
  fineEdgeRight := fun _ => PUnit.unit
  fineFaceEdge0 := fun face => nomatch face
  fineFaceEdge1 := fun face => nomatch face
  fineFaceEdge2 := fun face => nomatch face
  fineFaceEdge0_left := by
    intro face
    exact nomatch face
  fineFaceEdge0_right := by
    intro face
    exact nomatch face
  fineFaceEdge1_right := by
    intro face
    exact nomatch face
  fineChartSupport := fun _ => Finset.univ
  fineChartSupport_nonempty := by
    intro chart
    exact ⟨PUnit.unit, Finset.mem_univ _⟩
  chartMap := fun _ => PUnit.unit
  edgeMap := fun _ => some PUnit.unit
  faceMap := fun face => nomatch face
  edge_some_left := by
    intro fineEdge coarseEdge hequal
    cases coarseEdge
    rfl
  edge_some_right := by
    intro fineEdge coarseEdge hequal
    cases coarseEdge
    rfl
  edge_none_fiber := by
    intro fineEdge hequal
    simp at hequal
  face_some_edge0 := by
    intro fineFace
    exact nomatch fineFace
  face_some_edge1 := by
    intro fineFace
    exact nomatch fineFace
  face_some_edge2 := by
    intro fineFace
    exact nomatch fineFace
  face_none_edge0 := by
    intro fineFace
    exact nomatch fineFace
  face_none_edge1 := by
    intro fineFace
    exact nomatch fineFace
  face_none_edge2 := by
    intro fineFace
    exact nomatch fineFace
  chartSupport_compatible_source := by
    intro fineChart source hsource
    exact Finset.mem_univ _

/-- Positive raw presentation: one coarse and one fine self-loop edge. -/
def positivePresentation : FiniteComparisonPresentation :=
  selfLoopPresentation PUnit

/-- Negative raw presentation: one coarse self-loop and two parallel fine
self-loop edges, both mapped to the coarse edge. -/
def negativePresentation : FiniteComparisonPresentation :=
  selfLoopPresentation Bool

/-- The unique selected coarse edge in the full target subset of either raw
fixture.  This private instance helper is derived through the public
raw-selection API and supplies a basis coordinate for rank computation; it
does not store a rank or checker result.

Position: private selected-cell API for the self-loop matrix proofs.  Its
material premise is complete raw edge coverage, not a supplied basis or matrix. -/
private def fullCoarseEdge (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).CoarseEdgeIn Finset.univ :=
  ⟨PUnit.unit, by
    apply ((selfLoopPresentation FineEdge).mem_coarseEdgesIn_iff_raw
      Finset.univ PUnit.unit).2
    refine ⟨PUnit.unit, ?_, Finset.mem_univ _⟩
    rw [(selfLoopPresentation FineEdge).mem_coarseEdgeSupportFinset_iff_raw]
    simp [selfLoopPresentation]⟩

/-- A selected fine edge in the full target subset of a self-loop fixture.
This private instance helper is derived through the public raw-selection API
and supplies a basis coordinate, not a comparison certificate.

Position: private selected-cell API for the self-loop matrix proofs.  Its edge
argument and complete raw coverage determine the coordinate without a result bit. -/
private def fullFineEdge (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge]
    (edge : FineEdge) :
    (selfLoopPresentation FineEdge).FineEdgeIn Finset.univ :=
  ⟨edge, by
    apply ((selfLoopPresentation FineEdge).mem_fineEdgesIn_iff_raw
      Finset.univ edge).2
    refine ⟨PUnit.unit, ?_, Finset.mem_univ _⟩
    rw [(selfLoopPresentation FineEdge).mem_fineEdgeSupportFinset_iff_raw]
    simp [selfLoopPresentation]⟩

/-- Forgetting the selection proof identifies the full selected coarse-edge
type with the singleton coarse-edge table.

Position: private equivalence API supporting the fixture rank proofs.  It is
derived from the full raw selection and accepts no supplied basis equivalence. -/
private def fullCoarseEdgeEquiv (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).CoarseEdgeIn Finset.univ ≃ PUnit where
  toFun edge := edge.1
  invFun _ := fullCoarseEdge FineEdge
  left_inv edge := Subtype.ext (by rfl)
  right_inv target := by cases target; rfl

/-- Forgetting the selection proof identifies the full selected fine-edge
type with the raw fine-edge table.

Position: private equivalence API supporting the fixture rank proofs.  It is
derived from raw edge coverage and accepts no supplied basis equivalence. -/
private def fullFineEdgeEquiv (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).FineEdgeIn Finset.univ ≃ FineEdge where
  toFun edge := edge.1
  invFun := fullFineEdge FineEdge
  left_inv edge := Subtype.ext (by rfl)
  right_inv edge := rfl

/-- The positive block matrix has a unit entry in its comparison block.  This
private instance API computes the entry through the generic block-map
evaluation lemmas from the raw partial edge table; the unit value is not
stored in `positivePresentation`. -/
private theorem positive_h1RankBlockMatrix_entry :
    positivePresentation.h1RankBlockMatrix Finset.univ
      (Sum.inr (fullFineEdge PUnit PUnit.unit))
      (Sum.inl (fullCoarseEdge PUnit)) = 1 := by
  have hmap :
      positivePresentation.edgeMapOptionIn Finset.univ
          (fullFineEdge PUnit PUnit.unit) =
        some (fullCoarseEdge PUnit) :=
    (positivePresentation.edgeMapOptionIn_eq_some_iff Finset.univ
      (fullFineEdge PUnit PUnit.unit) (fullCoarseEdge PUnit)).2 rfl
  rw [positivePresentation.h1RankBlockMatrix_apply,
    positivePresentation.h1RankBlockLinearMap_apply_inr,
    positivePresentation.edgePullback1LinearMap_apply,
    positivePresentation.fineD0LinearMap_apply, hmap]
  simp [
    positivePresentation, selfLoopPresentation, fullFineEdge, fullCoarseEdge]

/-- The negative block matrix has a unit entry in its comparison block.  This
private instance API computes the entry through the generic block-map
evaluation lemmas from the raw partial edge table; the unit value is not
stored in `negativePresentation`. -/
private theorem negative_h1RankBlockMatrix_entry :
    negativePresentation.h1RankBlockMatrix Finset.univ
      (Sum.inr (fullFineEdge Bool false))
      (Sum.inl (fullCoarseEdge Bool)) = 1 := by
  have hmap :
      negativePresentation.edgeMapOptionIn Finset.univ
          (fullFineEdge Bool false) =
        some (fullCoarseEdge Bool) :=
    (negativePresentation.edgeMapOptionIn_eq_some_iff Finset.univ
      (fullFineEdge Bool false) (fullCoarseEdge Bool)).2 rfl
  rw [negativePresentation.h1RankBlockMatrix_apply,
    negativePresentation.h1RankBlockLinearMap_apply_inr,
    negativePresentation.edgePullback1LinearMap_apply,
    negativePresentation.fineD0LinearMap_apply, hmap]
  simp [
    negativePresentation, selfLoopPresentation, fullFineEdge, fullCoarseEdge]

/-- Empty face tables make the raw coarse degree-one matrix zero.

Position: private matrix-evaluation API for the uniformity instance proofs.  The
zero conclusion comes from the raw empty coarse-face table, not a zero-matrix field. -/
private theorem coarseD1Matrix_eq_zero (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).coarseD1Matrix Finset.univ = 0 := by
  ext face edge
  exact nomatch face.1

/-- Self-loop endpoints make the raw coarse degree-zero matrix zero.  This
private instance API uses the definition-owner matrix/linear-map evaluation
lemmas and the explicit endpoint equality, with no supplied zero matrix.

Position: private matrix-evaluation API for the uniformity instance proofs; its
material inputs are the raw self-loop endpoints and complete selected-edge table. -/
private theorem coarseD0Matrix_eq_zero (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).coarseD0Matrix Finset.univ = 0 := by
  ext edge chart
  rw [(selfLoopPresentation FineEdge).coarseD0Matrix_apply,
    (selfLoopPresentation FineEdge).coarseD0LinearMap_apply]
  have hendpoints :
      (selfLoopPresentation FineEdge).coarseEdgeRightIn Finset.univ edge =
        (selfLoopPresentation FineEdge).coarseEdgeLeftIn Finset.univ edge := by
    apply Subtype.ext
    rfl
  simp
  rw [hendpoints]
  ring

/-- Self-loop endpoints make the raw fine degree-zero matrix zero.  This
private instance API uses the definition-owner matrix/linear-map evaluation
lemmas and the explicit endpoint equality, with no supplied zero matrix.

Position: private matrix-evaluation API for the uniformity instance proofs; its
material inputs are the raw fine self-loop endpoints and complete edge table. -/
private theorem fineD0Matrix_eq_zero (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).fineD0Matrix Finset.univ = 0 := by
  ext edge chart
  rw [(selfLoopPresentation FineEdge).fineD0Matrix_apply,
    (selfLoopPresentation FineEdge).fineD0LinearMap_apply]
  have hendpoints :
      (selfLoopPresentation FineEdge).fineEdgeRightIn Finset.univ edge =
        (selfLoopPresentation FineEdge).fineEdgeLeftIn Finset.univ edge := by
    apply Subtype.ext
    rfl
  simp
  rw [hendpoints]
  ring

/-- Empty face tables make the raw fine degree-one matrix zero.

Position: private matrix-evaluation API for the uniformity instance proofs.  The
zero conclusion comes from the raw empty fine-face table, not a zero-matrix field. -/
private theorem fineD1Matrix_eq_zero (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).fineD1Matrix Finset.univ = 0 := by
  ext face edge
  exact nomatch face.1

/-- The raw H¹ block matrix is the outer product of the all-one fine-edge
column with the row selecting the unique coarse-edge coordinate.  This private
instance API derives every entry through the public block-map evaluation
surface and raw self-loop tables; it supplies neither the matrix nor its rank.

Position: private block-matrix API feeding the semantic rank theorem for both
fixtures.  Complete raw edge coverage and computed map entries are its only
material inputs; the outer-product formula is proved rather than supplied. -/
private theorem h1RankBlockMatrix_eq_vecMulVec (FineEdge : Type)
    [Fintype FineEdge] [DecidableEq FineEdge] [SelfLoopEntries FineEdge] :
    (selfLoopPresentation FineEdge).h1RankBlockMatrix Finset.univ =
      Matrix.vecMulVec (fun _ => (1 : ℚ))
        (fun index => match index with
          | Sum.inl _ => 1
          | Sum.inr _ => 0) := by
  ext row column
  cases row with
  | inl face => exact nomatch face.1
  | inr edge =>
      cases column with
      | inl coarseEdge =>
          rw [(selfLoopPresentation FineEdge).h1RankBlockMatrix_apply,
            (selfLoopPresentation FineEdge).h1RankBlockLinearMap_apply_inr,
            (selfLoopPresentation FineEdge).edgePullback1LinearMap_apply,
            (selfLoopPresentation FineEdge).fineD0LinearMap_apply]
          have hmap :
              (selfLoopPresentation FineEdge).edgeMapOptionIn
                Finset.univ edge = some (fullCoarseEdge FineEdge) := by
            exact ((selfLoopPresentation FineEdge).edgeMapOptionIn_eq_some_iff
              Finset.univ edge (fullCoarseEdge FineEdge)).2 rfl
          have hcoarse : coarseEdge = fullCoarseEdge FineEdge := by
            apply Subtype.ext
            rfl
          subst coarseEdge
          simp [Matrix.vecMulVec, hmap]
      | inr chart =>
          rw [(selfLoopPresentation FineEdge).h1RankBlockMatrix_apply,
            (selfLoopPresentation FineEdge).h1RankBlockLinearMap_apply_inr,
            (selfLoopPresentation FineEdge).edgePullback1LinearMap_apply,
            (selfLoopPresentation FineEdge).fineD0LinearMap_apply]
          have hendpoints :
              (selfLoopPresentation FineEdge).fineEdgeRightIn
                  Finset.univ edge =
                (selfLoopPresentation FineEdge).fineEdgeLeftIn
                  Finset.univ edge := by
            apply Subtype.ext
            rfl
          cases hmap : (selfLoopPresentation FineEdge).edgeMapOptionIn
              Finset.univ edge <;>
            simp [Matrix.vecMulVec] <;>
            rw [hendpoints] <;> ring

/-- The positive raw presentation computes a nonzero rank-one induced H¹
comparison on its unique nonempty target subset. -/
theorem positive_fullTarget_h1Rank :
    positivePresentation.computedASubnerveH1Rank Finset.univ = 1 := by
  rw [FiniteComparisonPresentation.computedASubnerveH1Rank,
    rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
    rationalMatrixRank_eq_rank]
  have hblockLe :
      (positivePresentation.h1RankBlockMatrix Finset.univ).rank ≤ 1 := by
    rw [positivePresentation, h1RankBlockMatrix_eq_vecMulVec]
    exact Matrix.rank_vecMulVec_le _ _
  have hblockPos :
      0 < (positivePresentation.h1RankBlockMatrix Finset.univ).rank :=
    rank_pos_of_entry_ne_zero
      (positivePresentation.h1RankBlockMatrix Finset.univ) (by
        rw [positive_h1RankBlockMatrix_entry]
        norm_num)
  have hblock :
      (positivePresentation.h1RankBlockMatrix Finset.univ).rank = 1 := by
    omega
  have hcoarseD1 :
      (positivePresentation.coarseD1Matrix Finset.univ).rank = 0 := by
    rw [positivePresentation, coarseD1Matrix_eq_zero, Matrix.rank_zero]
  have hfineD0 :
      (positivePresentation.fineD0Matrix Finset.univ).rank = 0 := by
    rw [positivePresentation, fineD0Matrix_eq_zero, Matrix.rank_zero]
  omega

/-- The negative raw presentation also computes a nonzero rank-one induced H¹
comparison on its unique nonempty target subset. -/
theorem negative_fullTarget_h1Rank :
    negativePresentation.computedASubnerveH1Rank Finset.univ = 1 := by
  rw [FiniteComparisonPresentation.computedASubnerveH1Rank,
    rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
    rationalMatrixRank_eq_rank]
  have hblockLe :
      (negativePresentation.h1RankBlockMatrix Finset.univ).rank ≤ 1 := by
    rw [negativePresentation, h1RankBlockMatrix_eq_vecMulVec]
    exact Matrix.rank_vecMulVec_le _ _
  have hentry :
      negativePresentation.h1RankBlockMatrix Finset.univ
        (Sum.inr (fullFineEdge Bool false))
        (Sum.inl (fullCoarseEdge Bool)) ≠ 0 := by
    rw [negative_h1RankBlockMatrix_entry]
    norm_num
  have hblockPos :
      0 < (negativePresentation.h1RankBlockMatrix Finset.univ).rank :=
    rank_pos_of_entry_ne_zero
      (negativePresentation.h1RankBlockMatrix Finset.univ) hentry
  have hblock :
      (negativePresentation.h1RankBlockMatrix Finset.univ).rank = 1 := by
    omega
  have hcoarseD1 :
      (negativePresentation.coarseD1Matrix Finset.univ).rank = 0 := by
    rw [negativePresentation, coarseD1Matrix_eq_zero, Matrix.rank_zero]
  have hfineD0 :
      (negativePresentation.fineD0Matrix Finset.univ).rank = 0 := by
    rw [negativePresentation, fineD0Matrix_eq_zero, Matrix.rank_zero]
  omega

/-- The positive raw presentation fires the exact evaluator at nonzero H¹
rank with zero kernel and cokernel defect. -/
theorem positive_fullTarget_firing :
    positivePresentation.computedASubnerveH1Rank Finset.univ = 1 ∧
      positivePresentation.computedASubnerveDefect Finset.univ = (0, 0) := by
  refine ⟨positive_fullTarget_h1Rank, ?_⟩
  rw [FiniteComparisonPresentation.computedASubnerveDefect,
    rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
    rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
    positive_fullTarget_h1Rank]
  have hcoarseCard :
      Fintype.card (positivePresentation.CoarseEdgeIn Finset.univ) = 1 := by
    simpa [positivePresentation] using
      Fintype.card_congr (fullCoarseEdgeEquiv PUnit)
  have hfineCard :
      Fintype.card (positivePresentation.FineEdgeIn Finset.univ) = 1 := by
    simpa [positivePresentation] using
      Fintype.card_congr (fullFineEdgeEquiv PUnit)
  have hcoarseD1 :
      (positivePresentation.coarseD1Matrix Finset.univ).rank = 0 := by
    rw [positivePresentation, coarseD1Matrix_eq_zero, Matrix.rank_zero]
  have hcoarseD0 :
      (positivePresentation.coarseD0Matrix Finset.univ).rank = 0 := by
    rw [positivePresentation, coarseD0Matrix_eq_zero, Matrix.rank_zero]
  have hfineD1 :
      (positivePresentation.fineD1Matrix Finset.univ).rank = 0 := by
    rw [positivePresentation, fineD1Matrix_eq_zero, Matrix.rank_zero]
  have hfineD0 :
      (positivePresentation.fineD0Matrix Finset.univ).rank = 0 := by
    rw [positivePresentation, fineD0Matrix_eq_zero, Matrix.rank_zero]
  simp [hcoarseCard, hfineCard, hcoarseD1, hcoarseD0, hfineD1, hfineD0]

/-- The negative raw presentation fires the exact evaluator at nonzero H¹
rank with a one-dimensional cokernel defect. -/
theorem negative_fullTarget_firing :
    negativePresentation.computedASubnerveH1Rank Finset.univ = 1 ∧
      negativePresentation.computedASubnerveDefect Finset.univ = (0, 1) := by
  refine ⟨negative_fullTarget_h1Rank, ?_⟩
  rw [FiniteComparisonPresentation.computedASubnerveDefect,
    rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
    rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
    negative_fullTarget_h1Rank]
  have hcoarseCard :
      Fintype.card (negativePresentation.CoarseEdgeIn Finset.univ) = 1 := by
    simpa [negativePresentation] using
      Fintype.card_congr (fullCoarseEdgeEquiv Bool)
  have hfineCard :
      Fintype.card (negativePresentation.FineEdgeIn Finset.univ) = 2 := by
    simpa [negativePresentation] using
      Fintype.card_congr (fullFineEdgeEquiv Bool)
  have hcoarseD1 :
      (negativePresentation.coarseD1Matrix Finset.univ).rank = 0 := by
    rw [negativePresentation, coarseD1Matrix_eq_zero, Matrix.rank_zero]
  have hcoarseD0 :
      (negativePresentation.coarseD0Matrix Finset.univ).rank = 0 := by
    rw [negativePresentation, coarseD0Matrix_eq_zero, Matrix.rank_zero]
  have hfineD1 :
      (negativePresentation.fineD1Matrix Finset.univ).rank = 0 := by
    rw [negativePresentation, fineD1Matrix_eq_zero, Matrix.rank_zero]
  have hfineD0 :
      (negativePresentation.fineD0Matrix Finset.univ).rank = 0 := by
    rw [negativePresentation, fineD0Matrix_eq_zero, Matrix.rank_zero]
  simp [hcoarseCard, hfineCard, hcoarseD1, hcoarseD0, hfineD1, hfineD0]

/-- The generic all-subset checker returns true on the positive raw
presentation. -/
theorem positive_uniformPresentationCheck :
    positivePresentation.uniformPresentationCheck = true := by
  apply (FiniteComparisonPresentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects
    positivePresentation).2
  intro A hA
  have hunit : PUnit.unit ∈ A := by
    obtain ⟨target, htarget⟩ := hA
    cases target
    exact htarget
  have hAuniv : A = Finset.univ := by
    ext target
    cases target
    simp [hunit]
  rw [hAuniv]
  exact positive_fullTarget_firing.2

/-- The generic all-subset checker returns false on the negative raw
presentation. -/
theorem negative_uniformPresentationCheck :
    negativePresentation.uniformPresentationCheck = false := by
  cases hcheck : negativePresentation.uniformPresentationCheck with
  | false => rfl
  | true =>
      have hall :=
        (FiniteComparisonPresentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects
          negativePresentation).1 hcheck
      have hzero := hall Finset.univ
        (⟨PUnit.unit, Finset.mem_univ _⟩ : (Finset.univ :
          Finset negativePresentation.CoarseTarget).Nonempty)
      rw [negative_fullTarget_firing.2] at hzero
      norm_num at hzero

/-- The positive raw presentation satisfies the full semantic uniformity
predicate, by soundness of the same checker that was executed above. -/
theorem positive_uniformPresentation :
    UniformPresentation positivePresentation :=
  positivePresentation.uniformPresentationCheck_eq_true_iff.mp
    positive_uniformPresentationCheck

/-- The negative raw presentation fails the full semantic uniformity
predicate, by completeness of the same checker that was executed above. -/
theorem negative_not_uniformPresentation :
    ¬ UniformPresentation negativePresentation := by
  intro huniform
  have htrue := negativePresentation.uniformPresentationCheck_eq_true_iff.mpr
    huniform
  rw [negative_uniformPresentationCheck] at htrue
  contradiction

end UniformPresentationInstancePairs

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
