import ResearchLean.AG.UniformInvariance.GLocalV1T3T6Witnesses
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# Semantic uniformity labels for the registered T3/T6 pair

This module discharges fixed GOAL claims (v)(b) and (v)(c).  Starting only
from the registered raw T3/T6 presentations, it proves the three exact T3
`H¹` block profiles, fires the sound-and-complete finite checker positively
for T3, and proves the exact `3 → 1` target-zero dimension mismatch before
firing the checker negatively for T6.

The proof does not import the full-observation equality module and does not
use the Round-15 or Stop-B labels.  Matrix ranks are established from raw
selected columns, explicit rational determinants, and spanning relations;
no rank, defect, checker result, or semantic label is supplied as a field,
premise, typeclass, or external certificate.

## Implementation notes

The executable rank search is deliberately not reduced wholesale: its generic
correctness theorem first turns each rank into semantic matrix rank.  A local
selected-column lemma then proves exact ranks from a nonzero Gram determinant
and an explicit spanning proof.  This keeps kernel checking small and exposes
the incidence facts that materially distinguish the ternary 3- and 6-cycles.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase
open FiniteComparisonPresentation
open ExecutableRationalLinearAlgebra

namespace GLocalV1T3T6Witnesses

/-! ## Literal quotient complexes -/

/-- Coarse T3 `A`-subnerve complex used by the exact profile theorems.

Position: notation for fixed GOAL claim (v)(b).  It abbreviates the canonical
semantic construction from the registered raw presentation and adds no
dimension, rank, defect, or label data. -/
abbrev t3CoarseComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  t3Presentation.coarseSupportedNerve.targetSubsetComplex
    (↑A : Set (Fin 2))

/-- Fine T3 preimage-subnerve complex used by the exact profile theorems.

Position: fine-side notation for fixed GOAL claim (v)(b).  Its subset is the
canonical computed preimage, not a supplied block or cohomology certificate. -/
abbrev t3FineComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  t3Presentation.fineSupportedNerve.targetSubsetComplex
    (t3Presentation.canonicalFinePreimage A)

/-- Coarse T6 `A`-subnerve complex used by the target-zero mismatch theorem.

Position: notation for fixed GOAL claim (v)(c), generated from the registered
raw T6 presentation without carrying an expected dimension or label. -/
abbrev t6CoarseComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  t6Presentation.coarseSupportedNerve.targetSubsetComplex
    (↑A : Set (Fin 2))

/-- Fine T6 preimage-subnerve complex used by the target-zero mismatch theorem.

Position: fine-side notation for fixed GOAL claim (v)(c).  The canonical
preimage remains computed from the raw factor and target subset. -/
abbrev t6FineComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  t6Presentation.fineSupportedNerve.targetSubsetComplex
    (t6Presentation.canonicalFinePreimage A)

/-! ## Raw selected-cell counts and zero differentials -/

/-- All selected T3/T6 degree-zero differentials vanish because every raw
edge is a self-loop.

Position: shared incidence normalization for claims (v)(b)–(c).  The premise
is only one of the two registered presentations and a target subset; the
conclusion is derived from raw endpoints rather than an `H¹` certificate. -/
theorem identitySplit_coarseD0Matrix_eq_zero
    (P : FiniteComparisonPresentation)
    (hP : P = t3Presentation ∨ P = t6Presentation)
    (A : Finset P.CoarseTarget) : P.coarseD0Matrix A = 0 := by
  ext edge chart
  rw [FiniteComparisonPresentation.coarseD0Matrix_apply,
    FiniteComparisonPresentation.coarseD0LinearMap_apply]
  have hendpoints : P.coarseEdgeRightIn A edge =
      P.coarseEdgeLeftIn A edge := by
    apply Subtype.ext
    rcases hP with rfl | rfl <;>
      simp [t3Presentation, t6Presentation, identitySplitPresentation,
        edgeChart]
  rw [hendpoints, sub_self]
  rfl

/-- Fine-side companion: every selected degree-zero differential vanishes
because the registered fine edges are the same raw self-loops.

Position: shared fine incidence normalization for claims (v)(b)–(c), using
only the registered raw endpoint table. -/
theorem identitySplit_fineD0Matrix_eq_zero
    (P : FiniteComparisonPresentation)
    (hP : P = t3Presentation ∨ P = t6Presentation)
    (A : Finset P.CoarseTarget) : P.fineD0Matrix A = 0 := by
  ext edge chart
  rw [FiniteComparisonPresentation.fineD0Matrix_apply,
    FiniteComparisonPresentation.fineD0LinearMap_apply]
  have hendpoints : P.fineEdgeRightIn A edge =
      P.fineEdgeLeftIn A edge := by
    apply Subtype.ext
    rcases hP with rfl | rfl <;>
      simp [t3Presentation, t6Presentation, identitySplitPresentation,
        edgeChart]
  rw [hendpoints, sub_self]
  rfl

/-- T3 selected edge counts on the three nonempty target scopes are exactly
`4/1`, `3/3`, and `4/4` on the coarse/fine sides.

Position: raw finite-cardinality input to fixed GOAL claim (v)(b).  The six
numbers are computed from registered supports and the canonical factor, not
provided as rank or cohomology fields. -/
theorem t3_selectedEdgeCard_profile :
    Fintype.card (t3Presentation.CoarseEdgeIn targetZero) = 4 ∧
    Fintype.card (t3Presentation.FineEdgeIn targetZero) = 1 ∧
    Fintype.card (t3Presentation.CoarseEdgeIn targetOne) = 3 ∧
    Fintype.card (t3Presentation.FineEdgeIn targetOne) = 3 ∧
    Fintype.card (t3Presentation.CoarseEdgeIn targetFull) = 4 ∧
    Fintype.card (t3Presentation.FineEdgeIn targetFull) = 4 := by
  decide +kernel

/-- T6 target zero selects all seven coarse edges but only the anchor fine
edge.

Position: raw finite-cardinality input to fixed GOAL claim (v)(c).  It follows
from the registered support split and contains no expected `H¹` dimension. -/
theorem t6_targetZero_selectedEdgeCards :
    Fintype.card (t6Presentation.CoarseEdgeIn targetZero) = 7 ∧
    Fintype.card (t6Presentation.FineEdgeIn targetZero) = 1 := by
  decide +kernel

/-! ## T3 differential ranks -/

/-- The three non-anchor T3 coarse edges selected at target zero.

Position: private typed enumeration for the raw selected-column rank proof in
claim (v)(b); membership is computed from the registered support table. -/
private def t3TargetZeroNeutralCoarseEdge (index : Fin 3) :
    t3Presentation.CoarseEdgeIn targetZero :=
  ⟨index.succ, by fin_cases index <;> decide⟩

/-- The T3 coarse degree-one matrix has rank three at target zero.

Position: raw-matrix rank theorem for claim (v)(b).  The proof selects the
three neutral columns, checks their Gram determinant, and proves that the
remaining anchor column is zero from the face table. -/
theorem t3_targetZero_coarseD1_rank :
    (t3Presentation.coarseD1Matrix targetZero).rank = 3 := by
  apply rank_eq_of_selectedColumns_basis
      (t3Presentation.coarseD1Matrix targetZero)
      t3TargetZeroNeutralCoarseEdge
  · decide +kernel
  · intro column
    obtain ⟨column, hcolumn⟩ := column
    fin_cases column
    · have hzero :
          (t3Presentation.coarseD1Matrix targetZero).col
              (⟨(0 : Fin 4), hcolumn⟩ :
                t3Presentation.CoarseEdgeIn targetZero) = 0 := by
        funext face
        obtain ⟨face, hface⟩ := face
        change t3Presentation.coarseD1Matrix targetZero
            (⟨face, hface⟩ : t3Presentation.CoarseFaceIn targetZero)
            (⟨(0 : Fin 4), hcolumn⟩ :
              t3Presentation.CoarseEdgeIn targetZero) = 0
        fin_cases face <;>
          rw [FiniteComparisonPresentation.coarseD1Matrix_apply,
            FiniteComparisonPresentation.coarseD1LinearMap_apply] <;>
          simp [Subtype.ext_iff, t3Presentation,
            identitySplitPresentation, t3FaceEdge0, t3FaceEdge1,
            t3FaceEdge2]
      change (t3Presentation.coarseD1Matrix targetZero).col
          (⟨(0 : Fin 4), hcolumn⟩ :
            t3Presentation.CoarseEdgeIn targetZero) ∈ _
      rw [hzero]
      exact Submodule.zero_mem _
    · apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetZero).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨1, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetZero).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨2, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetZero).col
      apply Subtype.ext
      rfl

/-- The three selected T3 coarse edges at target one.

Position: private typed enumeration for the target-one raw rank proof in claim
(v)(b); zero is excluded by the registered support split. -/
private def t3TargetOneCoarseEdge (index : Fin 3) :
    t3Presentation.CoarseEdgeIn targetOne :=
  ⟨index.succ, by fin_cases index <;> decide⟩

/-- The three selected T3 fine edges at target one.

Position: fine-side private enumeration for the target-one raw rank proof;
membership follows from the computed preimage of the registered factor. -/
private def t3TargetOneFineEdge (index : Fin 3) :
    t3Presentation.FineEdgeIn targetOne :=
  ⟨index.succ, by fin_cases index <;> decide⟩

/-- The T3 coarse degree-one matrix has rank three at target one.

Position: target-one raw-matrix rank theorem for claim (v)(b).  All selected
columns are the explicit neutral basis and their Gram determinant is nonzero. -/
theorem t3_targetOne_coarseD1_rank :
    (t3Presentation.coarseD1Matrix targetOne).rank = 3 := by
  apply rank_eq_of_selectedColumns_basis
      (t3Presentation.coarseD1Matrix targetOne)
      t3TargetOneCoarseEdge
  · decide +kernel
  · intro column
    obtain ⟨column, hcolumn⟩ := column
    fin_cases column
    · have : False := (by decide :
          (0 : Fin 4) ∉ t3Presentation.coarseEdgesIn targetOne) hcolumn
      contradiction
    · apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetOne).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨1, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetOne).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨2, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetOne).col
      apply Subtype.ext
      rfl

/-- The T3 fine degree-one matrix has rank three at target one.

Position: fine target-one raw-matrix rank theorem for claim (v)(b).  It is
proved independently from the fine selected cells and raw fine face table. -/
theorem t3_targetOne_fineD1_rank :
    (t3Presentation.fineD1Matrix targetOne).rank = 3 := by
  apply rank_eq_of_selectedColumns_basis
      (t3Presentation.fineD1Matrix targetOne)
      t3TargetOneFineEdge
  · decide +kernel
  · intro column
    obtain ⟨column, hcolumn⟩ := column
    fin_cases column
    · have : False := (by decide :
          (0 : Fin 4) ∉ t3Presentation.fineEdgesIn targetOne) hcolumn
      contradiction
    · apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply congrArg (t3Presentation.fineD1Matrix targetOne).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨1, ?_⟩
      apply congrArg (t3Presentation.fineD1Matrix targetOne).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨2, ?_⟩
      apply congrArg (t3Presentation.fineD1Matrix targetOne).col
      apply Subtype.ext
      rfl

/-- The three non-anchor T3 coarse edges selected at the full target.

Position: private typed enumeration for the full-target coarse rank proof in
claim (v)(b); it contains only raw neutral edge indices. -/
private def t3TargetFullNeutralCoarseEdge (index : Fin 3) :
    t3Presentation.CoarseEdgeIn targetFull :=
  ⟨index.succ, by fin_cases index <;> decide⟩

/-- The three non-anchor T3 fine edges selected at the full target.

Position: fine-side private enumeration for the full-target rank proof in
claim (v)(b), derived from the registered support table. -/
private def t3TargetFullNeutralFineEdge (index : Fin 3) :
    t3Presentation.FineEdgeIn targetFull :=
  ⟨index.succ, by fin_cases index <;> decide⟩

/-- The T3 coarse degree-one matrix has rank three at the full target.

Position: full-target raw-matrix rank theorem for claim (v)(b).  The neutral
columns have nonzero Gram determinant and the anchor column is zero. -/
theorem t3_targetFull_coarseD1_rank :
    (t3Presentation.coarseD1Matrix targetFull).rank = 3 := by
  apply rank_eq_of_selectedColumns_basis
      (t3Presentation.coarseD1Matrix targetFull)
      t3TargetFullNeutralCoarseEdge
  · decide +kernel
  · intro column
    obtain ⟨column, hcolumn⟩ := column
    fin_cases column
    · have hzero :
          (t3Presentation.coarseD1Matrix targetFull).col
              (⟨(0 : Fin 4), hcolumn⟩ :
                t3Presentation.CoarseEdgeIn targetFull) = 0 := by
        funext face
        obtain ⟨face, hface⟩ := face
        change t3Presentation.coarseD1Matrix targetFull
            (⟨face, hface⟩ : t3Presentation.CoarseFaceIn targetFull)
            (⟨(0 : Fin 4), hcolumn⟩ :
              t3Presentation.CoarseEdgeIn targetFull) = 0
        fin_cases face <;>
          rw [FiniteComparisonPresentation.coarseD1Matrix_apply,
            FiniteComparisonPresentation.coarseD1LinearMap_apply] <;>
          simp [Subtype.ext_iff, t3Presentation,
            identitySplitPresentation, t3FaceEdge0, t3FaceEdge1,
            t3FaceEdge2]
      change (t3Presentation.coarseD1Matrix targetFull).col
          (⟨(0 : Fin 4), hcolumn⟩ :
            t3Presentation.CoarseEdgeIn targetFull) ∈ _
      rw [hzero]
      exact Submodule.zero_mem _
    · apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetFull).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨1, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetFull).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨2, ?_⟩
      apply congrArg (t3Presentation.coarseD1Matrix targetFull).col
      apply Subtype.ext
      rfl

/-- The T3 fine degree-one matrix has rank three at the full target.

Position: fine full-target raw-matrix rank theorem for claim (v)(b), proved
from the fine incidence table rather than transferred from the coarse result. -/
theorem t3_targetFull_fineD1_rank :
    (t3Presentation.fineD1Matrix targetFull).rank = 3 := by
  apply rank_eq_of_selectedColumns_basis
      (t3Presentation.fineD1Matrix targetFull)
      t3TargetFullNeutralFineEdge
  · decide +kernel
  · intro column
    obtain ⟨column, hcolumn⟩ := column
    fin_cases column
    · have hzero :
          (t3Presentation.fineD1Matrix targetFull).col
              (⟨(0 : Fin 4), hcolumn⟩ :
                t3Presentation.FineEdgeIn targetFull) = 0 := by
        funext face
        obtain ⟨face, hface⟩ := face
        change t3Presentation.fineD1Matrix targetFull
            (⟨face, hface⟩ : t3Presentation.FineFaceIn targetFull)
            (⟨(0 : Fin 4), hcolumn⟩ :
              t3Presentation.FineEdgeIn targetFull) = 0
        fin_cases face <;>
          rw [FiniteComparisonPresentation.fineD1Matrix_apply,
            FiniteComparisonPresentation.fineD1LinearMap_apply] <;>
          simp [Subtype.ext_iff, t3Presentation,
            identitySplitPresentation, t3FaceEdge0, t3FaceEdge1,
            t3FaceEdge2]
      change (t3Presentation.fineD1Matrix targetFull).col
          (⟨(0 : Fin 4), hcolumn⟩ :
            t3Presentation.FineEdgeIn targetFull) ∈ _
      rw [hzero]
      exact Submodule.zero_mem _
    · apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply congrArg (t3Presentation.fineD1Matrix targetFull).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨1, ?_⟩
      apply congrArg (t3Presentation.fineD1Matrix targetFull).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨2, ?_⟩
      apply congrArg (t3Presentation.fineD1Matrix targetFull).col
      apply Subtype.ext
      rfl

/-- The T3 fine degree-one matrix at target zero has no selected face rows.

Position: target-zero fine rank normalization for claim (v)(b), obtained from
the raw selected-face cardinality rather than a supplied zero map. -/
theorem t3_targetZero_fineD1_rank :
    (t3Presentation.fineD1Matrix targetZero).rank = 0 := by
  have hle := Matrix.rank_le_card_height
    (t3Presentation.fineD1Matrix targetZero)
  have hfaces : Fintype.card (t3Presentation.FineFaceIn targetZero) = 0 := by
    decide +kernel
  omega

/-! ## T6 target-zero differential ranks -/

/-- The seven raw T6 coarse edges selected at target zero.

Position: private typed enumeration for the exact coarse `d₁` rank proof in
claim (v)(c).  Membership is computed from the registered target-zero support
table and carries no linear-algebra result. -/
private def t6TargetZeroCoarseEdge (index : Fin 7) :
    t6Presentation.CoarseEdgeIn targetZero :=
  ⟨index, by fin_cases index <;> decide⟩

/-- The four consecutive neutral columns used in the T6 rank lower bound.

Position: private selected-column enumeration for claim (v)(c).  It records
only raw edge indices one through four, not a supplied basis certificate. -/
private def t6TargetZeroSelectedCoarseEdge (index : Fin 4) :
    t6Presentation.CoarseEdgeIn targetZero :=
  t6TargetZeroCoarseEdge ⟨index + 1, by omega⟩

/-- The T6 anchor column is zero in the target-zero coarse `d₁` matrix.

Position: raw incidence relation used in claim (v)(c).  It is derived from
the registered six-face boundary table and does not use the expected rank. -/
theorem t6_targetZero_coarseD1_column_zero :
    (t6Presentation.coarseD1Matrix targetZero).col
        (t6TargetZeroCoarseEdge 0) = 0 := by
  funext face
  obtain ⟨face, hface⟩ := face
  change t6Presentation.coarseD1Matrix targetZero
      (⟨face, hface⟩ : t6Presentation.CoarseFaceIn targetZero)
      (t6TargetZeroCoarseEdge 0) = 0
  fin_cases face <;>
    rw [FiniteComparisonPresentation.coarseD1Matrix_apply,
      FiniteComparisonPresentation.coarseD1LinearMap_apply] <;>
    simp [t6TargetZeroCoarseEdge, Subtype.ext_iff, t6Presentation,
      identitySplitPresentation, t6FaceEdge0, t6FaceEdge1, t6FaceEdge2]

/-- T6 coarse column five is generated by selected columns one, two, and four.

Position: first raw spanning relation for claim (v)(c), proved entrywise from
the registered cyclic face table rather than supplied as a rank witness. -/
theorem t6_targetZero_coarseD1_column_five :
    (t6Presentation.coarseD1Matrix targetZero).col
        (t6TargetZeroCoarseEdge 5) =
      (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 1) +
      (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 2) -
      (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 4) := by
  funext face
  obtain ⟨face, hface⟩ := face
  change t6Presentation.coarseD1Matrix targetZero
      (⟨face, hface⟩ : t6Presentation.CoarseFaceIn targetZero)
      (t6TargetZeroCoarseEdge 5) = _
  fin_cases face <;>
    simp only [Matrix.col_apply, Pi.add_apply, Pi.sub_apply] <;>
    simp_rw [FiniteComparisonPresentation.coarseD1Matrix_apply,
      FiniteComparisonPresentation.coarseD1LinearMap_apply] <;>
    simp [Pi.single_apply, t6TargetZeroCoarseEdge, Subtype.ext_iff,
      t6Presentation, identitySplitPresentation, t6FaceEdge0,
      t6FaceEdge1, t6FaceEdge2]

/-- T6 coarse column six is generated by selected columns one, three, and four.

Position: second raw spanning relation for claim (v)(c), again extracted
entrywise from the cyclic boundary table with no rank or dimension premise. -/
theorem t6_targetZero_coarseD1_column_six :
    (t6Presentation.coarseD1Matrix targetZero).col
        (t6TargetZeroCoarseEdge 6) =
      -(t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 1) +
      (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 3) +
      (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 4) := by
  funext face
  obtain ⟨face, hface⟩ := face
  change t6Presentation.coarseD1Matrix targetZero
      (⟨face, hface⟩ : t6Presentation.CoarseFaceIn targetZero)
      (t6TargetZeroCoarseEdge 6) = _
  fin_cases face <;>
    simp only [Matrix.col_apply, Pi.add_apply, Pi.neg_apply] <;>
    simp_rw [FiniteComparisonPresentation.coarseD1Matrix_apply,
      FiniteComparisonPresentation.coarseD1LinearMap_apply] <;>
    simp [Pi.single_apply, t6TargetZeroCoarseEdge, Subtype.ext_iff,
      t6Presentation, identitySplitPresentation, t6FaceEdge0,
      t6FaceEdge1, t6FaceEdge2]

/-- The T6 target-zero coarse degree-one matrix has exact rank four.

Position: exact raw-matrix rank theorem required by fixed GOAL claim (v)(c).
The proof computes the `4×4` Gram matrix of columns one through four, checks
its determinant in the kernel, and spans the remaining columns using the
three preceding incidence relations. -/
theorem t6_targetZero_coarseD1_rank :
    (t6Presentation.coarseD1Matrix targetZero).rank = 4 := by
  apply rank_eq_of_selectedColumns_basis _ t6TargetZeroSelectedCoarseEdge
  · have hgram :
        columnGram (t6Presentation.coarseD1Matrix targetZero)
            t6TargetZeroSelectedCoarseEdge =
          (!![(3 : ℚ), -2, 1, 0;
              -2, 3, -2, 1;
              1, -2, 3, -2;
              0, 1, -2, 3] : Matrix (Fin 4) (Fin 4) ℚ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> decide +kernel
    rw [hgram]
    decide +kernel
  · intro column
    obtain ⟨column, hcolumn⟩ := column
    fin_cases column
    · change (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 0) ∈ _
      rw [t6_targetZero_coarseD1_column_zero]
      exact Submodule.zero_mem _
    · apply Submodule.subset_span
      refine ⟨0, ?_⟩
      apply congrArg (t6Presentation.coarseD1Matrix targetZero).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨1, ?_⟩
      apply congrArg (t6Presentation.coarseD1Matrix targetZero).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨2, ?_⟩
      apply congrArg (t6Presentation.coarseD1Matrix targetZero).col
      apply Subtype.ext
      rfl
    · apply Submodule.subset_span
      refine ⟨3, ?_⟩
      apply congrArg (t6Presentation.coarseD1Matrix targetZero).col
      apply Subtype.ext
      rfl
    · change (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 5) ∈ _
      rw [t6_targetZero_coarseD1_column_five]
      exact Submodule.sub_mem _ (Submodule.add_mem _
        (Submodule.subset_span ⟨0, rfl⟩)
        (Submodule.subset_span ⟨1, rfl⟩))
        (Submodule.subset_span ⟨3, rfl⟩)
    · change (t6Presentation.coarseD1Matrix targetZero).col
          (t6TargetZeroCoarseEdge 6) ∈ _
      rw [t6_targetZero_coarseD1_column_six]
      exact Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.neg_mem _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.subset_span ⟨2, rfl⟩))
        (Submodule.subset_span ⟨3, rfl⟩)

/-- The T6 fine degree-one matrix at target zero has no selected face rows.

Position: fine-side target-zero rank normalization for claim (v)(c), obtained
from the registered selected-face table rather than an expected dimension. -/
theorem t6_targetZero_fineD1_rank :
    (t6Presentation.fineD1Matrix targetZero).rank = 0 := by
  have hle := Matrix.rank_le_card_height
    (t6Presentation.fineD1Matrix targetZero)
  have hfaces : Fintype.card (t6Presentation.FineFaceIn targetZero) = 0 := by
    decide +kernel
  omega

/-! ## T3 induced-H¹ block ranks -/

/-- Fine-chart columns of the induced-H¹ block matrix vanish for either
registered identity-split presentation.

Position: shared raw block-matrix normalization for claims (v)(b)–(c).  The
premise identifies one registered presentation; the proof uses only its
self-loop endpoints and generated partial edge map, not an H¹ rank. -/
theorem identitySplit_h1RankBlockMatrix_inr_column_zero
    (P : FiniteComparisonPresentation)
    (hP : P = t3Presentation ∨ P = t6Presentation)
    (A : Finset P.CoarseTarget) (chart : P.FineChartIn A) :
    (P.h1RankBlockMatrix A).col (Sum.inr chart) = 0 := by
  funext row
  rw [Matrix.col_apply, P.h1RankBlockMatrix_apply]
  cases row with
  | inl face =>
      rw [P.h1RankBlockLinearMap_apply_inl,
        P.coarseD1LinearMap_apply]
      simp
  | inr edge =>
      rw [P.h1RankBlockLinearMap_apply_inr,
        P.edgePullback1LinearMap_apply, P.fineD0LinearMap_apply]
      have hendpoints : P.fineEdgeRightIn A edge =
          P.fineEdgeLeftIn A edge := by
        apply Subtype.ext
        rcases hP with rfl | rfl <;>
          simp [t3Presentation, t6Presentation,
            identitySplitPresentation, edgeChart]
      cases hmap : P.edgeMapOptionIn A edge <;>
        simp [Pi.single_apply] <;>
        rw [hendpoints] <;> ring

/-- All four T3 target-zero coarse-edge columns selected inside the induced-H¹
block matrix.

Position: private typed enumeration for claim (v)(b); it is generated from the
raw selected-edge table and contains no block-rank certificate. -/
private def t3TargetZeroH1SelectedColumn (index : Fin 4) :
    t3Presentation.CoarseEdgeIn targetZero ⊕
      t3Presentation.FineChartIn targetZero :=
  Sum.inl ⟨index, by fin_cases index <;> decide⟩

/-- The T3 target-zero induced-H¹ block matrix has exact rank four.

Position: first exact block-rank theorem for claim (v)(b).  Its four coarse
edge columns pass the Gram test, span every coarse column, and the remaining
fine-chart columns vanish by the registered self-loop incidence. -/
theorem t3_targetZero_h1RankBlock_rank :
    (t3Presentation.h1RankBlockMatrix targetZero).rank = 4 := by
  apply rank_eq_of_selectedColumns_basis _ t3TargetZeroH1SelectedColumn
  · decide +kernel
  · intro column
    cases column with
    | inl edge =>
        obtain ⟨edge, hedge⟩ := edge
        fin_cases edge
        · apply Submodule.subset_span
          refine ⟨0, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetZero).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨1, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetZero).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨2, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetZero).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨3, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetZero).col
          congr 1
    | inr chart =>
        rw [identitySplit_h1RankBlockMatrix_inr_column_zero
          t3Presentation (Or.inl rfl)]
        exact Submodule.zero_mem _

/-- The three T3 target-one coarse-edge columns selected inside the induced-H¹
block matrix.

Position: private target-one enumeration for claim (v)(b), containing only
raw retained neutral edges and no expected rank. -/
private def t3TargetOneH1SelectedColumn (index : Fin 3) :
    t3Presentation.CoarseEdgeIn targetOne ⊕
      t3Presentation.FineChartIn targetOne :=
  Sum.inl ⟨index.succ, by fin_cases index <;> decide⟩

/-- The T3 target-one induced-H¹ block matrix has exact rank three.

Position: second exact block-rank theorem for claim (v)(b).  The proof selects
all retained coarse edges, rejects the absent anchor, and derives zero
fine-chart columns from the raw self-loop table. -/
theorem t3_targetOne_h1RankBlock_rank :
    (t3Presentation.h1RankBlockMatrix targetOne).rank = 3 := by
  apply rank_eq_of_selectedColumns_basis _ t3TargetOneH1SelectedColumn
  · decide +kernel
  · intro column
    cases column with
    | inl edge =>
        obtain ⟨edge, hedge⟩ := edge
        fin_cases edge
        · have : False := (by decide :
              (0 : Fin 4) ∉ t3Presentation.coarseEdgesIn targetOne) hedge
          contradiction
        · apply Submodule.subset_span
          refine ⟨0, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetOne).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨1, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetOne).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨2, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetOne).col
          congr 1
    | inr chart =>
        rw [identitySplit_h1RankBlockMatrix_inr_column_zero
          t3Presentation (Or.inl rfl)]
        exact Submodule.zero_mem _

/-- All four T3 full-target coarse-edge columns selected inside the induced-H¹
block matrix.

Position: private full-target enumeration for claim (v)(b), obtained from raw
edge coverage and carrying no H¹ or defect value. -/
private def t3TargetFullH1SelectedColumn (index : Fin 4) :
    t3Presentation.CoarseEdgeIn targetFull ⊕
      t3Presentation.FineChartIn targetFull :=
  Sum.inl ⟨index, by fin_cases index <;> decide⟩

/-- The T3 full-target induced-H¹ block matrix has exact rank four.

Position: third exact block-rank theorem for claim (v)(b).  The selected raw
coarse columns pass the Gram test and span the block after fine-chart columns
are proved zero from incidence. -/
theorem t3_targetFull_h1RankBlock_rank :
    (t3Presentation.h1RankBlockMatrix targetFull).rank = 4 := by
  apply rank_eq_of_selectedColumns_basis _ t3TargetFullH1SelectedColumn
  · decide +kernel
  · intro column
    cases column with
    | inl edge =>
        obtain ⟨edge, hedge⟩ := edge
        fin_cases edge
        · apply Submodule.subset_span
          refine ⟨0, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetFull).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨1, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetFull).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨2, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetFull).col
          congr 1
        · apply Submodule.subset_span
          refine ⟨3, ?_⟩
          apply congrArg (t3Presentation.h1RankBlockMatrix targetFull).col
          congr 1
    | inr chart =>
        rw [identitySplit_h1RankBlockMatrix_inr_column_zero
          t3Presentation (Or.inl rfl)]
        exact Submodule.zero_mem _

/-! ## Exact semantic profiles and checker labels -/

/-- T3 target zero has actual quotient-H¹ dimensions `1 → 1`, computed map
rank one, and zero exact defect.

Position: first closed block profile in fixed GOAL claim (v)(b).  All four
components are derived from raw selected-cell counts and matrix ranks; none is
stored in the presentation or accepted as a premise. -/
theorem t3_targetZero_profile :
    Module.finrank ℚ (t3CoarseComplex targetZero).H1 = 1 ∧
    Module.finrank ℚ (t3FineComplex targetZero).H1 = 1 ∧
    t3Presentation.computedASubnerveH1Rank targetZero = 1 ∧
    t3Presentation.computedASubnerveDefect targetZero = (0, 0) := by
  have hcoarseD0 :
      (t3Presentation.coarseD0Matrix targetZero).rank = 0 := by
    rw [identitySplit_coarseD0Matrix_eq_zero t3Presentation (Or.inl rfl),
      Matrix.rank_zero]
  have hfineD0 :
      (t3Presentation.fineD0Matrix targetZero).rank = 0 := by
    rw [identitySplit_fineD0Matrix_eq_zero t3Presentation (Or.inl rfl),
      Matrix.rank_zero]
  have hcomputed :
      t3Presentation.computedASubnerveH1Rank targetZero = 1 := by
    rw [t3Presentation.computedASubnerveH1Rank_eq_rankFormula,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      rationalMatrixRank_eq_rank, t3_targetZero_h1RankBlock_rank,
      t3_targetZero_coarseD1_rank, hfineD0]
  have hdefect :
      t3Presentation.computedASubnerveDefect targetZero = (0, 0) := by
    rw [t3Presentation.computedASubnerveDefect_eq_rankFormula,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.1,
      t3_selectedEdgeCard_profile.2.1,
      t3_targetZero_coarseD1_rank, hcoarseD0,
      t3_targetZero_fineD1_rank, hfineD0, hcomputed]
  refine ⟨?_, ?_, hcomputed, hdefect⟩
  · rw [t3Presentation.coarseH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.1,
      t3_targetZero_coarseD1_rank, hcoarseD0]
  · rw [t3Presentation.fineH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.2.1,
      t3_targetZero_fineD1_rank, hfineD0]

/-- T3 target one has actual quotient-H¹ dimensions `0 → 0`, computed map
rank zero, and zero exact defect.

Position: second closed block profile in fixed GOAL claim (v)(b), derived from
the retained neutral incidence matrices and not from a Boolean label. -/
theorem t3_targetOne_profile :
    Module.finrank ℚ (t3CoarseComplex targetOne).H1 = 0 ∧
    Module.finrank ℚ (t3FineComplex targetOne).H1 = 0 ∧
    t3Presentation.computedASubnerveH1Rank targetOne = 0 ∧
    t3Presentation.computedASubnerveDefect targetOne = (0, 0) := by
  have hcoarseD0 :
      (t3Presentation.coarseD0Matrix targetOne).rank = 0 := by
    rw [identitySplit_coarseD0Matrix_eq_zero t3Presentation (Or.inl rfl),
      Matrix.rank_zero]
  have hfineD0 :
      (t3Presentation.fineD0Matrix targetOne).rank = 0 := by
    rw [identitySplit_fineD0Matrix_eq_zero t3Presentation (Or.inl rfl),
      Matrix.rank_zero]
  have hcomputed :
      t3Presentation.computedASubnerveH1Rank targetOne = 0 := by
    rw [t3Presentation.computedASubnerveH1Rank_eq_rankFormula,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      rationalMatrixRank_eq_rank, t3_targetOne_h1RankBlock_rank,
      t3_targetOne_coarseD1_rank, hfineD0]
  have hdefect :
      t3Presentation.computedASubnerveDefect targetOne = (0, 0) := by
    rw [t3Presentation.computedASubnerveDefect_eq_rankFormula,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.2.2.1,
      t3_selectedEdgeCard_profile.2.2.2.1,
      t3_targetOne_coarseD1_rank, hcoarseD0,
      t3_targetOne_fineD1_rank, hfineD0, hcomputed]
  refine ⟨?_, ?_, hcomputed, hdefect⟩
  · rw [t3Presentation.coarseH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.2.2.1,
      t3_targetOne_coarseD1_rank, hcoarseD0]
  · rw [t3Presentation.fineH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.2.2.2.1,
      t3_targetOne_fineD1_rank, hfineD0]

/-- T3 full target has actual quotient-H¹ dimensions `1 → 1`, computed map
rank one, and zero exact defect.

Position: third closed block profile in fixed GOAL claim (v)(b), completing
the three nonempty target scopes from raw ranks before the checker fires. -/
theorem t3_targetFull_profile :
    Module.finrank ℚ (t3CoarseComplex targetFull).H1 = 1 ∧
    Module.finrank ℚ (t3FineComplex targetFull).H1 = 1 ∧
    t3Presentation.computedASubnerveH1Rank targetFull = 1 ∧
    t3Presentation.computedASubnerveDefect targetFull = (0, 0) := by
  have hcoarseD0 :
      (t3Presentation.coarseD0Matrix targetFull).rank = 0 := by
    rw [identitySplit_coarseD0Matrix_eq_zero t3Presentation (Or.inl rfl),
      Matrix.rank_zero]
  have hfineD0 :
      (t3Presentation.fineD0Matrix targetFull).rank = 0 := by
    rw [identitySplit_fineD0Matrix_eq_zero t3Presentation (Or.inl rfl),
      Matrix.rank_zero]
  have hcomputed :
      t3Presentation.computedASubnerveH1Rank targetFull = 1 := by
    rw [t3Presentation.computedASubnerveH1Rank_eq_rankFormula,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      rationalMatrixRank_eq_rank, t3_targetFull_h1RankBlock_rank,
      t3_targetFull_coarseD1_rank, hfineD0]
  have hdefect :
      t3Presentation.computedASubnerveDefect targetFull = (0, 0) := by
    rw [t3Presentation.computedASubnerveDefect_eq_rankFormula,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.2.2.2.2.1,
      t3_selectedEdgeCard_profile.2.2.2.2.2,
      t3_targetFull_coarseD1_rank, hcoarseD0,
      t3_targetFull_fineD1_rank, hfineD0, hcomputed]
  refine ⟨?_, ?_, hcomputed, hdefect⟩
  · rw [t3Presentation.coarseH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.2.2.2.2.1,
      t3_targetFull_coarseD1_rank, hcoarseD0]
  · rw [t3Presentation.fineH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t3_selectedEdgeCard_profile.2.2.2.2.2,
      t3_targetFull_fineD1_rank, hfineD0]

/-- The generic all-nonempty-subset checker returns true for registered T3.

Position: executable label endpoint for fixed GOAL claim (v)(b).  The proof
classifies every nonempty `Fin 2` subset and uses the three independently
derived zero-defect profiles; no expected checker bit is read. -/
theorem t3_uniformPresentationCheck :
    t3Presentation.uniformPresentationCheck = true := by
  apply
    (t3Presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).2
  intro A hA
  by_cases hzero : (0 : Fin 2) ∈ A
  · by_cases hone : (1 : Fin 2) ∈ A
    · have hscope : A = targetFull := by
        ext target
        fin_cases target <;> simp [targetFull, hzero, hone]
      rw [hscope]
      exact t3_targetFull_profile.2.2.2
    · have hscope : A = targetZero := by
        ext target
        fin_cases target <;>
          simp [targetZero, hzero, hone, t3Presentation,
            identitySplitPresentation]
      rw [hscope]
      exact t3_targetZero_profile.2.2.2
  · have hone : (1 : Fin 2) ∈ A := by
      obtain ⟨target, htarget⟩ := hA
      fin_cases target
      · contradiction
      · exact htarget
    have hscope : A = targetOne := by
      ext target
      fin_cases target <;>
        simp [targetOne, hzero, hone, t3Presentation,
          identitySplitPresentation]
    rw [hscope]
    exact t3_targetOne_profile.2.2.2

/-- Registered T3 satisfies semantic uniform presentation invariance.

Position: semantic endpoint of fixed GOAL claim (v)(b), obtained by soundness
and completeness of the same checker whose three raw profiles were proved
above. -/
theorem t3_uniformPresentation : UniformPresentation t3Presentation :=
  t3Presentation.uniformPresentationCheck_eq_true_iff.mp
    t3_uniformPresentationCheck

/-- T6 target zero has exact actual quotient-H¹ dimensions `3 → 1`.

Position: mandatory nondegenerate dimension mismatch in fixed GOAL claim
(v)(c).  Both dimensions are derived from selected-edge counts and explicit
raw differential ranks, not merely inferred from a nonzero defect. -/
theorem t6_targetZero_h1_profile :
    Module.finrank ℚ (t6CoarseComplex targetZero).H1 = 3 ∧
    Module.finrank ℚ (t6FineComplex targetZero).H1 = 1 := by
  have hcoarseD0 :
      (t6Presentation.coarseD0Matrix targetZero).rank = 0 := by
    rw [identitySplit_coarseD0Matrix_eq_zero t6Presentation (Or.inr rfl),
      Matrix.rank_zero]
  have hfineD0 :
      (t6Presentation.fineD0Matrix targetZero).rank = 0 := by
    rw [identitySplit_fineD0Matrix_eq_zero t6Presentation (Or.inr rfl),
      Matrix.rank_zero]
  constructor
  · rw [t6Presentation.coarseH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t6_targetZero_selectedEdgeCards.1,
      t6_targetZero_coarseD1_rank, hcoarseD0]
  · rw [t6Presentation.fineH1Finrank_eq_card_sub_rationalMatrixRanks,
      rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank,
      t6_targetZero_selectedEdgeCards.2,
      t6_targetZero_fineD1_rank, hfineD0]

/-- The actual T6 target-zero H¹ comparison is not bijective.

Position: semantic mismatch theorem for fixed GOAL claim (v)(c).  A hypothetical
linear equivalence would identify the independently established dimensions
three and one, yielding a contradiction. -/
theorem t6_targetZero_h1Map_not_bijective :
    ¬ Function.Bijective
      (t6Presentation.toGeometry.aSubnerveComparisonHom
        (↑targetZero : Set (Fin 2))).h1Map := by
  intro hbijective
  let comparisonEquiv := LinearEquiv.ofBijective
    (t6Presentation.toGeometry.aSubnerveComparisonHom
      (↑targetZero : Set (Fin 2))).h1Map hbijective
  have hdim := comparisonEquiv.finrank_eq
  change Module.finrank ℚ (t6CoarseComplex targetZero).H1 =
    Module.finrank ℚ (t6FineComplex targetZero).H1 at hdim
  rw [t6_targetZero_h1_profile.1,
    t6_targetZero_h1_profile.2] at hdim
  omega

/-- The computed T6 target-zero defect is nonzero.

Position: executable defect endpoint for fixed GOAL claim (v)(c).  Correctness
transfers a hypothetical zero computed defect to the actual H¹ map, where it
contradicts the exact dimension-derived nonbijectivity above. -/
theorem t6_targetZero_defect_ne_zero :
    t6Presentation.computedASubnerveDefect targetZero ≠ (0, 0) := by
  intro hzero
  have hsemantic :
      t6Presentation.toGeometry.aSubnerveDefect
          (↑targetZero : Set (Fin 2)) = (0, 0) := by
    rw [← t6Presentation.computedASubnerveDefect_eq_aSubnerveDefect]
    exact hzero
  exact t6_targetZero_h1Map_not_bijective
    ((t6Presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑targetZero : Set (Fin 2))).1 hsemantic)

/-- The generic all-nonempty-subset checker returns false for registered T6.

Position: executable label endpoint for fixed GOAL claim (v)(c).  Its failure
is forced by the proven target-zero nonzero defect, not by an external Stop-B
label or a supplied Boolean. -/
theorem t6_uniformPresentationCheck :
    t6Presentation.uniformPresentationCheck = false := by
  cases hcheck : t6Presentation.uniformPresentationCheck with
  | false => rfl
  | true =>
      have hall :=
        (t6Presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).1
          hcheck
      exact (t6_targetZero_defect_ne_zero
        (hall targetZero (by decide))).elim

/-- Registered T6 fails semantic uniform presentation invariance.

Position: semantic endpoint of fixed GOAL claim (v)(c), obtained from checker
completeness after the exact target-zero quotient-H¹ mismatch has been proved. -/
theorem t6_not_uniformPresentation : ¬ UniformPresentation t6Presentation := by
  intro huniform
  have htrue := t6Presentation.uniformPresentationCheck_eq_true_iff.mpr
    huniform
  rw [t6_uniformPresentationCheck] at htrue
  contradiction

end GLocalV1T3T6Witnesses
end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
