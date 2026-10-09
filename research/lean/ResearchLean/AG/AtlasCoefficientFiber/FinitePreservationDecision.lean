import ResearchLean.AG.AtlasCoefficientFiber.NativeDiagnosticMatrices
import ResearchLean.AG.AtlasCoefficientFiber.FiniteTauDecision
import ResearchLean.AG.AtlasCoefficientFiber.DefectDiagnostics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite preservation decisions for the same original comparisons

Position: G-135 E, J and preservation over all A and all occurrence labels.
The executable kernel reads rational source/target homology projectors and
the actual generated comparison matrix. C19 proves these are the original
homology spaces and original map.

## Implementation notes

Native Set-selected cell enumeration is noncomputable transport; the rank
and Bool kernel is finite rational arithmetic. All A are enumerated as all
Finsets of the input-generated finite target, then returned to all Sets.
Law uses the original occurrence-label type and actual generated comparison;
identical supports are not deduplicated. No finite instance on all Law values,
expected rank, or preservation certificate is required.
-/
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open Matrix RationalCoordinates
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra
universe u

/-- E computable actual dimensions minus actual map rank, retaining the
source/target projections instead of ambient row/column counts. -/
def rationalProjectionDefect {I J : Type u} [Fintype I] [Fintype J]
    (p : Matrix I I ℚ) (q : Matrix J J ℚ) (t : Matrix J I ℚ) : ℕ × ℕ :=
  (rationalMatrixRank p - rationalMatrixRank t,
    rationalMatrixRank q - rationalMatrixRank t)

/-- E finite rational kernel for preservation of the represented actual map. -/
def rationalPreservationDecision {I J : Type u} [Fintype I] [Fintype J]
    (p : Matrix I I ℚ) (q : Matrix J J ℚ) (t : Matrix J I ℚ) : Bool :=
  decide (rationalProjectionDefect p q t = (0,0))

/-- Owner Bool correspondence refers to the same computed dimension pair. -/
theorem rationalPreservationDecision_eq_true_iff {I J : Type u} [Fintype I] [Fintype J]
    (p : Matrix I I ℚ) (q : Matrix J J ℚ) (t : Matrix J I ℚ) :
    rationalPreservationDecision p q t = true ↔ rationalProjectionDefect p q t = (0,0) := by
  simp only [rationalPreservationDecision, decide_eq_true_eq]

/-- E the zero-dimensional empty case uses the same kernel. -/
theorem rationalPreservationDecision_empty :
    rationalPreservationDecision (0 : Matrix (Fin 0) (Fin 0) ℚ)
      (0 : Matrix (Fin 0) (Fin 0) ℚ) (0 : Matrix (Fin 0) (Fin 0) ℚ) = true := by
  decide +kernel

/-- E a retained target class without a comparison preimage fails the same kernel. -/
theorem rationalPreservationDecision_failure :
    rationalPreservationDecision (1 : Matrix (Fin 1) (Fin 1) ℚ)
      (1 : Matrix (Fin 1) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 1) ℚ) = false := by
  decide +kernel

noncomputable section
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

/-- E original coarse/fine d0,d1 and the same F1 generate J for every A. -/
def primitiveDiagnostic (A : Set qc.Target) : ℕ × ℕ := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  letI := Fintype.ofFinite (Nc.EdgeInTargetSubset A)
  letI := Fintype.ofFinite (Nc.FaceInTargetSubset A)
  letI := Fintype.ofFinite (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
  letI := Fintype.ofFinite (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
  letI := Fintype.ofFinite (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
  exact rationalProjectionDefect (cellularH1Projection Nc A)
    (cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A)) (nativeTMatrix M A)

/-- E computed J is exactly the existing original direct comparison defect. -/
theorem primitiveDiagnostic_eq_blockDefect (A : Set qc.Target) :
    primitiveDiagnostic M A = blockDefect (M.aSubnerveComparisonHom A).h1Map := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  letI := Fintype.ofFinite (Nc.EdgeInTargetSubset A)
  letI := Fintype.ofFinite (Nc.FaceInTargetSubset A)
  letI := Fintype.ofFinite (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
  letI := Fintype.ofFinite (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
  letI := Fintype.ofFinite (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
  rw [primitiveDiagnostic, rationalProjectionDefect, ← nativeTMatrix_blockDefect,
    directH1_defect]

/-- E native finite preservation is generated solely by the same primitive J. -/
def primitivePreservationDecision (A : Set qc.Target) : Bool :=
  decide (primitiveDiagnostic M A = (0,0))

/-- E every native Bool is necessary and sufficient for original blockDefect zero. -/
theorem primitivePreservationDecision_eq_true_iff (A : Set qc.Target) :
    primitivePreservationDecision M A = true ↔
      blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) := by
  simp only [primitivePreservationDecision, decide_eq_true_eq, primitiveDiagnostic_eq_blockDefect]

/-- E the same decision is the original coefficient/fiber preservation criterion. -/
theorem primitivePreservationDecision_eq_true_iff_coefficient (A : Set qc.Target) :
    primitivePreservationDecision M A = true ↔
      Function.Bijective (unitH1 M A) ∧ Function.Injective (connectingTau M A) :=
  (primitivePreservationDecision_eq_true_iff M A).trans (coefficient_zeroDefect_iff M A)

variable [Fintype Source]

/-- E finite all-A kernel generated by the finite Source and surjective reading. -/
def allAPreservationDecision : Bool := by
  classical
  letI := readingTarget_finite qc
  letI := Fintype.ofFinite qc.Target
  exact finiteFamilyDecision (fun s : Finset qc.Target => primitivePreservationDecision M s)

/-- E all finite subsets are exactly all original Sets, including the empty Set. -/
theorem allAPreservationDecision_eq_true_iff :
    allAPreservationDecision M = true ↔
      ∀ A : Set qc.Target, blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) := by
  classical
  letI := readingTarget_finite qc
  letI := Fintype.ofFinite qc.Target
  rw [allAPreservationDecision, finiteFamilyDecision_eq_true_iff]
  simp only [primitivePreservationDecision_eq_true_iff]
  exact allFinsets_iff_allSets (fun A => blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))

variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- E all original occurrence labels retain multiplicity in the finite decision. -/
def lawPreservationDecision : Bool :=
  finiteFamilyDecision (fun l : LawValueLabel laws =>
    primitivePreservationDecision M (labelValueFiber laws qc ha l))

/-- E each occurrence label has the same original block comparison and defect. -/
theorem lawPreservationDecision_eq_true_iff_labels :
    lawPreservationDecision M laws ha = true ↔ ∀ l : LawValueLabel laws,
      blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l)).h1Map = (0,0) := by
  rw [lawPreservationDecision, finiteFamilyDecision_eq_true_iff]
  exact forall_congr' (fun l => primitivePreservationDecision_eq_true_iff M _)

/-- E original Law defect is zero exactly when every original occurrence block
is zero; nonnegative sums preserve duplicate supports and empty families. -/
theorem lawBlockDefect_zero_iff_labels :
    blockDefect (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha)) = (0,0) ↔
      ∀ l : LawValueLabel laws,
        blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l)).h1Map = (0,0) := by
  classical
  rw [lawH1Defect_subset_sum]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · rintro ⟨hs, ht⟩ l
    exact Prod.ext (hs l) (ht l)
  · intro hh
    exact ⟨fun l => congrArg Prod.fst (hh l), fun l => congrArg Prod.snd (hh l)⟩

/-- E finite label preservation is necessary and sufficient for the same
existing generated Law blockDefect, with no finiteness on all Value types. -/
theorem lawPreservationDecision_eq_true_iff :
    lawPreservationDecision M laws ha = true ↔
      blockDefect (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha)) = (0,0) :=
  (lawPreservationDecision_eq_true_iff_labels M laws ha).trans
    (lawBlockDefect_zero_iff_labels M laws ha).symm

/-- E the computed Law diagnostic keeps each occurrence summand exactly once. -/
def primitiveLawDiagnostic : ℕ × ℕ :=
  (∑ l : LawValueLabel laws, (primitiveDiagnostic M (labelValueFiber laws qc ha l)).1,
    ∑ l : LawValueLabel laws, (primitiveDiagnostic M (labelValueFiber laws qc ha l)).2)

/-- E the full computed pair agrees with the same existing generated Law defect. -/
theorem primitiveLawDiagnostic_eq_blockDefect :
    primitiveLawDiagnostic M laws ha =
      blockDefect (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha)) := by
  rw [primitiveLawDiagnostic, lawH1Defect_subset_sum]
  simp only [primitiveDiagnostic_eq_blockDefect]

end
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.rationalProjectionDefect
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPreservationDecision
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPreservationDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPreservationDecision_empty
#print axioms AAT.AG.AtlasCoefficientFiber.rationalPreservationDecision_failure
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveDiagnostic
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveDiagnostic_eq_blockDefect
#print axioms AAT.AG.AtlasCoefficientFiber.primitivePreservationDecision
#print axioms AAT.AG.AtlasCoefficientFiber.primitivePreservationDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.primitivePreservationDecision_eq_true_iff_coefficient
#print axioms AAT.AG.AtlasCoefficientFiber.allAPreservationDecision
#print axioms AAT.AG.AtlasCoefficientFiber.allAPreservationDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.lawPreservationDecision
#print axioms AAT.AG.AtlasCoefficientFiber.lawPreservationDecision_eq_true_iff_labels
#print axioms AAT.AG.AtlasCoefficientFiber.lawBlockDefect_zero_iff_labels
#print axioms AAT.AG.AtlasCoefficientFiber.lawPreservationDecision_eq_true_iff
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveLawDiagnostic
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveLawDiagnostic_eq_blockDefect

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
