import ResearchLean.AG.AtlasCoefficientFiber.SupportDegenerate
import ResearchLean.AG.AtlasCoefficientFiber.SupportPushforward
import ResearchLean.AG.AtlasCoefficientFiber.QuotientDual

/-!
# G-135 D：原K′/Lの台包含と同じP双対

## Implementation notes

元細chainの包含を原Lによるliteral quotientへ降ろす。
Pとの双対比較は原ε評価の全商代表で証明し、任意の中間商で置き換えない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 原次数0細chain包含を同じL0による商へ降ろす。 -/
def supportQuotient0 : (K0 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL0 M A) →ₗ[ℚ]
    (K0 Nf (comparisonFactor qc qf h ⁻¹' B) ⧸ degenerateL0 M B) :=
  Submodule.mapQ _ _ (selectedInclude Nf.chartSupport (fun _ ht => hab ht))
    (supportDegenerateL0_mem M hab)

/-- 同じ次数0商の全原細chain代表式。 -/
@[simp] theorem supportQuotient0_mk (x : K0 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    supportQuotient0 M hab (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (selectedInclude Nf.chartSupport (fun _ ht => hab ht) x) :=
  Submodule.mapQ_apply _ _ _ x

/-- 原次数1細chain包含を同じL1による商へ降ろす。 -/
def supportQuotient1 : (K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A) →ₗ[ℚ]
    (K1 Nf (comparisonFactor qc qf h ⁻¹' B) ⧸ degenerateL1 M B) :=
  Submodule.mapQ _ _ (selectedInclude Nf.edgeSupport (fun _ ht => hab ht))
    (supportDegenerateL1_mem M hab)

/-- 同じ次数1商の全原細chain代表式。 -/
@[simp] theorem supportQuotient1_mk (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    supportQuotient1 M hab (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x) :=
  Submodule.mapQ_apply _ _ _ x

/-- 原次数2細chain包含を同じL2による商へ降ろす。 -/
def supportQuotient2 : (K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A) →ₗ[ℚ]
    (K2 Nf (comparisonFactor qc qf h ⁻¹' B) ⧸ degenerateL2 M B) :=
  Submodule.mapQ _ _ (selectedInclude Nf.faceSupport (fun _ ht => hab ht))
    (supportDegenerateL2_mem M hab)

/-- 同じ次数2商の全原細chain代表式。 -/
@[simp] theorem supportQuotient2_mk (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    supportQuotient2 M hab (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (selectedInclude Nf.faceSupport (fun _ ht => hab ht) x) :=
  Submodule.mapQ_apply _ _ _ x

/-- 原商微分1は同じ細微分を介して台包含と可換。 -/
theorem supportQuotient_boundary1
    (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A) :
    supportQuotient0 M hab (quotientBoundary1 M A x) =
      quotientBoundary1 M B (supportQuotient1 M hab x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    calc
      supportQuotient0 M hab (quotientBoundary1 M A (Submodule.Quotient.mk x)) =
          supportQuotient0 M hab (Submodule.Quotient.mk (chainD1 Nf _ x)) :=
        congrArg (supportQuotient0 M hab) (quotientBoundary1_mk M A x)
      _ = Submodule.Quotient.mk (selectedInclude Nf.chartSupport (fun _ ht => hab ht) (chainD1 Nf _ x)) :=
        supportQuotient0_mk M hab _
      _ = Submodule.Quotient.mk (chainD1 Nf _ (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x)) :=
        congrArg Submodule.Quotient.mk
          (LinearMap.congr_fun (supportChainInclude_boundary1 Nf (fun _ ht => hab ht)) x)
      _ = quotientBoundary1 M B (Submodule.Quotient.mk (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x)) :=
        (quotientBoundary1_mk M B _).symm
      _ = quotientBoundary1 M B (supportQuotient1 M hab (Submodule.Quotient.mk x)) :=
        congrArg (quotientBoundary1 M B) (supportQuotient1_mk M hab x).symm

/-- 原商微分2は同じ細微分を介して台包含と可換。 -/
theorem supportQuotient_boundary2
    (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A) :
    supportQuotient1 M hab (quotientBoundary2 M A x) =
      quotientBoundary2 M B (supportQuotient2 M hab x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    calc
      supportQuotient1 M hab (quotientBoundary2 M A (Submodule.Quotient.mk x)) =
          supportQuotient1 M hab (Submodule.Quotient.mk (chainD2 Nf _ x)) :=
        congrArg (supportQuotient1 M hab) (quotientBoundary2_mk M A x)
      _ = Submodule.Quotient.mk (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (chainD2 Nf _ x)) :=
        supportQuotient1_mk M hab _
      _ = Submodule.Quotient.mk (chainD2 Nf _ (selectedInclude Nf.faceSupport (fun _ ht => hab ht) x)) :=
        congrArg Submodule.Quotient.mk
          (LinearMap.congr_fun (supportChainInclude_boundary2 Nf (fun _ ht => hab ht)) x)
      _ = quotientBoundary2 M B (Submodule.Quotient.mk (selectedInclude Nf.faceSupport (fun _ ht => hab ht) x)) :=
        (quotientBoundary2_mk M B _).symm
      _ = quotientBoundary2 M B (supportQuotient2 M hab (Submodule.Quotient.mk x)) :=
        congrArg (quotientBoundary2 M B) (supportQuotient2_mk M hab x).symm

/-- 原P0≃(K′0/L0)*は同じ原商包含と元εに対して自然。 -/
theorem supportEvaluationQuotientDual0 (z : (pushforwardComplex M B).C0)
    (x : K0 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL0 M A) :
    evaluationQuotientDual0 M A (supportPushforward0 M hab z) x =
      evaluationQuotientDual0 M B z (supportQuotient0 M hab x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    calc
      evaluationQuotientDual0 M A (supportPushforward0 M hab z) (Submodule.Quotient.mk x) =
          freeDualEquiv _ (evaluation0 M A (supportPushforward0 M hab z)) x :=
        evaluationQuotientDual0_mk M A _ x
      _ = freeDualEquiv _ (selectedRestrict Nf.chartSupport (fun _ ht => hab ht) (evaluation0 M B z)) x :=
        congrArg (fun f => freeDualEquiv _ f x) (supportEvaluation0 M hab z)
      _ = freeDualEquiv _ (evaluation0 M B z)
          (selectedInclude Nf.chartSupport (fun _ ht => hab ht) x) := by
        rw [selectedRestrict_eq_dual]
        exact dualCellMap_dual (selectedInclude Nf.chartSupport (fun _ ht => hab ht))
          (evaluation0 M B z) x
      _ = evaluationQuotientDual0 M B z
          (Submodule.Quotient.mk (selectedInclude Nf.chartSupport (fun _ ht => hab ht) x)) :=
        (evaluationQuotientDual0_mk M B z _).symm
      _ = evaluationQuotientDual0 M B z (supportQuotient0 M hab (Submodule.Quotient.mk x)) :=
        congrArg (evaluationQuotientDual0 M B z) (supportQuotient0_mk M hab x).symm

/-- 原P1≃(K′1/L1)*は同じ原商包含と元εに対して自然。 -/
theorem supportEvaluationQuotientDual1 (z : (pushforwardComplex M B).C1)
    (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A) :
    evaluationQuotientDual1 M A (supportPushforward1 M hab z) x =
      evaluationQuotientDual1 M B z (supportQuotient1 M hab x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    calc
      evaluationQuotientDual1 M A (supportPushforward1 M hab z) (Submodule.Quotient.mk x) =
          freeDualEquiv _ (evaluation1 M A (supportPushforward1 M hab z)) x :=
        evaluationQuotientDual1_mk M A _ x
      _ = freeDualEquiv _ (selectedRestrict Nf.edgeSupport (fun _ ht => hab ht) (evaluation1 M B z)) x :=
        congrArg (fun f => freeDualEquiv _ f x) (supportEvaluation1 M hab z)
      _ = freeDualEquiv _ (evaluation1 M B z)
          (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x) := by
        rw [selectedRestrict_eq_dual]
        exact dualCellMap_dual (selectedInclude Nf.edgeSupport (fun _ ht => hab ht))
          (evaluation1 M B z) x
      _ = evaluationQuotientDual1 M B z
          (Submodule.Quotient.mk (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x)) :=
        (evaluationQuotientDual1_mk M B z _).symm
      _ = evaluationQuotientDual1 M B z (supportQuotient1 M hab (Submodule.Quotient.mk x)) :=
        congrArg (evaluationQuotientDual1 M B z) (supportQuotient1_mk M hab x).symm

/-- 原P2≃(K′2/L2)*は同じ原商包含と元εに対して自然。 -/
theorem supportEvaluationQuotientDual2 (z : (pushforwardComplex M B).C2)
    (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A) :
    evaluationQuotientDual2 M A (supportPushforward2 M hab z) x =
      evaluationQuotientDual2 M B z (supportQuotient2 M hab x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    calc
      evaluationQuotientDual2 M A (supportPushforward2 M hab z) (Submodule.Quotient.mk x) =
          freeDualEquiv _ (evaluation2 M A (supportPushforward2 M hab z)) x :=
        evaluationQuotientDual2_mk M A _ x
      _ = freeDualEquiv _ (selectedRestrict Nf.faceSupport (fun _ ht => hab ht) (evaluation2 M B z)) x :=
        congrArg (fun f => freeDualEquiv _ f x) (supportEvaluation2 M hab z)
      _ = freeDualEquiv _ (evaluation2 M B z)
          (selectedInclude Nf.faceSupport (fun _ ht => hab ht) x) := by
        rw [selectedRestrict_eq_dual]
        exact dualCellMap_dual (selectedInclude Nf.faceSupport (fun _ ht => hab ht))
          (evaluation2 M B z) x
      _ = evaluationQuotientDual2 M B z
          (Submodule.Quotient.mk (selectedInclude Nf.faceSupport (fun _ ht => hab ht) x)) :=
        (evaluationQuotientDual2_mk M B z _).symm
      _ = evaluationQuotientDual2 M B z (supportQuotient2 M hab (Submodule.Quotient.mk x)) :=
        congrArg (evaluationQuotientDual2 M B z) (supportQuotient2_mk M hab x).symm

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient0
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient0_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient1
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient1_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient2
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient2_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient_boundary1
#print axioms AAT.AG.AtlasCoefficientFiber.supportQuotient_boundary2
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationQuotientDual0
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationQuotientDual1
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationQuotientDual2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
