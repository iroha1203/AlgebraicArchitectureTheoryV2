import ResearchLean.AG.AtlasCoefficientFiber.DualShortExact
import ResearchLean.AG.AtlasCoefficientFiber.RestrictionHomology
import ResearchLean.AG.AtlasDefectComposition.ConeHomologySequence
import Mathlib.Algebra.Homology.HomologySequence

/-!
# G-135 B：実短完全列の連結射と五項列

指定された実εとL双対制限の短完全列へmathlibのhomology sequenceを適用する。
Rとの同定は原κから構成済みの同型を使う。

## Implementation notes

連結射は標準ShortExact.δから独立に生成する。三つの隣接完全性は同じ標準列を
可逆座標同定で移す。完全性や単射性を新しい入力fieldへ置く案は採用しない。
carrier filtrationとの同定は後続構成の未完義務としてreportへ記録する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ実εの標準一次homology射。 -/
def evaluationH1 : (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) →ₗ[ℚ]
    (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) 1).hom

/-- 同じ実制限の標準一次homology射を原始Rへ移す。 -/
def fiberRestrictionH1 :
    (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) →ₗ[ℚ]
      R M A :=
  (restrictionStandardHomologyREquiv M A).toLinearMap.comp
    (HomologicalComplex.homologyMap (zeroExtensionMap (restrictionHom M A)) 1).hom

/-- 同じ短完全列の標準連結射を指定R上へ移したτ。 -/
def connectingTau : R M A →ₗ[ℚ] (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ) :=
  ((evaluationRestriction_shortExact M A).δ (1 : ℤ) 2 (by rfl)).hom.comp
    (restrictionStandardHomologyREquiv M A).symm.toLinearMap

/-- 同じ実εの標準二次homology射。 -/
def evaluationH2 : (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ) →ₗ[ℚ]
    (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (2 : ℤ) :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) 2).hom

/-- τは同じ標準δを指定Rの逆座標へ評価する。 -/
@[simp] theorem connectingTau_apply (z : R M A) :
    connectingTau M A z = (evaluationRestriction_shortExact M A).δ (1 : ℤ) 2 (by rfl)
      ((restrictionStandardHomologyREquiv M A).symm z) := rfl

/-- 実制限をRへ移す射の所有評価API。 -/
@[simp] theorem fiberRestrictionH1_apply
    (z : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ)) :
    fiberRestrictionH1 M A z = restrictionStandardHomologyREquiv M A
      (HomologicalComplex.homologyMap (zeroExtensionMap (restrictionHom M A)) 1 z) := rfl

/-- 実εの一次射を標準homology mapへ評価する所有API。 -/
@[simp] theorem evaluationH1_apply
    (z : (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ)) :
    evaluationH1 M A z = HomologicalComplex.homologyMap
      (zeroExtensionMap (evaluationHom M A)) 1 z := rfl

/-- 実εの二次射を標準homology mapへ評価する所有API。 -/
@[simp] theorem evaluationH2_apply
    (z : (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ)) :
    evaluationH2 M A z = HomologicalComplex.homologyMap
      (zeroExtensionMap (evaluationHom M A)) 2 z := rfl

/-- 指定Rへの同定を戻すとτは標準δそのものである。 -/
@[simp] theorem connectingTau_restrictionStandardHomologyREquiv
    (z : (zeroExtension (restrictionComplex M A)).homology (1 : ℤ)) :
    connectingTau M A (restrictionStandardHomologyREquiv M A z) =
      (evaluationRestriction_shortExact M A).δ (1 : ℤ) 2 (by rfl) z := by
  rw [connectingTau_apply, LinearEquiv.symm_apply_apply]

/-- 原始H⁰Q零性から、同じ実εのH¹射が単射となる。 -/
theorem evaluationH1_injective : Function.Injective (evaluationH1 M A) := by
  have he := (evaluationRestriction_shortExact M A).homology_exact₁ (0 : ℤ) 1 (by rfl)
  have hz : (evaluationRestriction_shortExact M A).δ (0 : ℤ) 1 (by rfl) = 0 :=
    (restrictionComplex_H0_isZero M A).eq_of_src _ _
  have hm := he.mono_g hz
  exact (ModuleCat.mono_iff_injective _).mp hm

/-- 指定五項列のH¹P、H¹C′、Rでの完全性。 -/
theorem fiveTerm_exact_at_fineH1 : Function.Exact (evaluationH1 M A) (fiberRestrictionH1 M A) := by
  have he := (evaluationRestriction_shortExact M A).homology_exact₂ (1 : ℤ)
  exact transportShortComplex_exact _ (Iso.refl _) (Iso.refl _)
    (restrictionStandardHomologyREquiv M A).toModuleIso he

/-- 指定五項列のH¹C′、R、H²Pでの完全性。 -/
theorem fiveTerm_exact_at_fiber : Function.Exact (fiberRestrictionH1 M A) (connectingTau M A) := by
  have he := (evaluationRestriction_shortExact M A).homology_exact₃ (1 : ℤ) 2 (by rfl)
  exact transportShortComplex_exact _ (Iso.refl _)
    (restrictionStandardHomologyREquiv M A).toModuleIso (Iso.refl _) he

/-- 指定五項列のR、H²P、H²C′での完全性。 -/
theorem fiveTerm_exact_at_pushforwardH2 : Function.Exact (connectingTau M A) (evaluationH2 M A) := by
  have he := (evaluationRestriction_shortExact M A).homology_exact₁ (1 : ℤ) 2 (by rfl)
  exact transportShortComplex_exact _ (restrictionStandardHomologyREquiv M A).toModuleIso
    (Iso.refl _) (Iso.refl _) he

/-- 最初の二射の合成は零。 -/
theorem fiberRestrictionH1_evaluationH1 :
    (fiberRestrictionH1 M A).comp (evaluationH1 M A) = 0 :=
  (fiveTerm_exact_at_fineH1 M A).linearMap_comp_eq_zero

/-- Rへの制限と標準連結射の合成は零。 -/
theorem connectingTau_fiberRestrictionH1 :
    (connectingTau M A).comp (fiberRestrictionH1 M A) = 0 :=
  (fiveTerm_exact_at_fiber M A).linearMap_comp_eq_zero

/-- 連結射と実εの二次射の合成は零。 -/
theorem evaluationH2_connectingTau :
    (evaluationH2 M A).comp (connectingTau M A) = 0 :=
  (fiveTerm_exact_at_pushforwardH2 M A).linearMap_comp_eq_zero

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH1
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRestrictionH1
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH2
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_apply
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRestrictionH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_restrictionStandardHomologyREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH1_injective
#print axioms AAT.AG.AtlasCoefficientFiber.fiveTerm_exact_at_fineH1
#print axioms AAT.AG.AtlasCoefficientFiber.fiveTerm_exact_at_fiber
#print axioms AAT.AG.AtlasCoefficientFiber.fiveTerm_exact_at_pushforwardH2
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRestrictionH1_evaluationH1
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_fiberRestrictionH1
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH2_connectingTau
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
