import ResearchLean.AG.AtlasCoefficientFiber.WitnessTwoComparison
import ResearchLean.AG.AtlasCoefficientFiber.WitnessTwoCoefficients

/-!
# G-135 W2：独立Pの全三次数原始座標

## Implementation notes

Pは原右Kanのまま、構成済み原ηの逆から粗原始表へ同定する。
原Kanから生成されたη逆を使い、Pを粗複体として選び直す方法は元順像を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessTwo
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 独立生成Pと粗原始表の全三次数両逆。 -/
def pNamedEquiv (A : Set Bool) (hA : A.Nonempty) : ThreeCochainComplex.CochainEquiv
    (pushforwardComplex M A) (namedComplex Nc) where
  e0 := (etaEquiv A).e0.symm.trans (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e0
  e1 := (etaEquiv A).e1.symm.trans (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1
  e2 := (etaEquiv A).e2.symm.trans (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e2
  comm0 z := by
    change (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 ((etaEquiv A).symm.e1 ((pushforwardComplex M A).d0 z)) =
      (namedComplex Nc).d0 ((fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e0 ((etaEquiv A).symm.e0 z))
    rw [(etaEquiv A).symm.comm0,(fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).comm0]
  comm1 z := by
    change (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e2 ((etaEquiv A).symm.e2 ((pushforwardComplex M A).d1 z)) =
      (namedComplex Nc).d1 ((fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 ((etaEquiv A).symm.e1 z))
    rw [(etaEquiv A).symm.comm1,(fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).comm1]

/-- 元ηと原P座標の全三成分square。 -/
theorem eta_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (unitHom M A) (pNamedEquiv A hA).toHom =
      (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z
  · change (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e0 ((etaEquiv A).e0.symm ((etaEquiv A).e0 z)) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
  · change (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 ((etaEquiv A).e1.symm ((etaEquiv A).e1 z)) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
  · change (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e2 ((etaEquiv A).e2.symm ((etaEquiv A).e2 z)) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
/-- 元εの原始r0/r1/r2との全三成分square。 -/
theorem epsilon_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (evaluationHom M A)
      (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
    cochainComp (pNamedEquiv A hA).toHom (incidenceNamedHom M) := by
  have hs : cochainComp (cochainComp (unitHom M A) (evaluationHom M A))
      (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
      cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom M) := by
    rw [← aSubnerveComparisonHom_factorization]
    exact subset_square A hA
  apply cochain_ext <;> apply LinearMap.ext <;> intro z
  · have h := congrArg (fun f => f.f0 ((etaEquiv A).e0.symm z)) hs
    change (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).e0
      ((evaluationHom M A).f0 ((etaEquiv A).e0 ((etaEquiv A).e0.symm z))) =
        (incidenceNamedHom M).f0 ((fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e0 ((etaEquiv A).e0.symm z)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  · have h := congrArg (fun f => f.f1 ((etaEquiv A).e1.symm z)) hs
    change (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).e1
      ((evaluationHom M A).f1 ((etaEquiv A).e1 ((etaEquiv A).e1.symm z))) =
        (incidenceNamedHom M).f1 ((fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 ((etaEquiv A).e1.symm z)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  · have h := congrArg (fun f => f.f2 ((etaEquiv A).e2.symm z)) hs
    change (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).e2
      ((evaluationHom M A).f2 ((etaEquiv A).e2 ((etaEquiv A).e2.symm z))) =
        (incidenceNamedHom M).f2 ((fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e2 ((etaEquiv A).e2.symm z)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h

end AAT.AG.AtlasCoefficientFiber.WitnessTwo
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.pNamedEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.eta_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.epsilon_square
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessTwo
