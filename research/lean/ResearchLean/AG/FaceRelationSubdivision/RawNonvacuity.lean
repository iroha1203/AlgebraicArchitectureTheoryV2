import ResearchLean.AG.FaceRelationSubdivision.RawChainEquivalence
import ResearchLean.AG.FaceRelationSubdivision.ElementaryRawEquivalence

/-!
# 原始有限列出力の非空性と零表の失敗

## Implementation notes

正操作は原始入力から出力を構成済み。零r/s/補正という偽の出力は
非空chartの基底に対する往復式を満たせないことを別に検査する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence

/-- 非空chartがある原始入力では零r/s/粗側補正は出力certificateにならない。 -/
theorem not_zero_chart_output (P : RawChainEquivalence Nc Nf) (v : Nc.nerve.Chart)
    (hr : P.r0 = SupportedBasisMap.zero _ _) (hs : P.s0 = SupportedBasisMap.zero _ _)
    (hk : P.k0 = SupportedBasisMap.zero _ _) : False := by
  have he := LinearMap.congr_fun P.rs_k0 (Finsupp.single v 1)
  simp only [hr, hs, hk, SupportedBasisMap.raw_zero, LinearMap.comp_zero,
    zero_add, LinearMap.zero_apply, LinearMap.id_apply] at he
  have hv := congrArg (fun x : Nc.nerve.Chart →₀ ℚ => x v) he
  simp only [Finsupp.zero_apply, Finsupp.single_eq_same] at hv
  norm_num at hv

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
