import ResearchLean.AG.FaceRelationSubdivision.RawChainEquivalence

/-!
# 原始正逆有限和と二補正の括弧づけ

## Implementation notes

出力の等号は原始有限和の等号で検査し、台proofやchain式proofの選択はdataにしない。
H1だけの括弧づけ一致で代替する案は二補正の構成を確認できないため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q0 q1 q2 q3 : Reading Source}
variable {N0 : TargetSupportedNerve q0} {N1 : TargetSupportedNerve q1}
variable {N2 : TargetSupportedNerve q2} {N3 : TargetSupportedNerve q3}
namespace RawChainEquivalence

/-- 二つの原始補正も含め、三段の括弧づけ変更で出力は一致。 -/
theorem trans_assoc (P : RawChainEquivalence N0 N1) (Q : RawChainEquivalence N1 N2)
    (R : RawChainEquivalence N2 N3) : (P.trans Q).trans R = P.trans (Q.trans R) := by
  apply ext
  all_goals apply SupportedBasisMap.ext_raw
  all_goals simp only [trans_r0, trans_r1, trans_r2, trans_s0, trans_s1, trans_s2,
    trans_h0, trans_h1, trans_k0, trans_k1, composedH0_raw, composedH1_raw,
    symm_r0, symm_r1, symm_s1, symm_s2, symm_h0, symm_h1,
    SupportedBasisMap.raw_comp, LinearMap.comp_assoc, LinearMap.comp_add, LinearMap.add_comp,
    add_assoc]

/-- 空列を左に付けても同じ原始出力。 -/
theorem refl_trans (P : RawChainEquivalence N0 N1) : (refl N0).trans P = P := by
  apply ext
  all_goals apply SupportedBasisMap.ext_raw
  all_goals simp only [trans_r0, trans_r1, trans_r2, trans_s0, trans_s1, trans_s2,
    trans_h0, trans_h1, trans_k0, trans_k1, composedH0_raw, composedH1_raw,
    symm_r0, symm_r1, symm_s1, symm_s2, symm_h0, symm_h1,
    refl_r0, refl_r1, refl_r2, refl_s0, refl_s1, refl_s2, refl_h0, refl_h1, refl_k0, refl_k1,
    SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero,
    LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, zero_add]

/-- 空列を右に付けても同じ原始出力。 -/
theorem trans_refl (P : RawChainEquivalence N0 N1) : P.trans (refl N1) = P := by
  apply ext
  all_goals apply SupportedBasisMap.ext_raw
  all_goals simp only [trans_r0, trans_r1, trans_r2, trans_s0, trans_s1, trans_s2,
    trans_h0, trans_h1, trans_k0, trans_k1, composedH0_raw, composedH1_raw,
    symm_r0, symm_r1, symm_s1, symm_s2, symm_h0, symm_h1,
    refl_r0, refl_r1, refl_r2, refl_s0, refl_s1, refl_s2, refl_h0, refl_h1, refl_k0, refl_k1,
    SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero,
    LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, zero_add]

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
