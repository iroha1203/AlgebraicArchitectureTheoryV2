import ResearchLean.AG.FaceRelationSubdivision.PresentationRawEquivalence
import ResearchLean.AG.FaceRelationSubdivision.PresentationInverse

/-!
# 同じreadingの原始表示逆と有限列出力

## Implementation notes

原始全単射の逆を全三セル名・零補正で照合する。
逆Law診断から原始表示を選ぶ案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source} {N M : TargetSupportedNerve q}
namespace CellPresentationEquiv
variable (E : CellPresentationEquiv q q (Reading.coarserThan_refl q) N M)

/-- 原始表示逆の出力は同じ有限和二方向交換である。 -/
theorem rawEquivalence_symmSelf : E.rawEquivalence.symm = E.symmSelf.rawEquivalence := by
  apply RawChainEquivalence.ext
  · apply SupportedBasisMap.ext
    intro x
    simp only [RawChainEquivalence.symm_r0, rawEquivalence_s0, rawEquivalence_r0,
      sourceS0_basis, sourceR0_basis, symmSelf_chart]
  · apply SupportedBasisMap.ext
    intro x
    simp only [RawChainEquivalence.symm_r1, rawEquivalence_s1, rawEquivalence_r1,
      sourceS1_basis, sourceR1_basis, symmSelf_edge]
  · apply SupportedBasisMap.ext
    intro x
    simp only [RawChainEquivalence.symm_r2, rawEquivalence_s2, rawEquivalence_r2,
      sourceS2_basis, sourceR2_basis, symmSelf_face]
  · apply SupportedBasisMap.ext
    intro x
    simp only [RawChainEquivalence.symm_s0, rawEquivalence_r0, rawEquivalence_s0,
      sourceR0_basis, sourceS0_basis, symmSelf_chart, Equiv.symm_symm]
  · apply SupportedBasisMap.ext
    intro x
    simp only [RawChainEquivalence.symm_s1, rawEquivalence_r1, rawEquivalence_s1,
      sourceR1_basis, sourceS1_basis, symmSelf_edge, Equiv.symm_symm]
  · apply SupportedBasisMap.ext
    intro x
    simp only [RawChainEquivalence.symm_s2, rawEquivalence_r2, rawEquivalence_s2,
      sourceR2_basis, sourceS2_basis, symmSelf_face, Equiv.symm_symm]
  · simp only [RawChainEquivalence.symm_h0, rawEquivalence_k0, rawEquivalence_h0]
  · simp only [RawChainEquivalence.symm_h1, rawEquivalence_k1, rawEquivalence_h1]
  · simp only [RawChainEquivalence.symm_k0, rawEquivalence_h0, rawEquivalence_k0]
  · simp only [RawChainEquivalence.symm_k1, rawEquivalence_h1, rawEquivalence_k1]
end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
