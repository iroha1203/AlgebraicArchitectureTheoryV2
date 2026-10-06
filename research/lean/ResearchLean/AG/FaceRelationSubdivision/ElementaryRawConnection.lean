import ResearchLean.AG.FaceRelationSubdivision.ElementaryRawEquivalence
import ResearchLean.AG.FaceRelationSubdivision.RawLawHomotopy
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom
import ResearchLean.AG.FaceRelationSubdivision.ElementaryLawMaps

/-!
# 有限列正基本操作の同じ実射と受理済み基本比較

## Implementation notes

Source台へ移した原始表を公開成分APIで既存の独立Law射・subset収縮に照合する。
新しい有限列の比較を既存比較と別物のまま使う案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
/-- 有限列の正操作実subset Rは受理済み同じ原始収縮射。 -/
theorem rawEquivalence_targetR_eq (A : Set q.Target) :
    (rawEquivalence N e).targetRHom A A rfl = (chainContraction N e A).rHom := by
  have h : (rawEquivalence N e).targetRHom A A rfl =
      subsetFiniteHom (r0 N e) (r1 N e) (r2 N e) (r_comm01 N e) (r_comm12 N e) A := by
    apply cochain_ext
    · rw [RawChainEquivalence.targetRHom_f0, rawEquivalence_r0,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f0]
    · rw [RawChainEquivalence.targetRHom_f1, rawEquivalence_r1,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f1]
    · rw [RawChainEquivalence.targetRHom_f2, rawEquivalence_r2,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f2]
  exact h.trans (rSubsetFiniteHom_eq N e A)
/-- 有限列の正操作実subset Sは受理済み同じ原始収縮射。 -/
theorem rawEquivalence_targetS_eq (A : Set q.Target) :
    (rawEquivalence N e).targetSHom A A rfl = (chainContraction N e A).sHom := by
  have h : (rawEquivalence N e).targetSHom A A rfl =
      subsetFiniteHom (s0 N e) (s1 N e) (s2 N e) (s_comm01 N e) (s_comm12 N e) A := by
    apply cochain_ext
    · rw [RawChainEquivalence.targetSHom_f0, rawEquivalence_s0,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f0]
    · rw [RawChainEquivalence.targetSHom_f1, rawEquivalence_s1,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f1]
    · rw [RawChainEquivalence.targetSHom_f2, rawEquivalence_s2,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f2]
  exact h.trans (sSubsetFiniteHom_eq N e A)
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
/-- 有限列正操作の実Law Rは受理済み同じ独立原始Law射。 -/
theorem rawEquivalence_lawR_eq : (rawEquivalence N e).lawR laws ha ha = lawR N e laws ha := by
  apply cochain_ext
  · rw [RawChainEquivalence.lawR_f0, rawEquivalence_r0,
      SupportedBasisMap.toSource_mixedLawDual, lawR_f0]
  · rw [RawChainEquivalence.lawR_f1, rawEquivalence_r1,
      SupportedBasisMap.toSource_mixedLawDual, lawR_f1]
  · rw [RawChainEquivalence.lawR_f2, rawEquivalence_r2,
      SupportedBasisMap.toSource_mixedLawDual, lawR_f2]
/-- 有限列正操作の実Law Sは受理済み同じ独立原始Law射。 -/
theorem rawEquivalence_lawS_eq : (rawEquivalence N e).lawS laws ha ha = lawS N e laws ha := by
  apply cochain_ext
  · rw [RawChainEquivalence.lawS_f0, rawEquivalence_s0,
      SupportedBasisMap.toSource_mixedLawDual, lawS_f0]
  · rw [RawChainEquivalence.lawS_f1, rawEquivalence_s1,
      SupportedBasisMap.toSource_mixedLawDual, lawS_f1]
  · rw [RawChainEquivalence.lawS_f2, rawEquivalence_s2,
      SupportedBasisMap.toSource_mixedLawDual, lawS_f2]
omit [Fintype Source] in
/-- 有限列正操作の同じ実Law補正0も受理済み原始補正。 -/
theorem rawEquivalence_lawH0_eq :
    (rawEquivalence N e).h0.mixedLawDual laws ha ha = lawH0 N e laws ha := by
  rw [rawEquivalence_h0, SupportedBasisMap.toSource_mixedLawDual, lawH0_eq]
omit [Fintype Source] in
/-- 有限列正操作の同じ実Law補正1も受理済み原始補正。 -/
theorem rawEquivalence_lawH1_eq :
    (rawEquivalence N e).h1.mixedLawDual laws ha ha = lawH1 N e laws ha := by
  rw [rawEquivalence_h1, SupportedBasisMap.toSource_mixedLawDual, lawH1_eq]
end TriangleAddition
namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
/-- 有限列の正操作実subset Rは受理済み同じ原始収縮射。 -/
theorem rawEquivalence_targetR_eq (A : Set q.Target) :
    (rawEquivalence N e).targetRHom A A rfl = (chainContraction N e A).rHom := by
  have h : (rawEquivalence N e).targetRHom A A rfl =
      subsetFiniteHom (r0 N e) (r1 N e) (r2 N e) (r_comm01 N e) (r_comm12 N e) A := by
    apply cochain_ext
    · rw [RawChainEquivalence.targetRHom_f0, rawEquivalence_r0,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f0]
    · rw [RawChainEquivalence.targetRHom_f1, rawEquivalence_r1,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f1]
    · rw [RawChainEquivalence.targetRHom_f2, rawEquivalence_r2,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f2]
  exact h.trans (rSubsetFiniteHom_eq N e A)
/-- 有限列の正操作実subset Sは受理済み同じ原始収縮射。 -/
theorem rawEquivalence_targetS_eq (A : Set q.Target) :
    (rawEquivalence N e).targetSHom A A rfl = (chainContraction N e A).sHom := by
  have h : (rawEquivalence N e).targetSHom A A rfl =
      subsetFiniteHom (s0 N e) (s1 N e) (s2 N e) (s_comm01 N e) (s_comm12 N e) A := by
    apply cochain_ext
    · rw [RawChainEquivalence.targetSHom_f0, rawEquivalence_s0,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f0]
    · rw [RawChainEquivalence.targetSHom_f1, rawEquivalence_s1,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f1]
    · rw [RawChainEquivalence.targetSHom_f2, rawEquivalence_s2,
        SupportedBasisMap.toSource_mixedSelected, subsetFiniteHom_f2]
  exact h.trans (sSubsetFiniteHom_eq N e A)
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
/-- 有限列正操作の実Law Rは受理済み同じ独立原始Law射。 -/
theorem rawEquivalence_lawR_eq : (rawEquivalence N e).lawR laws ha ha = lawR N e laws ha := by
  apply cochain_ext
  · rw [RawChainEquivalence.lawR_f0, rawEquivalence_r0,
      SupportedBasisMap.toSource_mixedLawDual, lawR_f0]
  · rw [RawChainEquivalence.lawR_f1, rawEquivalence_r1,
      SupportedBasisMap.toSource_mixedLawDual, lawR_f1]
  · rw [RawChainEquivalence.lawR_f2, rawEquivalence_r2,
      SupportedBasisMap.toSource_mixedLawDual, lawR_f2]
/-- 有限列正操作の実Law Sは受理済み同じ独立原始Law射。 -/
theorem rawEquivalence_lawS_eq : (rawEquivalence N e).lawS laws ha ha = lawS N e laws ha := by
  apply cochain_ext
  · rw [RawChainEquivalence.lawS_f0, rawEquivalence_s0,
      SupportedBasisMap.toSource_mixedLawDual, lawS_f0]
  · rw [RawChainEquivalence.lawS_f1, rawEquivalence_s1,
      SupportedBasisMap.toSource_mixedLawDual, lawS_f1]
  · rw [RawChainEquivalence.lawS_f2, rawEquivalence_s2,
      SupportedBasisMap.toSource_mixedLawDual, lawS_f2]
omit [Fintype Source] in
/-- 有限列正操作の同じ実Law補正0も受理済み原始補正。 -/
theorem rawEquivalence_lawH0_eq :
    (rawEquivalence N e).h0.mixedLawDual laws ha ha = lawH0 N e laws ha := by
  rw [rawEquivalence_h0, SupportedBasisMap.toSource_mixedLawDual, lawH0_eq]
omit [Fintype Source] in
/-- 有限列正操作の同じ実Law補正1も受理済み原始補正。 -/
theorem rawEquivalence_lawH1_eq :
    (rawEquivalence N e).h1.mixedLawDual laws ha ha = lawH1 N e laws ha := by
  rw [rawEquivalence_h1, SupportedBasisMap.toSource_mixedLawDual, lawH1_eq]
end EdgeSubdivision
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
