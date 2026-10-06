import ResearchLean.AG.FaceRelationSubdivision.PrimitiveOperationPath
import ResearchLean.AG.FaceRelationSubdivision.RawLawHomotopy
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom

/-!
# 原始有限合成と同じ実三成分射

## Implementation notes

直接生成した有限和を全三成分で各段の実cochain合成と照合する。
H1だけの次元比較で代替する案は同じ写像の接続を消すため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qm qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf)

/-- 直接原始R合成の全三成分は同じ実target subset合成。 -/
theorem targetRHom_trans (Ac : Set qc.Target) (Am : Set qm.Target) (Af : Set qf.Target)
    (hP : qm.read ⁻¹' Am = qc.read ⁻¹' Ac) (hQ : qf.read ⁻¹' Af = qm.read ⁻¹' Am) :
    (P.trans Q).targetRHom Ac Af (hQ.trans hP) = cochainComp (P.targetRHom Ac Am hP) (Q.targetRHom Am Af hQ) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f0, targetRHom_f0, targetRHom_f0, targetRHom_f0,
      trans_r0, Q.r0.mixedSelected_comp Af Am hQ P.r0 Ac hP, dualCellMap_comp]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f1, targetRHom_f1, targetRHom_f1, targetRHom_f1,
      trans_r1, Q.r1.mixedSelected_comp Af Am hQ P.r1 Ac hP, dualCellMap_comp]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f2, targetRHom_f2, targetRHom_f2, targetRHom_f2,
      trans_r2, Q.r2.mixedSelected_comp Af Am hQ P.r2 Ac hP, dualCellMap_comp]
    rfl
/-- 直接原始S合成の全三成分は同じ実target subset合成。 -/
theorem targetSHom_trans (Ac : Set qc.Target) (Am : Set qm.Target) (Af : Set qf.Target)
    (hP : qm.read ⁻¹' Am = qc.read ⁻¹' Ac) (hQ : qf.read ⁻¹' Af = qm.read ⁻¹' Am) :
    (P.trans Q).targetSHom Ac Af (hQ.trans hP) = cochainComp (Q.targetSHom Am Af hQ) (P.targetSHom Ac Am hP) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f0, targetSHom_f0, targetSHom_f0, targetSHom_f0,
      trans_s0, P.s0.mixedSelected_comp Ac Am hP.symm Q.s0 Af hQ.symm, dualCellMap_comp]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f1, targetSHom_f1, targetSHom_f1, targetSHom_f1,
      trans_s1, P.s1.mixedSelected_comp Ac Am hP.symm Q.s1 Af hQ.symm, dualCellMap_comp]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f2, targetSHom_f2, targetSHom_f2, targetSHom_f2,
      trans_s2, P.s2.mixedSelected_comp Ac Am hP.symm Q.s2 Af hQ.symm, dualCellMap_comp]
    rfl
/-- 空列の独立target R射は同じ実恒等。 -/
theorem targetRHom_refl (N : TargetSupportedNerve qc) (A : Set qc.Target) :
    (refl N).targetRHom A A rfl = cochainId (N.targetSubsetComplex A) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [targetRHom_f0, refl_r0, SupportedBasisMap.mixedSelected_identity,
      dualCellMap_identity, LinearMap.id_apply, cochainId_f0]
  · apply LinearMap.ext
    intro z
    rw [targetRHom_f1, refl_r1, SupportedBasisMap.mixedSelected_identity,
      dualCellMap_identity, LinearMap.id_apply, cochainId_f1]
  · apply LinearMap.ext
    intro z
    rw [targetRHom_f2, refl_r2, SupportedBasisMap.mixedSelected_identity,
      dualCellMap_identity, LinearMap.id_apply, cochainId_f2]
/-- 空列の独立target S射は同じ実恒等。 -/
theorem targetSHom_refl (N : TargetSupportedNerve qc) (A : Set qc.Target) :
    (refl N).targetSHom A A rfl = cochainId (N.targetSubsetComplex A) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [targetSHom_f0, refl_s0, SupportedBasisMap.mixedSelected_identity,
      dualCellMap_identity, LinearMap.id_apply, cochainId_f0]
  · apply LinearMap.ext
    intro z
    rw [targetSHom_f1, refl_s1, SupportedBasisMap.mixedSelected_identity,
      dualCellMap_identity, LinearMap.id_apply, cochainId_f1]
  · apply LinearMap.ext
    intro z
    rw [targetSHom_f2, refl_s2, SupportedBasisMap.mixedSelected_identity,
      dualCellMap_identity, LinearMap.id_apply, cochainId_f2]
variable [Fintype Source]
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc)
variable (hm : laws.Adequate qm) (hf : laws.Adequate qf)

/-- 直接原始R合成の独立Law全三成分は同じ実合成。 -/
theorem lawR_trans : (P.trans Q).lawR laws hc hf =
    cochainComp (P.lawR laws hc hm) (Q.lawR laws hm hf) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f0, lawR_f0, lawR_f0, lawR_f0,
      trans_r0, Q.r0.mixedLawDual_comp laws hf hm P.r0 hc]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f1, lawR_f1, lawR_f1, lawR_f1,
      trans_r1, Q.r1.mixedLawDual_comp laws hf hm P.r1 hc]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f2, lawR_f2, lawR_f2, lawR_f2,
      trans_r2, Q.r2.mixedLawDual_comp laws hf hm P.r2 hc]
    rfl
/-- 直接原始S合成の独立Law全三成分は同じ実合成。 -/
theorem lawS_trans : (P.trans Q).lawS laws hc hf =
    cochainComp (Q.lawS laws hm hf) (P.lawS laws hc hm) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f0, lawS_f0, lawS_f0, lawS_f0,
      trans_s0, P.s0.mixedLawDual_comp laws hc hm Q.s0 hf]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f1, lawS_f1, lawS_f1, lawS_f1,
      trans_s1, P.s1.mixedLawDual_comp laws hc hm Q.s1 hf]
    rfl
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f2, lawS_f2, lawS_f2, lawS_f2,
      trans_s2, P.s2.mixedLawDual_comp laws hc hm Q.s2 hf]
    rfl
/-- 空列の独立LawR射は同じ実恒等。 -/
theorem lawR_refl (N : TargetSupportedNerve qc) :
    (refl N).lawR laws hc hc = cochainId (N.lawGeneratedComplex laws hc) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [lawR_f0, refl_r0, SupportedBasisMap.mixedLawDual_identity, LinearMap.id_apply, cochainId_f0]
  · apply LinearMap.ext
    intro z
    rw [lawR_f1, refl_r1, SupportedBasisMap.mixedLawDual_identity, LinearMap.id_apply, cochainId_f1]
  · apply LinearMap.ext
    intro z
    rw [lawR_f2, refl_r2, SupportedBasisMap.mixedLawDual_identity, LinearMap.id_apply, cochainId_f2]
/-- 空列の独立LawS射は同じ実恒等。 -/
theorem lawS_refl (N : TargetSupportedNerve qc) :
    (refl N).lawS laws hc hc = cochainId (N.lawGeneratedComplex laws hc) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [lawS_f0, refl_s0, SupportedBasisMap.mixedLawDual_identity, LinearMap.id_apply, cochainId_f0]
  · apply LinearMap.ext
    intro z
    rw [lawS_f1, refl_s1, SupportedBasisMap.mixedLawDual_identity, LinearMap.id_apply, cochainId_f1]
  · apply LinearMap.ext
    intro z
    rw [lawS_f2, refl_s2, SupportedBasisMap.mixedLawDual_identity, LinearMap.id_apply, cochainId_f2]
end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
