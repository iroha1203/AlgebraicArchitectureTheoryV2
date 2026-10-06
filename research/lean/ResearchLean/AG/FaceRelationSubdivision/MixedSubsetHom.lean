import ResearchLean.AG.FaceRelationSubdivision.MixedSelectedFunctor
import ResearchLean.AG.FaceRelationSubdivision.RawChainEquivalence

/-!
# 異なるreadingで同じ原始有限和の実subset Hom

## Implementation notes

自由chainの原始非零項から実選択セル射を生成し、その双対を既存複体へ渡す。
Source逆像が同じという支持適合は有限操作列のreading因子から導く方向仮定。
対象同型の共役を比較の定義にする案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}

/-- 三つの原始有限和から同じ実subset Homを独立生成する。 -/
def mixedSubsetFiniteHom
    (M0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport))
    (M1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport))
    (M2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport))
    (h01 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw = M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
    (h12 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw = M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw)
    (Ac : Set qc.Target) (Af : Set qf.Target) (hA : qf.read ⁻¹' Af = qc.read ⁻¹' Ac) :
    ThreeCochainComplex.Hom (Nc.targetSubsetComplex Ac) (Nf.targetSubsetComplex Af) :=
  dualSubsetHom Ac Af (M0.mixedSelected Af Ac hA) (M1.mixedSelected Af Ac hA)
    (M2.mixedSelected Af Ac hA)
    (by
      have h := M1.mixedSelected_square Af Ac hA M0
        (TargetSupportedNerve.rawD1 Nf) (TargetSupportedNerve.rawD1 Nc) h01
      simpa only [TargetSupportedNerve.selected_rawD1] using h)
    (by
      have h := M2.mixedSelected_square Af Ac hA M1
        (TargetSupportedNerve.rawD2 Nf) (TargetSupportedNerve.rawD2 Nc) h12
      simpa only [TargetSupportedNerve.selected_rawD2] using h)

namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf) (Ac : Set qc.Target) (Af : Set qf.Target)
variable (hA : qf.read ⁻¹' Af = qc.read ⁻¹' Ac)

/-- 同じ原始rから実target subset比較を独立生成する。 -/
def targetRHom := mixedSubsetFiniteHom P.r0 P.r1 P.r2 P.r_comm01 P.r_comm12 Ac Af hA
/-- 同じ原始sから実target subset逆比較を独立生成する。 -/
def targetSHom := mixedSubsetFiniteHom P.s0 P.s1 P.s2 P.s_comm01 P.s_comm12 Af Ac hA.symm

/-- 実target比較の次数0も同じ独立選択有限和。 -/
@[simp] theorem targetRHom_f0 : (P.targetRHom Ac Af hA).f0 = dualCellMap (P.r0.mixedSelected Af Ac hA) := rfl
/-- 実target比較の次数1も同じ独立選択有限和。 -/
@[simp] theorem targetRHom_f1 : (P.targetRHom Ac Af hA).f1 = dualCellMap (P.r1.mixedSelected Af Ac hA) := rfl
/-- 実target比較の次数2も同じ独立選択有限和。 -/
@[simp] theorem targetRHom_f2 : (P.targetRHom Ac Af hA).f2 = dualCellMap (P.r2.mixedSelected Af Ac hA) := rfl
/-- 実target逆比較の次数0も同じ独立選択有限和。 -/
@[simp] theorem targetSHom_f0 : (P.targetSHom Ac Af hA).f0 = dualCellMap (P.s0.mixedSelected Ac Af hA.symm) := rfl
/-- 実target逆比較の次数1も同じ独立選択有限和。 -/
@[simp] theorem targetSHom_f1 : (P.targetSHom Ac Af hA).f1 = dualCellMap (P.s1.mixedSelected Ac Af hA.symm) := rfl
/-- 実target逆比較の次数2も同じ独立選択有限和。 -/
@[simp] theorem targetSHom_f2 : (P.targetSHom Ac Af hA).f2 = dualCellMap (P.s2.mixedSelected Ac Af hA.symm) := rfl

/-- 原始二方向を交換した実target順射は同じ逆射。 -/
theorem targetRHom_symm : P.symm.targetRHom Af Ac hA.symm = P.targetSHom Ac Af hA := by
  apply AtlasDefectComposition.cochain_ext <;> rfl
/-- 原始二方向を交換した実target逆射は同じ順射。 -/
theorem targetSHom_symm : P.symm.targetSHom Af Ac hA.symm = P.targetRHom Ac Af hA := by
  apply AtlasDefectComposition.cochain_ext <;> rfl

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
