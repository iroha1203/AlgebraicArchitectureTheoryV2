import ResearchLean.AG.FaceRelationSubdivision.SourceSupportedBasis

/-!
# 原始有限和の正逆二補正

## Implementation notes

このrecordは原始操作の証明出力であり、操作入力にはしない。二つの補正を
保持し、逆縮約の順序が混在しても有限合成の同じ基底像を計算できる。
標準HomotopyEquivを入力にする案は独立有限和の構成を消すため採らない。
一般合成のfield仮定は方向仮定、各操作への適用では原始セル表から放電する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {qc qm qf : Reading Source}

/-- 原始支持有限和と両側の具体補正式の出力。 -/
structure RawChainEquivalence (Nc : TargetSupportedNerve qc) (Nf : TargetSupportedNerve qf) where
  r0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport)
  r1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport)
  r2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport)
  s0 : SupportedBasisMap (sourceSupport qc Nc.chartSupport) (sourceSupport qf Nf.chartSupport)
  s1 : SupportedBasisMap (sourceSupport qc Nc.edgeSupport) (sourceSupport qf Nf.edgeSupport)
  s2 : SupportedBasisMap (sourceSupport qc Nc.faceSupport) (sourceSupport qf Nf.faceSupport)
  h0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qf Nf.edgeSupport)
  h1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qf Nf.faceSupport)
  k0 : SupportedBasisMap (sourceSupport qc Nc.chartSupport) (sourceSupport qc Nc.edgeSupport)
  k1 : SupportedBasisMap (sourceSupport qc Nc.edgeSupport) (sourceSupport qc Nc.faceSupport)
  r_comm01 : (TargetSupportedNerve.rawD1 Nc).raw.comp r1.raw = r0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw
  r_comm12 : (TargetSupportedNerve.rawD2 Nc).raw.comp r2.raw = r1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw
  s_comm01 : (TargetSupportedNerve.rawD1 Nf).raw.comp s1.raw = s0.raw.comp (TargetSupportedNerve.rawD1 Nc).raw
  s_comm12 : (TargetSupportedNerve.rawD2 Nf).raw.comp s2.raw = s1.raw.comp (TargetSupportedNerve.rawD2 Nc).raw
  sr_h0 : s0.raw.comp r0.raw + (TargetSupportedNerve.rawD1 Nf).raw.comp h0.raw = LinearMap.id
  sr_h1 : s1.raw.comp r1.raw + (TargetSupportedNerve.rawD2 Nf).raw.comp h1.raw + h0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw = LinearMap.id
  sr_h2 : s2.raw.comp r2.raw + h1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw = LinearMap.id
  rs_k0 : r0.raw.comp s0.raw + (TargetSupportedNerve.rawD1 Nc).raw.comp k0.raw = LinearMap.id
  rs_k1 : r1.raw.comp s1.raw + (TargetSupportedNerve.rawD2 Nc).raw.comp k1.raw + k0.raw.comp (TargetSupportedNerve.rawD1 Nc).raw = LinearMap.id
  rs_k2 : r2.raw.comp s2.raw + k1.raw.comp (TargetSupportedNerve.rawD2 Nc).raw = LinearMap.id

namespace RawChainEquivalence
variable {Nc : TargetSupportedNerve qc} {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}

/-- 同じ二射を逆方向に用い、二補正を交換する。 -/
def symm (P : RawChainEquivalence Nc Nf) : RawChainEquivalence Nf Nc where
  r0 := P.s0; r1 := P.s1; r2 := P.s2
  s0 := P.r0; s1 := P.r1; s2 := P.r2
  h0 := P.k0; h1 := P.k1; k0 := P.h0; k1 := P.h1
  r_comm01 := P.s_comm01; r_comm12 := P.s_comm12
  s_comm01 := P.r_comm01; s_comm12 := P.r_comm12
  sr_h0 := P.rs_k0; sr_h1 := P.rs_k1; sr_h2 := P.rs_k2
  rs_k0 := P.sr_h0; rs_k1 := P.sr_h1; rs_k2 := P.sr_h2

/-- 逆出力のrは同じs。 -/
@[simp] theorem symm_r0 (P : RawChainEquivalence Nc Nf) : P.symm.r0 = P.s0 := rfl
/-- 逆出力の辺rは同じs。 -/
@[simp] theorem symm_r1 (P : RawChainEquivalence Nc Nf) : P.symm.r1 = P.s1 := rfl
/-- 逆出力の面rは同じs。 -/
@[simp] theorem symm_r2 (P : RawChainEquivalence Nc Nf) : P.symm.r2 = P.s2 := rfl
/-- 逆出力のsは同じr。 -/
@[simp] theorem symm_s0 (P : RawChainEquivalence Nc Nf) : P.symm.s0 = P.r0 := rfl
/-- 逆出力の辺sは同じr。 -/
@[simp] theorem symm_s1 (P : RawChainEquivalence Nc Nf) : P.symm.s1 = P.r1 := rfl
/-- 逆出力の面sは同じr。 -/
@[simp] theorem symm_s2 (P : RawChainEquivalence Nc Nf) : P.symm.s2 = P.r2 := rfl
/-- 逆出力の頂点補正は旧側補正。 -/
@[simp] theorem symm_h0 (P : RawChainEquivalence Nc Nf) : P.symm.h0 = P.k0 := rfl
/-- 逆出力の辺補正は旧側補正。 -/
@[simp] theorem symm_h1 (P : RawChainEquivalence Nc Nf) : P.symm.h1 = P.k1 := rfl

/-- 原始二段合成のfine側頂点補正 h12+s12 h01 r12。 -/
def composedH0 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :=
  Q.h0.add ((Q.r0.comp P.h0).comp Q.s1)
/-- 原始二段合成のfine側辺補正 h12+s12 h01 r12。 -/
def composedH1 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :=
  Q.h1.add ((Q.r1.comp P.h1).comp Q.s2)
/-- 合成頂点補正の全セル射。 -/
@[simp] theorem composedH0_raw (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (composedH0 P Q).raw = Q.h0.raw + Q.s1.raw.comp (P.h0.raw.comp Q.r0.raw) := by
  simp only [composedH0, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]
/-- 合成辺補正の全セル射。 -/
@[simp] theorem composedH1_raw (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (composedH1 P Q).raw = Q.h1.raw + Q.s2.raw.comp (P.h1.raw.comp Q.r1.raw) := by
  simp only [composedH1, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]

/-- 頂点の二段補正を同じ原始三射の可換式から導く。 -/
theorem composed_sr_h0 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (Q.s0.raw.comp P.s0.raw).comp (P.r0.raw.comp Q.r0.raw) +
      (TargetSupportedNerve.rawD1 Nf).raw.comp (composedH0 P Q).raw = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    composedH0_raw, map_add]
  have hQ := LinearMap.congr_fun Q.sr_h0 x
  have hP := congrArg Q.s0.raw (LinearMap.congr_fun P.sr_h0 (Q.r0.raw x))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add] at hQ hP
  have hc := LinearMap.congr_fun Q.s_comm01 (P.h0.raw (Q.r0.raw x))
  simp only [LinearMap.comp_apply] at hc
  rw [hc]
  have hh := (congrArg (fun y => y + (TargetSupportedNerve.rawD1 Nf).raw (Q.h0.raw x)) hP).trans hQ
  convert hh using 1; abel

/-- 辺の二段補正は両微分の同じchain可換式を使う。 -/
theorem composed_sr_h1 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (Q.s1.raw.comp P.s1.raw).comp (P.r1.raw.comp Q.r1.raw) +
      (TargetSupportedNerve.rawD2 Nf).raw.comp (composedH1 P Q).raw +
      (composedH0 P Q).raw.comp (TargetSupportedNerve.rawD1 Nf).raw = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    composedH0_raw, composedH1_raw, map_add]
  have hQ := LinearMap.congr_fun Q.sr_h1 x
  have hP := congrArg Q.s1.raw (LinearMap.congr_fun P.sr_h1 (Q.r1.raw x))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add] at hQ hP
  have hc2 := LinearMap.congr_fun Q.s_comm12 (P.h1.raw (Q.r1.raw x))
  have hc1 := LinearMap.congr_fun Q.r_comm01 x
  simp only [LinearMap.comp_apply] at hc1 hc2
  rw [hc2, ← hc1]
  have hh := (congrArg (fun y => y + (TargetSupportedNerve.rawD2 Nf).raw (Q.h1.raw x) +
    Q.h0.raw ((TargetSupportedNerve.rawD1 Nf).raw x)) hP).trans hQ
  convert hh using 1; abel

/-- 面の二段補正は同じ三辺符号和の可換式を使う。 -/
theorem composed_sr_h2 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (Q.s2.raw.comp P.s2.raw).comp (P.r2.raw.comp Q.r2.raw) +
      (composedH1 P Q).raw.comp (TargetSupportedNerve.rawD2 Nf).raw = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    composedH1_raw]
  have hQ := LinearMap.congr_fun Q.sr_h2 x
  have hP := congrArg Q.s2.raw (LinearMap.congr_fun P.sr_h2 (Q.r2.raw x))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add] at hQ hP
  have hc := LinearMap.congr_fun Q.r_comm12 x
  simp only [LinearMap.comp_apply] at hc
  rw [← hc]
  have hh := (congrArg (fun y => y + Q.h1.raw ((TargetSupportedNerve.rawD2 Nf).raw x)) hP).trans hQ
  convert hh using 1; abel

/-- 原始恒等列。両補正は零有限和である。 -/
def refl (N : TargetSupportedNerve qc) : RawChainEquivalence N N where
  r0 := SupportedBasisMap.identity _; r1 := SupportedBasisMap.identity _
  r2 := SupportedBasisMap.identity _; s0 := SupportedBasisMap.identity _
  s1 := SupportedBasisMap.identity _; s2 := SupportedBasisMap.identity _
  h0 := SupportedBasisMap.zero _ _; h1 := SupportedBasisMap.zero _ _
  k0 := SupportedBasisMap.zero _ _; k1 := SupportedBasisMap.zero _ _
  r_comm01 := by simp only [SupportedBasisMap.raw_identity, LinearMap.comp_id, LinearMap.id_comp]
  r_comm12 := by simp only [SupportedBasisMap.raw_identity, LinearMap.comp_id, LinearMap.id_comp]
  s_comm01 := by simp only [SupportedBasisMap.raw_identity, LinearMap.comp_id, LinearMap.id_comp]
  s_comm12 := by simp only [SupportedBasisMap.raw_identity, LinearMap.comp_id, LinearMap.id_comp]
  sr_h0 := by simp only [SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero, LinearMap.comp_id, LinearMap.comp_zero, add_zero]
  sr_h1 := by simp only [SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero, LinearMap.comp_id, LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
  sr_h2 := by simp only [SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero, LinearMap.comp_id, LinearMap.zero_comp, add_zero]
  rs_k0 := by simp only [SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero, LinearMap.comp_id, LinearMap.comp_zero, add_zero]
  rs_k1 := by simp only [SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero, LinearMap.comp_id, LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
  rs_k2 := by simp only [SupportedBasisMap.raw_identity, SupportedBasisMap.raw_zero, LinearMap.comp_id, LinearMap.zero_comp, add_zero]

/-- 原始有限和の二段合成と正逆の二補正を計算する。 -/
def trans (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    RawChainEquivalence Nc Nf where
  r0 := Q.r0.comp P.r0; r1 := Q.r1.comp P.r1; r2 := Q.r2.comp P.r2
  s0 := P.s0.comp Q.s0; s1 := P.s1.comp Q.s1; s2 := P.s2.comp Q.s2
  h0 := composedH0 P Q; h1 := composedH1 P Q
  k0 := composedH0 Q.symm P.symm; k1 := composedH1 Q.symm P.symm
  r_comm01 := by
    simp only [SupportedBasisMap.raw_comp]
    rw [← LinearMap.comp_assoc, P.r_comm01, LinearMap.comp_assoc, Q.r_comm01, LinearMap.comp_assoc]
  r_comm12 := by
    simp only [SupportedBasisMap.raw_comp]
    rw [← LinearMap.comp_assoc, P.r_comm12, LinearMap.comp_assoc, Q.r_comm12, LinearMap.comp_assoc]
  s_comm01 := by
    simp only [SupportedBasisMap.raw_comp]
    rw [← LinearMap.comp_assoc, Q.s_comm01, LinearMap.comp_assoc, P.s_comm01, LinearMap.comp_assoc]
  s_comm12 := by
    simp only [SupportedBasisMap.raw_comp]
    rw [← LinearMap.comp_assoc, Q.s_comm12, LinearMap.comp_assoc, P.s_comm12, LinearMap.comp_assoc]
  sr_h0 := by simpa only [SupportedBasisMap.raw_comp] using composed_sr_h0 P Q
  sr_h1 := by simpa only [SupportedBasisMap.raw_comp] using composed_sr_h1 P Q
  sr_h2 := by simpa only [SupportedBasisMap.raw_comp] using composed_sr_h2 P Q
  rs_k0 := by simpa only [SupportedBasisMap.raw_comp, symm_s0, symm_r0] using composed_sr_h0 Q.symm P.symm
  rs_k1 := by simpa only [SupportedBasisMap.raw_comp, symm_s1, symm_r1] using composed_sr_h1 Q.symm P.symm
  rs_k2 := by simpa only [SupportedBasisMap.raw_comp, symm_s2, symm_r2] using composed_sr_h2 Q.symm P.symm

/-- 二段合成のr0は同じ原始有限和の合成。 -/
@[simp] theorem trans_r0 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).r0 = Q.r0.comp P.r0 := rfl

/-- 二段合成のr1は同じ原始有限和の合成。 -/
@[simp] theorem trans_r1 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).r1 = Q.r1.comp P.r1 := rfl

/-- 二段合成のr2は同じ原始有限和の合成。 -/
@[simp] theorem trans_r2 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).r2 = Q.r2.comp P.r2 := rfl

/-- 二段合成のs0は同じ原始有限和の合成。 -/
@[simp] theorem trans_s0 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).s0 = P.s0.comp Q.s0 := rfl

/-- 二段合成のs1は同じ原始有限和の合成。 -/
@[simp] theorem trans_s1 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).s1 = P.s1.comp Q.s1 := rfl

/-- 二段合成のs2は同じ原始有限和の合成。 -/
@[simp] theorem trans_s2 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).s2 = P.s2.comp Q.s2 := rfl

/-- 二段合成のh0は計算された同じ補正。 -/
@[simp] theorem trans_h0 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).h0 = composedH0 P Q := rfl

/-- 二段合成のh1は計算された同じ補正。 -/
@[simp] theorem trans_h1 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).h1 = composedH1 P Q := rfl

/-- 二段合成のk0は計算された同じ補正。 -/
@[simp] theorem trans_k0 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).k0 = composedH0 Q.symm P.symm := rfl

/-- 二段合成のk1は計算された同じ補正。 -/
@[simp] theorem trans_k1 (P : RawChainEquivalence Nc Nm) (Q : RawChainEquivalence Nm Nf) :
    (P.trans Q).k1 = composedH1 Q.symm P.symm := rfl

/-- 空列のr0は同じ原始恒等基底。 -/
@[simp] theorem refl_r0 (N : TargetSupportedNerve qc) :
    (refl N).r0 = SupportedBasisMap.identity (sourceSupport qc N.chartSupport) := rfl

/-- 空列のr1は同じ原始恒等基底。 -/
@[simp] theorem refl_r1 (N : TargetSupportedNerve qc) :
    (refl N).r1 = SupportedBasisMap.identity (sourceSupport qc N.edgeSupport) := rfl

/-- 空列のr2は同じ原始恒等基底。 -/
@[simp] theorem refl_r2 (N : TargetSupportedNerve qc) :
    (refl N).r2 = SupportedBasisMap.identity (sourceSupport qc N.faceSupport) := rfl

/-- 空列のs0は同じ原始恒等基底。 -/
@[simp] theorem refl_s0 (N : TargetSupportedNerve qc) :
    (refl N).s0 = SupportedBasisMap.identity (sourceSupport qc N.chartSupport) := rfl

/-- 空列のs1は同じ原始恒等基底。 -/
@[simp] theorem refl_s1 (N : TargetSupportedNerve qc) :
    (refl N).s1 = SupportedBasisMap.identity (sourceSupport qc N.edgeSupport) := rfl

/-- 空列のs2は同じ原始恒等基底。 -/
@[simp] theorem refl_s2 (N : TargetSupportedNerve qc) :
    (refl N).s2 = SupportedBasisMap.identity (sourceSupport qc N.faceSupport) := rfl

/-- 出力の原始有限和と二補正が一致すれば証明出力全体が一致する。 -/
@[ext] theorem ext {P Q : RawChainEquivalence Nc Nf}
    (hr0 : P.r0 = Q.r0) (hr1 : P.r1 = Q.r1) (hr2 : P.r2 = Q.r2)
    (hs0 : P.s0 = Q.s0) (hs1 : P.s1 = Q.s1) (hs2 : P.s2 = Q.s2)
    (hh0 : P.h0 = Q.h0) (hh1 : P.h1 = Q.h1)
    (hk0 : P.k0 = Q.k0) (hk1 : P.k1 = Q.k1) : P = Q := by
  cases P
  cases Q
  cases hr0; cases hr1; cases hr2; cases hs0; cases hs1; cases hs2
  cases hh0; cases hh1; cases hk0; cases hk1
  rfl

/-- 空列のh0は零原始補正。 -/
@[simp] theorem refl_h0 (N : TargetSupportedNerve qc) :
    (refl N).h0 = SupportedBasisMap.zero (sourceSupport qc N.chartSupport) (sourceSupport qc N.edgeSupport) := rfl

/-- 空列のh1は零原始補正。 -/
@[simp] theorem refl_h1 (N : TargetSupportedNerve qc) :
    (refl N).h1 = SupportedBasisMap.zero (sourceSupport qc N.edgeSupport) (sourceSupport qc N.faceSupport) := rfl

/-- 空列のk0は零原始補正。 -/
@[simp] theorem refl_k0 (N : TargetSupportedNerve qc) :
    (refl N).k0 = SupportedBasisMap.zero (sourceSupport qc N.chartSupport) (sourceSupport qc N.edgeSupport) := rfl

/-- 空列のk1は零原始補正。 -/
@[simp] theorem refl_k1 (N : TargetSupportedNerve qc) :
    (refl N).k1 = SupportedBasisMap.zero (sourceSupport qc N.edgeSupport) (sourceSupport qc N.faceSupport) := rfl

/-- 原始正逆交換後の粗側頂点補正は元のfine補正。 -/
@[simp] theorem symm_k0 (P : RawChainEquivalence Nc Nf) : P.symm.k0 = P.h0 := rfl
/-- 原始正逆交換後の粗側辺補正は元のfine補正。 -/
@[simp] theorem symm_k1 (P : RawChainEquivalence Nc Nf) : P.symm.k1 = P.h1 := rfl

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
