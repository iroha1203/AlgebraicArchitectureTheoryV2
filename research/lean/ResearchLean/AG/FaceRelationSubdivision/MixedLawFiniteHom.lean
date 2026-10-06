import ResearchLean.AG.FaceRelationSubdivision.MixedLawDifferential
import ResearchLean.AG.FaceRelationSubdivision.RawChainEquivalence

/-!
# 混在reading原始chain射の実Law Hom

## Implementation notes

三つの独立Law有限和を既存複体の成分に置き、原始chain正方形を
同じ実微分へ渡す。Hom同値をfieldで受け取らず、全三成分を原始係数から生成する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source}
variable (Nc : TargetSupportedNerve qc) (Nf : TargetSupportedNerve qf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc) (hf : laws.Adequate qf)

/-- 原始Source支持有限和とchain式から同じ実Law Homを生成する。 -/
def mixedLawFiniteHom
    (M0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport))
    (M1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport))
    (M2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport))
    (h01 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw = M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
    (h12 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw = M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw) :
    ThreeCochainComplex.Hom (Nc.lawGeneratedComplex laws hc) (Nf.lawGeneratedComplex laws hf) where
  f0 := M0.mixedLawDual laws hf hc
  f1 := M1.mixedLawDual laws hf hc
  f2 := M2.mixedLawDual laws hf hc
  comm0 := by
    intro z
    have h := M1.mixedLawDual_square laws hf hc M0
      (TargetSupportedNerve.sourceD1 Nf) (TargetSupportedNerve.sourceD1 Nc) h01
    rw [mixedLaw_sourceD1, mixedLaw_sourceD1] at h
    exact LinearMap.congr_fun h z
  comm1 := by
    intro z
    have h := M2.mixedLawDual_square laws hf hc M1
      (TargetSupportedNerve.sourceD2 Nf) (TargetSupportedNerve.sourceD2 Nc) h12
    rw [mixedLaw_sourceD2, mixedLaw_sourceD2] at h
    exact LinearMap.congr_fun h z

/-- 混在reading独立Law Homの次数0は同じ原始有限和。 -/
@[simp] theorem mixedLawFiniteHom_f0
    (M0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport))
    (M1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport))
    (M2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport))
    (h01 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw = M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
    (h12 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw = M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw) :
    (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12).f0 = M0.mixedLawDual laws hf hc := rfl

/-- 混在reading独立Law Homの次数1は同じ原始有限和。 -/
@[simp] theorem mixedLawFiniteHom_f1
    (M0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport))
    (M1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport))
    (M2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport))
    (h01 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw = M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
    (h12 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw = M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw) :
    (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12).f1 = M1.mixedLawDual laws hf hc := rfl

/-- 混在reading独立Law Homの次数2は同じ原始有限和。 -/
@[simp] theorem mixedLawFiniteHom_f2
    (M0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport))
    (M1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport))
    (M2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport))
    (h01 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw = M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
    (h12 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw = M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw) :
    (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12).f2 = M2.mixedLawDual laws hf hc := rfl

namespace RawChainEquivalence
variable {Nc Nf} (P : RawChainEquivalence Nc Nf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc) (hf : laws.Adequate qf)

/-- 同じ原始rから独立生成する実Law比較。 -/
def lawR : ThreeCochainComplex.Hom (Nc.lawGeneratedComplex laws hc) (Nf.lawGeneratedComplex laws hf) :=
  mixedLawFiniteHom Nc Nf laws hc hf P.r0 P.r1 P.r2 P.r_comm01 P.r_comm12
/-- 同じ原始sから独立生成する実Law逆比較。 -/
def lawS : ThreeCochainComplex.Hom (Nf.lawGeneratedComplex laws hf) (Nc.lawGeneratedComplex laws hc) :=
  mixedLawFiniteHom Nf Nc laws hf hc P.s0 P.s1 P.s2 P.s_comm01 P.s_comm12

/-- 独立Law比較の次数0は同じ原始有限和。 -/
@[simp] theorem lawR_f0 : (P.lawR laws hc hf).f0 = P.r0.mixedLawDual laws hf hc := rfl
/-- 独立Law比較の次数1は同じ原始有限和。 -/
@[simp] theorem lawR_f1 : (P.lawR laws hc hf).f1 = P.r1.mixedLawDual laws hf hc := rfl
/-- 独立Law比較の次数2は同じ原始有限和。 -/
@[simp] theorem lawR_f2 : (P.lawR laws hc hf).f2 = P.r2.mixedLawDual laws hf hc := rfl
/-- 独立Law逆比較の次数0は同じ原始有限和。 -/
@[simp] theorem lawS_f0 : (P.lawS laws hc hf).f0 = P.s0.mixedLawDual laws hc hf := rfl
/-- 独立Law逆比較の次数1は同じ原始有限和。 -/
@[simp] theorem lawS_f1 : (P.lawS laws hc hf).f1 = P.s1.mixedLawDual laws hc hf := rfl
/-- 独立Law逆比較の次数2は同じ原始有限和。 -/
@[simp] theorem lawS_f2 : (P.lawS laws hc hf).f2 = P.s2.mixedLawDual laws hc hf := rfl

/-- 正逆出力を交換すると独立Law正射は同じ独立逆射。 -/
theorem lawR_symm : P.symm.lawR laws hf hc = P.lawS laws hc hf := by
  apply cochain_ext <;> rfl
/-- 正逆出力を交換すると独立Law逆射は同じ独立正射。 -/
theorem lawS_symm : P.symm.lawS laws hf hc = P.lawR laws hc hf := by
  apply cochain_ext <;> rfl

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
