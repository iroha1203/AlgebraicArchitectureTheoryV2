import ResearchLean.AG.FaceRelationSubdivision.MixedLawFiniteHom
import ResearchLean.AG.FaceRelationSubdivision.MixedLawCorrections
import ResearchLean.AG.FaceRelationSubdivision.ThreeHomotopy

/-!
# 同じ原始二補正の実Law標準ホモトピー

## Implementation notes

二補正の各原始有限和を独立Law座標化し、三つの実微分式からmathlibの
標準HomotopyEquivを生成する。ホモトピー同値を入力にする案は用いない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf) (laws : FiniteLawFamily Source)
variable (hc : laws.Adequate qc) (hf : laws.Adequate qf)

omit [Fintype Source] in
/-- 頂点の原始補正を同じ実Law d0へ運ぶ。 -/
theorem law_correction0 (z) : z =
    P.h0.mixedLawDual laws hf hf (Nf.lawGeneratedD0 laws hf z) +
      P.r0.mixedLawDual laws hf hc (P.s0.mixedLawDual laws hc hf z) := by
  have h := SupportedBasisMap.mixedLaw_correction_two laws hf (P.r0.comp P.s0)
    P.h0 (TargetSupportedNerve.sourceD1 Nf) (by
      simpa only [SupportedBasisMap.raw_comp, TargetSupportedNerve.sourceD1_raw] using P.sr_h0)
  rw [P.r0.mixedLawDual_comp laws hf hc P.s0 hf, mixedLaw_sourceD1] at h
  have hx := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hx
  exact hx.symm.trans (add_comm _ _)

omit [Fintype Source] in
/-- 辺の原始補正を同じ実Law d0/d1へ運ぶ。 -/
theorem law_correction1 (z) : z =
    P.h1.mixedLawDual laws hf hf (Nf.lawGeneratedD1 laws hf z) +
      Nf.lawGeneratedD0 laws hf (P.h0.mixedLawDual laws hf hf z) +
      P.r1.mixedLawDual laws hf hc (P.s1.mixedLawDual laws hc hf z) := by
  have h := SupportedBasisMap.mixedLaw_correction_three laws hf (P.r1.comp P.s1)
    P.h1 (TargetSupportedNerve.sourceD2 Nf) (TargetSupportedNerve.sourceD1 Nf) P.h0 (by
      simpa only [SupportedBasisMap.raw_comp, TargetSupportedNerve.sourceD1_raw,
        TargetSupportedNerve.sourceD2_raw] using P.sr_h1)
  rw [P.r1.mixedLawDual_comp laws hf hc P.s1 hf, mixedLaw_sourceD1, mixedLaw_sourceD2] at h
  have hx := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hx
  exact hx.symm.trans (by abel)

omit [Fintype Source] in
/-- 面の原始補正を同じ実Law d1へ運ぶ。 -/
theorem law_correction2 (z) : z =
    Nf.lawGeneratedD1 laws hf (P.h1.mixedLawDual laws hf hf z) +
      P.r2.mixedLawDual laws hf hc (P.s2.mixedLawDual laws hc hf z) := by
  have h := SupportedBasisMap.mixedLaw_correction_two laws hf (P.r2.comp P.s2)
    (TargetSupportedNerve.sourceD2 Nf) P.h1 (by
      simpa only [SupportedBasisMap.raw_comp, TargetSupportedNerve.sourceD2_raw] using P.sr_h2)
  rw [P.r2.mixedLawDual_comp laws hf hc P.s2 hf, mixedLaw_sourceD2] at h
  have hx := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hx
  exact hx.symm.trans (add_comm _ _)

/-- 同じ独立Law有限和のfine側標準補正。 -/
def lawFineHomotopy :
    Homotopy (zeroExtensionMap (cochainId (Nf.lawGeneratedComplex laws hf)))
      (zeroExtensionMap (cochainComp (P.lawS laws hc hf) (P.lawR laws hc hf))) :=
  threeHomotopy _ _ (P.h0.mixedLawDual laws hf hf) (P.h1.mixedLawDual laws hf hf)
    (by
      intro z
      rw [cochainId_f0, cochainComp_f0, lawR_f0, lawS_f0,
      TargetSupportedNerve.lawGeneratedComplex_d0]
      exact P.law_correction0 laws hc hf z)
    (by
      intro z
      rw [cochainId_f1, cochainComp_f1, lawR_f1, lawS_f1,
      TargetSupportedNerve.lawGeneratedComplex_d0, TargetSupportedNerve.lawGeneratedComplex_d1]
      exact P.law_correction1 laws hc hf z)
    (by
      intro z
      rw [cochainId_f2, cochainComp_f2, lawR_f2, lawS_f2,
      TargetSupportedNerve.lawGeneratedComplex_d1]
      exact P.law_correction2 laws hc hf z)

/-- 同じ原始r/s/h/kから全三次数の実Law標準同値を生成する。 -/
def lawHomotopyEquiv : HomotopyEquiv
    (zeroExtension (Nc.lawGeneratedComplex laws hc)) (zeroExtension (Nf.lawGeneratedComplex laws hf)) where
  hom := zeroExtensionMap (P.lawR laws hc hf)
  inv := zeroExtensionMap (P.lawS laws hc hf)
  homotopyHomInvId := by
    simpa only [lawR_symm, lawS_symm, zeroExtensionMap_comp, zeroExtensionMap_id] using
      (P.symm.lawFineHomotopy laws hf hc).symm
  homotopyInvHomId := by
    simpa only [zeroExtensionMap_comp, zeroExtensionMap_id] using
      (P.lawFineHomotopy laws hc hf).symm

/-- 標準同値の順方向は同じ独立実Law比較。 -/
@[simp] theorem lawHomotopyEquiv_hom :
    (P.lawHomotopyEquiv laws hc hf).hom = zeroExtensionMap (P.lawR laws hc hf) := rfl
/-- 標準同値の逆方向は同じ独立実Law逆比較。 -/
@[simp] theorem lawHomotopyEquiv_inv :
    (P.lawHomotopyEquiv laws hc hf).inv = zeroExtensionMap (P.lawS laws hc hf) := rfl

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
