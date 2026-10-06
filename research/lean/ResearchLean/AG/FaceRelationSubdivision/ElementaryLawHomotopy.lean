import ResearchLean.AG.FaceRelationSubdivision.ElementaryLawMaps
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteIdentities
import Formal.Util.AssertStandardAxioms

/-!
# 両正操作の同じ実Law射の標準ホモトピー

## Implementation notes

原始rs/sr等式をLaw有限和の公開APIで移す。各入力N/eから得た式で
三項補正を放電し、同じr/sをmathlib HomotopyEquivへ渡す。
対象同値や期待rankから射を選ぶ方法は使用しない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}
namespace TriangleAddition
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じ独立Law r/sの旧側往復は恒等。 -/
theorem law_cochain_rs : cochainComp (lawR N e laws ha) (lawS N e laws ha) =
    cochainId (N.lawGeneratedComplex laws ha) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f0, lawS_f0, lawR_f0, cochainId_f0]
    exact LinearMap.congr_fun
      (SupportedBasisMap.lawDual_comp_eq_identity laws ha (s0 N e) (r0 N e) (rs0 N e)) z
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f1, lawS_f1, lawR_f1, cochainId_f1]
    exact LinearMap.congr_fun
      (SupportedBasisMap.lawDual_comp_eq_identity laws ha (s1 N e) (r1 N e) (rs1 N e)) z
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f2, lawS_f2, lawR_f2, cochainId_f2]
    exact LinearMap.congr_fun
      (SupportedBasisMap.lawDual_comp_eq_identity laws ha (s2 N e) (r2 N e) (rs2 N e)) z

omit [Fintype Source] in
/-- 頂点の原始補正式は同じLaw微分と補正になる。 -/
theorem law_correction0 (z) :
    z = lawH0 N e laws ha ((supported N e).lawGeneratedD0 laws ha z) +
      (r0 N e).lawDual laws ha ((s0 N e).lawDual laws ha z) := by
  have hr : ((r0 N e).comp (s0 N e)).raw +
      ((h0 N e).comp (TargetSupportedNerve.rawD1 (supported N e))).raw = LinearMap.id := by
    simpa only [SupportedBasisMap.raw_comp] using sr_h0 N e
  have h := SupportedBasisMap.lawDual_add_eq_identity laws ha
    ((r0 N e).comp (s0 N e)) ((h0 N e).comp (TargetSupportedNerve.rawD1 (supported N e))) hr
  rw [SupportedBasisMap.lawDual_comp, SupportedBasisMap.lawDual_comp, lawDual_rawD1] at h
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [lawH0_eq]
  exact hz.symm.trans (add_comm _ _)

omit [Fintype Source] in
/-- 辺の原始補正式は同じ二Law微分と補正になる。 -/
theorem law_correction1 (z) :
    z = lawH1 N e laws ha ((supported N e).lawGeneratedD1 laws ha z) +
      (supported N e).lawGeneratedD0 laws ha (lawH0 N e laws ha z) +
      (r1 N e).lawDual laws ha ((s1 N e).lawDual laws ha z) := by
  have hr : ((r1 N e).comp (s1 N e)).raw +
      ((h1 N e).comp (TargetSupportedNerve.rawD2 (supported N e))).raw +
      ((TargetSupportedNerve.rawD1 (supported N e)).comp (h0 N e)).raw = LinearMap.id := by
    simpa only [SupportedBasisMap.raw_comp] using sr_h1 N e
  have h := SupportedBasisMap.lawDual_add_add_eq_identity laws ha
    ((r1 N e).comp (s1 N e)) ((h1 N e).comp (TargetSupportedNerve.rawD2 (supported N e)))
    ((TargetSupportedNerve.rawD1 (supported N e)).comp (h0 N e)) hr
  rw [SupportedBasisMap.lawDual_comp, SupportedBasisMap.lawDual_comp,
    SupportedBasisMap.lawDual_comp, lawDual_rawD1, lawDual_rawD2] at h
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [lawH0_eq, lawH1_eq]
  exact hz.symm.trans (by abel)

omit [Fintype Source] in
/-- 面の原始補正式は同じLaw微分と補正になる。 -/
theorem law_correction2 (z) :
    z = (supported N e).lawGeneratedD1 laws ha (lawH1 N e laws ha z) +
      (r2 N e).lawDual laws ha ((s2 N e).lawDual laws ha z) := by
  have hr : ((r2 N e).comp (s2 N e)).raw +
      ((TargetSupportedNerve.rawD2 (supported N e)).comp (h1 N e)).raw = LinearMap.id := by
    simpa only [SupportedBasisMap.raw_comp] using sr_h2 N e
  have h := SupportedBasisMap.lawDual_add_eq_identity laws ha
    ((r2 N e).comp (s2 N e)) ((TargetSupportedNerve.rawD2 (supported N e)).comp (h1 N e)) hr
  rw [SupportedBasisMap.lawDual_comp, SupportedBasisMap.lawDual_comp, lawDual_rawD2] at h
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [lawH1_eq]
  exact hz.symm.trans (add_comm _ _)

/-- 同じ独立Law r/sと原始hから標準ホモトピー同値を構成する。 -/
def lawHomotopyEquiv : HomotopyEquiv
    (zeroExtension (N.lawGeneratedComplex laws ha))
    (zeroExtension ((supported N e).lawGeneratedComplex laws ha)) where
  hom := zeroExtensionMap (lawR N e laws ha)
  inv := zeroExtensionMap (lawS N e laws ha)
  homotopyHomInvId := Homotopy.ofEq (by
    rw [← zeroExtensionMap_comp, law_cochain_rs, zeroExtensionMap_id])
  homotopyInvHomId := by
    simpa only [zeroExtensionMap_comp, zeroExtensionMap_id] using
      (threeHomotopy (cochainId ((supported N e).lawGeneratedComplex laws ha))
        (cochainComp (lawS N e laws ha) (lawR N e laws ha))
        (lawH0 N e laws ha) (lawH1 N e laws ha)
        (by intro z; rw [cochainId_f0, cochainComp_f0, lawR_f0, lawS_f0,
          TargetSupportedNerve.lawGeneratedComplex_d0]; exact law_correction0 N e laws ha z)
        (by intro z; rw [cochainId_f1, cochainComp_f1, lawR_f1, lawS_f1,
          TargetSupportedNerve.lawGeneratedComplex_d0, TargetSupportedNerve.lawGeneratedComplex_d1]
            ; exact law_correction1 N e laws ha z)
        (by intro z; rw [cochainId_f2, cochainComp_f2, lawR_f2, lawS_f2,
          TargetSupportedNerve.lawGeneratedComplex_d1]; exact law_correction2 N e laws ha z)).symm

/-- 標準同値の順方向は同じ実Law比較。 -/
@[simp] theorem lawHomotopyEquiv_hom : (lawHomotopyEquiv N e laws ha).hom =
    zeroExtensionMap (lawR N e laws ha) := rfl
/-- 標準同値の逆方向は同じ実Law有限和section。 -/
@[simp] theorem lawHomotopyEquiv_inv : (lawHomotopyEquiv N e laws ha).inv =
    zeroExtensionMap (lawS N e laws ha) := rfl

end TriangleAddition

namespace EdgeSubdivision
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じ独立Law r/sの旧側往復は恒等。 -/
theorem law_cochain_rs : cochainComp (lawR N e laws ha) (lawS N e laws ha) =
    cochainId (N.lawGeneratedComplex laws ha) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f0, lawS_f0, lawR_f0, cochainId_f0]
    exact LinearMap.congr_fun
      (SupportedBasisMap.lawDual_comp_eq_identity laws ha (s0 N e) (r0 N e) (rs0 N e)) z
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f1, lawS_f1, lawR_f1, cochainId_f1]
    exact LinearMap.congr_fun
      (SupportedBasisMap.lawDual_comp_eq_identity laws ha (s1 N e) (r1 N e) (rs1 N e)) z
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f2, lawS_f2, lawR_f2, cochainId_f2]
    exact LinearMap.congr_fun
      (SupportedBasisMap.lawDual_comp_eq_identity laws ha (s2 N e) (r2 N e) (rs2 N e)) z

omit [Fintype Source] in
/-- 頂点の原始補正式は同じLaw微分と補正になる。 -/
theorem law_correction0 (z) :
    z = lawH0 N e laws ha ((supported N e).lawGeneratedD0 laws ha z) +
      (r0 N e).lawDual laws ha ((s0 N e).lawDual laws ha z) := by
  have hr : ((r0 N e).comp (s0 N e)).raw +
      ((h0 N e).comp (TargetSupportedNerve.rawD1 (supported N e))).raw = LinearMap.id := by
    simpa only [SupportedBasisMap.raw_comp] using sr_h0 N e
  have h := SupportedBasisMap.lawDual_add_eq_identity laws ha
    ((r0 N e).comp (s0 N e)) ((h0 N e).comp (TargetSupportedNerve.rawD1 (supported N e))) hr
  rw [SupportedBasisMap.lawDual_comp, SupportedBasisMap.lawDual_comp, lawDual_rawD1] at h
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [lawH0_eq]
  exact hz.symm.trans (add_comm _ _)

omit [Fintype Source] in
/-- 辺の原始補正式は同じ二Law微分と補正になる。 -/
theorem law_correction1 (z) :
    z = lawH1 N e laws ha ((supported N e).lawGeneratedD1 laws ha z) +
      (supported N e).lawGeneratedD0 laws ha (lawH0 N e laws ha z) +
      (r1 N e).lawDual laws ha ((s1 N e).lawDual laws ha z) := by
  have hr : ((r1 N e).comp (s1 N e)).raw +
      ((h1 N e).comp (TargetSupportedNerve.rawD2 (supported N e))).raw +
      ((TargetSupportedNerve.rawD1 (supported N e)).comp (h0 N e)).raw = LinearMap.id := by
    simpa only [SupportedBasisMap.raw_comp] using sr_h1 N e
  have h := SupportedBasisMap.lawDual_add_add_eq_identity laws ha
    ((r1 N e).comp (s1 N e)) ((h1 N e).comp (TargetSupportedNerve.rawD2 (supported N e)))
    ((TargetSupportedNerve.rawD1 (supported N e)).comp (h0 N e)) hr
  rw [SupportedBasisMap.lawDual_comp, SupportedBasisMap.lawDual_comp,
    SupportedBasisMap.lawDual_comp, lawDual_rawD1, lawDual_rawD2] at h
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [lawH0_eq, lawH1_eq]
  exact hz.symm.trans (by abel)

omit [Fintype Source] in
/-- 面の原始補正式は同じLaw微分と補正になる。 -/
theorem law_correction2 (z) :
    z = (supported N e).lawGeneratedD1 laws ha (lawH1 N e laws ha z) +
      (r2 N e).lawDual laws ha ((s2 N e).lawDual laws ha z) := by
  have hr : ((r2 N e).comp (s2 N e)).raw +
      ((TargetSupportedNerve.rawD2 (supported N e)).comp (h1 N e)).raw = LinearMap.id := by
    simpa only [SupportedBasisMap.raw_comp] using sr_h2 N e
  have h := SupportedBasisMap.lawDual_add_eq_identity laws ha
    ((r2 N e).comp (s2 N e)) ((TargetSupportedNerve.rawD2 (supported N e)).comp (h1 N e)) hr
  rw [SupportedBasisMap.lawDual_comp, SupportedBasisMap.lawDual_comp, lawDual_rawD2] at h
  have hz := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [lawH1_eq]
  exact hz.symm.trans (add_comm _ _)

/-- 同じ独立Law r/sと原始hから標準ホモトピー同値を構成する。 -/
def lawHomotopyEquiv : HomotopyEquiv
    (zeroExtension (N.lawGeneratedComplex laws ha))
    (zeroExtension ((supported N e).lawGeneratedComplex laws ha)) where
  hom := zeroExtensionMap (lawR N e laws ha)
  inv := zeroExtensionMap (lawS N e laws ha)
  homotopyHomInvId := Homotopy.ofEq (by
    rw [← zeroExtensionMap_comp, law_cochain_rs, zeroExtensionMap_id])
  homotopyInvHomId := by
    simpa only [zeroExtensionMap_comp, zeroExtensionMap_id] using
      (threeHomotopy (cochainId ((supported N e).lawGeneratedComplex laws ha))
        (cochainComp (lawS N e laws ha) (lawR N e laws ha))
        (lawH0 N e laws ha) (lawH1 N e laws ha)
        (by intro z; rw [cochainId_f0, cochainComp_f0, lawR_f0, lawS_f0,
          TargetSupportedNerve.lawGeneratedComplex_d0]; exact law_correction0 N e laws ha z)
        (by intro z; rw [cochainId_f1, cochainComp_f1, lawR_f1, lawS_f1,
          TargetSupportedNerve.lawGeneratedComplex_d0, TargetSupportedNerve.lawGeneratedComplex_d1]
            ; exact law_correction1 N e laws ha z)
        (by intro z; rw [cochainId_f2, cochainComp_f2, lawR_f2, lawS_f2,
          TargetSupportedNerve.lawGeneratedComplex_d1]; exact law_correction2 N e laws ha z)).symm

/-- 標準同値の順方向は同じ実Law比較。 -/
@[simp] theorem lawHomotopyEquiv_hom : (lawHomotopyEquiv N e laws ha).hom =
    zeroExtensionMap (lawR N e laws ha) := rfl
/-- 標準同値の逆方向は同じ実Law有限和section。 -/
@[simp] theorem lawHomotopyEquiv_inv : (lawHomotopyEquiv N e laws ha).inv =
    zeroExtensionMap (lawS N e laws ha) := rfl

end EdgeSubdivision

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
