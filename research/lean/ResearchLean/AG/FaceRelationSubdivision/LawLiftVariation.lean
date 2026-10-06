import ResearchLean.AG.FaceRelationSubdivision.FiniteHomComposition
import ResearchLean.AG.FaceRelationSubdivision.ThreeHomotopy
import ResearchLean.AG.FaceRelationSubdivision.HomotopyDiagnostics

/-!
# 同じ原始二次補正の独立Law射

## Implementation notes

一般入力は原始支持有限和sとtおよびsのchain式。tから直接新sectionを作り、
生成された同じ実Law微分による標準ホモトピーと旧H1一致を証明する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source} {Nc Nf : TargetSupportedNerve q}
variable (s0 : SupportedBasisMap Nc.chartSupport Nf.chartSupport)
variable (s1 : SupportedBasisMap Nc.edgeSupport Nf.edgeSupport)
variable (s2 : SupportedBasisMap Nc.faceSupport Nf.faceSupport)
variable (hs0 : (TargetSupportedNerve.rawD1 Nf).raw.comp s1.raw = s0.raw.comp (TargetSupportedNerve.rawD1 Nc).raw)
variable (hs1 : (TargetSupportedNerve.rawD2 Nf).raw.comp s2.raw = s1.raw.comp (TargetSupportedNerve.rawD2 Nc).raw)
variable (t : SupportedBasisMap Nc.edgeSupport Nf.faceSupport)

include hs0 in
/-- s+∂t の端点chain式は原始d1d2=0から生成する。 -/
theorem lawLift_raw_comm01 : (TargetSupportedNerve.rawD1 Nf).raw.comp
    (s1.add (t.comp (TargetSupportedNerve.rawD2 Nf))).raw =
    s0.raw.comp (TargetSupportedNerve.rawD1 Nc).raw := by
  rw [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp, LinearMap.comp_add,
    ← LinearMap.comp_assoc, TargetSupportedNerve.rawD1_comp_rawD2,
    LinearMap.zero_comp, add_zero]
  exact hs0

include hs1 in
/-- s+t∂ の面chain式は同じ原始有限和から生成する。 -/
theorem lawLift_raw_comm12 : (TargetSupportedNerve.rawD2 Nf).raw.comp
    (s2.add ((TargetSupportedNerve.rawD2 Nc).comp t)).raw =
    (s1.add (t.comp (TargetSupportedNerve.rawD2 Nf))).raw.comp
      (TargetSupportedNerve.rawD2 Nc).raw := by
  simp only [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp,
    LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc]
  rw [hs1]

variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
/-- 原始有限和s+∂t+t∂から独立生成する新sectionの実Law Hom。 -/
def lawLiftHom [Fintype Source] := lawFiniteHom s0
  (s1.add (t.comp (TargetSupportedNerve.rawD2 Nf)))
  (s2.add ((TargetSupportedNerve.rawD2 Nc).comp t))
  (lawLift_raw_comm01 s0 s1 hs0 t) (lawLift_raw_comm12 s1 s2 hs1 t) laws ha
/-- 新sectionの次数0は同じ原始有限和。 -/
@[simp] theorem lawLiftHom_f0 [Fintype Source] : (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha).f0 =
    s0.lawDual laws ha := rfl
/-- 新sectionの次数1は同じ原始有限和。 -/
@[simp] theorem lawLiftHom_f1 [Fintype Source] : (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha).f1 =
    (s1.add (t.comp (TargetSupportedNerve.rawD2 Nf))).lawDual laws ha := rfl
/-- 新sectionの次数2は同じ原始有限和。 -/
@[simp] theorem lawLiftHom_f2 [Fintype Source] : (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha).f2 =
    (s2.add ((TargetSupportedNerve.rawD2 Nc).comp t)).lawDual laws ha := rfl

/-- 独立生成次数1は同じ実微分のt補正。 -/
theorem lawLiftHom_correction1 [Fintype Source] (z) :
    (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha).f1 z =
      t.lawDual laws ha (Nf.lawGeneratedD1 laws ha z) + s1.lawDual laws ha z := by
  rw [lawLiftHom_f1, SupportedBasisMap.lawDual_add, SupportedBasisMap.lawDual_comp,
    lawDual_rawD2]
  exact add_comm _ _
/-- 独立生成次数2も同じ実微分のt補正。 -/
theorem lawLiftHom_correction2 [Fintype Source] (z) :
    (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha).f2 z =
      Nc.lawGeneratedD1 laws ha (t.lawDual laws ha z) + s2.lawDual laws ha z := by
  rw [lawLiftHom_f2, SupportedBasisMap.lawDual_add, SupportedBasisMap.lawDual_comp,
    lawDual_rawD2]
  exact add_comm _ _

/-- 同じ原始tから、独立新sectionと元sectionを結ぶ標準ホモトピー。 -/
def lawLiftHomotopy [Fintype Source] : Homotopy
    (zeroExtensionMap (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha))
    (zeroExtensionMap (lawFiniteHom s0 s1 s2 hs0 hs1 laws ha)) :=
  threeHomotopy _ _ 0 (t.lawDual laws ha)
    (by intro z; simp only [lawLiftHom_f0, lawFiniteHom_f0, LinearMap.zero_apply, zero_add])
    (by intro z
        simpa only [lawFiniteHom_f1, LinearMap.zero_apply, map_zero, add_zero,
          TargetSupportedNerve.lawGeneratedComplex_d1] using
          lawLiftHom_correction1 s0 s1 s2 hs0 hs1 t laws ha z)
    (by intro z
        simpa only [lawFiniteHom_f2, TargetSupportedNerve.lawGeneratedComplex_d1] using
          lawLiftHom_correction2 s0 s1 s2 hs0 hs1 t laws ha z)

/-- 同じ新sectionと元sectionの全整数次数読み戻しは一致する。 -/
theorem lawLiftHom_homologyMap [Fintype Source] (n : ℤ) :
    HomologicalComplex.homologyMap (zeroExtensionMap (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha)) n =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawFiniteHom s0 s1 s2 hs0 hs1 laws ha)) n :=
  (lawLiftHomotopy s0 s1 s2 hs0 hs1 t laws ha).homologyMap_eq n
/-- 同じ読み戻しを既存H1商へ戻して同じh1Mapを得る。 -/
theorem lawLiftHom_h1Map [Fintype Source] :
    (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha).h1Map =
      (lawFiniteHom s0 s1 s2 hs0 hs1 laws ha).h1Map := by
  have hn := oldH1Iso_natural (lawLiftHom s0 s1 s2 hs0 hs1 t laws ha)
  rw [lawLiftHom_homologyMap, oldH1Iso_natural] at hn
  have hm := (cancel_mono (oldH1Iso (Nc.lawGeneratedComplex laws ha)).hom).mp hn
  exact (ModuleCat.hom_ext_iff.mp hm).symm

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
