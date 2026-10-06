import ResearchLean.AG.FaceRelationSubdivision.SupportRestriction
import ResearchLean.AG.FaceRelationSubdivision.FiniteHomComposition

/-!
# 支持包含の実subset制限と同じ有限和の自然性

## Implementation notes

原始微分も台を保つ有限基底射なので包含と可換になる。
双対から既存subset複体のHomを作り、全三成分と既存H1に接続する。
各部分集合に任意の制限Homを入力する案は、原始セルの包含を隠すため採らない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}

/-- 原始支持包含の双対は同じ実d0と可換。 -/
theorem subsetRestrict_comm0 (N : TargetSupportedNerve q) {A B : Set q.Target}
    (h : A ⊆ B) (z : (N.targetSubsetComplex B).C0) :
    selectedRestrict N.edgeSupport h ((N.targetSubsetComplex B).d0 z) =
      (N.targetSubsetComplex A).d0 (selectedRestrict N.chartSupport h z) := by
  have hn := (TargetSupportedNerve.rawD1 N).dual_selected_restrict_natural h
  rw [TargetSupportedNerve.selected_rawD1, TargetSupportedNerve.selected_rawD1,
    dualCellMap_chainD1, dualCellMap_chainD1] at hn
  exact LinearMap.congr_fun hn z

/-- 原始支持包含の双対は同じ実d1と可換。 -/
theorem subsetRestrict_comm1 (N : TargetSupportedNerve q) {A B : Set q.Target}
    (h : A ⊆ B) (z : (N.targetSubsetComplex B).C1) :
    selectedRestrict N.faceSupport h ((N.targetSubsetComplex B).d1 z) =
      (N.targetSubsetComplex A).d1 (selectedRestrict N.edgeSupport h z) := by
  have hn := (TargetSupportedNerve.rawD2 N).dual_selected_restrict_natural h
  rw [TargetSupportedNerve.selected_rawD2, TargetSupportedNerve.selected_rawD2,
    dualCellMap_chainD2, dualCellMap_chainD2] at hn
  exact LinearMap.congr_fun hn z

/-- 同じセル包含の双対から生成した既存subset複体の実制限。 -/
def subsetRestrictHom (N : TargetSupportedNerve q) {A B : Set q.Target}
    (h : A ⊆ B) : ThreeCochainComplex.Hom (N.targetSubsetComplex B)
      (N.targetSubsetComplex A) where
  f0 := selectedRestrict N.chartSupport h
  f1 := selectedRestrict N.edgeSupport h
  f2 := selectedRestrict N.faceSupport h
  comm0 := subsetRestrict_comm0 N h
  comm1 := subsetRestrict_comm1 N h

/-- 実制限の次数0は同じセル包含の双対。 -/
@[simp] theorem subsetRestrictHom_f0 (N : TargetSupportedNerve q) {A B : Set q.Target}
    (h : A ⊆ B) : (subsetRestrictHom N h).f0 = selectedRestrict N.chartSupport h := rfl
/-- 実制限の次数1は同じセル包含の双対。 -/
@[simp] theorem subsetRestrictHom_f1 (N : TargetSupportedNerve q) {A B : Set q.Target}
    (h : A ⊆ B) : (subsetRestrictHom N h).f1 = selectedRestrict N.edgeSupport h := rfl
/-- 実制限の次数2は同じセル包含の双対。 -/
@[simp] theorem subsetRestrictHom_f2 (N : TargetSupportedNerve q) {A B : Set q.Target}
    (h : A ⊆ B) : (subsetRestrictHom N h).f2 = selectedRestrict N.faceSupport h := rfl

/-- 全三成分で支持制限の恒等則。 -/
theorem subsetRestrictHom_refl (N : TargetSupportedNerve q) (A : Set q.Target) :
    subsetRestrictHom N (Set.Subset.refl A) = cochainId (N.targetSubsetComplex A) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [subsetRestrictHom_f0, cochainId_f0, selectedRestrict_refl, LinearMap.id_apply]
  · apply LinearMap.ext; intro z
    rw [subsetRestrictHom_f1, cochainId_f1, selectedRestrict_refl, LinearMap.id_apply]
  · apply LinearMap.ext; intro z
    rw [subsetRestrictHom_f2, cochainId_f2, selectedRestrict_refl, LinearMap.id_apply]

/-- 直接支持制限は同じ二つの実Homの合成。 -/
theorem subsetRestrictHom_comp (N : TargetSupportedNerve q) {A B C : Set q.Target}
    (hab : A ⊆ B) (hbc : B ⊆ C) : subsetRestrictHom N (hab.trans hbc) =
      cochainComp (subsetRestrictHom N hbc) (subsetRestrictHom N hab) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [subsetRestrictHom_f0, cochainComp_f0, subsetRestrictHom_f0,
      subsetRestrictHom_f0, selectedRestrict_comp N.chartSupport hab hbc]
    rfl
  · apply LinearMap.ext; intro z
    rw [subsetRestrictHom_f1, cochainComp_f1, subsetRestrictHom_f1,
      subsetRestrictHom_f1, selectedRestrict_comp N.edgeSupport hab hbc]
    rfl
  · apply LinearMap.ext; intro z
    rw [subsetRestrictHom_f2, cochainComp_f2, subsetRestrictHom_f2,
      subsetRestrictHom_f2, selectedRestrict_comp N.faceSupport hab hbc]
    rfl

variable {Nc Nf : TargetSupportedNerve q}
variable (M0 : SupportedBasisMap Nf.chartSupport Nc.chartSupport)
variable (M1 : SupportedBasisMap Nf.edgeSupport Nc.edgeSupport)
variable (M2 : SupportedBasisMap Nf.faceSupport Nc.faceSupport)
variable (hc0 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw =
    M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
variable (hc1 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw =
    M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw)

/-- 全三成分で直接原始有限和Homは同じ支持制限と可換。 -/
theorem subsetFinite_restrict_square {A B : Set q.Target} (h : A ⊆ B) :
    cochainComp (subsetFiniteHom M0 M1 M2 hc0 hc1 B) (subsetRestrictHom Nf h) =
      cochainComp (subsetRestrictHom Nc h) (subsetFiniteHom M0 M1 M2 hc0 hc1 A) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainComp_f0, subsetFiniteHom_f0, subsetFiniteHom_f0,
      subsetRestrictHom_f0, subsetRestrictHom_f0]
    exact LinearMap.congr_fun (M0.dual_selected_restrict_natural h) z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainComp_f1, subsetFiniteHom_f1, subsetFiniteHom_f1,
      subsetRestrictHom_f1, subsetRestrictHom_f1]
    exact LinearMap.congr_fun (M1.dual_selected_restrict_natural h) z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainComp_f2, subsetFiniteHom_f2, subsetFiniteHom_f2,
      subsetRestrictHom_f2, subsetRestrictHom_f2]
    exact LinearMap.congr_fun (M2.dual_selected_restrict_natural h) z

/-- 同じ実有限和と支持制限は既存H1商でも可換。 -/
theorem subsetFinite_restrict_h1_square {A B : Set q.Target} (h : A ⊆ B) :
    (subsetRestrictHom Nf h).h1Map.comp (subsetFiniteHom M0 M1 M2 hc0 hc1 B).h1Map =
      (subsetFiniteHom M0 M1 M2 hc0 hc1 A).h1Map.comp (subsetRestrictHom Nc h).h1Map := by
  have hn := congrArg ThreeCochainComplex.Hom.h1Map
    (subsetFinite_restrict_square M0 M1 M2 hc0 hc1 h)
  simpa only [cochainComp_h1Map] using hn

/-- 同じ有限和比較と制限は標準零延長の全次数で可換。 -/
theorem subsetFinite_restrict_zeroExtension_square {A B : Set q.Target} (h : A ⊆ B) :
    zeroExtensionMap (subsetFiniteHom M0 M1 M2 hc0 hc1 B) ≫
        zeroExtensionMap (subsetRestrictHom Nf h) =
      zeroExtensionMap (subsetRestrictHom Nc h) ≫
        zeroExtensionMap (subsetFiniteHom M0 M1 M2 hc0 hc1 A) := by
  have hn := congrArg zeroExtensionMap (subsetFinite_restrict_square M0 M1 M2 hc0 hc1 h)
  simpa only [zeroExtensionMap_comp] using hn

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
