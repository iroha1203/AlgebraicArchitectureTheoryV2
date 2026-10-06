import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetCorrections

/-!
# 異なるreadingの全実target subsetでの標準同値

## Implementation notes

同じ原始r/s/h/kの独立選択有限和を双対化し、既存subsetの実微分と接続する。
台のSource逆像適合は有限列の因子から放電する。Source表示だけの同型で
実target比較の構成を代替する案は採らない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf) (Ac : Set qc.Target) (Af : Set qf.Target)
variable (hA : qf.read ⁻¹' Af = qc.read ⁻¹' Ac)

/-- 原始頂点補正の同じ実target subset式。 -/
theorem target_correction0 (z) : z =
    dualCellMap (P.h0.mixedSelected Af Af rfl) (Nf.targetSubsetD0 Af z) +
      dualCellMap (P.r0.mixedSelected Af Ac hA) (dualCellMap (P.s0.mixedSelected Ac Af hA.symm) z) := by
  have h := SupportedBasisMap.mixedSelectedDual_correction_two (P.r0.comp P.s0)
    P.h0 (TargetSupportedNerve.rawD1 Nf).toSource (by
      simpa only [SupportedBasisMap.raw_comp, SupportedBasisMap.toSource_raw] using P.sr_h0) Af
  rw [P.r0.mixedSelected_comp Af Ac hA P.s0 Af hA.symm, dualCellMap_comp,
    SupportedBasisMap.toSource_mixedSelected, TargetSupportedNerve.selected_rawD1,
    dualCellMap_chainD1] at h
  have hx := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hx
  exact hx.symm.trans (add_comm _ _)

/-- 原始辺補正の同じ実target subset二微分式。 -/
theorem target_correction1 (z) : z =
    dualCellMap (P.h1.mixedSelected Af Af rfl) (Nf.targetSubsetD1 Af z) +
      Nf.targetSubsetD0 Af (dualCellMap (P.h0.mixedSelected Af Af rfl) z) +
      dualCellMap (P.r1.mixedSelected Af Ac hA) (dualCellMap (P.s1.mixedSelected Ac Af hA.symm) z) := by
  have h := SupportedBasisMap.mixedSelectedDual_correction_three (P.r1.comp P.s1)
    P.h1 (TargetSupportedNerve.rawD2 Nf).toSource (TargetSupportedNerve.rawD1 Nf).toSource P.h0 (by
      simpa only [SupportedBasisMap.raw_comp, SupportedBasisMap.toSource_raw] using P.sr_h1) Af
  rw [P.r1.mixedSelected_comp Af Ac hA P.s1 Af hA.symm, dualCellMap_comp,
    SupportedBasisMap.toSource_mixedSelected, SupportedBasisMap.toSource_mixedSelected,
    TargetSupportedNerve.selected_rawD1, TargetSupportedNerve.selected_rawD2,
    dualCellMap_chainD1, dualCellMap_chainD2] at h
  have hx := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hx
  exact hx.symm.trans (by abel)

/-- 原始面補正の同じ実target subset式。 -/
theorem target_correction2 (z) : z =
    Nf.targetSubsetD1 Af (dualCellMap (P.h1.mixedSelected Af Af rfl) z) +
      dualCellMap (P.r2.mixedSelected Af Ac hA) (dualCellMap (P.s2.mixedSelected Ac Af hA.symm) z) := by
  have h := SupportedBasisMap.mixedSelectedDual_correction_two (P.r2.comp P.s2)
    (TargetSupportedNerve.rawD2 Nf).toSource P.h1 (by
      simpa only [SupportedBasisMap.raw_comp, SupportedBasisMap.toSource_raw] using P.sr_h2) Af
  rw [P.r2.mixedSelected_comp Af Ac hA P.s2 Af hA.symm, dualCellMap_comp,
    SupportedBasisMap.toSource_mixedSelected, TargetSupportedNerve.selected_rawD2,
    dualCellMap_chainD2] at h
  have hx := LinearMap.congr_fun h z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hx
  exact hx.symm.trans (add_comm _ _)

/-- 同じ独立実target subset射のfine側標準補正。 -/
def targetFineHomotopy : Homotopy
    (zeroExtensionMap (cochainId (Nf.targetSubsetComplex Af)))
      (zeroExtensionMap (cochainComp (P.targetSHom Ac Af hA) (P.targetRHom Ac Af hA))) :=
  threeHomotopy _ _ (dualCellMap (P.h0.mixedSelected Af Af rfl)) (dualCellMap (P.h1.mixedSelected Af Af rfl))
    (by
      intro z
      rw [cochainId_f0, cochainComp_f0, targetRHom_f0, targetSHom_f0, TargetSupportedNerve.targetSubsetComplex_d0]
      exact P.target_correction0 Ac Af hA z)
    (by
      intro z
      rw [cochainId_f1, cochainComp_f1, targetRHom_f1, targetSHom_f1,
        TargetSupportedNerve.targetSubsetComplex_d0, TargetSupportedNerve.targetSubsetComplex_d1]
      exact P.target_correction1 Ac Af hA z)
    (by
      intro z
      rw [cochainId_f2, cochainComp_f2, targetRHom_f2, targetSHom_f2, TargetSupportedNerve.targetSubsetComplex_d1]
      exact P.target_correction2 Ac Af hA z)

/-- 同じ実fine補正の標準Homotopy成分は生成した二つの独立有限和。 -/
@[simp] theorem targetFineHomotopy_hom (i j : ℤ) :
    (P.targetFineHomotopy Ac Af hA).hom i j =
      homotopyComponent (dualCellMap (P.h0.mixedSelected Af Af rfl))
        (dualCellMap (P.h1.mixedSelected Af Af rfl)) i j := rfl

/-- 同じ原始二補正から全実target subsetの標準同値を生成する。 -/
def targetHomotopyEquiv : HomotopyEquiv (zeroExtension (Nc.targetSubsetComplex Ac))
    (zeroExtension (Nf.targetSubsetComplex Af)) where
  hom := zeroExtensionMap (P.targetRHom Ac Af hA)
  inv := zeroExtensionMap (P.targetSHom Ac Af hA)
  homotopyHomInvId := by
    simpa only [targetRHom_symm, targetSHom_symm, zeroExtensionMap_comp, zeroExtensionMap_id] using
      (P.symm.targetFineHomotopy Af Ac hA.symm).symm
  homotopyInvHomId := by
    simpa only [zeroExtensionMap_comp, zeroExtensionMap_id] using (P.targetFineHomotopy Ac Af hA).symm

/-- 実target標準同値の順射は同じ独立生成比較。 -/
@[simp] theorem targetHomotopyEquiv_hom :
    (P.targetHomotopyEquiv Ac Af hA).hom = zeroExtensionMap (P.targetRHom Ac Af hA) := rfl
/-- 実target標準同値の逆射は同じ独立生成逆比較。 -/
@[simp] theorem targetHomotopyEquiv_inv :
    (P.targetHomotopyEquiv Ac Af hA).inv = zeroExtensionMap (P.targetSHom Ac Af hA) := rfl

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
