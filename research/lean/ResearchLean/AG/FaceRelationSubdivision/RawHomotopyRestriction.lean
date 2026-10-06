import ResearchLean.AG.FaceRelationSubdivision.HomotopyComponentNaturality
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHomotopy
import ResearchLean.AG.FaceRelationSubdivision.MixedRestrictionHom
import ResearchLean.AG.FaceRelationSubdivision.OperationPathRestriction

/-!
# 同じ原始二補正の標準Homotopyと全支持制限

## Implementation notes

生成したh/k有限和の包含自然性を標準Homotopy全整数次数へ接続する。
操作列の二補正を任意の対象同値で置き換える案は採らない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf) {Ac Bc : Set qc.Target} {Af Bf : Set qf.Target}

/-- 同じ実fine補正は標準Homotopyの全整数次数で支持制限と可換。 -/
theorem targetFineHomotopy_restrict_natural (hf : Af ⊆ Bf)
    (hA : qf.read ⁻¹' Af = qc.read ⁻¹' Ac) (hB : qf.read ⁻¹' Bf = qc.read ⁻¹' Bc) (i j : ℤ) :
    (P.targetFineHomotopy Bc Bf hB).hom i j ≫ (zeroExtensionMap (subsetRestrictHom Nf hf)).f j =
      (zeroExtensionMap (subsetRestrictHom Nf hf)).f i ≫ (P.targetFineHomotopy Ac Af hA).hom i j := by
  rw [targetFineHomotopy_hom, targetFineHomotopy_hom]
  apply homotopyComponent_natural (subsetRestrictHom Nf hf) (subsetRestrictHom Nf hf)
  · rw [subsetRestrictHom_f0, subsetRestrictHom_f1]
    exact P.target_h0_restrict_natural hf
  · rw [subsetRestrictHom_f1, subsetRestrictHom_f2]
    exact P.target_h1_restrict_natural hf

/-- 同じ実coarse補正も標準Homotopyの全整数次数で支持制限と可換。 -/
theorem targetCoarseHomotopy_restrict_natural (hc : Ac ⊆ Bc)
    (hA : qf.read ⁻¹' Af = qc.read ⁻¹' Ac) (hB : qf.read ⁻¹' Bf = qc.read ⁻¹' Bc) (i j : ℤ) :
    (P.symm.targetFineHomotopy Bf Bc hB.symm).hom i j ≫ (zeroExtensionMap (subsetRestrictHom Nc hc)).f j =
      (zeroExtensionMap (subsetRestrictHom Nc hc)).f i ≫ (P.symm.targetFineHomotopy Af Ac hA.symm).hom i j :=
  P.symm.targetFineHomotopy_restrict_natural hc hA.symm hB.symm i j

end RawChainEquivalence
namespace PrimitiveOperationPath
variable (path : PrimitiveOperationPath qc Nc qf Nf) {A B : Set qc.Target}

/-- 原始有限列のfine補正は任意A包含Bと標準全整数次数で可換。 -/
theorem fineHomotopy_restrict_natural (h : A ⊆ B) (i j : ℤ) :
    (path.rawEquivalence.targetFineHomotopy B (path.targetSubset B) (path.source_subset_eq B)).hom i j ≫
        (zeroExtensionMap (subsetRestrictHom Nf (path.targetSubset_mono h))).f j =
      (zeroExtensionMap (subsetRestrictHom Nf (path.targetSubset_mono h))).f i ≫
        (path.rawEquivalence.targetFineHomotopy A (path.targetSubset A) (path.source_subset_eq A)).hom i j :=
  path.rawEquivalence.targetFineHomotopy_restrict_natural (path.targetSubset_mono h)
    (path.source_subset_eq A) (path.source_subset_eq B) i j

/-- 原始有限列のcoarse補正も任意A包含Bと標準全整数次数で可換。 -/
theorem coarseHomotopy_restrict_natural (h : A ⊆ B) (i j : ℤ) :
    (path.rawEquivalence.symm.targetFineHomotopy (path.targetSubset B) B (path.source_subset_eq B).symm).hom i j ≫
        (zeroExtensionMap (subsetRestrictHom Nc h)).f j =
      (zeroExtensionMap (subsetRestrictHom Nc h)).f i ≫
        (path.rawEquivalence.symm.targetFineHomotopy (path.targetSubset A) A (path.source_subset_eq A).symm).hom i j :=
  path.rawEquivalence.targetCoarseHomotopy_restrict_natural h
    (path.source_subset_eq A) (path.source_subset_eq B) i j

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
