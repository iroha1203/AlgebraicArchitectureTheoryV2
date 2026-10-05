import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyReconstruction
import ResearchLean.AG.AtlasDefectComposition.FiniteFamilyReindexNaturality
import Formal.Util.AssertStandardAxioms
/-! # 指定族の全実比較の復元正方形

Implementation notes: 実零成分削除、元の添字並べ替え、元のセル同型を合成する。
各 block の比較正方形を全族へ送り、全比較を保持する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
universe u v
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve.{u,max u v} q) (E : TargetSupportedNerve.{u,max u v} r) (h : q.CoarserThan r)
variable {F G : Family (SupportSignature.family N E h)}
variable (f : Hom (SupportSignature.family N E h) F G)
variable (M : TargetSupportedNerveMorphism q r h N E)
set_option maxHeartbeats 800000 in
/-- 非零署名の元の添字全単射は全実 active 族比較と可換する。 -/
theorem activeReconstruction_square :
    FiniteComplexFamily.map _ _ (fun i : Active (SupportSignature.family N E h) F => comparisonBlock N E h F M i.1) ≫
      (FiniteFamilyReindex.iso (fun i : Active (SupportSignature.family N E h) F => fineBlock N E h F i.1) f.equiv (fun i : Active (SupportSignature.family N E h) G => fineBlock N E h G i.1) (fineBlockIso N E h f)).hom =
    (FiniteFamilyReindex.iso (fun i : Active (SupportSignature.family N E h) F => coarseBlock N E h F i.1) f.equiv (fun i : Active (SupportSignature.family N E h) G => coarseBlock N E h G i.1) (coarseBlockIso N E h f)).hom ≫
      FiniteComplexFamily.map _ _ (fun i : Active (SupportSignature.family N E h) G => comparisonBlock N E h G M i.1) :=
  FiniteFamilyReindex.square (fun i : Active (SupportSignature.family N E h) F => coarseBlock N E h F i.1) (fun i : Active (SupportSignature.family N E h) F => fineBlock N E h F i.1) (fun i : Active (SupportSignature.family N E h) G => coarseBlock N E h G i.1) (fun i : Active (SupportSignature.family N E h) G => fineBlock N E h G i.1) f.equiv _ _ (coarseBlockIso N E h f) (fineBlockIso N E h f) (block_square N E h f M)
/-- 指定署名射が生成する全族複体同型は実生成比較と可換する。 -/
theorem reconstruction_square : comparison N E h F M ≫ (fineReconstructionIso N E h f).hom =
    (coarseReconstructionIso N E h f).hom ≫ comparison N E h G M := by
  let ec := FiniteFamilyReindex.iso (fun i : Active (SupportSignature.family N E h) F => coarseBlock N E h F i.1) f.equiv (fun i : Active (SupportSignature.family N E h) G => coarseBlock N E h G i.1) (coarseBlockIso N E h f)
  let ef := FiniteFamilyReindex.iso (fun i : Active (SupportSignature.family N E h) F => fineBlock N E h F i.1) f.equiv (fun i : Active (SupportSignature.family N E h) G => fineBlock N E h G i.1) (fineBlockIso N E h f)
  let ug := FiniteComplexFamily.map _ _ (fun i : Active (SupportSignature.family N E h) G => comparisonBlock N E h G M i.1)
  have hg : (coarseActiveIso N E h G).inv ≫ comparison N E h G M = ug ≫ (fineActiveIso N E h G).inv := by
    apply (cancel_mono (fineActiveIso N E h G).hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [active_square N E h G M,Iso.inv_hom_id_assoc]
  have hr := activeReconstruction_square N E h f M
  have hh := congrArg (fun z => (coarseActiveIso N E h F).hom ≫ z ≫ (fineActiveIso N E h G).inv) hr
  have hf := congrArg (fun z => z ≫ ef.hom ≫ (fineActiveIso N E h G).inv) (active_square N E h F M)
  dsimp only [fineReconstructionIso,coarseReconstructionIso,Iso.trans_hom,Iso.symm_hom]
  simpa only [Category.assoc,ec,ef,ug,hg] using hf.trans hh

end AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
