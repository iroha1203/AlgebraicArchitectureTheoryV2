import ResearchLean.AG.AtlasDefectComposition.SelectedFamilies
import ResearchLean.AG.AtlasDefectComposition.SupportZeroBlock
import ResearchLean.AG.AtlasDefectComposition.FiniteFamilyZeroDeletion
import ResearchLean.AG.AtlasDefectComposition.FiniteConeFamily
import Formal.Util.AssertStandardAxioms
/-! # selected block 族から生成する実比較複体

Implementation notes: 元の subset 族へ既存の生成手続きを適用する。
零署名の削除条件は全名付きセルの空性から放電する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
universe u v
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve.{u,max u v} q) (E : TargetSupportedNerve.{u,max u v} r) (h : q.CoarserThan r)
variable (F : Family (SupportSignature.family N E h))
/-- 各元の block の粗側実零延長。 -/
def coarseBlock (i : F.Index) := zeroExtension (N.targetSubsetComplex (F.subset i))
/-- 各元の block の細側実零延長。 -/
def fineBlock (i : F.Index) := zeroExtension (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' F.subset i))
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 各元の block での実生成比較。 -/
def comparisonBlock (i : F.Index) : coarseBlock N E h F i ⟶ fineBlock N E h F i :=
  zeroExtensionMap (M.aSubnerveComparisonHom (F.subset i))
/-- 指定族の実粗側複体。 -/
def coarse := FiniteComplexFamily.complex (coarseBlock N E h F)
/-- 指定族の実細側複体。 -/
def fine := FiniteComplexFamily.complex (fineBlock N E h F)
/-- 同じ指定添字を通る実族比較。 -/
def comparison : coarse N E h F ⟶ fine N E h F :=
  FiniteComplexFamily.map _ _ (comparisonBlock N E h F M)
/-- 各元の block の実錐。 -/
def coneBlock (i : F.Index) := mappingCone (comparisonBlock N E h F M i)
/-- 零署名で除く粗側実成分の零性はセル署名から得られる。 -/
theorem coarseZero (i : F.Index) (hi : ¬ SignatureGeometry.sigma (SupportSignature.family N E h) (F.subset i) ≠ ⊥) (m : ℤ) :
    Subsingleton ((coarseBlock N E h F i).X m) :=
  SupportZeroBlock.coarse_subsingleton_X N E h (not_not.mp hi) m
/-- 零署名で除く細側実成分も零である。 -/
theorem fineZero (i : F.Index) (hi : ¬ SignatureGeometry.sigma (SupportSignature.family N E h) (F.subset i) ≠ ⊥) (m : ℤ) :
    Subsingleton ((fineBlock N E h F i).X m) :=
  SupportZeroBlock.fine_subsingleton_X N E h (not_not.mp hi) m
/-- 零署名で除く実錐成分も全次数で零である。 -/
theorem coneZero (i : F.Index) (hi : ¬ SignatureGeometry.sigma (SupportSignature.family N E h) (F.subset i) ≠ ⊥) (m : ℤ) :
    Subsingleton ((coneBlock N E h F M i).X m) :=
  SupportZeroBlock.cone_subsingleton_X N E h (not_not.mp hi) M m
/-- 実粗族から非零署名添字だけを読む指定同型。 -/
def coarseActiveIso : coarse N E h F ≅ FiniteComplexFamily.complex (fun i : Active (SupportSignature.family N E h) F => coarseBlock N E h F i.1) :=
  FiniteFamilyZeroDeletion.iso _ _ (coarseZero N E h F)
/-- 実細族から非零署名添字だけを読む指定同型。 -/
def fineActiveIso : fine N E h F ≅ FiniteComplexFamily.complex (fun i : Active (SupportSignature.family N E h) F => fineBlock N E h F i.1) :=
  FiniteFamilyZeroDeletion.iso _ _ (fineZero N E h F)
/-- 零署名の削除は実族比較と可換である。 -/
theorem active_square : comparison N E h F M ≫ (fineActiveIso N E h F).hom =
    (coarseActiveIso N E h F).hom ≫ FiniteComplexFamily.map _ _
      (fun i : Active (SupportSignature.family N E h) F => comparisonBlock N E h F M i.1) := by
  ext m x
  rfl
/-- 実族比較錐を元の非零署名添字の錐族へ同定する。 -/
def coneActiveIso : mappingCone (comparison N E h F M) ≅
    FiniteComplexFamily.complex (fun i : Active (SupportSignature.family N E h) F => coneBlock N E h F M i.1) :=
  FiniteConeFamily.iso (comparisonBlock N E h F M) ≪≫
    FiniteFamilyZeroDeletion.iso _ _ (coneZero N E h F M)
end AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
