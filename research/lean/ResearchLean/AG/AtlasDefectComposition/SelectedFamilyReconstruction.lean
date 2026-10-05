import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyComplex
import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyCanonical
import ResearchLean.AG.AtlasDefectComposition.FiniteFamilyReindex
import Formal.Util.AssertStandardAxioms
/-! # 署名を保つ指定射からの実族復元

Implementation notes: 各非零 block の元のセルを固定した同型を指定添字全単射で並べる。
零 block の削除も実零性から構成済みの同型を使う。
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
/-- 指定射が各対応添字で保持する元の全名付きセル選択。 -/
theorem blockAlphaEq (i : Active (SupportSignature.family N E h) F) :
    SupportSignature.alpha N E h (G.subset (f.equiv i).1) = SupportSignature.alpha N E h (F.subset i.1) :=
  congrArg (fun s => s.val.val) (f.signature_eq i)
/-- 対応 block の実粗側同型。元の選択セルを固定する。 -/
def coarseBlockIso (i : Active (SupportSignature.family N E h) F) :
    coarseBlock N E h F i.1 ≅ coarseBlock N E h G (f.equiv i).1 :=
  SupportReconstruction.coarseIso N E h (blockAlphaEq N E h f i)
/-- 対応 block の実細側同型。同じ逆像選択を保持する。 -/
def fineBlockIso (i : Active (SupportSignature.family N E h) F) :
    fineBlock N E h F i.1 ≅ fineBlock N E h G (f.equiv i).1 :=
  SupportReconstruction.fineIso N E h (blockAlphaEq N E h f i)
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 各対応 block の指定同型は元の実比較と可換である。 -/
theorem block_square (i : Active (SupportSignature.family N E h) F) :
    comparisonBlock N E h F M i.1 ≫ (fineBlockIso N E h f i).hom =
      (coarseBlockIso N E h f i).hom ≫ comparisonBlock N E h G M (f.equiv i).1 :=
  SupportReconstruction.complex_square N E h (blockAlphaEq N E h f i) M
/-- 各対応 block の実錐同型。負号と比較も同じ原始入力から読む。 -/
def coneBlockIso (i : Active (SupportSignature.family N E h) F) :
    coneBlock N E h F M i.1 ≅ coneBlock N E h G M (f.equiv i).1 :=
  SupportReconstruction.coneIso N E h (blockAlphaEq N E h f i) M
/-- 指定射は全実粗族複体の同型を生成する。 -/
def coarseReconstructionIso : coarse N E h F ≅ coarse N E h G :=
  coarseActiveIso N E h F ≪≫ FiniteFamilyReindex.iso _ f.equiv _ (coarseBlockIso N E h f) ≪≫
    (coarseActiveIso N E h G).symm
/-- 指定射は全実細族複体の同型を生成する。 -/
def fineReconstructionIso : fine N E h F ≅ fine N E h G :=
  fineActiveIso N E h F ≪≫ FiniteFamilyReindex.iso _ f.equiv _ (fineBlockIso N E h f) ≪≫
    (fineActiveIso N E h G).symm
/-- 指定射は全実族比較錐の同型を生成する。 -/
def coneReconstructionIso : mappingCone (comparison N E h F M) ≅ mappingCone (comparison N E h G M) :=
  coneActiveIso N E h F M ≪≫ FiniteFamilyReindex.iso _ f.equiv _ (coneBlockIso N E h f M) ≪≫
    (coneActiveIso N E h G M).symm
/-- 重複度付き全署名は全実族錐を指定 canonical 族から復元する。 -/
def canonicalConeIso (F : Family (SupportSignature.family N E h)) :
    mappingCone (comparison N E h F M) ≅ mappingCone (comparison N E h
      (canonicalFamily (SupportSignature.family N E h) (multiplicity (SupportSignature.family N E h) F)) M) :=
  coneReconstructionIso N E h
    (homOfFiberCards (SupportSignature.family N E h) (fun s => by
      have he := canonical_multiplicity (SupportSignature.family N E h)
        (multiplicity (SupportSignature.family N E h) F)
      exact (congrArg (fun m => m s) he).symm)) M
/-- 多重度から復元する同型は全整数次数の実錐 homology へ送れる。 -/
def canonicalConeHomologyEquiv (F : Family (SupportSignature.family N E h)) (m : ℤ) :=
  (HomologicalComplex.homologyMapIso (canonicalConeIso N E h M F) m).toLinearEquiv
end AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
