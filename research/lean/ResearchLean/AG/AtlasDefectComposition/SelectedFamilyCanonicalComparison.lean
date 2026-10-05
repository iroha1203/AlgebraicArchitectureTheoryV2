import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyComparison
import Formal.Util.AssertStandardAxioms
/-! # 多重度付き canonical 族からの全実比較の復元

Implementation notes: 多重度が生成する指定添字全単射を両側で共有する。
元の実比較正方形を通して coarse・fine の指定同型を接続する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
universe u v
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve.{u,max u v} q) (E : TargetSupportedNerve.{u,max u v} r) (h : q.CoarserThan r)
variable (F : Family (SupportSignature.family N E h))
/-- 元の署名 fiber の濃度から生成する canonical 族への指定射。 -/
def canonicalHom : Hom (SupportSignature.family N E h) F
    (canonicalFamily (SupportSignature.family N E h) (multiplicity (SupportSignature.family N E h) F)) :=
  homOfFiberCards (SupportSignature.family N E h) (fun s => by
    have he := canonical_multiplicity (SupportSignature.family N E h) (multiplicity (SupportSignature.family N E h) F)
    exact (congrArg (fun m => m s) he).symm)
/-- 重複度付き署名から全実 coarse 複体を復元する。 -/
def canonicalCoarseIso := coarseReconstructionIso N E h (canonicalHom N E h F)
/-- 同じ指定添字全単射で全実 fine 複体を復元する。 -/
def canonicalFineIso := fineReconstructionIso N E h (canonicalHom N E h F)
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 重複度による全比較の復元は元の実生成射を保つ。 -/
theorem canonical_square : comparison N E h F M ≫ (canonicalFineIso N E h F).hom =
    (canonicalCoarseIso N E h F).hom ≫ comparison N E h
      (canonicalFamily (SupportSignature.family N E h) (multiplicity (SupportSignature.family N E h) F)) M :=
  reconstruction_square N E h (canonicalHom N E h F) M
end AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilyComplex
