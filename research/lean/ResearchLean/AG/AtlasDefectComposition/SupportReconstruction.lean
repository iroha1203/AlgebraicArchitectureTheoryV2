import ResearchLean.AG.AtlasDefectComposition.SupportFunctor
import Formal.Util.AssertStandardAxioms
/-! # 同署名からの実比較・錐の復元

Implementation notes: 同署名を両方向の全セル包含へ評価し、元のセルを固定した
両側複体同型と実比較正方形から標準錐同型を構成する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition.SupportReconstruction
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r) (h : q.CoarserThan r)
variable {A B : Set q.Target} (heq : SupportSignature.alpha N E h A = SupportSignature.alpha N E h B)
/-- 同署名の粗側指定 cochain 同値。元の全名付きセルを固定する。 -/
def coarseEquiv := SubsetRestriction.cochainEquiv N
  (SupportRestriction.coarseLE N E h heq.le) (SupportRestriction.coarseLE N E h heq.ge)
/-- 同署名の細側指定 cochain 同値。同じ inverse-image family を読む。 -/
def fineEquiv := SubsetRestriction.cochainEquiv E
  (SupportRestriction.fineLE N E h heq.le) (SupportRestriction.fineLE N E h heq.ge)
/-- 同署名の粗側標準零延長同型。 -/
def coarseIso := cochainEquivZeroExtensionIso (coarseEquiv N E h heq)
/-- 同署名の細側標準零延長同型。 -/
def fineIso := cochainEquivZeroExtensionIso (fineEquiv N E h heq)
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 指定 cochain 同値は実 A-subnerve 比較と可換する。 -/
theorem comparison_square :
    cochainComp (M.aSubnerveComparisonHom B) (fineEquiv N E h heq).toHom =
      cochainComp (coarseEquiv N E h heq).toHom (M.aSubnerveComparisonHom A) :=
  SupportRestriction.comparison_square N E h heq.le M
/-- 同署名の標準零延長同型は実比較の正方形を与える。 -/
theorem complex_square :
    zeroExtensionMap (M.aSubnerveComparisonHom B) ≫ (fineIso N E h heq).hom =
      (coarseIso N E h heq).hom ≫ zeroExtensionMap (M.aSubnerveComparisonHom A) :=
  SupportRestriction.complex_square N E h heq.le M
/-- 同署名の実比較錐は指定 chain 同型を持つ。 -/
def coneIso : mappingCone (zeroExtensionMap (M.aSubnerveComparisonHom B)) ≅
    mappingCone (zeroExtensionMap (M.aSubnerveComparisonHom A)) :=
  coneMapIso _ _ (coarseIso N E h heq) (fineIso N E h heq) (complex_square N E h heq M)
/-- 同署名の錐同型は全整数次数の homology 同型へ移る。 -/
def coneHomologyEquiv (m : ℤ) :=
  (HomologicalComplex.homologyMapIso (coneIso N E h heq M) m).toLinearEquiv
/-- 任意の実 subset と指定署名代表は全セル選択が一致する。 -/
theorem representative_eq (A : Set q.Target) :
    SupportSignature.alpha N E h (SupportFunctor.representative N E h (SupportSignature.sigma N E h A)) =
      SupportSignature.alpha N E h A := by
  rw [SupportFunctor.alpha_representative]
  rfl
/-- 元の実 subset 比較錐を署名代表の比較錐へ復元する指定同型。 -/
def representativeConeIso (A : Set q.Target) := coneIso N E h (representative_eq N E h A) M
/-- 閉包しても全セルを固定した実比較錐同型を持つ。 -/
def closureConeIso (A : Set q.Target) := coneIso N E h
  (SignatureGeometry.alpha_closure (SupportSignature.family N E h) A) M
end AAT.AG.AtlasDefectComposition.SupportReconstruction
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportReconstruction
