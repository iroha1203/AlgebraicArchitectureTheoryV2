import ResearchLean.AG.AtlasDefectComposition.SupportRestriction
import ResearchLean.AG.AtlasDefectComposition.SignatureUniversal
import Mathlib.CategoryTheory.Category.Preorder
import Formal.Util.AssertStandardAxioms
/-! # 署名の反対圏上の実比較複体

Implementation notes: 各署名を gamma の閉集合で標準的に代表する。
射は実セルの台制限であり、恒等・合成は全三次数の制限法則から従う。
-/
noncomputable section
open CategoryTheory Opposite
namespace AAT.AG.AtlasDefectComposition.SupportFunctor
open CanonicalResolution ResolutionInvariance TwoPhase
universe u v
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve.{u,v} q) (E : TargetSupportedNerve.{u,v} r) (h : q.CoarserThan r)
/-- 全セル署名の指定閉集合代表。元の target 上の subset を復元する。 -/
def representative (s : SupportSignature.Signature N E h) : Set q.Target :=
  SignatureGeometry.gamma (SupportSignature.family N E h) s.val
/-- 指定代表は元の全名付きセル署名を保持する。 -/
@[simp] theorem alpha_representative (s : SupportSignature.Signature N E h) :
    SupportSignature.alpha N E h (representative N E h s) = s.val := by
  change SignatureGeometry.alpha (SupportSignature.family N E h)
    (SignatureGeometry.gamma (SupportSignature.family N E h) s.val) = s.val
  exact SignatureGeometry.alpha_gamma_signature (SupportSignature.family N E h) s
/-- 署名包含は指定代表の包含を与える。 -/
theorem representative_mono : Monotone (representative N E h) := by
  intro s t hst
  exact SignatureGeometry.gamma_mono (SupportSignature.family N E h) hst
variable {s t z : SupportSignature.Signature N E h}
/-- 署名包含を全セル選択の包含として読む。 -/
theorem alpha_le (hst : s ≤ t) :
    SupportSignature.alpha N E h (representative N E h s) ⊆
      SupportSignature.alpha N E h (representative N E h t) := by
  simpa only [alpha_representative] using hst
/-- 署名の指定代表上の粗側標準複体。 -/
def coarseComplex (s : SupportSignature.Signature N E h) := zeroExtension (N.targetSubsetComplex (representative N E h s))
/-- 署名の指定代表の同じ逆像上の細側標準複体。 -/
def fineComplex (s : SupportSignature.Signature N E h) := zeroExtension (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' representative N E h s))
/-- 粗側 complex の逆向き実セル制限。 -/
def coarseMap (hst : s ≤ t) : coarseComplex N E h t ⟶ coarseComplex N E h s :=
  zeroExtensionMap (SubsetRestriction.hom N (SupportRestriction.coarseLE N E h (alpha_le N E h hst)))
/-- 細側 complex の逆向き実セル制限。同じ inverse-image family を保つ。 -/
def fineMap (hst : s ≤ t) : fineComplex N E h t ⟶ fineComplex N E h s :=
  zeroExtensionMap (SubsetRestriction.hom E (SupportRestriction.fineLE N E h (alpha_le N E h hst)))
/-- 粗側の実台制限は恒等を保つ。 -/
theorem coarseMap_id (s : SupportSignature.Signature N E h) : coarseMap N E h (le_refl s) = 𝟙 _ := by
  change zeroExtensionMap (SubsetRestriction.hom N
    (SubsetRestriction.selectedLE_refl N (representative N E h s))) = _
  rw [SubsetRestriction.hom_id,zeroExtensionMap_id]
  rfl
/-- 細側の実台制限は恒等を保つ。 -/
theorem fineMap_id (s : SupportSignature.Signature N E h) : fineMap N E h (le_refl s) = 𝟙 _ := by
  change zeroExtensionMap (SubsetRestriction.hom E
    (SubsetRestriction.selectedLE_refl E (comparisonFactor q r h ⁻¹' representative N E h s))) = _
  rw [SubsetRestriction.hom_id,zeroExtensionMap_id]
  rfl
/-- 粗側の実台制限は逆向き合成を保つ。 -/
theorem coarseMap_comp (hst : s ≤ t) (htz : t ≤ z) :
    coarseMap N E h htz ≫ coarseMap N E h hst = coarseMap N E h (hst.trans htz) := by
  rw [coarseMap,coarseMap,coarseMap,← zeroExtensionMap_comp]
  congr 1
/-- 細側の実台制限は逆向き合成を保つ。 -/
theorem fineMap_comp (hst : s ≤ t) (htz : t ≤ z) :
    fineMap N E h htz ≫ fineMap N E h hst = fineMap N E h (hst.trans htz) := by
  rw [fineMap,fineMap,fineMap,← zeroExtensionMap_comp]
  congr 1
/-- Eの粗側実複体を署名反対圏上の関手へまとめる。 -/
def coarseFunctor : (SupportSignature.Signature N E h)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} ℚ) ℤ where
  obj s := coarseComplex N E h s.unop
  map f := coarseMap N E h (leOfHom f.unop)
  map_id s := coarseMap_id N E h s.unop
  map_comp f g := (coarseMap_comp N E h (leOfHom g.unop) (leOfHom f.unop)).symm
/-- Eの細側実複体を同じ署名反対圏上の関手へまとめる。 -/
def fineFunctor : (SupportSignature.Signature N E h)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} ℚ) ℤ where
  obj s := fineComplex N E h s.unop
  map f := fineMap N E h (leOfHom f.unop)
  map_id s := fineMap_id N E h s.unop
  map_comp f g := (fineMap_comp N E h (leOfHom g.unop) (leOfHom f.unop)).symm
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 各署名における実 A-subnerve 比較の標準零延長。 -/
def comparison (s : SupportSignature.Signature N E h) : coarseComplex N E h s ⟶ fineComplex N E h s :=
  zeroExtensionMap (M.aSubnerveComparisonHom (representative N E h s))
/-- 実比較は署名包含の台制限と可換する。 -/
theorem comparison_natural (hst : s ≤ t) :
    comparison N E h M t ≫ fineMap N E h hst = coarseMap N E h hst ≫ comparison N E h M s :=
  SupportRestriction.complex_square N E h (alpha_le N E h hst) M
/-- 同じ原始比較は二つの反対圏関手の自然変換になる。 -/
def comparisonNat : coarseFunctor N E h ⟶ fineFunctor N E h where
  app s := comparison N E h M s.unop
  naturality _ _ f := (comparison_natural N E h M (leOfHom f.unop)).symm
end AAT.AG.AtlasDefectComposition.SupportFunctor
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportFunctor
