import ResearchLean.AG.AtlasDefectComposition.SupportFunctor
import Formal.Util.AssertStandardAxioms
/-! # 台署名上の実錐関手

Implementation notes: 実比較自然変換の各正方形に標準 mappingCone.map を適用する。
恒等・合成は両側の実制限関手と標準錐射の法則から従う。
-/
noncomputable section
open CategoryTheory CochainComplex Opposite
namespace AAT.AG.AtlasDefectComposition.SupportFunctor
open CanonicalResolution ResolutionInvariance TwoPhase
universe u v
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve.{u,v} q) (E : TargetSupportedNerve.{u,v} r) (h : q.CoarserThan r)
variable (M : TargetSupportedNerveMorphism q r h N E)
variable {s t z : SupportSignature.Signature N E h}
/-- 各署名の実比較錐。 -/
def cone (s : SupportSignature.Signature N E h) := mappingCone (comparison N E h M s)
/-- 署名包含の実可換正方形が誘導する逆向き錐射。 -/
def coneMap (hst : s ≤ t) : cone N E h M t ⟶ cone N E h M s :=
  mappingCone.map _ _ (coarseMap N E h hst) (fineMap N E h hst) (comparison_natural N E h M hst)
/-- 錐の台制限は恒等を保つ。 -/
theorem coneMap_id (s : SupportSignature.Signature N E h) : coneMap N E h M (le_refl s) = 𝟙 _ := by
  unfold coneMap
  simpa only [coarseMap_id,fineMap_id] using mappingCone.map_id (comparison N E h M s)
/-- 錐の台制限は逆向き合成を保つ。 -/
theorem coneMap_comp (hst : s ≤ t) (htz : t ≤ z) :
    coneMap N E h M htz ≫ coneMap N E h M hst = coneMap N E h M (hst.trans htz) := by
  unfold coneMap
  simpa only [coarseMap_comp,fineMap_comp] using
    (mappingCone.map_comp (comparison N E h M z) (comparison N E h M t)
      (comparison N E h M s) (coarseMap N E h htz) (fineMap N E h htz)
      (comparison_natural N E h M htz) (coarseMap N E h hst) (fineMap N E h hst)
      (comparison_natural N E h M hst)).symm
/-- 実比較錐の署名反対圏上の関手。射も原始比較と実制限から生成する。 -/
def coneFunctor : (SupportSignature.Signature N E h)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} ℚ) ℤ where
  obj s := cone N E h M s.unop
  map f := coneMap N E h M (leOfHom f.unop)
  map_id s := coneMap_id N E h M s.unop
  map_comp f g := (coneMap_comp N E h M (leOfHom g.unop) (leOfHom f.unop)).symm
/-- 各整数次数の錐 homology も同じ実射の関手である。 -/
def coneHomologyFunctor (m : ℤ) := coneFunctor N E h M ⋙ HomologicalComplex.homologyFunctor _ _ m
end AAT.AG.AtlasDefectComposition.SupportFunctor
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportFunctor
