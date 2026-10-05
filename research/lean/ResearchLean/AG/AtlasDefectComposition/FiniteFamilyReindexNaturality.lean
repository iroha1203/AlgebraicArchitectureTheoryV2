import ResearchLean.AG.AtlasDefectComposition.FiniteFamilyReindex
import Formal.Util.AssertStandardAxioms
/-! # 指定族並べ替えと実比較の自然性

Implementation notes: 元の添字全単射の transport は eqToHom の自然性で処理する。
各対応成分の正方形だけから全族の正方形を構成する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.FiniteFamilyReindex
universe u v
variable {J K : Type u} (F F' : J → CochainComplex (ModuleCat.{max u v} ℚ) ℤ)
variable (G G' : K → CochainComplex (ModuleCat.{max u v} ℚ) ℤ) (e : J ≃ K)
variable (a : ∀ j, F j ⟶ F' j) (b : ∀ k, G k ⟶ G' k)
variable (sc : ∀ j, F j ≅ G (e j)) (sf : ∀ j, F' j ≅ G' (e j))
variable (h : ∀ j, a j ≫ (sf j).hom = (sc j).hom ≫ b (e j))
include h in
/-- 逆添字の同じ型へ transport した成分同型も元の比較と可換する。 -/
theorem block_square (k : K) : a (e.symm k) ≫ (blockIso F' e G' sf k).hom =
    (blockIso F e G sc k).hom ≫ b k := by
  simp only [blockIso,Iso.trans_hom,eqToIso.hom]
  rw [← Category.assoc,h,Category.assoc,eqToHom_naturality b (e.apply_symm_apply k)]
  rw [Category.assoc]
include h in
/-- 指定添字並べ替え同型は実族比較と可換である。 -/
theorem square : FiniteComplexFamily.map F F' a ≫ (iso F' e G' sf).hom =
    (iso F e G sc).hom ≫ FiniteComplexFamily.map G G' b := by
  ext m x
  funext k
  change (blockIso F' e G' sf k).hom.f m ((a (e.symm k)).f m (x (e.symm k))) =
    (b k).f m ((blockIso F e G sc k).hom.f m (x (e.symm k)))
  exact congrArg (fun f => f.f m (x (e.symm k))) (block_square F F' G G' e a b sc sf h k)
end AAT.AG.AtlasDefectComposition.FiniteFamilyReindex
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.FiniteFamilyReindex
