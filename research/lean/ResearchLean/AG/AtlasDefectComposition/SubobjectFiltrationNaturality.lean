import ResearchLean.AG.AtlasDefectComposition.FiniteConeFiltration
import ResearchLean.AG.AtlasDefectComposition.ConeTowerNaturalFunctors
import Formal.Util.AssertStandardAxioms
/-! # 実部分複体 filtration と実逐次商の台自然性

Implementation notes: terminal の実 Subobject の underlying 同型から射を生成する。
元のモデル射が全埋め込みと可換するので、各実部分複体と実商へ誘導できる。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable {C D : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ} (τ : C ⟶ D)
/-- terminal埋め込みは元の自然変換の指定モデル射に自然である。 -/
theorem embedding_natural (n : ℕ) (i : Fin (n+1)) :
    embedding C n i ≫ modelMap τ n = modelMap τ i.val ≫ embedding D n i := by
  simpa only [modelNatTrans_app] using
    (modelNatTrans τ).naturality (homOfLE (Nat.le_of_lt_succ i.isLt))
/-- 全有限段の実部分複体を指定モデル射から送る実射。 -/
def filtrationMap (n : ℕ) (i : Fin (n+1)) :
    (filtration C n i : CochainComplex (ModuleCat.{w} ℚ) ℤ) ⟶
      (filtration D n i : CochainComplex (ModuleCat.{w} ℚ) ℤ) :=
  (Subobject.underlyingIso (embedding C n i)).hom ≫ modelMap τ i.val ≫
    (Subobject.underlyingIso (embedding D n i)).inv
/-- 実部分複体の射は terminal 全体への実包含と可換する。 -/
theorem filtrationMap_arrow (n : ℕ) (i : Fin (n+1)) :
    filtrationMap τ n i ≫ (filtration D n i).arrow =
      (filtration C n i).arrow ≫ modelMap τ n := by
  rw [filtration_arrow,filtration_arrow]
  dsimp only [filtrationMap]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [embedding_natural]
/-- 実filtrationの全隣接包含は元のモデル制限と可換する。 -/
theorem filtrationInclusion_natural (n : ℕ) (i : Fin n) :
    filtrationInclusion C n i ≫ filtrationMap τ n i.succ =
      filtrationMap τ n i.castSucc ≫ filtrationInclusion D n i := by
  rw [filtrationInclusion_eq,filtrationInclusion_eq]
  dsimp only [filtrationMap,Fin.val_castSucc,Fin.val_succ]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [← Category.assoc (inclusion C i.val),inclusion_natural]
  simp only [Category.assoc]
/-- 実filtration隣接包含の実cokernelを送る指定射。 -/
def filtrationQuotientMap (n : ℕ) (i : Fin n) :
    cokernel (filtrationInclusion C n i) ⟶ cokernel (filtrationInclusion D n i) :=
  cokernel.map _ _ (filtrationMap τ n i.castSucc) (filtrationMap τ n i.succ)
    (filtrationInclusion_natural τ n i)
/-- F の実部分複体商の指定同値の射は同じ台自然変換に自然である。 -/
theorem filtrationQuotientEquiv_hom_natural (n : ℕ) (i : Fin n) :
    filtrationQuotientMap τ n i ≫ (filtrationQuotientEquiv D n i).hom =
      (filtrationQuotientEquiv C n i).hom ≫ adjacentConeMap τ i.val := by
  apply (cancel_epi (cokernel.π (filtrationInclusion C n i))).mp
  rw [filtrationQuotientEquiv_hom,filtrationQuotientEquiv_hom]
  dsimp only [filtrationQuotientMap]
  simp only [Category.assoc,cokernel.π_desc_assoc]
  dsimp only [filtrationMap,Fin.val_succ]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  simpa only [Category.assoc,quotientMap_π_assoc] using congrArg
    (fun k => (Subobject.underlyingIso (embedding C n i.succ)).hom ≫
      cokernel.π (inclusion C i.val) ≫ k) (successiveQuotientEquiv_hom_natural τ i.val)
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
