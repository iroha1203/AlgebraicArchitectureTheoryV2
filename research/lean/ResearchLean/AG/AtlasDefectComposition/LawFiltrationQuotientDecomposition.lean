import ResearchLean.AG.AtlasDefectComposition.LawFiniteModelDecomposition
import ResearchLean.AG.AtlasDefectComposition.FiltrationNaturalFunctors
import Formal.Util.AssertStandardAxioms
/-! # 実部分複体と実逐次商の全Law直和

Implementation notes: 実Subobjectのunderlyingと実cokernelの加法的関手を使う。
全Lawの有限filtrationを同じ全発生ラベルの有限filtrationへ全指定射で接続する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} [Fintype Source] {n : ℕ}
variable (P : Fin (n+1) ⥤ RawResolution Source) (laws : FiniteLawFamily Source)
variable (ha : laws.Adequate (P.obj 0).reading)
local instance (T : (Fin (n+1) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ) ⥤
    CochainComplex (ModuleCat.{u} ℚ) ℤ) :
    HasBiproduct (T.obj ∘ lawLabelPathDiagram P laws ha) := HasBiproduct.of_hasProduct _
/-- F の全Law実部分複体を全ラベル実部分複体の標準直和へ移す。 -/
def lawFiltrationStageSumIso (i : Fin (n+1)) :=
  lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i)
/-- F の全Law実部分複体の逐次cokernelを全ラベル実逐次商の標準直和へ移す。 -/
def lawFiltrationQuotientSumIso (i : Fin n) :=
  lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.filtrationQuotientFunctor n i)
/-- F の実部分複体包含は全ラベル実包含の直和となる。 -/
theorem law_filtration_inclusion_sum (i : Fin n) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i.castSucc)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i.castSucc).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i.succ).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationInclusionNatTrans n i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationInclusionNatTrans n i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i.succ)).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationInclusionNatTrans n i))
/-- F の実部分複体から実商への射は全ラベル商射の直和となる。 -/
theorem law_filtration_quotient_projection_sum (i : Fin n) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i.succ)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i.succ).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.filtrationQuotientFunctor n i).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationQuotientProjectionNatTrans n i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationQuotientProjectionNatTrans n i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.filtrationQuotientFunctor n i)).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationQuotientProjectionNatTrans n i))
/-- F の実部分複体商の指定同値のhomは全ラベル指定射の直和となる。 -/
theorem law_filtration_quotient_equivalence_sum (i : Fin n) :
    (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.filtrationQuotientFunctor n i)).hom ≫
      biproduct.map (f := (ConeTower.extendFunctor n ⋙ ConeTower.filtrationQuotientFunctor n i).obj ∘ lawLabelPathDiagram P laws ha)
        (g := (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i.val).obj ∘ lawLabelPathDiagram P laws ha)
        (fun l => (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationQuotientEquivNatTrans n i)).app (lawLabelPathDiagram P laws ha l)) =
      (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationQuotientEquivNatTrans n i)).app (lawPathDiagram P laws ha) ≫
        (lawConstructionSumIso P laws ha (ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i.val)).hom :=
  lawConstructionSumIso_natural P laws ha _ _ (Functor.whiskerLeft (ConeTower.extendFunctor n) (ConeTower.filtrationQuotientEquivNatTrans n i))
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
