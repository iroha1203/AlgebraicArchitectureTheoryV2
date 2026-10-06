import ResearchLean.AG.AtlasDefectComposition.FiniteSubsetPath
import ResearchLean.AG.AtlasDefectComposition.FiniteIndexTransport
import ResearchLean.AG.AtlasDefectComposition.FiltrationNaturalFunctors
import Formal.Util.AssertStandardAxioms
/-! # 全有限段の共通台署名上の実欠損構成

Implementation notes: 元の全段・全次数・元セル名を保持する共通署名を使う。
署名代表の実制限を diagram 関手へ組み立て、加法的モデル・錐・実商へ同じ射を通す。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {n : ℕ} (P : Fin (n+1) ⥤ RawResolution Source)
/-- 任意の全有限段の元セルを保持する共通台署名。 -/
abbrev PathSignature := SupportStages.Signature (pathReadings P) (pathNerves P) (pathCoarser P)
/-- 共通台署名の反対圏上の元の全有限比較図式。 -/
def signaturePathDiagram : (PathSignature P)ᵒᵖ ⥤
    (Fin (n+1) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ) where
  obj s := subsetPathDiagram P (SupportStages.representative _ _ _ s.unop)
  map f := subsetPathRestriction P (SupportStages.representativeLE _ _ _ (leOfHom f.unop))
  map_id _ := subsetPathRestriction_id P _
  map_comp _ _ := subsetPathRestriction_comp P _ _
/-- 同じ共通全セル署名の二subsetは実有限図式の同じセル制限で同型になる。 -/
def subsetPathSameSignatureIso (A B : Set (P.obj 0).reading.Target)
    (h : SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) A =
      SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) B) :
    subsetPathDiagram P A ≅ subsetPathDiagram P B where
  hom := subsetPathRestriction P h.ge
  inv := subsetPathRestriction P h.le
  hom_inv_id := by
    rw [← subsetPathRestriction_comp]
    exact subsetPathRestriction_id P A
  inv_hom_id := by
    rw [← subsetPathRestriction_comp]
    exact subsetPathRestriction_id P B
/-- 元の任意subset図式とその同じ共通署名の代表図式との実同型。 -/
def subsetPathSignatureIso (A : Set (P.obj 0).reading.Target) :
    subsetPathDiagram P A ≅ (signaturePathDiagram P).obj
      (Opposite.op (SupportStages.sigma (pathReadings P) (pathNerves P) (pathCoarser P) A)) :=
  subsetPathSameSignatureIso P _ _ (SupportStages.alpha_representative
    (pathReadings P) (pathNerves P) (pathCoarser P)
    (SupportStages.sigma (pathReadings P) (pathNerves P) (pathCoarser P) A)).symm
/-- 共通署名に沿う各段の実累積錐関手。 -/
def signatureConeFunctor (i : ℕ) :=
  signaturePathDiagram P ⋙ ConeTower.extendFunctor n ⋙ ConeTower.coneFunctor i
/-- 共通署名に沿う零始点の実有限モデル関手。 -/
def signatureModelFunctor (i : ℕ) :=
  signaturePathDiagram P ⋙ ConeTower.extendFunctor n ⋙ ConeTower.modelFunctor i
/-- 共通署名に沿う実モデル包含の実逐次cokernel関手。 -/
def signatureQuotientFunctor (i : ℕ) :=
  signaturePathDiagram P ⋙ ConeTower.extendFunctor n ⋙ ConeTower.quotientFunctor i
/-- 共通署名に沿う元の実隣接錐関手。 -/
def signatureAdjacentConeFunctor (i : ℕ) :=
  signaturePathDiagram P ⋙ ConeTower.extendFunctor n ⋙ ConeTower.adjacentConeFunctor i
/-- 共通署名上の実モデル包含の自然変換。 -/
def signatureInclusion (i : ℕ) : signatureModelFunctor P i ⟶ signatureModelFunctor P (i+1) :=
  Functor.whiskerLeft (signaturePathDiagram P ⋙ ConeTower.extendFunctor n) (ConeTower.inclusionNatTrans i)
/-- 共通署名上の実モデル射影の自然変換。 -/
def signatureAugmentation (i : ℕ) : signatureModelFunctor P i ⟶ signatureConeFunctor P i :=
  Functor.whiskerLeft (signaturePathDiagram P ⋙ ConeTower.extendFunctor n) (ConeTower.augmentationNatTrans i)
/-- 共通署名上の実商の指定homotopy同値のhomの自然変換。 -/
def signatureQuotientEquivalence (i : ℕ) : signatureQuotientFunctor P i ⟶ signatureAdjacentConeFunctor P i :=
  Functor.whiskerLeft (signaturePathDiagram P ⋙ ConeTower.extendFunctor n) (ConeTower.quotientEquivNatTrans i)
/-- 共通署名に沿うterminalモデルの実部分複体関手。 -/
def signatureFiltrationStageFunctor (i : Fin (n+1)) :=
  signaturePathDiagram P ⋙ ConeTower.extendFunctor n ⋙ ConeTower.filtrationStageFunctor n i
/-- 共通署名に沿う実部分複体包含の実逐次cokernel関手。 -/
def signatureFiltrationQuotientFunctor (i : Fin n) :=
  signaturePathDiagram P ⋙ ConeTower.extendFunctor n ⋙ ConeTower.filtrationQuotientFunctor n i
/-- 共通署名上の実部分複体包含の自然変換。 -/
def signatureFiltrationInclusion (i : Fin n) :
    signatureFiltrationStageFunctor P i.castSucc ⟶ signatureFiltrationStageFunctor P i.succ :=
  Functor.whiskerLeft (signaturePathDiagram P ⋙ ConeTower.extendFunctor n)
    (ConeTower.filtrationInclusionNatTrans n i)
/-- 共通署名上の実部分複体商の指定同値のhomの自然変換。 -/
def signatureFiltrationQuotientEquivalence (i : Fin n) :
    signatureFiltrationQuotientFunctor P i ⟶ signatureAdjacentConeFunctor P i.val :=
  Functor.whiskerLeft (signaturePathDiagram P ⋙ ConeTower.extendFunctor n)
    (ConeTower.filtrationQuotientEquivNatTrans n i)
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
