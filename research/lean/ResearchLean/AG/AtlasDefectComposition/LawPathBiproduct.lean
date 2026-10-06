import ResearchLean.AG.AtlasDefectComposition.FiniteSubsetPath
import ResearchLean.AG.AtlasDefectComposition.FiniteDiagramBiproduct
import ResearchLean.AG.AtlasDefectComposition.LawFiberDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 有限原始比較図式の全Law直和

Implementation notes: 同じ q₀ の全発生ラベル fiber を全段へ引き戻す。
各 block 同型と独立生成比較の既存自然性を diagram 同型へ接続し、
同じ署名へ写る異なるラベルも別の biproduct 添字として保持する。
-/
noncomputable section
open CategoryTheory Limits
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
universe u
variable {Source : Type u} [Fintype Source] {n : ℕ}
variable (P : Fin (n+1) ⥤ RawResolution Source) (laws : FiniteLawFamily Source)
variable (ha : laws.Adequate (P.obj 0).reading)
/-- 有限比較で一つの元ラベルを保持する実 q₀-fiber diagram。 -/
def lawLabelPathDiagram (l : LawValueLabel laws) :=
  subsetPathDiagram P (labelValueFiber laws (P.obj 0).reading ha l)
/-- 各段の元 block を同じ基底 fiber の逆像複体へ移す指定同型。 -/
def lawPathBlockIso (i : Fin (n+1)) (l : LawValueLabel laws) :
    zeroExtension ((P.obj i).nerve.lawValueBlockComplex laws (pathAdequate P laws ha i) l) ≅
      (lawLabelPathDiagram P laws ha l).obj i :=
  lawBlockSelectedSubsetZeroExtensionIso (P.obj i).nerve laws (pathAdequate P laws ha i) l
    _ (labelValueFiber_eq_preimage laws (P.obj 0).reading (P.obj i).reading
      ha (pathAdequate P laws ha i) (pathCoarser P i) l)
/-- 元 block の指定同型は元の全有限対射から生成した比較に自然である。 -/
theorem lawPathBlockIso_natural {i j : Fin (n+1)} (f : i ⟶ j) (l : LawValueLabel laws) :
    zeroExtensionMap ((P.map f).2.generatedBlockComparisonHom laws
      (pathAdequate P laws ha i) (pathAdequate P laws ha j) l) ≫
        (lawPathBlockIso P laws ha j l).hom =
      (lawPathBlockIso P laws ha i l).hom ≫ (lawLabelPathDiagram P laws ha l).map f :=
  lawBlockSelectedSubsetZeroExtensionIso_natural (P.obj i).nerve (P.obj j).nerve
    laws (pathAdequate P laws ha i) (P.map f).2 (pathAdequate P laws ha j) l _ _ _ _
    (SupportStages.pair_mapsTo (pathReadings P) (pathCoarser P)
      i j (P.map f).1 (labelValueFiber laws (P.obj 0).reading ha l))
/-- 全Lawを全ラベルの同じ基底 fiber 族へ移す各段の指定同型。 -/
def lawPathFamilyIso (i : Fin (n+1)) : (lawPathDiagram P laws ha).obj i ≅
    (FiniteComplexFamily.diagram (lawLabelPathDiagram P laws ha)).obj i :=
  lawZeroExtensionIso (P.obj i).nerve laws (pathAdequate P laws ha i) ≪≫
    FiniteComplexFamily.iso _ _ (lawPathBlockIso P laws ha i)
/-- 全Lawの各段同型は全原始比較から独立に生成した射に自然である。 -/
theorem lawPathFamilyIso_natural {i j : Fin (n+1)} (f : i ⟶ j) :
    (lawPathDiagram P laws ha).map f ≫ (lawPathFamilyIso P laws ha j).hom =
      (lawPathFamilyIso P laws ha i).hom ≫
        (FiniteComplexFamily.diagram (lawLabelPathDiagram P laws ha)).map f := by
  rw [lawPathDiagram_map,FiniteComplexFamily.diagram_map]
  dsimp only [lawPathFamilyIso,Iso.trans_hom]
  rw [← Category.assoc,lawZeroExtensionIso_natural,Category.assoc]
  rw [FiniteComplexFamily.iso_natural _ _ _ _ _ _
    (lawPathBlockIso_natural P laws ha f)]
  simp only [Category.assoc]
/-- 全ラベル族を保持する全Law diagram の自然同型。 -/
def lawPathFamilyNatIso : lawPathDiagram P laws ha ≅
    FiniteComplexFamily.diagram (lawLabelPathDiagram P laws ha) :=
  NatIso.ofComponents (lawPathFamilyIso P laws ha) (lawPathFamilyIso_natural P laws ha)
local instance : HasBiproduct (lawLabelPathDiagram P laws ha) :=
  HasBiproduct.of_hasProduct _
/-- F の全Law有限比較図式を同じ q₀ ラベル fiber の全標準直和へ同定する。 -/
def lawPathBiproductIso : lawPathDiagram P laws ha ≅ ⨁ (lawLabelPathDiagram P laws ha) :=
  lawPathFamilyNatIso P laws ha ≪≫ FiniteComplexFamily.diagramBiproductIso _
/-- 全Law直和同型は全有限対射を同じ元ラベル比較へ移す。 -/
theorem lawPathBiproductIso_natural {i j : Fin (n+1)} (f : i ⟶ j) :
    (lawPathDiagram P laws ha).map f ≫ (lawPathBiproductIso P laws ha).hom.app j =
      (lawPathBiproductIso P laws ha).hom.app i ≫ (⨁ (lawLabelPathDiagram P laws ha)).map f :=
  (lawPathBiproductIso P laws ha).hom.naturality f
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
