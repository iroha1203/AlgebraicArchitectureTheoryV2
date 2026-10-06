import ResearchLean.AG.AtlasDefectComposition.FiniteSubsetPath
import ResearchLean.AG.AtlasDefectComposition.BoundedConeModels
import ResearchLean.AG.AtlasDefectComposition.ConeModelFunctors
import Mathlib.CategoryTheory.Whiskering
import Formal.Util.AssertStandardAxioms
/-! # 同じ有限原始入力への tower と有限モデルの適用

Implementation notes: source/reading/nerve/原始射から生成した実 diagram に構成を適用する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {n : ℕ} (P : Fin (n+1) ⥤ RawResolution Source)
/-- 同じ q₀ subset の全段実 tower の入力 diagram。 -/
def subsetTowerInput (A : Set (P.obj 0).reading.Target) := ConeTower.extend (subsetPathDiagram P A)
/-- 任意の全段モデルへの実q₀部分集合入力の射影同値。 -/
def subsetModelEquiv (A : Set (P.obj 0).reading.Target) (i : Fin (n+1)) :
    HomotopyEquiv (ConeTower.model (subsetTowerInput P A) i.val)
      (ConeTower.cone (subsetTowerInput P A) i.val) := ConeTower.augmentation _ _
/-- 実原始subset入力における有限部分複体filtration。 -/
def subsetModelFiltration (A : Set (P.obj 0).reading.Target) :=
  ConeTower.filtration (subsetTowerInput P A) n
/-- 実部分複体の実逐次商と実隣接錐の同値。 -/
def subsetFiltrationQuotientEquiv (A : Set (P.obj 0).reading.Target) (i : Fin n) :=
  ConeTower.filtrationQuotientEquiv (subsetTowerInput P A) n i
/-- 全段の原始subset複体は全整数次数で有限次元である。 -/
theorem subsetTowerInput_finiteDimensional (A : Set (P.obj 0).reading.Target) (i : ℕ) (m : ℤ) :
    FiniteDimensional ℚ (((subsetTowerInput P A).obj i).X m) := by
  change FiniteDimensional ℚ (degreeObject _ m)
  infer_instance
/-- 全段の原始subset複体は三項の次数範囲を持つ。 -/
theorem subsetTowerInput_isZero (A : Set (P.obj 0).reading.Target) (i : ℕ) (m : ℤ)
    (hm : m < 0 ∨ 2 < m) : IsZero (((subsetTowerInput P A).obj i).X m) :=
  degreeObject_isZero _ m (by omega) (by omega) (by omega)
/-- 実原始subset入力の構成済みモデルは全次数で有限次元である。 -/
theorem subsetModel_finiteDimensional (A : Set (P.obj 0).reading.Target) (i : Fin (n+1)) (m : ℤ) :
    FiniteDimensional ℚ ((ConeTower.model (subsetTowerInput P A) i.val).X m) :=
  ConeTower.model_finite_dimensional _ (subsetTowerInput_finiteDimensional P A) _ _
/-- 実原始subset入力の第 i 段モデルの有限次数範囲。 -/
theorem subsetModel_isZero (A : Set (P.obj 0).reading.Target) (i : Fin (n+1)) (m : ℤ)
    (hm : m < -(i.val : ℤ) ∨ 2 < m) : IsZero ((ConeTower.model (subsetTowerInput P A) i.val).X m) :=
  ConeTower.model_bounded _ (subsetTowerInput_isZero P A) _ _ hm
/-- 全段の同じ署名包含に沿う実モデル tower の制限。 -/
def subsetModelRestriction {A B : Set (P.obj 0).reading.Target}
    (hAB : SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) A ⊆
      SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) B) :=
  ConeTower.modelNatTrans (Functor.whiskerLeft (ConeTower.clamp n) (subsetPathRestriction P hAB))
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate (P.obj 0).reading)
/-- 同じ全Law入力の全段実 tower diagram。 -/
def lawTowerInput := ConeTower.extend (lawPathDiagram P laws ha)
/-- 全Law入力の構成済み有限部分複体filtration。 -/
def lawModelFiltration := ConeTower.filtration (lawTowerInput P laws ha) n
/-- 全Law実包含の逐次商は実隣接全Law錐と同値である。 -/
def lawFiltrationQuotientEquiv (i : Fin n) :=
  ConeTower.filtrationQuotientEquiv (lawTowerInput P laws ha) n i
/-- 全Law diagram の全次数有限次元性は元の有限セルから導く。 -/
theorem lawTowerInput_finiteDimensional (i : ℕ) (m : ℤ) :
    FiniteDimensional ℚ (((lawTowerInput P laws ha).obj i).X m) := by
  change FiniteDimensional ℚ (degreeObject _ m)
  infer_instance
/-- 全Law diagram の三項次数範囲は元の零延長から導く。 -/
theorem lawTowerInput_isZero (i : ℕ) (m : ℤ) (hm : m < 0 ∨ 2 < m) :
    IsZero (((lawTowerInput P laws ha).obj i).X m) :=
  degreeObject_isZero _ m (by omega) (by omega) (by omega)
/-- 全Law実モデルも各次数で有限次元である。 -/
theorem lawModel_finiteDimensional (i : Fin (n+1)) (m : ℤ) :
    FiniteDimensional ℚ ((ConeTower.model (lawTowerInput P laws ha) i.val).X m) :=
  ConeTower.model_finite_dimensional _ (lawTowerInput_finiteDimensional P laws ha) _ _
/-- 全Law実モデルは同じ有限次数範囲を持つ。 -/
theorem lawModel_isZero (i : Fin (n+1)) (m : ℤ) (hm : m < -(i.val : ℤ) ∨ 2 < m) :
    IsZero ((ConeTower.model (lawTowerInput P laws ha) i.val).X m) :=
  ConeTower.model_bounded _ (lawTowerInput_isZero P laws ha) _ _ hm
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
