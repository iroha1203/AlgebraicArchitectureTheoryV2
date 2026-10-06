import ResearchLean.AG.AtlasDefectComposition.ConeCompositionHomotopy
import ResearchLean.AG.AtlasDefectComposition.ConeHomotopyTransport
import Mathlib.CategoryTheory.Functor.OfSequence
import Formal.Util.AssertStandardAxioms
/-! # 実累積比較の錐と零から始まるモデル tower

Implementation notes: 原始生成複体の diagram に適用できる一般構成。
モデル包含の実cokernelを構成し、元の射の単射性は要求しない。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
open scoped ZeroObject
namespace AAT.AG.AtlasDefectComposition.ConeTower
universe w
variable (C : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ)
/-- 基底から各段への diagram の実射。 -/
def cumulative (i : ℕ) : C.obj 0 ⟶ C.obj i := C.map (homOfLE (Nat.zero_le i))
/-- diagram の実隣接射。 -/
def adjacent (i : ℕ) : C.obj i ⟶ C.obj (i+1) := C.map (homOfLE (Nat.le_add_right i 1))
/-- 累積射は diagram の合成と一致する。 -/
theorem cumulative_comp (i : ℕ) : cumulative C (i+1) = cumulative C i ≫ adjacent C i := by
  simpa only [cumulative,adjacent] using
    C.map_comp (homOfLE (Nat.zero_le i)) (homOfLE (Nat.le_add_right i 1))
/-- 各段の実累積錐。 -/
def cone (i : ℕ) := mappingCone (cumulative C i)
/-- 累積錐と隣接錐を結ぶ全三射の標準 triangle。 -/
def triangle (i : ℕ) := compositionTriangle (cumulative C i) (adjacent C i)
  (cumulative C (i+1)) (cumulative_comp C i)
/-- 実累積錐の tower 射。 -/
def step (i : ℕ) : cone C i ⟶ cone C (i+1) := (triangle C i).mor₁
/-- F の累積 tower 射の公開式。triangle の内部を下流で展開しない。 -/
theorem step_eq (i : ℕ) : step C i =
    mappingCone.map (cumulative C i) (cumulative C (i+1)) (𝟙 (C.obj 0))
      (adjacent C i) (by rw [cumulative_comp C i];simp) :=
  compositionTriangle_mor₁ _ _ _ _
/-- 各段の triangle は distinguished である。 -/
theorem triangle_distinguished (i : ℕ) :
    (HomotopyCategory.quotient (ModuleCat.{w} ℚ) (ComplexShape.up ℤ)).mapTriangle.obj
      (triangle C i) ∈ distTriang (HomotopyCategory (ModuleCat.{w} ℚ) (ComplexShape.up ℤ)) :=
  compositionTriangle_distinguished _ _ _ _
/-- 反復累積錐は実隣接錐に homotopy 同値である。 -/
def stepConeEquiv (i : ℕ) : HomotopyEquiv (mappingCone (step C i)) (mappingCone (adjacent C i)) :=
  (compositionTriangleConeEquiv _ _ _ (cumulative_comp C i)).symm
/-- 初段の累積比較は恒等である。 -/
@[simp] theorem cumulative_zero : cumulative C 0 = 𝟙 _ := by
  simpa only [cumulative,show homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) from Subsingleton.elim _ _]
    using C.map_id 0
/-- 初段の累積錐は元の恒等錐から contractible である。 -/
def zeroContractible : Homotopy (𝟙 (cone C 0)) 0 := by
  let e : HomotopyEquiv (mappingCone (𝟙 (C.obj 0))) (cone C 0) :=
    coneMapHomotopyEquiv (𝟙 _) (cumulative C 0) (HomotopyEquiv.refl _)
      (HomotopyEquiv.refl _) (by simp [HomotopyEquiv.refl])
  exact e.homotopyInvHomId.symm.trans (by
    simpa only [zero_comp,comp_zero] using
      ((mappingCone.homotopyToZeroOfId (C.obj 0)).compLeft e.inv).compRight e.hom)
/-- 初段を実零複体から始める指定 homotopy 同値。 -/
def initialEquiv : HomotopyEquiv (0 : CochainComplex (ModuleCat.{w} ℚ) ℤ) (cone C 0) where
  hom := 0
  inv := 0
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := by simpa using (zeroContractible C).symm
/-- 各累積錐に指定 homotopy 同値を持つ構成済みモデル。 -/
structure ModelStage (i : ℕ) where
  complex : CochainComplex (ModuleCat.{w} ℚ) ℤ
  equivalence : HomotopyEquiv complex (cone C i)
/-- 零から始め、指定比較の mapping cylinder を反復したモデル。 -/
def stage : (i : ℕ) → ModelStage C i
  | 0 => ⟨0,initialEquiv C⟩
  | i+1 =>
    ⟨MappingCylinder.model ((stage i).equivalence.hom ≫ step C i),
      MappingCylinder.projectionHomotopyEquiv _⟩
/-- 各累積錐に同値な実モデル複体。 -/
def model (i : ℕ) := (stage C i).complex
/-- 各モデルの指定射影は累積錐への homotopy 同値である。 -/
def augmentation (i : ℕ) : HomotopyEquiv (model C i) (cone C i) := (stage C i).equivalence
/-- F の指定モデルの初段は実零複体である。 -/
@[simp] theorem model_zero : model C 0 = 0 := rfl
/-- F の零始点から累積錐への指定射影の公開式。 -/
@[simp] theorem augmentation_zero_hom : (augmentation C 0).hom = 0 := rfl
/-- 原始 tower 射を実モデルに結ぶ指定 chain map。 -/
def modelArrow (i : ℕ) : model C i ⟶ cone C (i+1) := (augmentation C i).hom ≫ step C i
/-- 零から始まる実モデルの隣接包含。 -/
def inclusion (i : ℕ) : model C i ⟶ model C (i+1) := MappingCylinder.inclusion (modelArrow C i)
/-- 元の比較の単射性によらない全次数のモデル包含。 -/
instance inclusion_degree_mono (i : ℕ) (m : ℤ) : Mono ((inclusion C i).f m) :=
  MappingCylinder.inclusion_degree_mono _ _
/-- 実モデル包含は部分複体の包含として単射である。 -/
instance inclusion_mono (i : ℕ) : Mono (inclusion C i) := MappingCylinder.inclusion_mono _
/-- 指定射影と実モデル包含は元の tower 射と可換する。 -/
theorem augmentation_square (i : ℕ) :
    inclusion C i ≫ (augmentation C (i+1)).hom = (augmentation C i).hom ≫ step C i :=
  MappingCylinder.factorization _
/-- 実包含の実逐次商と実隣接錐の chain homotopy 同値。 -/
def successiveQuotientEquiv (i : ℕ) :
    HomotopyEquiv (cokernel (inclusion C i)) (mappingCone (adjacent C i)) :=
  (HomotopyEquiv.ofIso (MappingCylinder.cokernelIso (modelArrow C i))).trans
    ((coneMapHomotopyEquiv (modelArrow C i) (step C i) (augmentation C i)
      (HomotopyEquiv.refl _) (by simp [modelArrow,HomotopyEquiv.refl])).trans (stepConeEquiv C i))
/-- 実単射列としてのモデル tower。 -/
def modelDiagram : ℕ ⥤ CochainComplex (ModuleCat.{w} ℚ) ℤ := Functor.ofSequence (inclusion C)
end AAT.AG.AtlasDefectComposition.ConeTower
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ConeTower
