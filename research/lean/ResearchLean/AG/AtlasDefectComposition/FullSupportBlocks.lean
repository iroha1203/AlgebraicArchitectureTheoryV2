import ResearchLean.AG.AtlasDefectComposition.FullSupportCoordinates
import ResearchLean.AG.ResolutionInvariance.LawValueCoordinateSubnerve
import Formal.Util.AssertStandardAxioms

/-! # 全台の各Law blockと名付きセル

M1の全台座標を一つの発生ラベルへ制限し、微分と元のincidenceを接続する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source Cell : Type u}

/-- 全台の一つの発生ラベルblockは元の名付きセルと同定できる。 -/
def fullBlockCoordinateEquiv (laws : FiniteLawFamily Source) (q : Reading Source)
    (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ) (label : LawValueLabel laws) :
    CellCoordinate.Block laws q ha Cell support label ≃ Cell :=
  Equiv.ofBijective (fun c => c.val.cell) ⟨
    CellCoordinate.block_cell_injective laws q ha Cell support label, by
    intro c
    refine ⟨⟨(fullCoordinateEquiv laws q ha support hs).symm (c, label), ?_⟩, rfl⟩
    apply LawValueLabel.ext <;> rfl⟩

/-- 全台block座標の逆は元のセル名を保持する。 -/
@[simp] theorem fullBlockCoordinateEquiv_symm_cell (laws : FiniteLawFamily Source)
    (q : Reading Source) (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ) (label : LawValueLabel laws) (c : Cell) :
    ((fullBlockCoordinateEquiv laws q ha support hs label).symm c).val.cell = c :=
  (fullBlockCoordinateEquiv laws q ha support hs label).apply_symm_apply c

/-- 全台の一ラベルcochainを名付きセルの関数へ移す線形同型。 -/
def fullBlockCochainEquiv (laws : FiniteLawFamily Source) (q : Reading Source)
    (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ) (label : LawValueLabel laws) :
    (CellCoordinate.Block laws q ha Cell support label → ℚ) ≃ₗ[ℚ] (Cell → ℚ) where
  toFun x c := x ((fullBlockCoordinateEquiv laws q ha support hs label).symm c)
  invFun x b := x b.val.cell
  left_inv x := funext (fun b => congrArg x
    ((fullBlockCoordinateEquiv laws q ha support hs label).symm_apply_apply b))
  right_inv x := funext (fun c => congrArg x
    (fullBlockCoordinateEquiv_symm_cell laws q ha support hs label c))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 全台block cochain同型の評価API。 -/
@[simp] theorem fullBlockCochainEquiv_apply (laws : FiniteLawFamily Source)
    (q : Reading Source) (ha : laws.Adequate q) (support : Cell → Set q.Target)
    (hs : ∀ c, support c = Set.univ) (label : LawValueLabel laws)
    (x : CellCoordinate.Block laws q ha Cell support label → ℚ) (c : Cell) :
    fullBlockCochainEquiv laws q ha support hs label x c =
      x ((fullBlockCoordinateEquiv laws q ha support hs label).symm c) := rfl

variable {q : Reading Source} (D : TargetSupportedNerve q)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (hs₀ : ∀ c, D.chartSupport c = Set.univ)
variable (hs₁ : ∀ e, D.edgeSupport e = Set.univ) (label : LawValueLabel laws)

/-- 全台のblock微分は元の辺端点の差を取る。 -/
theorem fullBlock_d0 (c : D.ChartBlockCoordinate laws ha label → ℚ)
    (e : D.nerve.EdgeComponent) :
    fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label
      (D.lawValueBlockD0 laws ha label c) e =
    fullBlockCochainEquiv laws q ha D.chartSupport hs₀ label c (D.nerve.edgeRight e) -
      fullBlockCochainEquiv laws q ha D.chartSupport hs₀ label c (D.nerve.edgeLeft e) := by
  let ec := (fullBlockCoordinateEquiv laws q ha D.edgeSupport hs₁ label).symm e
  have hr : D.edgeRightBlockCoordinate laws ha label ec =
      (fullBlockCoordinateEquiv laws q ha D.chartSupport hs₀ label).symm
        (D.nerve.edgeRight e) := by
    apply CellCoordinate.block_cell_injective laws q ha _ _ label
    change D.nerve.edgeRight ec.val.cell =
      ((fullBlockCoordinateEquiv laws q ha D.chartSupport hs₀ label).symm
        (D.nerve.edgeRight e)).val.cell
    simp only [ec, fullBlockCoordinateEquiv_symm_cell]
  have hl : D.edgeLeftBlockCoordinate laws ha label ec =
      (fullBlockCoordinateEquiv laws q ha D.chartSupport hs₀ label).symm
        (D.nerve.edgeLeft e) := by
    apply CellCoordinate.block_cell_injective laws q ha _ _ label
    change D.nerve.edgeLeft ec.val.cell =
      ((fullBlockCoordinateEquiv laws q ha D.chartSupport hs₀ label).symm
        (D.nerve.edgeLeft e)).val.cell
    simp only [ec, fullBlockCoordinateEquiv_symm_cell]
  change c (D.edgeRightBlockCoordinate laws ha label ec) -
    c (D.edgeLeftBlockCoordinate laws ha label ec) = _
  rw [hr, hl]
  rfl

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
