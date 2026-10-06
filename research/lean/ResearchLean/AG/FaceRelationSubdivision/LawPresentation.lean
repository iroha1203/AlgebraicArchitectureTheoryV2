import ResearchLean.AG.FaceRelationSubdivision.ReadingPullback
import ResearchLean.AG.FaceRelationSubdivision.LawFiberBridge
import Formal.Util.AssertStandardAxioms

/-!
# 表示同型の各Lawラベルにおける実同値

## Implementation notes

Law/valueを保持する座標全単射を各発生ラベルのfiberへ制限する。
両逆を持つこの同じ原始座標射から実block Homの標準同型を生成する。
対象同値だけから射の自然性を推測せず、新比較のblock/fiber可換式を使う。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace CellPresentationEquiv
variable (E : CellPresentationEquiv qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc)

/-- 共通座標constructorが同じ発生Law/valueラベルを保持する。 -/
theorem coordinateEquiv_label {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) (x) :
    (coordinateEquiv (h := h) laws hc e si sj hs x).lawValueLabel laws qc hc J sj =
      x.lawValueLabel laws qf (fineAdequate (h := h) laws hc) I si := by
  apply LawValueLabel.ext <;> rfl

/-- 同じ原始座標全単射を指定Law/valueラベルへ制限する。 -/
def blockCoordinateEquiv {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i))
    (l : LawValueLabel laws) :
    CellCoordinate.Block laws qf (fineAdequate (h := h) laws hc) I si l ≃
      CellCoordinate.Block laws qc hc J sj l where
  toFun x := ⟨coordinateEquiv (h := h) laws hc e si sj hs x.1,
    (coordinateEquiv_label laws hc e si sj hs x.1).trans x.2⟩
  invFun y := ⟨(coordinateEquiv (h := h) laws hc e si sj hs).symm y.1, by
    have hl := coordinateEquiv_label laws hc e si sj hs
      ((coordinateEquiv (h := h) laws hc e si sj hs).symm y.1)
    rw [Equiv.apply_symm_apply] at hl
    exact hl.symm.trans y.2⟩
  left_inv x := by apply Subtype.ext; exact Equiv.symm_apply_apply _ x.1
  right_inv y := by apply Subtype.ext; exact Equiv.apply_symm_apply _ y.1

/-- degree0の指定ラベル座標全単射。 -/
def chartBlockEquiv (l : LawValueLabel laws) : Nf.ChartBlockCoordinate laws (fineAdequate (h := h) laws hc) l ≃
    Nc.ChartBlockCoordinate laws hc l :=
  blockCoordinateEquiv laws hc E.chartEquiv Nf.chartSupport Nc.chartSupport E.chartSupport_eq l
/-- 同じラベル座標は独立生成したblock比較の座標。 -/
theorem chartBlockEquiv_eq_generated (l : LawValueLabel laws) (x) : E.chartBlockEquiv laws hc l x =
    E.comparison.chartBlockCoordinateMap laws hc (fineAdequate (h := h) laws hc) l x := by
  apply Subtype.ext
  apply CellCoordinate.ext <;> rfl
/-- 同じラベルのdegree0cochain同型。 -/
def blockCochain0 (l : LawValueLabel laws) := cochainEquivOfIndexEquiv (E.chartBlockEquiv laws hc l)
/-- 自分のラベル同型の基底評価API。 -/
@[simp] theorem blockCochain0_apply (l : LawValueLabel laws) (z) (x) :
    E.blockCochain0 laws hc l z x = z (E.chartBlockEquiv laws hc l x) := cochainEquivOfIndexEquiv_apply _ _ _
/-- 同じラベルの実degree0射と独立生成式は一致する。 -/
theorem blockCochain0_eq_generated (l : LawValueLabel laws) : (E.blockCochain0 laws hc l).toLinearMap =
    E.comparison.generatedBlockPullback0 laws hc (fineAdequate (h := h) laws hc) l := by
  apply LinearMap.ext
  intro z
  funext x
  rw [LinearEquiv.coe_coe, blockCochain0_apply, IncidenceSupportedComparison.generatedBlockPullback0_apply]
  rw [E.chartBlockEquiv_eq_generated]

/-- degree1の指定ラベル座標全単射。 -/
def edgeBlockEquiv (l : LawValueLabel laws) : Nf.EdgeBlockCoordinate laws (fineAdequate (h := h) laws hc) l ≃
    Nc.EdgeBlockCoordinate laws hc l :=
  blockCoordinateEquiv laws hc E.edgeEquiv Nf.edgeSupport Nc.edgeSupport E.edgeSupport_eq l
/-- 同じラベル座標は独立生成したblock比較の座標。 -/
theorem edgeBlockEquiv_eq_generated (l : LawValueLabel laws) (x) : E.edgeBlockEquiv laws hc l x =
    E.comparison.edgeBlockCoordinateMap laws hc (fineAdequate (h := h) laws hc) l x (E.edgeEquiv x.1.cell) rfl := by
  apply Subtype.ext
  apply CellCoordinate.ext <;> rfl
/-- 同じラベルのdegree1cochain同型。 -/
def blockCochain1 (l : LawValueLabel laws) := cochainEquivOfIndexEquiv (E.edgeBlockEquiv laws hc l)
/-- 自分のラベル同型の基底評価API。 -/
@[simp] theorem blockCochain1_apply (l : LawValueLabel laws) (z) (x) :
    E.blockCochain1 laws hc l z x = z (E.edgeBlockEquiv laws hc l x) := cochainEquivOfIndexEquiv_apply _ _ _
/-- 同じラベルの実degree1射と独立生成式は一致する。 -/
theorem blockCochain1_eq_generated (l : LawValueLabel laws) : (E.blockCochain1 laws hc l).toLinearMap =
    E.comparison.generatedBlockPullback1 laws hc (fineAdequate (h := h) laws hc) l := by
  apply LinearMap.ext
  intro z
  funext x
  rw [LinearEquiv.coe_coe, blockCochain1_apply, IncidenceSupportedComparison.generatedBlockPullback1_apply]
  rw [E.comparison.edgeBlockCoordinateMapOption_eq_some laws hc (fineAdequate (h := h) laws hc) l x (E.edgeEquiv x.1.cell) rfl]
  simp only [Option.elim_some]
  rw [E.edgeBlockEquiv_eq_generated]

/-- degree2の指定ラベル座標全単射。 -/
def faceBlockEquiv (l : LawValueLabel laws) : Nf.FaceBlockCoordinate laws (fineAdequate (h := h) laws hc) l ≃
    Nc.FaceBlockCoordinate laws hc l :=
  blockCoordinateEquiv laws hc E.faceEquiv Nf.faceSupport Nc.faceSupport E.faceSupport_eq l
/-- 同じラベル座標は独立生成したblock比較の座標。 -/
theorem faceBlockEquiv_eq_generated (l : LawValueLabel laws) (x) : E.faceBlockEquiv laws hc l x =
    E.comparison.faceBlockCoordinateMap laws hc (fineAdequate (h := h) laws hc) l x (E.faceEquiv x.1.cell) rfl := by
  apply Subtype.ext
  apply CellCoordinate.ext <;> rfl
/-- 同じラベルのdegree2cochain同型。 -/
def blockCochain2 (l : LawValueLabel laws) := cochainEquivOfIndexEquiv (E.faceBlockEquiv laws hc l)
/-- 自分のラベル同型の基底評価API。 -/
@[simp] theorem blockCochain2_apply (l : LawValueLabel laws) (z) (x) :
    E.blockCochain2 laws hc l z x = z (E.faceBlockEquiv laws hc l x) := cochainEquivOfIndexEquiv_apply _ _ _
/-- 同じラベルの実degree2射と独立生成式は一致する。 -/
theorem blockCochain2_eq_generated (l : LawValueLabel laws) : (E.blockCochain2 laws hc l).toLinearMap =
    E.comparison.generatedBlockPullback2 laws hc (fineAdequate (h := h) laws hc) l := by
  apply LinearMap.ext
  intro z
  funext x
  rw [LinearEquiv.coe_coe, blockCochain2_apply, IncidenceSupportedComparison.generatedBlockPullback2_apply]
  rw [E.comparison.faceBlockCoordinateMapOption_eq_some laws hc (fineAdequate (h := h) laws hc) l x (E.faceEquiv x.1.cell) rfl]
  simp only [Option.elim_some]
  rw [E.faceBlockEquiv_eq_generated]

/-- 同じラベル座標の両逆と原始微分から実block複体同値を作る。 -/
def blockCochainEquiv [Fintype Source] (l : LawValueLabel laws) : ThreeCochainComplex.CochainEquiv
    (Nc.lawValueBlockComplex laws hc l) (Nf.lawValueBlockComplex laws (fineAdequate (h := h) laws hc) l) where
  e0 := E.blockCochain0 laws hc l
  e1 := E.blockCochain1 laws hc l
  e2 := E.blockCochain2 laws hc l
  comm0 := by
    intro z
    change (E.blockCochain1 laws hc l).toLinearMap _ = _
    rw [E.blockCochain1_eq_generated]
    change _ = (Nf.lawValueBlockComplex laws (fineAdequate (h := h) laws hc) l).d0 ((E.blockCochain0 laws hc l).toLinearMap z)
    rw [E.blockCochain0_eq_generated]
    exact E.comparison.generatedBlockPullback_comm0 laws hc (fineAdequate (h := h) laws hc) l z
  comm1 := by
    intro z
    change (E.blockCochain2 laws hc l).toLinearMap _ = _
    rw [E.blockCochain2_eq_generated]
    change _ = (Nf.lawValueBlockComplex laws (fineAdequate (h := h) laws hc) l).d1 ((E.blockCochain1 laws hc l).toLinearMap z)
    rw [E.blockCochain1_eq_generated]
    exact E.comparison.generatedBlockPullback_comm1 laws hc (fineAdequate (h := h) laws hc) l z
/-- 実ラベル同値の順方向は全三次数で同じ独立生成Hom。 -/
theorem blockCochainEquiv_toHom [Fintype Source] (l : LawValueLabel laws) : (E.blockCochainEquiv laws hc l).toHom =
    E.comparison.generatedBlockComparisonHom laws hc (fineAdequate (h := h) laws hc) l := by
  apply cochain_ext
  · exact E.blockCochain0_eq_generated laws hc l
  · exact E.blockCochain1_eq_generated laws hc l
  · exact E.blockCochain2_eq_generated laws hc l
/-- 同じ実生成block Homの標準零延長同型。 -/
def blockZeroExtensionIso [Fintype Source] (l : LawValueLabel laws) := cochainEquivZeroExtensionIso (E.blockCochainEquiv laws hc l)
/-- ラベル標準同型の順方向は同じ実生成比較。 -/
theorem blockZeroExtensionIso_hom [Fintype Source] (l : LawValueLabel laws) : (E.blockZeroExtensionIso laws hc l).hom =
    zeroExtensionMap (E.comparison.generatedBlockComparisonHom laws hc (fineAdequate (h := h) laws hc) l) := by
  rw [blockZeroExtensionIso, cochainEquivZeroExtensionIso_hom, E.blockCochainEquiv_toHom]

/-- 同じ実生成law Homの既存H1商同型。 -/
def lawH1Equiv [Fintype Source] := (E.lawCochainEquiv laws hc).h1Equiv
/-- 既存H1商への同型は同じ実生成law H1写像。 -/
theorem lawH1Equiv_apply [Fintype Source] (x) : E.lawH1Equiv laws hc x =
    (E.comparison.generatedComparisonHom laws hc (fineAdequate (h := h) laws hc)).h1Map x := by
  rw [lawH1Equiv, ThreeCochainComplex.CochainEquiv.h1Equiv_apply, E.lawCochainEquiv_toHom]
/-- 同じ実生成law Homの全標準次数homology同型。 -/
def lawHomologyIso [Fintype Source] (n : ℤ) :=
  HomologicalComplex.homologyMapIso (E.lawZeroExtensionIso laws hc) n
/-- 全標準次数同型の順方向も同じ実生成law Hom。 -/
theorem lawHomologyIso_hom [Fintype Source] (n : ℤ) : (E.lawHomologyIso laws hc n).hom =
    HomologicalComplex.homologyMap (zeroExtensionMap
      (E.comparison.generatedComparisonHom laws hc (fineAdequate (h := h) laws hc))) n := by
  change HomologicalComplex.homologyMap (E.lawZeroExtensionIso laws hc).hom n = _
  rw [E.lawZeroExtensionIso_hom]

/-- 同じ実生成block Homの既存H1商同型。 -/
def blockH1Equiv [Fintype Source] (l : LawValueLabel laws) := (E.blockCochainEquiv laws hc l).h1Equiv
/-- 既存H1商への同型は同じ実生成block H1写像。 -/
theorem blockH1Equiv_apply [Fintype Source] (l : LawValueLabel laws) (x) : E.blockH1Equiv laws hc l x =
    (E.comparison.generatedBlockComparisonHom laws hc (fineAdequate (h := h) laws hc) l).h1Map x := by
  rw [blockH1Equiv, ThreeCochainComplex.CochainEquiv.h1Equiv_apply, E.blockCochainEquiv_toHom]
/-- 同じ実生成block Homの全標準次数homology同型。 -/
def blockHomologyIso [Fintype Source] (l : LawValueLabel laws) (n : ℤ) :=
  HomologicalComplex.homologyMapIso (E.blockZeroExtensionIso laws hc l) n
/-- 全標準次数同型の順方向も同じ実生成block Hom。 -/
theorem blockHomologyIso_hom [Fintype Source] (l : LawValueLabel laws) (n : ℤ) : (E.blockHomologyIso laws hc l n).hom =
    HomologicalComplex.homologyMap (zeroExtensionMap
      (E.comparison.generatedBlockComparisonHom laws hc (fineAdequate (h := h) laws hc) l)) n := by
  change HomologicalComplex.homologyMap (E.blockZeroExtensionIso laws hc l).hom n = _
  rw [E.blockZeroExtensionIso_hom]

/-- 同じ生成block比較を三次数の自然性で実fiberの標準同型へ移す。 -/
def fiberZeroExtensionIso [Fintype Source] (l : LawValueLabel laws) :=
  (lawBlockFiberZeroExtensionIso Nc laws hc l).symm ≪≫ E.blockZeroExtensionIso laws hc l ≪≫
    lawBlockFiberZeroExtensionIso Nf laws (fineAdequate (h := h) laws hc) l
/-- fiber標準同型の順方向は同じ独立生成fiber Hom。 -/
theorem fiberZeroExtensionIso_hom [Fintype Source] (l : LawValueLabel laws) :
    (E.fiberZeroExtensionIso laws hc l).hom =
    zeroExtensionMap (E.comparison.labelFiberComparisonHom laws hc (fineAdequate (h := h) laws hc) l) := by
  change ((lawBlockFiberZeroExtensionIso Nc laws hc l).inv ≫
    (E.blockZeroExtensionIso laws hc l).hom) ≫
      (lawBlockFiberZeroExtensionIso Nf laws (fineAdequate (h := h) laws hc) l).hom = _
  rw [E.blockZeroExtensionIso_hom, Category.assoc,
    lawBlockFiberZeroExtensionIso_natural Nc Nf laws hc E.comparison (fineAdequate (h := h) laws hc) l]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
/-- 同じ実fiber Homの全標準次数homology同型。 -/
def fiberHomologyIso [Fintype Source] (l : LawValueLabel laws) (n : ℤ) :=
  HomologicalComplex.homologyMapIso (E.fiberZeroExtensionIso laws hc l) n
/-- fiber homology同型の順方向は同じ実生成比較。 -/
theorem fiberHomologyIso_hom [Fintype Source] (l : LawValueLabel laws) (n : ℤ) :
    (E.fiberHomologyIso laws hc l n).hom = HomologicalComplex.homologyMap
      (zeroExtensionMap (E.comparison.labelFiberComparisonHom laws hc (fineAdequate (h := h) laws hc) l)) n := by
  change HomologicalComplex.homologyMap (E.fiberZeroExtensionIso laws hc l).hom n = _
  rw [E.fiberZeroExtensionIso_hom]
/-- 同じ実fiberの標準次数1同型を既存H1商へ読み戻す。 -/
def fiberOldH1Iso [Fintype Source] (l : LawValueLabel laws) :=
  oldH1Iso (Nc.targetSubsetComplex (labelValueFiber laws qc hc l)) ≪≫ E.fiberHomologyIso laws hc l 1 ≪≫
    (oldH1Iso (Nf.targetSubsetComplex (labelValueFiber laws qf (fineAdequate (h := h) laws hc) l))).symm
/-- 既存fiber H1商同型も同じ実生成H1写像である。 -/
theorem fiberOldH1Iso_hom [Fintype Source] (l : LawValueLabel laws) :
    (E.fiberOldH1Iso laws hc l).hom =
      ModuleCat.ofHom (E.comparison.labelFiberComparisonHom laws hc (fineAdequate (h := h) laws hc) l).h1Map := by
  change ((oldH1Iso (Nc.targetSubsetComplex (labelValueFiber laws qc hc l))).hom ≫
    (E.fiberHomologyIso laws hc l 1).hom) ≫
    (oldH1Iso (Nf.targetSubsetComplex (labelValueFiber laws qf (fineAdequate (h := h) laws hc) l))).inv = _
  rw [E.fiberHomologyIso_hom, oldH1Iso_natural]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
