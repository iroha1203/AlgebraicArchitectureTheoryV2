import ResearchLean.AG.AtlasDefectComposition.FullSupportGraph
import ResearchLean.AG.AtlasDefectComposition.CochainEquivalence
import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Formal.Util.AssertStandardAxioms
/-! # 全台blockの面incidence同定

グラフに限らず原始面を含む全台blockを名付き三項複体へ同定する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase Cohomology
universe u
variable {Source : Type u} {q : Reading Source} (D : TargetSupportedNerve q)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (hs₀ : ∀ c, D.chartSupport c = Set.univ)
variable (hs₁ : ∀ e, D.edgeSupport e = Set.univ)
variable (hs₂ : ∀ f, D.faceSupport f = Set.univ) (label : LawValueLabel laws)
/-- 全台blockの実degree-one微分は原始面の三辺を指定符号で読む。 -/
theorem fullBlock_d1 (c : D.EdgeBlockCoordinate laws ha label → ℚ)
    (f : D.nerve.FaceComponent) :
    fullBlockCochainEquiv laws q ha D.faceSupport hs₂ label
      (D.lawValueBlockD1 laws ha label c) f =
    fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label c (D.nerve.faceEdge0 f) -
      fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label c (D.nerve.faceEdge1 f) +
      fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label c (D.nerve.faceEdge2 f) := by
  let fc := (fullBlockCoordinateEquiv laws q ha D.faceSupport hs₂ label).symm f
  have h0 : D.faceEdge0BlockCoordinate laws ha label fc =
      (fullBlockCoordinateEquiv laws q ha D.edgeSupport hs₁ label).symm (D.nerve.faceEdge0 f) := by
    apply CellCoordinate.block_cell_injective laws q ha _ _ label
    change D.nerve.faceEdge0 fc.val.cell = _
    simp only [fc,fullBlockCoordinateEquiv_symm_cell]
  have h1 : D.faceEdge1BlockCoordinate laws ha label fc =
      (fullBlockCoordinateEquiv laws q ha D.edgeSupport hs₁ label).symm (D.nerve.faceEdge1 f) := by
    apply CellCoordinate.block_cell_injective laws q ha _ _ label
    change D.nerve.faceEdge1 fc.val.cell = _
    simp only [fc,fullBlockCoordinateEquiv_symm_cell]
  have h2 : D.faceEdge2BlockCoordinate laws ha label fc =
      (fullBlockCoordinateEquiv laws q ha D.edgeSupport hs₁ label).symm (D.nerve.faceEdge2 f) := by
    apply CellCoordinate.block_cell_injective laws q ha _ _ label
    change D.nerve.faceEdge2 fc.val.cell = _
    simp only [fc,fullBlockCoordinateEquiv_symm_cell]
  change c (D.faceEdge0BlockCoordinate laws ha label fc) -
    c (D.faceEdge1BlockCoordinate laws ha label fc) + c (D.faceEdge2BlockCoordinate laws ha label fc) = _
  rw [h0,h1,h2]
  rfl
/-- 名付き面の微分は原始三辺の交代和である。 -/
def faceDifference (N : CoverNerve.{u}) :
    (N.EdgeComponent → ℚ) →ₗ[ℚ] (N.FaceComponent → ℚ) where
  toFun c f := c (N.faceEdge0 f) - c (N.faceEdge1 f) + c (N.faceEdge2 f)
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring
/-- 名付き面の微分の公開評価API。 -/
@[simp] theorem faceDifference_apply (N : CoverNerve.{u})
    (c : N.EdgeComponent → ℚ) (f : N.FaceComponent) :
    faceDifference N c f = c (N.faceEdge0 f)-c (N.faceEdge1 f)+c (N.faceEdge2 f) := rfl
/-- 原始端点整合式だけから名付き二微分の合成零性を証明する。 -/
theorem named_d1_d0 (c : D.nerve.Chart → ℚ) :
    faceDifference D.nerve (graphDifference D.nerve c) = 0 := by
  funext f
  simp only [faceDifference_apply,graphDifference_apply,Pi.zero_apply,
    D.faceEdge0_left f,D.faceEdge0_right f,D.faceEdge1_right f]
  ring
/-- 原始セル名とincidenceから直接作る有理三項複体。 -/
def namedComplex : ThreeCochainComplex.{0,u} ℚ where
  C0 := D.nerve.Chart → ℚ
  C1 := D.nerve.EdgeComponent → ℚ
  C2 := D.nerve.FaceComponent → ℚ
  d0 := graphDifference D.nerve
  d1 := faceDifference D.nerve
  d1_comp_d0 := named_d1_d0 D
/-- 名付き原始複体の次数0微分を各辺の端点差分で読む公開API。 -/
@[simp] theorem namedComplex_d0_apply (c : D.nerve.Chart → ℚ)
    (e : D.nerve.EdgeComponent) :
    (namedComplex D).d0 c e = c (D.nerve.edgeRight e)-c (D.nerve.edgeLeft e) := rfl
/-- 名付き原始複体の次数1微分を各面の三辺差分で読む公開API。 -/
@[simp] theorem namedComplex_d1_apply (c : D.nerve.EdgeComponent → ℚ)
    (f : D.nerve.FaceComponent) :
    (namedComplex D).d1 c f =
      c (D.nerve.faceEdge0 f)-c (D.nerve.faceEdge1 f)+c (D.nerve.faceEdge2 f) := rfl
/-- 名付き次数0核のmembershipは全原始辺の端点差分零と同値である。 -/
theorem mem_ker_namedComplex_d0_iff (c : D.nerve.Chart → ℚ) :
    c ∈ LinearMap.ker (namedComplex D).d0 ↔
      ∀ e, c (D.nerve.edgeRight e)-c (D.nerve.edgeLeft e)=0 := by
  change (namedComplex D).d0 c = 0 ↔ _
  rw [funext_iff]
  rfl
/-- 全台の実生成Law blockと名付き原始セル三項複体の全成分同型。 -/
def fullBlockNamedEquivalence [Fintype Source] :
    ThreeCochainComplex.CochainEquiv (D.lawValueBlockComplex laws ha label) (namedComplex D) where
  e0 := fullBlockCochainEquiv laws q ha D.chartSupport hs₀ label
  e1 := fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label
  e2 := fullBlockCochainEquiv laws q ha D.faceSupport hs₂ label
  comm0 x := funext (fullBlock_d0 D laws ha hs₀ hs₁ label x)
  comm1 x := funext (fullBlock_d1 D laws ha hs₁ hs₂ label x)
/-- 全三成分同定の次数1は同じ原始名の生成 block 座標を評価する。 -/
@[simp] theorem fullBlockNamedEquivalence_e1 [Fintype Source]
    (z : D.EdgeBlockCoordinate laws ha label → ℚ) (e : D.nerve.EdgeComponent) :
    (fullBlockNamedEquivalence D laws ha hs₀ hs₁ hs₂ label).e1 z e=
      z ((fullBlockCoordinateEquiv laws q ha D.edgeSupport hs₁ label).symm e) :=
  fullBlockCochainEquiv_apply _ _ _ _ _ _ _ _

/-- 全chart台からK1の辺台も全targetになることを導く。 -/
theorem fullSupport_edge (hs : ∀ c, D.chartSupport c = Set.univ) :
    ∀ e, D.edgeSupport e = Set.univ := by
  intro e
  simp only [TargetSupportedNerve.edgeSupport,hs,Set.inter_self]
/-- 全chart台からK1の面台も全targetになることを導く。 -/
theorem fullSupport_face (hs : ∀ c, D.chartSupport c = Set.univ) :
    ∀ f, D.faceSupport f = Set.univ := by
  intro f
  simp [TargetSupportedNerve.faceSupport,TargetSupportedNerve.edgeSupport,hs]
include hs₀ hs₁ in
/-- 全台blockの実d⁰像次元と原始端点差分の像次元の一致。 -/
theorem fullBlockNamed_d0_rank [Fintype Source] :
    Module.finrank ℚ (LinearMap.range (D.lawValueBlockComplex laws ha label).d0) =
      Module.finrank ℚ (LinearMap.range (namedComplex D).d0) :=
  LinearConjugation.range_dimension _ _
    (fullBlockCochainEquiv laws q ha D.chartSupport hs₀ label)
    (fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label)
    (fun x => funext (fullBlock_d0 D laws ha hs₀ hs₁ label x))
include hs₁ hs₂ in
/-- 全台blockの実d¹像次元と原始面差分の像次元の一致。 -/
theorem fullBlockNamed_d1_rank [Fintype Source] :
    Module.finrank ℚ (LinearMap.range (D.lawValueBlockComplex laws ha label).d1) =
      Module.finrank ℚ (LinearMap.range (namedComplex D).d1) :=
  LinearConjugation.range_dimension _ _
    (fullBlockCochainEquiv laws q ha D.edgeSupport hs₁ label)
    (fullBlockCochainEquiv laws q ha D.faceSupport hs₂ label)
    (fun x => funext (fullBlock_d1 D laws ha hs₁ hs₂ label x))
/-- 全台blockの標準homologyを全次数で名付き原始セルhomologyへ移す。 -/
def fullBlockNamedHomologyEquiv [Fintype Source] (m : ℤ) :
    (zeroExtension (D.lawValueBlockComplex laws ha label)).homology m ≃ₗ[ℚ]
      (zeroExtension (namedComplex D)).homology m :=
  (HomologicalComplex.homologyMapIso
    (cochainEquivZeroExtensionIso (fullBlockNamedEquivalence D laws ha hs₀ hs₁ hs₂ label)) m).toLinearEquiv
/-- 全三成分同型の標準homology同定は同じ実Homの零延長を読む。 -/
@[simp] theorem fullBlockNamedHomologyEquiv_apply [Fintype Source] (m : ℤ)
    (x : (zeroExtension (D.lawValueBlockComplex laws ha label)).homology m) :
    fullBlockNamedHomologyEquiv D laws ha hs₀ hs₁ hs₂ label m x =
      HomologicalComplex.homologyMap (zeroExtensionMap
        (fullBlockNamedEquivalence D laws ha hs₀ hs₁ hs₂ label).toHom) m x := rfl
/-- 実block次数2cochainの標準類を名付き同定へ移すと同じ次数2座標を読む。 -/
theorem fullBlockNamedHomologyEquiv_oldH2_mk [Fintype Source]
    (z : (D.lawValueBlockComplex laws ha label).C2) :
    fullBlockNamedHomologyEquiv D laws ha hs₀ hs₁ hs₂ label 2
      (oldH2Equiv (D.lawValueBlockComplex laws ha label)
        ((LinearMap.range (D.lawValueBlockComplex laws ha label).d1).mkQ z)) =
    oldH2Equiv (namedComplex D) ((LinearMap.range (namedComplex D).d1).mkQ
      ((fullBlockNamedEquivalence D laws ha hs₀ hs₁ hs₂ label).e2 z)) := by
  rw [fullBlockNamedHomologyEquiv_apply, ← oldH2Equiv_natural, oldH2Map_mk]
  rfl

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
