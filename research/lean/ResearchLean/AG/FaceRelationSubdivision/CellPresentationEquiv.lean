import ResearchLean.AG.FaceRelationSubdivision.SubsetContraction
import ResearchLean.AG.FaceRelationSubdivision.IncidenceBasis
import Formal.Util.AssertStandardAxioms

/-!
# 支持セル表示同型とreading逆像比較

## Implementation notes

入力は名前の全単射、端点・三辺の等式、chart台の逆像だけである。
因子全射性から選択セル全単射を作り、Finsupp線形延長の両逆とchain式を証明する。
診断同型を入力にする案は採らず、同じ独立生成subset比較との等号を示す。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}

/-- 名前・incidence・chart台の原始表示同型。 -/
structure CellPresentationEquiv (qc qf : Reading Source) (h : qc.CoarserThan qf)
    (Nc : TargetSupportedNerve qc) (Nf : TargetSupportedNerve qf) where
  chartEquiv : Nf.nerve.Chart ≃ Nc.nerve.Chart
  edgeEquiv : Nf.nerve.EdgeComponent ≃ Nc.nerve.EdgeComponent
  faceEquiv : Nf.nerve.FaceComponent ≃ Nc.nerve.FaceComponent
  edge_left : ∀ e, chartEquiv (Nf.nerve.edgeLeft e) = Nc.nerve.edgeLeft (edgeEquiv e)
  edge_right : ∀ e, chartEquiv (Nf.nerve.edgeRight e) = Nc.nerve.edgeRight (edgeEquiv e)
  face_edge0 : ∀ f, edgeEquiv (Nf.nerve.faceEdge0 f) = Nc.nerve.faceEdge0 (faceEquiv f)
  face_edge1 : ∀ f, edgeEquiv (Nf.nerve.faceEdge1 f) = Nc.nerve.faceEdge1 (faceEquiv f)
  face_edge2 : ∀ f, edgeEquiv (Nf.nerve.faceEdge2 f) = Nc.nerve.faceEdge2 (faceEquiv f)
  chartSupport_eq : ∀ v, Nf.chartSupport v =
    comparisonFactor qc qf h ⁻¹' Nc.chartSupport (chartEquiv v)

namespace CellPresentationEquiv
variable (E : CellPresentationEquiv qc qf h Nc Nf)
/-- K1辺台の逆像等式。 -/
theorem edgeSupport_eq (e : Nf.nerve.EdgeComponent) : Nf.edgeSupport e =
    comparisonFactor qc qf h ⁻¹' Nc.edgeSupport (E.edgeEquiv e) := by
  ext t
  simp only [TargetSupportedNerve.mem_edgeSupport_iff, E.chartSupport_eq,
    Set.mem_preimage, E.edge_left, E.edge_right]
/-- K1面台の逆像等式。 -/
theorem faceSupport_eq (f : Nf.nerve.FaceComponent) : Nf.faceSupport f =
    comparisonFactor qc qf h ⁻¹' Nc.faceSupport (E.faceEquiv f) := by
  ext t
  simp only [TargetSupportedNerve.mem_faceSupport_iff, E.edgeSupport_eq,
    Set.mem_preimage, E.face_edge0, E.face_edge1, E.face_edge2]
/-- 原始表から全セルを写す新比較を生成する。 -/
def comparison : IncidenceSupportedComparison qc qf h Nc Nf where
  chartMap := E.chartEquiv
  edgeMap := fun e => some (E.edgeEquiv e)
  faceMap := fun f => some (E.faceEquiv f)
  edge_some_left := by intro e b hb; cases Option.some.inj hb; exact E.edge_left e
  edge_some_right := by intro e b hb; cases Option.some.inj hb; exact E.edge_right e
  edge_none_fiber := by intro e he; cases he
  face_some_edge0 := by intro f b hb; cases Option.some.inj hb; exact congrArg some (E.face_edge0 f)
  face_some_edge1 := by intro f b hb; cases Option.some.inj hb; exact congrArg some (E.face_edge1 f)
  face_some_edge2 := by intro f b hb; cases Option.some.inj hb; exact congrArg some (E.face_edge2 f)
  face_none_incidence := by intro f hf; cases hf
  chartSupport_compatible := by
    intro v t ht
    rw [E.chartSupport_eq v] at ht
    exact ht
/-- 生成比較のchart像。 -/
@[simp] theorem comparison_chart (v) : E.comparison.chartMap v = E.chartEquiv v := rfl
/-- 生成比較の辺像。 -/
@[simp] theorem comparison_edge (e) : E.comparison.edgeMap e = some (E.edgeEquiv e) := rfl
/-- 生成比較の面像。 -/
@[simp] theorem comparison_face (f) : E.comparison.faceMap f = some (E.faceEquiv f) := rfl
/-- 逆像部分集合のmaps-to証明を生成する。 -/
theorem subsetMapsTo (A : Set qc.Target) :
    ∀ t, t ∈ comparisonFactor qc qf h ⁻¹' A → comparisonFactor qc qf h t ∈ A := by
  intro t ht
  exact ht
/-- 全射因子の逆像はセル支持の選択を保つ。 -/
theorem selected_iff {I : Type u} (supp : I → Set qc.Target) (A : Set qc.Target) (i : I) :
    (∃ t, t ∈ comparisonFactor qc qf h ⁻¹' supp i ∧
      t ∈ comparisonFactor qc qf h ⁻¹' A) ↔ ∃ t, t ∈ supp i ∧ t ∈ A := by
  constructor
  · rintro ⟨t, ht, ha⟩; exact ⟨comparisonFactor qc qf h t, ht, ha⟩
  · rintro ⟨t, ht, ha⟩
    obtain ⟨s, rfl⟩ := comparisonFactor_surjective qc qf h t
    exact ⟨s, ht, ha⟩
/-- 支持逆像と名前から選択セル全単射を構成する。 -/
def selectedEquiv {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i))
    (A : Set qc.Target) : Selected si (comparisonFactor qc qf h ⁻¹' A) ≃ Selected sj A where
  toFun i := ⟨e i, (selected_iff (qc := qc) (qf := qf) (h := h) sj A (e i)).mp (by simpa only [hs] using i.2)⟩
  invFun j := ⟨e.symm j, by rw [hs, Equiv.apply_symm_apply]; exact (selected_iff (qc := qc) (qf := qf) (h := h) sj A j).mpr j.2⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.1
  right_inv j := by apply Subtype.ext; exact e.apply_symm_apply j.1
/-- 選択セル全単射の元の名前。 -/
@[simp] theorem selectedEquiv_val {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i))
    (A : Set qc.Target) (i : Selected si (comparisonFactor qc qf h ⁻¹' A)) :
    (selectedEquiv e si sj hs A i).1 = e i.1 := rfl
/-- 全Aの選択頂点全単射。 -/
def chartSelected (A : Set qc.Target) :
    Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) ≃ Nc.ChartInTargetSubset A :=
  selectedEquiv E.chartEquiv Nf.chartSupport Nc.chartSupport E.chartSupport_eq A
/-- 全Aの選択辺全単射。 -/
def edgeSelected (A : Set qc.Target) :
    Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) ≃ Nc.EdgeInTargetSubset A :=
  selectedEquiv E.edgeEquiv Nf.edgeSupport Nc.edgeSupport E.edgeSupport_eq A
/-- 全Aの選択面全単射。 -/
def faceSelected (A : Set qc.Target) :
    Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) ≃ Nc.FaceInTargetSubset A :=
  selectedEquiv E.faceEquiv Nf.faceSupport Nc.faceSupport E.faceSupport_eq A
/-- 選択chart像のセル名。 -/
@[simp] theorem chartSelected_val (A : Set qc.Target) (v) : (E.chartSelected A v).1 = E.chartEquiv v.1 := rfl
/-- 選択辺像のセル名。 -/
@[simp] theorem edgeSelected_val (A : Set qc.Target) (e) : (E.edgeSelected A e).1 = E.edgeEquiv e.1 := rfl
/-- 選択面像のセル名。 -/
@[simp] theorem faceSelected_val (A : Set qc.Target) (f) : (E.faceSelected A f).1 = E.faceEquiv f.1 := rfl

/-- 同じセル名のdegree0自由加群同型。 -/
def r0 (A : Set qc.Target) : K0 Nf (comparisonFactor qc qf h ⁻¹' A) ≃ₗ[ℚ] K0 Nc A :=
  Finsupp.domLCongr (E.chartSelected A)
/-- 原始r0の基底評価。 -/
@[simp] theorem r0_single (A : Set qc.Target) (v) (a : ℚ) :
    E.r0 A (Finsupp.single v a) = Finsupp.single (E.chartSelected A v) a := Finsupp.domLCongr_single _ _ _
/-- 原始r0は独立生成比較の同じchain射。 -/
theorem r0_eq_generated (A : Set qc.Target) : (E.r0 A).toLinearMap =
    E.comparison.supportedChainMap0 A (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A) := by
  apply Finsupp.lhom_ext
  intro v a
  rw [LinearEquiv.coe_coe, r0_single, IncidenceSupportedComparison.supportedChainMap0_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  congr 1

/-- 同じセル名のdegree1自由加群同型。 -/
def r1 (A : Set qc.Target) : K1 Nf (comparisonFactor qc qf h ⁻¹' A) ≃ₗ[ℚ] K1 Nc A :=
  Finsupp.domLCongr (E.edgeSelected A)
/-- 原始r1の基底評価。 -/
@[simp] theorem r1_single (A : Set qc.Target) (v) (a : ℚ) :
    E.r1 A (Finsupp.single v a) = Finsupp.single (E.edgeSelected A v) a := Finsupp.domLCongr_single _ _ _
/-- 原始r1は独立生成比較の同じchain射。 -/
theorem r1_eq_generated (A : Set qc.Target) : (E.r1 A).toLinearMap =
    E.comparison.supportedChainMap1 A (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A) := by
  apply Finsupp.lhom_ext
  intro v a
  rw [LinearEquiv.coe_coe, r1_single, IncidenceSupportedComparison.supportedChainMap1_single,
    E.comparison.targetSubsetEdgeMapOption_eq_some A _ (subsetMapsTo A) v (E.edgeEquiv v.1) rfl,
    rationalOptionCell_some, Finsupp.smul_single, smul_eq_mul, mul_one]
  congr 1

/-- 同じセル名のdegree2自由加群同型。 -/
def r2 (A : Set qc.Target) : K2 Nf (comparisonFactor qc qf h ⁻¹' A) ≃ₗ[ℚ] K2 Nc A :=
  Finsupp.domLCongr (E.faceSelected A)
/-- 原始r2の基底評価。 -/
@[simp] theorem r2_single (A : Set qc.Target) (v) (a : ℚ) :
    E.r2 A (Finsupp.single v a) = Finsupp.single (E.faceSelected A v) a := Finsupp.domLCongr_single _ _ _
/-- 原始r2は独立生成比較の同じchain射。 -/
theorem r2_eq_generated (A : Set qc.Target) : (E.r2 A).toLinearMap =
    E.comparison.supportedChainMap2 A (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A) := by
  apply Finsupp.lhom_ext
  intro v a
  rw [LinearEquiv.coe_coe, r2_single, IncidenceSupportedComparison.supportedChainMap2_single,
    E.comparison.targetSubsetFaceMapOption_eq_some A _ (subsetMapsTo A) v (E.faceEquiv v.1) rfl,
    rationalOptionCell_some, Finsupp.smul_single, smul_eq_mul, mul_one]
  congr 1

/-- rの原始degree1chain式。 -/
theorem r_comm01 (A : Set qc.Target) : (chainD1 Nc A).comp (E.r1 A).toLinearMap =
    (E.r0 A).toLinearMap.comp (chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)) := by
  rw [E.r0_eq_generated, E.r1_eq_generated]
  apply LinearMap.ext
  intro x
  exact (E.comparison.supportedChainMap_comm1 A _ (subsetMapsTo A) x).symm

/-- rの原始degree2chain式。 -/
theorem r_comm12 (A : Set qc.Target) : (chainD2 Nc A).comp (E.r2 A).toLinearMap =
    (E.r1 A).toLinearMap.comp (chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)) := by
  rw [E.r1_eq_generated, E.r2_eq_generated]
  apply LinearMap.ext
  intro x
  exact (E.comparison.supportedChainMap_comm2 A _ (subsetMapsTo A) x).symm

/-- chain式と両逆から逆方向のchain式を導出する。 -/
theorem inverse_comm {I J K L : Type u} [AddCommGroup I] [Module ℚ I]
    [AddCommGroup J] [Module ℚ J] [AddCommGroup K] [Module ℚ K]
    [AddCommGroup L] [Module ℚ L] (a : I ≃ₗ[ℚ] J) (b : K ≃ₗ[ℚ] L)
    (di : K →ₗ[ℚ] I) (dj : L →ₗ[ℚ] J)
    (hc : dj.comp b.toLinearMap = a.toLinearMap.comp di) :
    di.comp b.symm.toLinearMap = a.symm.toLinearMap.comp dj := by
  apply LinearMap.ext
  intro x
  apply a.injective
  have hx := LinearMap.congr_fun hc (b.symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hx.symm
/-- 同じ原始セルのr/sと零hから出力収縮を構成する。 -/
def chainContraction (A : Set qc.Target) :
    SubsetChainContraction Nc Nf A (comparisonFactor qc qf h ⁻¹' A) where
  r0 := (E.r0 A).toLinearMap
  r1 := (E.r1 A).toLinearMap
  r2 := (E.r2 A).toLinearMap
  s0 := (E.r0 A).symm.toLinearMap
  s1 := (E.r1 A).symm.toLinearMap
  s2 := (E.r2 A).symm.toLinearMap
  h0 := 0
  h1 := 0
  r_comm01 := E.r_comm01 A
  r_comm12 := E.r_comm12 A
  s_comm01 := inverse_comm _ _ _ _ (E.r_comm01 A)
  s_comm12 := inverse_comm _ _ _ _ (E.r_comm12 A)
  rs0 := by apply LinearMap.ext; intro x; exact (E.r0 A).apply_symm_apply x
  rs1 := by apply LinearMap.ext; intro x; exact (E.r1 A).apply_symm_apply x
  rs2 := by apply LinearMap.ext; intro x; exact (E.r2 A).apply_symm_apply x
  sr_h0 := by apply LinearMap.ext; intro x; simp
  sr_h1 := by apply LinearMap.ext; intro x; simp
  sr_h2 := by apply LinearMap.ext; intro x; simp

/-- 同じセルr/sの標準cochain鎖ホモトピー同値。 -/
def cochainHomotopyEquiv (A : Set qc.Target) := (E.chainContraction A).cochainHomotopyEquiv
/-- 双対生成の順方向は独立生成した同じ実subset比較。 -/
theorem rHom_eq_generated (A : Set qc.Target) : (E.chainContraction A).rHom =
    E.comparison.targetSubsetComparisonHom A (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (E.r0 A).toLinearMap z) x =
      freeDualEquiv _ (E.comparison.targetSubsetPullback0 A
        (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A) z) x
    rw [dualCellMap_dual, E.r0_eq_generated, E.comparison.supportedChainMap0_dual]
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (E.r1 A).toLinearMap z) x =
      freeDualEquiv _ (E.comparison.targetSubsetPullback1 A
        (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A) z) x
    rw [dualCellMap_dual, E.r1_eq_generated, E.comparison.supportedChainMap1_dual]
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (E.r2 A).toLinearMap z) x =
      freeDualEquiv _ (E.comparison.targetSubsetPullback2 A
        (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A) z) x
    rw [dualCellMap_dual, E.r2_eq_generated, E.comparison.supportedChainMap2_dual]

/-- 全標準次数の同型。 -/
def homologyIso (A : Set qc.Target) (n : ℤ) := (E.chainContraction A).homologyIso n
/-- 同型の順方向は同じ実比較のhomologyMap。 -/
theorem homologyIso_hom (A : Set qc.Target) (n : ℤ) : (E.homologyIso A n).hom =
    HomologicalComplex.homologyMap (zeroExtensionMap
      (E.comparison.targetSubsetComparisonHom A (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A))) n := by
  change ((E.chainContraction A).homologyIso n).hom = _
  rw [SubsetChainContraction.homologyIso_hom, E.rHom_eq_generated]
/-- 同じ実生成比較の既存H1商同型。 -/
def oldH1ComparisonIso (A : Set qc.Target) := (E.chainContraction A).oldH1ComparisonIso
/-- 既存H1同型の順方向も同じ実生成H1写像。 -/
theorem oldH1ComparisonIso_hom (A : Set qc.Target) : (E.oldH1ComparisonIso A).hom =
    ModuleCat.ofHom (E.comparison.targetSubsetComparisonHom A
      (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A)).h1Map := by
  rw [oldH1ComparisonIso, SubsetChainContraction.oldH1ComparisonIso_hom, E.rHom_eq_generated]

/-- 逆s0も同じ原始逆セル名の基底を送る。 -/
@[simp] theorem r0_symm_single (A : Set qc.Target) (v) (a : ℚ) :
    (E.r0 A).symm (Finsupp.single v a) = Finsupp.single ((E.chartSelected A).symm v) a := by
  change (Finsupp.domLCongr (E.chartSelected A) : _ ≃ₗ[ℚ] _).symm (Finsupp.single v a) = _
  rw [Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
/-- 収縮出力の原始degree0射。 -/
@[simp] theorem chainContraction_r0 (A : Set qc.Target) : (E.chainContraction A).r0 = (E.r0 A).toLinearMap := rfl
/-- 収縮出力の原始degree0逆射。 -/
@[simp] theorem chainContraction_s0 (A : Set qc.Target) : (E.chainContraction A).s0 = (E.r0 A).symm.toLinearMap := rfl

/-- 逆s1も同じ原始逆セル名の基底を送る。 -/
@[simp] theorem r1_symm_single (A : Set qc.Target) (v) (a : ℚ) :
    (E.r1 A).symm (Finsupp.single v a) = Finsupp.single ((E.edgeSelected A).symm v) a := by
  change (Finsupp.domLCongr (E.edgeSelected A) : _ ≃ₗ[ℚ] _).symm (Finsupp.single v a) = _
  rw [Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
/-- 収縮出力の原始degree1射。 -/
@[simp] theorem chainContraction_r1 (A : Set qc.Target) : (E.chainContraction A).r1 = (E.r1 A).toLinearMap := rfl
/-- 収縮出力の原始degree1逆射。 -/
@[simp] theorem chainContraction_s1 (A : Set qc.Target) : (E.chainContraction A).s1 = (E.r1 A).symm.toLinearMap := rfl

/-- 逆s2も同じ原始逆セル名の基底を送る。 -/
@[simp] theorem r2_symm_single (A : Set qc.Target) (v) (a : ℚ) :
    (E.r2 A).symm (Finsupp.single v a) = Finsupp.single ((E.faceSelected A).symm v) a := by
  change (Finsupp.domLCongr (E.faceSelected A) : _ ≃ₗ[ℚ] _).symm (Finsupp.single v a) = _
  rw [Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
/-- 収縮出力の原始degree2射。 -/
@[simp] theorem chainContraction_r2 (A : Set qc.Target) : (E.chainContraction A).r2 = (E.r2 A).toLinearMap := rfl
/-- 収縮出力の原始degree2逆射。 -/
@[simp] theorem chainContraction_s2 (A : Set qc.Target) : (E.chainContraction A).s2 = (E.r2 A).symm.toLinearMap := rfl
/-- 表示同型の原始ホモトピー成分は零。 -/
@[simp] theorem chainContraction_h0 (A : Set qc.Target) : (E.chainContraction A).h0 = 0 := rfl
/-- 表示同型の原始ホモトピー成分は零。 -/
@[simp] theorem chainContraction_h1 (A : Set qc.Target) : (E.chainContraction A).h1 = 0 := rfl

/-- 標準ホモトピー同値の順方向も同じ実生成比較。 -/
theorem cochainHomotopyEquiv_hom (A : Set qc.Target) : (E.cochainHomotopyEquiv A).hom =
    zeroExtensionMap (E.comparison.targetSubsetComparisonHom A (comparisonFactor qc qf h ⁻¹' A) (subsetMapsTo A)) := by
  change (E.chainContraction A).cochainHomotopyEquiv.hom = _
  rw [SubsetChainContraction.cochainHomotopyEquiv_hom, E.rHom_eq_generated]
/-- 標準同値の逆方向は同じ逆セル名射の双対。 -/
theorem cochainHomotopyEquiv_inv (A : Set qc.Target) : (E.cochainHomotopyEquiv A).inv =
    zeroExtensionMap (E.chainContraction A).sHom := rfl

end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
