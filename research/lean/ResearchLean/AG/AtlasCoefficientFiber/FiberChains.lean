import ResearchLean.AG.AtlasCoefficientFiber.RawBlocks

/-!
# G-135 B §1：原セルの全Φへの両方向分類

粗chartを添字とする全fiberを使い、原名前付き基底から有限直積chainへの同定を作る。

## Implementation notes

各原セルをcarrierで分類したSigmaと、mathlibのsigmaFinsupp/Pi同型を使う。
有限な粗chart添字によりPiは有限直和でもある。選んだ一fiberだけを使う案は
原支持chain全体への逆写像を与えないため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open scoped Classical
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 全細chartは原chart carrierのΦへの非交和である。 -/
def phiChartPartition : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) ≃
    Σ c : Nc.ChartInTargetSubset A, PhiChart M A c :=
  (Equiv.sigmaFiberEquiv (Carrier.chart M A _ (fun _ ht => ht))).symm

/-- 全垂直辺は、宣言上のnoneを保つΦ辺の非交和である。 -/
def phiEdgePartition : VerticalEdge M A ≃ Σ c : Nc.ChartInTargetSubset A, PhiEdge M A c where
  toFun e := ⟨Carrier.chart M A _ (fun _ ht => ht) (Nf.targetSubsetEdgeLeft _ e.1),
    ⟨e.1, e.2, rfl⟩⟩
  invFun e := ⟨e.2.1, e.2.2.1⟩
  left_inv e := rfl
  right_inv e := by
    rcases e with ⟨c, e, hn, hc⟩
    cases hc
    rfl

/-- 全垂直面は、三つのnone出現を保持したΦ面の非交和である。 -/
def phiFacePartition : VerticalFace M A ≃ Σ c : Nc.ChartInTargetSubset A, PhiFace M A c where
  toFun f := ⟨Carrier.chart M A _ (fun _ ht => ht)
      (Nf.targetSubsetEdgeLeft _ (Nf.targetSubsetFaceEdge0 _ f.1)),
    ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2, rfl⟩⟩
  invFun f := ⟨f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1, f.2.2.2.2.2.1⟩
  left_inv f := rfl
  right_inv f := by
    rcases f with ⟨c, f, hn, h0, h1, h2, hc⟩
    cases hc
    rfl

/-- Φ chartの非交和から元の同じ細chart名へ戻る。 -/
@[simp] theorem phiChartPartition_symm_val (c : Nc.ChartInTargetSubset A) (v : PhiChart M A c) :
    (phiChartPartition M A).symm ⟨c, v⟩ = v.1 := rfl

/-- Φ辺の非交和から元の同じ垂直辺名へ戻る。 -/
@[simp] theorem phiEdgePartition_symm_val (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) :
    ((phiEdgePartition M A).symm ⟨c, e⟩).1 = e.1 := rfl

/-- Φ面の非交和から元の同じ垂直面名へ戻る。 -/
@[simp] theorem phiFacePartition_symm_val (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) :
    ((phiFacePartition M A).symm ⟨c, f⟩).1 = f.1 := rfl

/-- 辺分類の逆の実部分型値。所属証明を下流へ露出させない。 -/
@[simp] theorem phiEdgePartition_symm_apply (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) :
    (phiEdgePartition M A).symm ⟨c, e⟩ = ⟨e.1, e.2.1⟩ := rfl

/-- 面分類の逆の実部分型値。 -/
@[simp] theorem phiFacePartition_symm_apply (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) :
    (phiFacePartition M A).symm ⟨c, f⟩ =
      ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1⟩ := rfl

/-- 元K′₀と全Φ chart chainの有限直積の両方向同型。 -/
def phiChainEquiv0 : K0 Nf (comparisonFactor qc qf h ⁻¹' A) ≃ₗ[ℚ]
    (c : Nc.ChartInTargetSubset A) → (PhiChart M A c →₀ ℚ) := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  exact (Finsupp.domLCongr (phiChartPartition M A)).trans (Finsupp.sigmaFinsuppLEquivPiFinsupp ℚ)

/-- 元E_v chainと全Φ辺chainの有限直積の両方向同型。 -/
def phiChainEquiv1 : (VerticalEdge M A →₀ ℚ) ≃ₗ[ℚ]
    (c : Nc.ChartInTargetSubset A) → (PhiEdge M A c →₀ ℚ) := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  exact (Finsupp.domLCongr (phiEdgePartition M A)).trans (Finsupp.sigmaFinsuppLEquivPiFinsupp ℚ)

/-- 元F_v chainと全Φ面chainの有限直積の両方向同型。 -/
def phiChainEquiv2 : (VerticalFace M A →₀ ℚ) ≃ₗ[ℚ]
    (c : Nc.ChartInTargetSubset A) → (PhiFace M A c →₀ ℚ) := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  exact (Finsupp.domLCongr (phiFacePartition M A)).trans (Finsupp.sigmaFinsuppLEquivPiFinsupp ℚ)

/-- chart同定の各係数は元の同じchartの係数。 -/
@[simp] theorem phiChainEquiv0_apply (x : K0 Nf (comparisonFactor qc qf h ⁻¹' A))
    (c : Nc.ChartInTargetSubset A) (v : PhiChart M A c) : phiChainEquiv0 M A x c v = x v.1 := by
  simp [phiChainEquiv0, Finsupp.domCongr_apply]

/-- 辺同定の各係数は元の同じ垂直辺の係数。 -/
@[simp] theorem phiChainEquiv1_apply (x : VerticalEdge M A →₀ ℚ)
    (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) :
    phiChainEquiv1 M A x c e = x ⟨e.1, e.2.1⟩ := by
  simp [phiChainEquiv1, Finsupp.domCongr_apply]

/-- 面同定の各係数は元の同じ垂直面の係数。 -/
@[simp] theorem phiChainEquiv2_apply (x : VerticalFace M A →₀ ℚ)
    (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) :
    phiChainEquiv2 M A x c f = x ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1⟩ := by
  simp [phiChainEquiv2, Finsupp.domCongr_apply]

/-- chart基底のfiber係数は、同じ原chart名のKronecker係数。 -/
@[simp] theorem phiChainEquiv0_single (v : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (r : ℚ) (c : Nc.ChartInTargetSubset A) (w : PhiChart M A c) :
    phiChainEquiv0 M A (Finsupp.single v r) c w = if v = w.1 then r else 0 := by
  classical
  rw [phiChainEquiv0_apply, Finsupp.single_apply]

/-- 垂直辺基底のfiber係数は、同じ原細辺名のKronecker係数。 -/
@[simp] theorem phiChainEquiv1_single (e : VerticalEdge M A) (r : ℚ)
    (c : Nc.ChartInTargetSubset A) (w : PhiEdge M A c) :
    phiChainEquiv1 M A (Finsupp.single e r) c w = if e.1 = w.1 then r else 0 := by
  classical
  rw [phiChainEquiv1_apply, Finsupp.single_apply]
  simp only [Subtype.ext_iff]

/-- 垂直面基底のfiber係数は、同じ原細面名のKronecker係数。 -/
@[simp] theorem phiChainEquiv2_single (f : VerticalFace M A) (r : ℚ)
    (c : Nc.ChartInTargetSubset A) (w : PhiFace M A c) :
    phiChainEquiv2 M A (Finsupp.single f r) c w = if f.1 = w.1 then r else 0 := by
  classical
  rw [phiChainEquiv2_apply, Finsupp.single_apply]
  simp only [Subtype.ext_iff]

/-- 元のchart基底を、そのcarrier以外のΦへ送ると零。 -/
theorem phiChainEquiv0_single_other (v : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (r : ℚ) (c : Nc.ChartInTargetSubset A)
    (hc : Carrier.chart M A _ (fun _ ht => ht) v ≠ c) :
    phiChainEquiv0 M A (Finsupp.single v r) c = 0 := by
  classical
  ext w
  rw [phiChainEquiv0_single]
  have hn : v ≠ w.1 := fun he => hc (he ▸ w.2)
  simp only [if_neg hn, Finsupp.zero_apply]

/-- 元の垂直辺基底を、そのcarrier以外のΦへ送ると零。 -/
theorem phiChainEquiv1_single_other (e : VerticalEdge M A) (r : ℚ)
    (c : Nc.ChartInTargetSubset A)
    (hc : Carrier.chart M A _ (fun _ ht => ht) (Nf.targetSubsetEdgeLeft _ e.1) ≠ c) :
    phiChainEquiv1 M A (Finsupp.single e r) c = 0 := by
  classical
  ext w
  rw [phiChainEquiv1_single]
  have hn : e.1 ≠ w.1 := fun he => hc (he ▸ w.2.2)
  simp only [if_neg hn, Finsupp.zero_apply]

/-- 元の垂直面基底を、そのcarrier以外のΦへ送ると零。 -/
theorem phiChainEquiv2_single_other (f : VerticalFace M A) (r : ℚ)
    (c : Nc.ChartInTargetSubset A)
    (hc : Carrier.chart M A _ (fun _ ht => ht)
      (Nf.targetSubsetEdgeLeft _ (Nf.targetSubsetFaceEdge0 _ f.1)) ≠ c) :
    phiChainEquiv2 M A (Finsupp.single f r) c = 0 := by
  classical
  ext w
  rw [phiChainEquiv2_single]
  have hn : f.1 ≠ w.1 := fun he => hc (he ▸ w.2.2.2.2.2)
  simp only [if_neg hn, Finsupp.zero_apply]

/-- Φ chart基底を実原chart基底から復元する。 -/
@[simp] theorem phiChainEquiv0_single_same (c : Nc.ChartInTargetSubset A) (v : PhiChart M A c) (r : ℚ) :
    phiChainEquiv0 M A (Finsupp.single v.1 r) c = Finsupp.single v r := by
  classical
  ext w
  rw [phiChainEquiv0_single, Finsupp.single_apply]
  simp only [Subtype.ext_iff]

/-- Φ辺基底を実原垂直辺基底から復元する。 -/
@[simp] theorem phiChainEquiv1_single_same (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) (r : ℚ) :
    phiChainEquiv1 M A (Finsupp.single ⟨e.1, e.2.1⟩ r) c = Finsupp.single e r := by
  classical
  ext w
  rw [phiChainEquiv1_single, Finsupp.single_apply]
  simp only [Subtype.ext_iff]

/-- Φ面基底を実原垂直面基底から復元する。 -/
@[simp] theorem phiChainEquiv2_single_same (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) (r : ℚ) :
    phiChainEquiv2 M A (Finsupp.single ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1⟩ r) c =
      Finsupp.single f r := by
  classical
  ext w
  rw [phiChainEquiv2_single, Finsupp.single_apply]
  simp only [Subtype.ext_iff]

/-- 全Φ分類は同じ原a微分と各原Φ端点差分に可換。 -/
theorem phiChainEquiv_comm1 (x : VerticalEdge M A →₀ ℚ) (c : Nc.ChartInTargetSubset A) :
    phiChainEquiv0 M A (verticalEdgeBoundary M A x) c =
      phiBoundary1 M A c (phiChainEquiv1 M A x c) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | single e r =>
    let ce := Carrier.chart M A _ (fun _ ht => ht) (Nf.targetSubsetEdgeLeft _ e.1)
    by_cases hc : ce = c
    · let ee : PhiEdge M A c := ⟨e.1, e.2, hc⟩
      change phiChainEquiv0 M A (chainD1 Nf _ (verticalEdgeInclusion M A (Finsupp.single e r))) c = _
      rw [verticalEdgeInclusion_single, chainD1_single]
      have he : e = (⟨ee.1, ee.2.1⟩ : VerticalEdge M A) := rfl
      rw [he, phiChainEquiv1_single_same, phiBoundary1_single]
      simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply]
      rw [show Nf.targetSubsetEdgeRight _ e.1 = (phiEndpoint M A ee true).1 from rfl,
        show Nf.targetSubsetEdgeLeft _ e.1 = (phiEndpoint M A ee false).1 from rfl,
        phiChainEquiv0_single_same, phiChainEquiv0_single_same]
    · have hr : Carrier.chart M A _ (fun _ ht => ht) (Nf.targetSubsetEdgeRight _ e.1) ≠ c := by
        have he : Carrier.chart M A _ (fun _ ht => ht) (Nf.targetSubsetEdgeLeft _ e.1) =
            Carrier.chart M A _ (fun _ ht => ht) (Nf.targetSubsetEdgeRight _ e.1) :=
          M.targetSubsetChartMap_edgeLeft_eq_right_of_none A _ _ e.1 e.2
        exact fun hh => hc (he.trans hh)
      change phiChainEquiv0 M A (chainD1 Nf _ (verticalEdgeInclusion M A (Finsupp.single e r))) c = _
      rw [verticalEdgeInclusion_single, chainD1_single,
        phiChainEquiv1_single_other M A e r c hc, map_zero]
      simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply]
      rw [phiChainEquiv0_single_other M A (Nf.targetSubsetEdgeRight (comparisonFactor qc qf h ⁻¹' A) e.1) 1 c hr,
        phiChainEquiv0_single_other M A (Nf.targetSubsetEdgeLeft (comparisonFactor qc qf h ⁻¹' A) e.1) 1 c hc]
      simp

/-- 全Φ分類は同じ原V微分と各原Φ三辺和に可換。 -/
theorem phiChainEquiv_comm2 (x : VerticalFace M A →₀ ℚ) (c : Nc.ChartInTargetSubset A) :
    phiChainEquiv1 M A (verticalBoundary M A x) c =
      phiBoundary2 M A c (phiChainEquiv2 M A x c) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | single f r =>
    let cf := Carrier.chart M A _ (fun _ ht => ht)
      (Nf.targetSubsetEdgeLeft _ (Nf.targetSubsetFaceEdge0 _ f.1))
    let ff : PhiFace M A cf := ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2, rfl⟩
    by_cases hc : cf = c
    · let fc : PhiFace M A c := ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2, hc⟩
      have hf : f = (⟨fc.1, fc.2.1, fc.2.2.1, fc.2.2.2.1, fc.2.2.2.2.1⟩ : VerticalFace M A) := rfl
      rw [hf, phiChainEquiv2_single_same, phiBoundary2_single, verticalBoundary_single]
      simp only [map_smul, map_add, map_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
      have he (i : Fin 3) : verticalFaceEdge M A f i =
          (⟨(phiFaceEdge M A fc i).1, (phiFaceEdge M A fc i).2.1⟩ : VerticalEdge M A) := rfl
      rw [he 0, he 1, he 2, phiChainEquiv1_single_same,
        phiChainEquiv1_single_same, phiChainEquiv1_single_same]
    · rw [phiChainEquiv2_single_other M A f r c hc, map_zero, verticalBoundary_single]
      simp only [map_smul, map_sub, map_add, Pi.smul_apply, Pi.sub_apply, Pi.add_apply]
      have he (i : Fin 3) : Carrier.chart M A _ (fun _ ht => ht)
          (Nf.targetSubsetEdgeLeft _ (verticalFaceEdge M A f i).1) ≠ c := by
        have hh := phiFace_edge_chart M A ff i
        exact fun hh' => hc (hh.symm.trans hh')
      rw [phiChainEquiv1_single_other M A _ 1 c (he 0),
        phiChainEquiv1_single_other M A _ 1 c (he 1),
        phiChainEquiv1_single_other M A _ 1 c (he 2)]
      simp

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.phiChartPartition
#print axioms AAT.AG.AtlasCoefficientFiber.phiEdgePartition
#print axioms AAT.AG.AtlasCoefficientFiber.phiFacePartition
#print axioms AAT.AG.AtlasCoefficientFiber.phiChartPartition_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiEdgePartition_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiFacePartition_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiEdgePartition_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiFacePartition_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv0
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv1
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv2
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv0_single
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv1_single
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv2_single
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv0_single_other
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv1_single_other
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv2_single_other
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv0_single_same
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv1_single_same
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv2_single_same
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.phiChainEquiv_comm2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
