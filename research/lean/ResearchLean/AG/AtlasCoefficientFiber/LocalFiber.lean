import ResearchLean.AG.AtlasCoefficientFiber.PushforwardCoefficient
import ResearchLean.AG.FaceRelationSubdivision.SupportedChain

/-!
# G-135 A：原始セル逆像と持ち上げ関係

## Implementation notes

Φのセルは退化Option値とchart像で選び、Γの頂点はmapped辺、
関係は二つの混在面パターンで選ぶ。辺の端点が同じ粗chartに写るという
条件だけでΦを作る案は、mapped粗loopを取り込むため採らない。
Γの関係には元の面名と二出現を残し、simple graphへの置換はしない。
自由chainはG-134のfreeMapと同じℚ基底で作る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- Φ_cのchartは、選択済みchartの原始像がcであるもの。A・設計§1。 -/
abbrev PhiChart (c : Nc.ChartInTargetSubset A) :=
  {v : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) //
    Carrier.chart M A _ (fun _ ht => ht) v = c}

/-- Φ_cの辺は宣言上の退化辺のみ。mapped粗loopを含めない。A・設計§1。 -/
abbrev PhiEdge (c : Nc.ChartInTargetSubset A) :=
  {e : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) //
    M.edgeMap e.1 = none ∧ Carrier.chart M A _ (fun _ ht => ht)
      (Nf.targetSubsetEdgeLeft _ e) = c}

/-- Φ_cの面は全三辺も退化する垂直面。三つの原始出現を選択条件に保持。 -/
abbrev PhiFace (c : Nc.ChartInTargetSubset A) :=
  {f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) //
    M.faceMap f.1 = none ∧ M.edgeMap (Nf.nerve.faceEdge0 f.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1) = none ∧
      Carrier.chart M A _ (fun _ ht => ht)
        (Nf.targetSubsetEdgeLeft _ (Nf.targetSubsetFaceEdge0 _ f)) = c}

/-- Γ_eの頂点は、同じ名前付き粗辺へmappedである細辺。 -/
abbrev GammaVertex (e : Nc.EdgeInTargetSubset A) :=
  {a : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) // M.edgeMap a.1 = some e.1}

/-- Γ_eの関係は原始二パターンの混在面。loopと平行面名をそのまま残す。 -/
abbrev GammaEdge (e : Nc.EdgeInTargetSubset A) :=
  {f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) //
    M.faceMap f.1 = none ∧
    ((M.edgeMap (Nf.nerve.faceEdge0 f.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e.1 ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1) = some e.1) ∨
    (M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e.1 ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e.1 ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1) = none))}

/-- Λ_Fは原始faceMapが同じ名前付き粗面を返す細面の集合。 -/
abbrev LambdaFace (F : Nc.FaceInTargetSubset A) :=
  {f : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) // M.faceMap f.1 = some F.1}

/-- Φの原始左・右端点。右端点の所属はMの退化端点等号から導く。 -/
def phiEndpoint {c : Nc.ChartInTargetSubset A} (e : PhiEdge M A c) (s : Bool) : PhiChart M A c :=
  ⟨edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e.1 s, by
    cases s
    · exact e.2.2
    · exact (M.targetSubsetChartMap_edgeLeft_eq_right_of_none A _ _ e.1 e.2.1).symm.trans e.2.2⟩

/-- Φ端点の元の細chart。所属証明を下流で剥かずに使うAPI。 -/
@[simp] theorem phiEndpoint_val {c : Nc.ChartInTargetSubset A} (e : PhiEdge M A c) (s : Bool) :
    (phiEndpoint M A e s).1 = edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) e.1 s := rfl

/-- 垂直面の三辺の原始carrier所属を三角形端点等号から導く。 -/
theorem phiFace_edge_chart {c : Nc.ChartInTargetSubset A} (f : PhiFace M A c) (i : Fin 3) :
    Carrier.chart M A _ (fun _ ht => ht)
      (Nf.targetSubsetEdgeLeft _ (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i)) = c := by
  fin_cases i
  · exact f.2.2.2.2.2
  · exact (congrArg (Carrier.chart M A _ (fun _ ht => ht))
      (Nf.targetSubset_left_faceEdge0_eq_left_faceEdge1 _ f.1).symm).trans f.2.2.2.2.2
  · exact ((congrArg (Carrier.chart M A _ (fun _ ht => ht))
      (Nf.targetSubset_right_faceEdge0_eq_left_faceEdge2 _ f.1).symm).trans
      (M.targetSubsetChartMap_edgeLeft_eq_right_of_none A _ _
        (Nf.targetSubsetFaceEdge0 _ f.1) f.2.2.1).symm).trans f.2.2.2.2.2

/-- Φ面の各辺は原始Optionがnone。 -/
theorem phiFace_edge_none {c : Nc.ChartInTargetSubset A} (f : PhiFace M A c) (i : Fin 3) :
    M.edgeMap (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i).1 = none := by
  fin_cases i
  · exact f.2.2.1
  · exact f.2.2.2.1
  · exact f.2.2.2.2.1

/-- Φの三辺を、同じ名前・出現位置で生成する。 -/
def phiFaceEdge {c : Nc.ChartInTargetSubset A} (f : PhiFace M A c) (i : Fin 3) : PhiEdge M A c :=
  ⟨faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i,
    phiFace_edge_none M A f i, phiFace_edge_chart M A f i⟩

/-- Φ面辺の細セル名を読む公開API。 -/
@[simp] theorem phiFaceEdge_val {c : Nc.ChartInTargetSubset A} (f : PhiFace M A c) (i : Fin 3) :
    (phiFaceEdge M A f i).1 = faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i := rfl

/-- Γの負符号の端点は両mixed型で細faceEdge1。 -/
def gammaSource {e : Nc.EdgeInTargetSubset A} (f : GammaEdge M A e) : GammaVertex M A e :=
  ⟨Nf.targetSubsetFaceEdge1 _ f.1, by rcases f.2.2 with hl | hr; exact hl.2.1; exact hr.2.1⟩

/-- Γの正符号の端点。左辺退化ならedge2、第三辺退化ならedge0。 -/
def gammaTarget {e : Nc.EdgeInTargetSubset A} (f : GammaEdge M A e) : GammaVertex M A e := by
  classical
  exact if h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none then
    ⟨Nf.targetSubsetFaceEdge2 _ f.1, by
      rcases f.2.2 with hl | hr
      · exact hl.2.2
      · cases h0.symm.trans hr.1⟩
  else
    ⟨Nf.targetSubsetFaceEdge0 _ f.1, by
      rcases f.2.2 with hl | hr
      · exact False.elim (h0 hl.1)
      · exact hr.1⟩

/-- Γの二端点を保持したℚ incidence。関係がloopなら同じ基底が相殺する。 -/
def gammaBoundary (e : Nc.EdgeInTargetSubset A) :
    (GammaEdge M A e →₀ ℚ) →ₗ[ℚ] (GammaVertex M A e →₀ ℚ) :=
  freeMap fun f => Finsupp.single (gammaTarget M A f) 1 - Finsupp.single (gammaSource M A f) 1

/-- 原始関係面のincidence列。期待するrankを入力にせず二端点から生成。 -/
@[simp] theorem gammaBoundary_single (e : Nc.EdgeInTargetSubset A) (f : GammaEdge M A e) (a : ℚ) :
    gammaBoundary M A e (Finsupp.single f a) = a •
      (Finsupp.single (gammaTarget M A f) 1 - Finsupp.single (gammaSource M A f) 1) :=
  freeMap_single _ _ _

/-- Φの原始端点差分。局所fiber cochainの次数0微分。 -/
def phiD0 (c : Nc.ChartInTargetSubset A) :
    (PhiChart M A c → ℚ) →ₗ[ℚ] (PhiEdge M A c → ℚ) where
  toFun z e := z (phiEndpoint M A e true) - z (phiEndpoint M A e false)
  map_add' z w := by funext e; dsimp; ring
  map_smul' r z := by funext e; dsimp; ring

/-- Φの原始三辺の符号付き和。局所fiber cochainの次数1微分。 -/
def phiD1 (c : Nc.ChartInTargetSubset A) :
    (PhiEdge M A c → ℚ) →ₗ[ℚ] (PhiFace M A c → ℚ) where
  toFun z f := z (phiFaceEdge M A f 0) - z (phiFaceEdge M A f 1) + z (phiFaceEdge M A f 2)
  map_add' z w := by funext f; dsimp; ring
  map_smul' r z := by funext f; dsimp; ring

/-- Φの第一微分の端点評価。下流の証明に用いる公開API。 -/
@[simp] theorem phiD0_apply (c : Nc.ChartInTargetSubset A) (z : PhiChart M A c → ℚ)
    (e : PhiEdge M A c) :
    phiD0 M A c z e = z (phiEndpoint M A e true) - z (phiEndpoint M A e false) := rfl

/-- Φの第二微分の三辺評価。下流の証明に用いる公開API。 -/
@[simp] theorem phiD1_apply (c : Nc.ChartInTargetSubset A) (z : PhiEdge M A c → ℚ)
    (f : PhiFace M A c) :
    phiD1 M A c z f = z (phiFaceEdge M A f 0) - z (phiFaceEdge M A f 1) +
      z (phiFaceEdge M A f 2) := rfl

/-- 同じ細incidenceの三頂点関係からΦのsquare-zeroを放電する。 -/
theorem phiD1_comp_phiD0 (c : Nc.ChartInTargetSubset A) (z : PhiChart M A c → ℚ) :
    phiD1 M A c (phiD0 M A c z) = 0 := by
  funext f
  have h01 : phiEndpoint M A (phiFaceEdge M A f 0) false =
      phiEndpoint M A (phiFaceEdge M A f 1) false := by
    apply Subtype.ext
    exact Nf.targetSubset_left_faceEdge0_eq_left_faceEdge1 _ f.1
  have h02 : phiEndpoint M A (phiFaceEdge M A f 0) true =
      phiEndpoint M A (phiFaceEdge M A f 2) false := by
    apply Subtype.ext
    exact Nf.targetSubset_right_faceEdge0_eq_left_faceEdge2 _ f.1
  have h12 : phiEndpoint M A (phiFaceEdge M A f 1) true =
      phiEndpoint M A (phiFaceEdge M A f 2) true := by
    apply Subtype.ext
    exact Nf.targetSubset_right_faceEdge1_eq_right_faceEdge2 _ f.1
  simp only [phiD1_apply, phiD0_apply, h01, h02, h12, Pi.zero_apply]
  ring

/-- A・設計§1の原始Φ複体。有限性と微分零性は選択セルから導出する。 -/
def phiComplex (c : Nc.ChartInTargetSubset A) : ThreeCochainComplex ℚ where
  C0 := PhiChart M A c → ℚ
  C1 := PhiEdge M A c → ℚ
  C2 := PhiFace M A c → ℚ
  d0 := phiD0 M A c
  d1 := phiD1 M A c
  d1_comp_d0 := phiD1_comp_phiD0 M A c

/-- 宣言上の退化辺が空なら、原Φの次数1空間は零である。 -/
theorem phiComplex_C1_subsingleton (c : Nc.ChartInTargetSubset A)
    [IsEmpty (PhiEdge M A c)] : Subsingleton (phiComplex M A c).C1 := by
  change Subsingleton (PhiEdge M A c → ℚ)
  infer_instance

/-- Φの原始三種類を細incidence圏へ戻す対象写像。 -/
def phiCellObj (c : Nc.ChartInTargetSubset A) :
    PhiChart M A c ⊕ (PhiEdge M A c ⊕ PhiFace M A c) →
      Inc Nf (comparisonFactor qc qf h ⁻¹' A)
  | .inl v => .chart v.1
  | .inr (.inl e) => .edge e.1
  | .inr (.inr f) => .face f.1

/-- Φ chartの細incidence対象値を読む定義所有者API。 -/
@[simp] theorem phiCellObj_chart (c : Nc.ChartInTargetSubset A) (v : PhiChart M A c) :
    phiCellObj M A c (.inl v) = .chart v.1 := rfl

/-- Φ edgeの細incidence対象値を読む定義所有者API。 -/
@[simp] theorem phiCellObj_edge (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) :
    phiCellObj M A c (.inr (.inl e)) = .edge e.1 := rfl

/-- Φ faceの細incidence対象値を読む定義所有者API。 -/
@[simp] theorem phiCellObj_face (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) :
    phiCellObj M A c (.inr (.inr f)) = .face f.1 := rfl

/-- Φのセル包含は三種類と各名前付き細セルを区別するので単射。 -/
theorem phiCellObj_injective (c : Nc.ChartInTargetSubset A) :
    Function.Injective (phiCellObj M A c) := by
  intro x y hh
  rcases x with v | (e | f) <;> rcases y with v' | (e' | f')
  · exact congrArg Sum.inl (Subtype.ext (Inc.chart.inj hh))
  · cases hh
  · cases hh
  · cases hh
  · exact congrArg (fun e => Sum.inr (Sum.inl e)) (Subtype.ext (Inc.edge.inj hh))
  · cases hh
  · cases hh
  · cases hh
  · exact congrArg (fun f => Sum.inr (Sum.inr f)) (Subtype.ext (Inc.face.inj hh))

/-- Φの原始セルincidence圏。元の端点・三辺の出現をfull induced categoryで保持。 -/
abbrev PhiInc (c : Nc.ChartInTargetSubset A) :=
  InducedCategory (Inc Nf (comparisonFactor qc qf h ⁻¹' A)) (phiCellObj M A c)

/-- Φの全原始セルのcarrierは同じ粗chart。所属条件から導出するAPI。 -/
theorem phiCellObj_carrier (c : Nc.ChartInTargetSubset A)
    (x : PhiChart M A c ⊕ (PhiEdge M A c ⊕ PhiFace M A c)) :
    (Carrier.preimageFunctor M A).obj (phiCellObj M A c x) = .chart c := by
  rcases x with v | (e | f)
  · exact congrArg Inc.chart v.2
  · exact (Carrier.preimageFunctor_obj_edge_of_none M A e.1 e.2.1).trans
      (congrArg Inc.chart e.2.2)
  · exact ((Carrier.preimageFunctor_obj_face M A f.1).trans
      (Carrier.face_of_vertical M A _ _ f.1 f.2.1 f.2.2.1 f.2.2.2.1)).trans
      (congrArg Inc.chart f.2.2.2.2.2)

/-- Γの二種類の原始セルを細incidence圏へ戻す対象写像。 -/
def gammaCellObj (e : Nc.EdgeInTargetSubset A) :
    GammaVertex M A e ⊕ GammaEdge M A e → Inc Nf (comparisonFactor qc qf h ⁻¹' A)
  | .inl v => .edge v.1
  | .inr f => .face f.1

/-- Γ mapped辺の対象値を読む定義所有者API。 -/
@[simp] theorem gammaCellObj_inl (e : Nc.EdgeInTargetSubset A) (v : GammaVertex M A e) :
    gammaCellObj M A e (.inl v) = .edge v.1 := rfl

/-- Γ mixed面の対象値を読む定義所有者API。 -/
@[simp] theorem gammaCellObj_inr (e : Nc.EdgeInTargetSubset A) (f : GammaEdge M A e) :
    gammaCellObj M A e (.inr f) = .face f.1 := rfl

/-- Γの原始セル名による包含は単射。二種類と各セル名を区別する。 -/
theorem gammaCellObj_injective (e : Nc.EdgeInTargetSubset A) :
    Function.Injective (gammaCellObj M A e) := by
  intro x y hh
  rcases x with v | f <;> rcases y with v' | f'
  · exact congrArg Sum.inl (Subtype.ext (Inc.edge.inj hh))
  · cases hh
  · cases hh
  · exact congrArg Sum.inr (Subtype.ext (Inc.face.inj hh))

/-- Γのincidence圏。混在面の二出現は異なるedgeFace射として残る。 -/
abbrev GammaInc (e : Nc.EdgeInTargetSubset A) :=
  InducedCategory (Inc Nf (comparisonFactor qc qf h ⁻¹' A)) (gammaCellObj M A e)

/-- Γの全原始セルのcarrierは同じ粗辺。loopや同名辺の出現を忘れない。 -/
theorem gammaCellObj_carrier (e : Nc.EdgeInTargetSubset A)
    (x : GammaVertex M A e ⊕ GammaEdge M A e) :
    (Carrier.preimageFunctor M A).obj (gammaCellObj M A e x) = .edge e := by
  rcases x with v | f
  · exact (Carrier.preimageFunctor_obj_edge_of_some M A v.1 e.1 v.2).trans
      (congrArg Inc.edge (Subtype.ext rfl))
  · rcases f.2.2 with hl | hr
    · exact ((Carrier.preimageFunctor_obj_face M A f.1).trans
        (Carrier.face_of_mixed_left M A _ _ f.1 f.2.1 hl.1 e.1 hl.2.1)).trans
        (congrArg Inc.edge (Subtype.ext rfl))
    · exact ((Carrier.preimageFunctor_obj_face M A f.1).trans
        (Carrier.face_of_mixed_right M A _ _ f.1 f.2.1 e.1 hr.1)).trans
        (congrArg Inc.edge (Subtype.ext rfl))

/-- Λの原始持ち上げのcarrierは同じ粗面。 -/
theorem lambdaFace_carrier (F : Nc.FaceInTargetSubset A) (f : LambdaFace M A F) :
    (Carrier.preimageFunctor M A).obj (.face f.1) = .face F :=
  (Carrier.preimageFunctor_obj_face_of_some M A f.1 F.1 f.2).trans
    (congrArg Inc.face (Subtype.ext rfl))

/-- 原始Φのchain端点差分。元の細chainと同じ符号で線形延長する。 -/
def phiBoundary1 (c : Nc.ChartInTargetSubset A) :
    (PhiEdge M A c →₀ ℚ) →ₗ[ℚ] (PhiChart M A c →₀ ℚ) :=
  freeMap fun e => Finsupp.single (phiEndpoint M A e true) 1 -
    Finsupp.single (phiEndpoint M A e false) 1

/-- 原始Φのchain三辺和。面名と三出現をそのまま線形延長する。 -/
def phiBoundary2 (c : Nc.ChartInTargetSubset A) :
    (PhiFace M A c →₀ ℚ) →ₗ[ℚ] (PhiEdge M A c →₀ ℚ) :=
  freeMap fun f => Finsupp.single (phiFaceEdge M A f 0) 1 -
    Finsupp.single (phiFaceEdge M A f 1) 1 + Finsupp.single (phiFaceEdge M A f 2) 1

/-- Φ chain第一微分の基底像。 -/
@[simp] theorem phiBoundary1_single (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) (r : ℚ) :
    phiBoundary1 M A c (Finsupp.single e r) = r •
      (Finsupp.single (phiEndpoint M A e true) 1 - Finsupp.single (phiEndpoint M A e false) 1) :=
  freeMap_single _ _ _

/-- Φ chain第二微分の基底像。 -/
@[simp] theorem phiBoundary2_single (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) (r : ℚ) :
    phiBoundary2 M A c (Finsupp.single f r) = r •
      (Finsupp.single (phiFaceEdge M A f 0) 1 - Finsupp.single (phiFaceEdge M A f 1) 1 +
        Finsupp.single (phiFaceEdge M A f 2) 1) := freeMap_single _ _ _

/-- Φの第一chain微分の双対は、独立した同じ原始端点cochain微分。 -/
theorem phiBoundary1_dual (c : Nc.ChartInTargetSubset A) (z : PhiChart M A c → ℚ)
    (x : PhiEdge M A c →₀ ℚ) :
    freeDualEquiv _ z (phiBoundary1 M A c x) = freeDualEquiv _ (phiD0 M A c z) x := by
  have hh : (freeDualEquiv _ z).comp (phiBoundary1 M A c) =
      freeDualEquiv _ (phiD0 M A c z) := by
    apply Finsupp.lhom_ext
    intro e r
    simp only [LinearMap.comp_apply, phiBoundary1_single, map_smul, map_sub,
      freeDualEquiv_single, one_mul, smul_eq_mul, phiD0_apply]
  exact LinearMap.congr_fun hh x

/-- Φの第二chain微分の双対は、同じ三辺cochain微分。 -/
theorem phiBoundary2_dual (c : Nc.ChartInTargetSubset A) (z : PhiEdge M A c → ℚ)
    (x : PhiFace M A c →₀ ℚ) :
    freeDualEquiv _ z (phiBoundary2 M A c x) = freeDualEquiv _ (phiD1 M A c z) x := by
  have hh : (freeDualEquiv _ z).comp (phiBoundary2 M A c) =
      freeDualEquiv _ (phiD1 M A c z) := by
    apply Finsupp.lhom_ext
    intro f r
    simp only [LinearMap.comp_apply, phiBoundary2_single, map_smul, map_sub, map_add,
      freeDualEquiv_single, one_mul, smul_eq_mul, phiD1_apply]
  exact LinearMap.congr_fun hh x

/-- Φ chainのsquare-zero。全双対評価で独立した原始cochain証明へ接続する。 -/
theorem phiBoundary1_comp_phiBoundary2 (c : Nc.ChartInTargetSubset A) :
    (phiBoundary1 M A c).comp (phiBoundary2 M A c) = 0 := by
  apply LinearMap.ext
  intro x
  apply freeDual_separates
  intro z
  rw [LinearMap.comp_apply, phiBoundary1_dual, phiBoundary2_dual, phiD1_comp_phiD0]
  simp

/-- Φ chart chainから元の細chart chainへの名前付き基底包含。 -/
def phiEmbed0 (c : Nc.ChartInTargetSubset A) :
    (PhiChart M A c →₀ ℚ) →ₗ[ℚ] K0 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  Finsupp.lmapDomain ℚ ℚ Subtype.val

/-- Φ edge chainから元の細edge chainへの名前付き基底包含。 -/
def phiEmbed1 (c : Nc.ChartInTargetSubset A) :
    (PhiEdge M A c →₀ ℚ) →ₗ[ℚ] K1 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  Finsupp.lmapDomain ℚ ℚ Subtype.val

/-- Φ face chainから元の細face chainへの名前付き基底包含。 -/
def phiEmbed2 (c : Nc.ChartInTargetSubset A) :
    (PhiFace M A c →₀ ℚ) →ₗ[ℚ] K2 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  Finsupp.lmapDomain ℚ ℚ Subtype.val

/-- Φ第一微分の包含は元の支持chain微分に可換。 -/
theorem phiEmbed_comm1 (c : Nc.ChartInTargetSubset A) :
    (phiEmbed0 M A c).comp (phiBoundary1 M A c) =
      (chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)).comp (phiEmbed1 M A c) := by
  apply Finsupp.lhom_ext
  intro e r
  simp only [LinearMap.comp_apply, phiBoundary1_single, phiEmbed0, phiEmbed1,
    map_smul, map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, chainD1_single]
  rfl

/-- Φ第二微分の包含は元の支持chain微分に可換。 -/
theorem phiEmbed_comm2 (c : Nc.ChartInTargetSubset A) :
    (phiEmbed1 M A c).comp (phiBoundary2 M A c) =
      (chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)).comp (phiEmbed2 M A c) := by
  apply Finsupp.lhom_ext
  intro f r
  simp only [LinearMap.comp_apply, phiBoundary2_single, phiEmbed1, phiEmbed2,
    map_smul, map_sub, map_add, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, chainD2_single]
  rfl

/-- Φ chart包含は単射。入力セル名のSubtype.valの単射性を使う。 -/
theorem phiEmbed0_injective (c : Nc.ChartInTargetSubset A) :
    Function.Injective (phiEmbed0 M A c) := Finsupp.mapDomain_injective Subtype.val_injective

/-- Φ edge包含は単射。mapped粗loopを追加せずに細chain部分空間となる。 -/
theorem phiEmbed1_injective (c : Nc.ChartInTargetSubset A) :
    Function.Injective (phiEmbed1 M A c) := Finsupp.mapDomain_injective Subtype.val_injective

/-- Φ face包含は単射。名前付き垂直面基底をそのまま保持する。 -/
theorem phiEmbed2_injective (c : Nc.ChartInTargetSubset A) :
    Function.Injective (phiEmbed2 M A c) := Finsupp.mapDomain_injective Subtype.val_injective

/-- Φのincidence対象は有限な原始選択セルの有限和。 -/
instance phiIncFinite (c : Nc.ChartInTargetSubset A) : Finite (PhiInc M A c) :=
  inferInstanceAs (Finite (PhiChart M A c ⊕ (PhiEdge M A c ⊕ PhiFace M A c)))

/-- Γのincidence対象は有限なmapped辺とmixed面の有限和。 -/
instance gammaIncFinite (e : Nc.EdgeInTargetSubset A) : Finite (GammaInc M A e) :=
  inferInstanceAs (Finite (GammaVertex M A e ⊕ GammaEdge M A e))

/-- Λは有限な選択済み細面の部分集合。持ち上げ存在を仮定しない。 -/
instance lambdaFaceFinite (F : Nc.FaceInTargetSubset A) : Finite (LambdaFace M A F) := inferInstance

/-- Γの負符号端点は同じ細faceEdge1。定義所有者API。 -/
@[simp] theorem gammaSource_val {e : Nc.EdgeInTargetSubset A} (f : GammaEdge M A e) :
    (gammaSource M A f).1 = Nf.targetSubsetFaceEdge1 _ f.1 := rfl

/-- 左mixed型のΓ正符号端点は同じ細faceEdge2。 -/
theorem gammaTarget_val_of_left {e : Nc.EdgeInTargetSubset A} (f : GammaEdge M A e)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none) :
    (gammaTarget M A f).1 = Nf.targetSubsetFaceEdge2 _ f.1 := by
  simp only [gammaTarget, dif_pos h0]

/-- 右mixed型のΓ正符号端点は同じ細faceEdge0。 -/
theorem gammaTarget_val_of_right {e : Nc.EdgeInTargetSubset A} (f : GammaEdge M A e)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = some e.1) :
    (gammaTarget M A f).1 = Nf.targetSubsetFaceEdge0 _ f.1 := by
  have hn : ¬ M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none := by rw [h0]; exact Option.some_ne_none _
  simp only [gammaTarget, dif_neg hn]

/-- 原始Γの有限有向多重グラフの頂点型。名前付きmapped辺を保持する。 -/
def GammaGraph (e : Nc.EdgeInTargetSubset A) : Type u := GammaVertex M A e

/-- Γの有向射は原始mixed面とその二端点の所属であり、loop・平行面を区別する。 -/
instance gammaGraphQuiver (e : Nc.EdgeInTargetSubset A) : Quiver (GammaGraph M A e) where
  Hom v w := {f : GammaEdge M A e // gammaSource M A f = v ∧ gammaTarget M A f = w}

/-- 原始Γ頂点の有限性を同じ有向グラフへ渡す。 -/
instance gammaGraphFinite (e : Nc.EdgeInTargetSubset A) : Finite (GammaGraph M A e) :=
  inferInstanceAs (Finite (GammaVertex M A e))

/-- loopも平行辺も原始mixed面の有限集合から生じるため、各Homが有限である。 -/
instance gammaGraphHomFinite (e : Nc.EdgeInTargetSubset A) (v w : GammaGraph M A e) :
    Finite (v ⟶ w) := inferInstanceAs (Finite {f : GammaEdge M A e //
      gammaSource M A f = v ∧ gammaTarget M A f = w})

/-- 原始mixed面を、その同じ二端点間の有向Γ射として生成する。 -/
def gammaGraphArrow (e : Nc.EdgeInTargetSubset A) (f : GammaEdge M A e) :
    @Quiver.Hom (GammaGraph M A e) (gammaGraphQuiver M A e) (gammaSource M A f) (gammaTarget M A f) :=
  ⟨f, rfl, rfl⟩

/-- Γ射が保持する原始mixed面名。定義所有者API。 -/
@[simp] theorem gammaGraphArrow_val (e : Nc.EdgeInTargetSubset A) (f : GammaEdge M A e) :
    (gammaGraphArrow M A e f).1 = f := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.PhiChart
#print axioms AAT.AG.AtlasCoefficientFiber.PhiEdge
#print axioms AAT.AG.AtlasCoefficientFiber.PhiFace
#print axioms AAT.AG.AtlasCoefficientFiber.GammaVertex
#print axioms AAT.AG.AtlasCoefficientFiber.GammaEdge
#print axioms AAT.AG.AtlasCoefficientFiber.LambdaFace
#print axioms AAT.AG.AtlasCoefficientFiber.phiEndpoint
#print axioms AAT.AG.AtlasCoefficientFiber.phiEndpoint_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiFace_edge_chart
#print axioms AAT.AG.AtlasCoefficientFiber.phiFace_edge_none
#print axioms AAT.AG.AtlasCoefficientFiber.phiFaceEdge
#print axioms AAT.AG.AtlasCoefficientFiber.phiFaceEdge_val
#print axioms AAT.AG.AtlasCoefficientFiber.gammaSource
#print axioms AAT.AG.AtlasCoefficientFiber.gammaTarget
#print axioms AAT.AG.AtlasCoefficientFiber.gammaBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.gammaBoundary_single
#print axioms AAT.AG.AtlasCoefficientFiber.phiD0
#print axioms AAT.AG.AtlasCoefficientFiber.phiD1
#print axioms AAT.AG.AtlasCoefficientFiber.phiD0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiD1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.phiD1_comp_phiD0
#print axioms AAT.AG.AtlasCoefficientFiber.phiComplex
#print axioms AAT.AG.AtlasCoefficientFiber.phiComplex_C1_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellObj
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellObj_chart
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellObj_edge
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellObj_face
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellObj_injective
#print axioms AAT.AG.AtlasCoefficientFiber.PhiInc
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellObj_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellObj
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellObj_inl
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellObj_inr
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellObj_injective
#print axioms AAT.AG.AtlasCoefficientFiber.GammaInc
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellObj_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaFace_carrier
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundary1
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundary2
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundary1_single
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundary2_single
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundary1_dual
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundary2_dual
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundary1_comp_phiBoundary2
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed0
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed1
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed2
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed_comm2
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed0_injective
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed1_injective
#print axioms AAT.AG.AtlasCoefficientFiber.phiEmbed2_injective
#print axioms AAT.AG.AtlasCoefficientFiber.phiIncFinite
#print axioms AAT.AG.AtlasCoefficientFiber.gammaIncFinite
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaFaceFinite
#print axioms AAT.AG.AtlasCoefficientFiber.gammaSource_val
#print axioms AAT.AG.AtlasCoefficientFiber.gammaTarget_val_of_left
#print axioms AAT.AG.AtlasCoefficientFiber.gammaTarget_val_of_right
#print axioms AAT.AG.AtlasCoefficientFiber.GammaGraph
#print axioms AAT.AG.AtlasCoefficientFiber.gammaGraphQuiver
#print axioms AAT.AG.AtlasCoefficientFiber.gammaGraphFinite
#print axioms AAT.AG.AtlasCoefficientFiber.gammaGraphHomFinite
#print axioms AAT.AG.AtlasCoefficientFiber.gammaGraphArrow
#print axioms AAT.AG.AtlasCoefficientFiber.gammaGraphArrow_val
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
