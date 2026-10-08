import ResearchLean.AG.AtlasCoefficientFiber.SupportCells
import ResearchLean.AG.AtlasCoefficientFiber.LocalFiber

/-!
# G-135 D：原Φセルと自由chainの同じ台包含

## Implementation notes

粗chartを同じ支持包含で含め、Φの細chart・none辺・全none面を元のセル名で含める。
原端点と三辺出現を保つため、自由chainの両微分との可換性を基底上で証明する。
全Φ homology間の任意の写像を先に選ぶ案は原fiber代表の包含を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)
variable (c : Nc.ChartInTargetSubset A)

/-- 原Φ chartの台包含は同じ細chart名と粗chart像を保つ。 -/
def supportPhiChartInclude (v : PhiChart M A c) :
    PhiChart M B (supportCellInclude Nc.chartSupport hab c) :=
  ⟨supportCellInclude Nf.chartSupport (fun _ ht => hab ht) v.1, by
    apply Subtype.ext
    have hv := congrArg Subtype.val v.2
    rw [Carrier.chart_val] at hv ⊢
    exact hv⟩

/-- 原Φ辺の包含は宣言noneと同じ粗chart像を保つ。 -/
def supportPhiEdgeInclude (e : PhiEdge M A c) :
    PhiEdge M B (supportCellInclude Nc.chartSupport hab c) :=
  ⟨supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e.1, e.2.1, by
    apply Subtype.ext
    have he := congrArg Subtype.val e.2.2
    rw [Carrier.chart_val] at he ⊢
    exact he⟩

/-- 原Φ面の包含は全三辺noneと同じ粗chart像を保つ。 -/
def supportPhiFaceInclude (f : PhiFace M A c) :
    PhiFace M B (supportCellInclude Nc.chartSupport hab c) :=
  ⟨supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1,
    f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1, by
    apply Subtype.ext
    have hf := congrArg Subtype.val f.2.2.2.2.2
    rw [Carrier.chart_val] at hf ⊢
    exact hf⟩

/-- Φ chart包含の元細chartは同じ支持セル包含。 -/
@[simp] theorem supportPhiChartInclude_val (v : PhiChart M A c) :
    (supportPhiChartInclude M hab c v).1 =
      supportCellInclude Nf.chartSupport (fun _ ht => hab ht) v.1 := rfl
/-- Φ辺包含の元細辺は同じ支持セル包含。 -/
@[simp] theorem supportPhiEdgeInclude_val (e : PhiEdge M A c) :
    (supportPhiEdgeInclude M hab c e).1 =
      supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e.1 := rfl
/-- Φ面包含の元細面は同じ支持セル包含。 -/
@[simp] theorem supportPhiFaceInclude_val (f : PhiFace M A c) :
    (supportPhiFaceInclude M hab c f).1 =
      supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f.1 := rfl

/-- 原Φの左右出現は同じ台包含と可換。 -/
theorem supportPhiChartInclude_endpoint (e : PhiEdge M A c) (s : Bool) :
    supportPhiChartInclude M hab c (phiEndpoint M A e s) =
      phiEndpoint M B (supportPhiEdgeInclude M hab c e) s := by
  apply Subtype.ext
  rw [supportPhiChartInclude_val, phiEndpoint_val, phiEndpoint_val, supportPhiEdgeInclude_val]
  exact supportCellInclude_endpoint Nf (fun _ ht => hab ht) e.1 s

/-- 原Φの三辺出現も同じ台包含と可換。 -/
theorem supportPhiEdgeInclude_faceEdge (f : PhiFace M A c) (i : Fin 3) :
    supportPhiEdgeInclude M hab c (phiFaceEdge M A f i) =
      phiFaceEdge M B (supportPhiFaceInclude M hab c f) i := by
  apply Subtype.ext
  rw [supportPhiEdgeInclude_val, phiFaceEdge_val, phiFaceEdge_val, supportPhiFaceInclude_val]
  exact supportCellInclude_faceEdge Nf (fun _ ht => hab ht) f.1 i

/-- 元Φの次数0自由chainを同じセル包含で含める。 -/
def supportPhiChain0 : (PhiChart M A c →₀ ℚ) →ₗ[ℚ]
    (PhiChart M B (supportCellInclude Nc.chartSupport hab c) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportPhiChartInclude M hab c)

/-- 元Φ次数0chain包含の全基底値。 -/
@[simp] theorem supportPhiChain0_single (x : PhiChart M A c) (r : ℚ) :
    supportPhiChain0 M hab c (Finsupp.single x r) =
      Finsupp.single (supportPhiChartInclude M hab c x) r := Finsupp.mapDomain_single

/-- 元Φの次数1自由chainを同じセル包含で含める。 -/
def supportPhiChain1 : (PhiEdge M A c →₀ ℚ) →ₗ[ℚ]
    (PhiEdge M B (supportCellInclude Nc.chartSupport hab c) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportPhiEdgeInclude M hab c)

/-- 元Φ次数1chain包含の全基底値。 -/
@[simp] theorem supportPhiChain1_single (x : PhiEdge M A c) (r : ℚ) :
    supportPhiChain1 M hab c (Finsupp.single x r) =
      Finsupp.single (supportPhiEdgeInclude M hab c x) r := Finsupp.mapDomain_single

/-- 元Φの次数2自由chainを同じセル包含で含める。 -/
def supportPhiChain2 : (PhiFace M A c →₀ ℚ) →ₗ[ℚ]
    (PhiFace M B (supportCellInclude Nc.chartSupport hab c) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportPhiFaceInclude M hab c)

/-- 元Φ次数2chain包含の全基底値。 -/
@[simp] theorem supportPhiChain2_single (x : PhiFace M A c) (r : ℚ) :
    supportPhiChain2 M hab c (Finsupp.single x r) =
      Finsupp.single (supportPhiFaceInclude M hab c x) r := Finsupp.mapDomain_single

/-- 元Φの第一chain微分は左右出現を保持して同じ台包含と可換。 -/
theorem supportPhiChain_boundary1 :
    (supportPhiChain0 M hab c).comp (phiBoundary1 M A c) =
      (phiBoundary1 M B (supportCellInclude Nc.chartSupport hab c)).comp (supportPhiChain1 M hab c) := by
  apply Finsupp.lhom_ext
  intro e r
  change supportPhiChain0 M hab c (phiBoundary1 M A c (Finsupp.single e r)) =
    phiBoundary1 M B (supportCellInclude Nc.chartSupport hab c)
      (supportPhiChain1 M hab c (Finsupp.single e r))
  rw [phiBoundary1_single, supportPhiChain1_single, phiBoundary1_single]
  simp only [map_smul, map_sub, supportPhiChain0_single, supportPhiChartInclude_endpoint]

/-- 元Φの第二chain微分は三辺の符号と出現を保持して可換。 -/
theorem supportPhiChain_boundary2 :
    (supportPhiChain1 M hab c).comp (phiBoundary2 M A c) =
      (phiBoundary2 M B (supportCellInclude Nc.chartSupport hab c)).comp (supportPhiChain2 M hab c) := by
  apply Finsupp.lhom_ext
  intro f r
  change supportPhiChain1 M hab c (phiBoundary2 M A c (Finsupp.single f r)) =
    phiBoundary2 M B (supportCellInclude Nc.chartSupport hab c)
      (supportPhiChain2 M hab c (Finsupp.single f r))
  rw [phiBoundary2_single, supportPhiChain2_single, phiBoundary2_single]
  simp only [map_smul, map_add, map_sub, supportPhiChain1_single, supportPhiEdgeInclude_faceEdge]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChartInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiEdgeInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiFaceInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChartInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiEdgeInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiFaceInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChartInclude_endpoint
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiEdgeInclude_faceEdge
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain0
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain0_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain1_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain2
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain2_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain_boundary1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiChain_boundary2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
