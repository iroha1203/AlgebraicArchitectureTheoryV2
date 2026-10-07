import ResearchLean.AG.AtlasCoefficientFiber.DegenerateCells
import ResearchLean.AG.AtlasCoefficientFiber.LocalNaturality

/-!
# G-135 A §4：原始閉条件から局所成分上の値を生成する

## Implementation notes

細chartの値が垂直辺の両端で一致すれば、Φの全incidenceで一定になる。
成分上の値はこの原始評価を標準ConnectedComponentsへ降ろして生成する。
成分値を別certificateとして受け取り、ε像の逆方向を仮定する経路は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u v

/-- 全incidenceで一定な有理評価を、標準連結成分の商へ降ろす。 -/
def componentFunction {J : Type u} [Category.{v} J] (z : J → ℚ)
    (hz : ∀ {i j : J}, (i ⟶ j) → z i = z j) : CategoryTheory.ConnectedComponents J → ℚ :=
  CategoryTheory.ConnectedComponents.liftFunctor J
    { obj := fun j => Discrete.mk (z j), map := fun f => Discrete.eqToHom (hz f) }

/-- 降ろした成分関数は各原始対象で元の評価を返す。 -/
@[simp] theorem componentFunction_mk {J : Type u} [Category.{v} J] (z : J → ℚ)
    (hz : ∀ {i j : J}, (i ⟶ j) → z i = z j) (j : J) :
    componentFunction z hz (CategoryTheory.ConnectedComponents.mk j) = z j := rfl

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- Φの辺を同じ原始E_vの辺として読む。 -/
def phiEdgeVertical {c : Nc.ChartInTargetSubset A} (e : PhiEdge M A c) : VerticalEdge M A :=
  ⟨e.1, e.2.1⟩

/-- Φ辺をE_vへ読む際も同じ細辺名を保持する。 -/
@[simp] theorem phiEdgeVertical_val {c : Nc.ChartInTargetSubset A} (e : PhiEdge M A c) :
    (phiEdgeVertical M A e).1 = e.1 := rfl

/-- Φの面を同じ原始F_vの面として読む。 -/
def phiFaceVertical {c : Nc.ChartInTargetSubset A} (f : PhiFace M A c) : VerticalFace M A :=
  ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1⟩

/-- Φ面をF_vへ読む際も同じ細面名を保持する。 -/
@[simp] theorem phiFaceVertical_val {c : Nc.ChartInTargetSubset A} (f : PhiFace M A c) :
    (phiFaceVertical M A f).1 = f.1 := rfl

/-- 垂直辺の端点閉条件から、全垂直三角形の三頂点で値が一致する。 -/
theorem verticalFace_vertex_values
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ e : VerticalEdge M A,
      z (edgeEndpoint Nf _ e.1 true) = z (edgeEndpoint Nf _ e.1 false))
    (f : VerticalFace M A) (i : Fin 3) :
    z (faceVertex Nf _ f.1 i) = z (faceVertex Nf _ f.1 0) := by
  have h0 := hz (verticalFaceEdge M A f 0)
  have h1 := hz (verticalFaceEdge M A f 1)
  simp only [verticalFaceEdge_val, edgeEndpoint_faceEdge] at h0 h1
  fin_cases i
  · rfl
  · exact h0
  · exact h1

/-- Φの各セルを、原始chart値で読む。面では頂点位置0を使う。 -/
def phiCellValue (c : Nc.ChartInTargetSubset A)
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) : PhiInc M A c → ℚ
  | .inl v => z v.1
  | .inr (.inl e) => z (edgeEndpoint Nf _ e.1 false)
  | .inr (.inr f) => z (faceVertex Nf _ f.1 0)

/-- Φ chartの原始評価。 -/
@[simp] theorem phiCellValue_chart (c : Nc.ChartInTargetSubset A)
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) (x : PhiChart M A c) :
    phiCellValue M A c z (.inl x) = z x.1 := rfl

/-- Φ edgeの原始左端点評価。 -/
@[simp] theorem phiCellValue_edge (c : Nc.ChartInTargetSubset A)
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) (x : PhiEdge M A c) :
    phiCellValue M A c z (.inr (.inl x)) = z (edgeEndpoint Nf _ x.1 false) := rfl

/-- Φ faceの原始頂点位置0評価。 -/
@[simp] theorem phiCellValue_face (c : Nc.ChartInTargetSubset A)
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) (x : PhiFace M A c) :
    phiCellValue M A c z (.inr (.inr x)) = z (faceVertex Nf _ x.1 0) := rfl

/-- 垂直辺閉条件を全Φ incidenceへ放電する。成分一定性を入力にしない。 -/
theorem phiCellValue_invariant (c : Nc.ChartInTargetSubset A)
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ e : VerticalEdge M A,
      z (edgeEndpoint Nf _ e.1 true) = z (edgeEndpoint Nf _ e.1 false))
    {i j : PhiInc M A c} (g : i ⟶ j) : phiCellValue M A c z i = phiCellValue M A c z j := by
  rcases i with v | (e | f) <;> rcases j with w | (a | t)
  · exact congrArg z (incHom_chart_chart_target _ _ g.hom).symm
  · rcases v with ⟨v, hv⟩; rcases a with ⟨a, ha⟩
    cases g.hom with
    | chartEdge _ _ s hh =>
      change z v = z (edgeEndpoint Nf _ a false)
      change v = edgeEndpoint Nf _ a s at hh
      rw [hh]
      cases s
      · rfl
      · exact hz ⟨a, ha.1⟩
  · rcases v with ⟨v, hv⟩; rcases t with ⟨t, ht⟩
    cases g.hom with
    | chartFace _ _ k hh =>
      change z v = z (faceVertex Nf _ t 0)
      change v = faceVertex Nf _ t k at hh
      rw [hh]
      exact verticalFace_vertex_values M A z hz ⟨t, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩ k
  · cases g.hom
  · exact congrArg (fun e => z (edgeEndpoint Nf _ e false)) (incHom_edge_edge_target _ _ g.hom).symm
  · rcases e with ⟨e, he⟩; rcases t with ⟨t, ht⟩
    cases g.hom with
    | edgeFace _ _ k hh =>
      change z (edgeEndpoint Nf _ e false) = z (faceVertex Nf _ t 0)
      change e = faceEdge Nf _ t k at hh
      rw [hh, edgeEndpoint_faceEdge]
      exact verticalFace_vertex_values M A z hz ⟨t, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩ _
  · cases g.hom
  · cases g.hom
  · exact congrArg (fun f => z (faceVertex Nf _ f 0)) (incHom_target_of_face _ g.hom |> Inc.face.inj).symm

/-- 垂直辺で閉じた細chart値から、全Φ成分上の同じ値を生成する。 -/
def phiDescendedValues (c : Nc.ChartInTargetSubset A)
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ e : VerticalEdge M A,
      z (edgeEndpoint Nf _ e.1 true) = z (edgeEndpoint Nf _ e.1 false)) :
    CategoryTheory.ConnectedComponents (PhiInc M A c) → ℚ :=
  componentFunction (phiCellValue M A c z) (phiCellValue_invariant M A c z hz)

/-- 生成したΦ成分値は全原始fine chartで元の値を返す。 -/
@[simp] theorem phiDescendedValues_chart (c : Nc.ChartInTargetSubset A)
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ e : VerticalEdge M A,
      z (edgeEndpoint Nf _ e.1 true) = z (edgeEndpoint Nf _ e.1 false)) (x : PhiChart M A c) :
    phiDescendedValues M A c z hz (CategoryTheory.ConnectedComponents.mk (.inl x)) = z x.1 := rfl

/-- Γの面の全mapped辺出現は、原始二端点閉条件により同じ負辺値を持つ。 -/
theorem gammaFace_edge_value (e : Nc.EdgeInTargetSubset A)
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ f : GammaEdge M A e, z (gammaSource M A f).1 = z (gammaTarget M A f).1)
    (f : GammaEdge M A e) (k : Fin 3)
    (hk : M.edgeMap (faceEdge Nf _ f.1 k).1 = some e.1) :
    z (faceEdge Nf _ f.1 k) = z (gammaSource M A f).1 := by
  rcases f.2.2 with hl | hr
  · have hval := (hz f).symm
    rw [gammaTarget_val_of_left M A f hl.1] at hval
    fin_cases k
    · cases hl.1.symm.trans hk
    · rw [gammaSource_val]; rfl
    · exact hval
  · have hval := (hz f).symm
    rw [gammaTarget_val_of_right M A f hr.1] at hval
    fin_cases k
    · exact hval
    · rw [gammaSource_val]; rfl
    · cases hr.2.2.symm.trans hk

/-- Γの各原始セルの値。混在面は同じ負辺出現で評価する。 -/
def gammaCellValue (e : Nc.EdgeInTargetSubset A)
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) : GammaInc M A e → ℚ
  | .inl v => z v.1
  | .inr f => z (gammaSource M A f).1

/-- Γ頂点の値は元の細辺値。 -/
@[simp] theorem gammaCellValue_vertex (e : Nc.EdgeInTargetSubset A)
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) (v : GammaVertex M A e) :
    gammaCellValue M A e z (.inl v) = z v.1 := rfl

/-- 原始二端点閉条件を全Γ incidenceへ放電する。 -/
theorem gammaCellValue_invariant (e : Nc.EdgeInTargetSubset A)
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ f : GammaEdge M A e, z (gammaSource M A f).1 = z (gammaTarget M A f).1)
    {i j : GammaInc M A e} (g : i ⟶ j) :
    gammaCellValue M A e z i = gammaCellValue M A e z j := by
  rcases i with v | f <;> rcases j with w | t
  · exact congrArg z (incHom_edge_edge_target _ _ g.hom).symm
  · rcases v with ⟨v, hv⟩
    cases g.hom with
    | edgeFace _ _ k hh =>
      change z v = z (gammaSource M A t).1
      change v = faceEdge Nf _ t.1 k at hh
      rw [hh]
      exact gammaFace_edge_value M A e z hz t k (by rw [← hh]; exact hv)
  · cases g.hom
  · have ht := (incHom_target_of_face _ g.hom |> Inc.face.inj).symm
    have hft : f = t := Subtype.ext ht
    rw [hft]

/-- 原始閉条件から全Γ成分上の値を生成する。 -/
def gammaDescendedValues (e : Nc.EdgeInTargetSubset A)
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ f : GammaEdge M A e, z (gammaSource M A f).1 = z (gammaTarget M A f).1) :
    CategoryTheory.ConnectedComponents (GammaInc M A e) → ℚ :=
  componentFunction (gammaCellValue M A e z) (gammaCellValue_invariant M A e z hz)

/-- Γへ降ろした値は全原始mapped辺で元の値を返す。 -/
@[simp] theorem gammaDescendedValues_vertex (e : Nc.EdgeInTargetSubset A)
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : ∀ f : GammaEdge M A e, z (gammaSource M A f).1 = z (gammaTarget M A f).1)
    (v : GammaVertex M A e) :
    gammaDescendedValues M A e z hz (CategoryTheory.ConnectedComponents.mk (.inl v)) = z v.1 := rfl

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.componentFunction
#print axioms AAT.AG.AtlasCoefficientFiber.componentFunction_mk
#print axioms AAT.AG.AtlasCoefficientFiber.phiEdgeVertical
#print axioms AAT.AG.AtlasCoefficientFiber.phiEdgeVertical_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiFaceVertical
#print axioms AAT.AG.AtlasCoefficientFiber.phiFaceVertical_val
#print axioms AAT.AG.AtlasCoefficientFiber.verticalFace_vertex_values
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellValue
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellValue_chart
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellValue_edge
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellValue_face
#print axioms AAT.AG.AtlasCoefficientFiber.phiCellValue_invariant
#print axioms AAT.AG.AtlasCoefficientFiber.phiDescendedValues
#print axioms AAT.AG.AtlasCoefficientFiber.phiDescendedValues_chart
#print axioms AAT.AG.AtlasCoefficientFiber.gammaFace_edge_value
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellValue
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellValue_vertex
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCellValue_invariant
#print axioms AAT.AG.AtlasCoefficientFiber.gammaDescendedValues
#print axioms AAT.AG.AtlasCoefficientFiber.gammaDescendedValues_vertex
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
