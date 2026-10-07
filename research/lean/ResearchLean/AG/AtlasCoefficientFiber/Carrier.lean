import ResearchLean.AG.AtlasCoefficientFiber.Incidence

/-!
# G-135 A：原始退化パターンとcarrier

## Implementation notes

carrierの対象値を、Optionセル像と原始符号付き零和から定める。
混在面を垂直面と区別し、既存subsetの支持輸送を再利用する。
セルごとにcarrier対象を別の入力として受け取る案では、その出所をMから
証明する義務がfieldへ移るため採らず、Option像から対象値を直接計算する。
退化面を一律にchartへ送る案は混在面の粗辺carrierを失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision CategoryTheory
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}

/-- 原始退化面は、垂直型または二つの混在型のいずれかである。 -/
theorem degenerate_face_cases (M : IncidenceSupportedComparison qc qf h Nc Nf)
    (f : Nf.nerve.FaceComponent) (hf : M.faceMap f = none) :
    (M.edgeMap (Nf.nerve.faceEdge0 f) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f) = none ∧
      M.edgeMap (Nf.nerve.faceEdge2 f) = none) ∨
    (∃ e, M.edgeMap (Nf.nerve.faceEdge0 f) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f) = some e ∧
      M.edgeMap (Nf.nerve.faceEdge2 f) = some e) ∨
    (∃ e, M.edgeMap (Nf.nerve.faceEdge0 f) = some e ∧
      M.edgeMap (Nf.nerve.faceEdge1 f) = some e ∧
      M.edgeMap (Nf.nerve.faceEdge2 f) = none) := by
  rcases (optionCell_incidence_iff _ _ _).mp (M.face_none_incidence f hf) with h0 | h2
  · cases he : M.edgeMap (Nf.nerve.faceEdge1 f) with
    | none => exact Or.inl ⟨h0.1, rfl, h0.2.symm.trans he⟩
    | some e => exact Or.inr (Or.inl ⟨e, h0.1, rfl, h0.2.symm.trans he⟩)
  · cases he : M.edgeMap (Nf.nerve.faceEdge0 f) with
    | none => exact Or.inl ⟨rfl, h2.2.symm.trans he, h2.1⟩
    | some e => exact Or.inr (Or.inr ⟨e, rfl, h2.2.symm.trans he, h2.1⟩)

namespace Carrier
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (Ac : Set qc.Target) (Af : Set qf.Target)
variable (hs : ∀ t, t ∈ Af → comparisonFactor qc qf h t ∈ Ac)

/-- 支持輸送によるchartのcarrier。 -/
def chart (c : Nf.ChartInTargetSubset Af) : Nc.ChartInTargetSubset Ac :=
  M.targetSubsetChartMap Ac Af hs c

/-- 辺のcarrierはmapped辺、または退化辺のchartである。 -/
def edge (e : Nf.EdgeInTargetSubset Af) : Inc Nc Ac :=
  match he : M.edgeMap e.1 with
  | none => .chart (chart M Ac Af hs (Nf.targetSubsetEdgeLeft Af e))
  | some a => .edge (M.targetSubsetEdgeMap Ac Af hs e a he)

/-- 面のcarrierはmapped面、混在面のmapped辺、または垂直面のchartである。 -/
def face (f : Nf.FaceInTargetSubset Af) : Inc Nc Ac :=
  match hf : M.faceMap f.1 with
  | some a => .face (M.targetSubsetFaceMap Ac Af hs f a hf)
  | none =>
    match h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) with
    | some e => .edge (M.targetSubsetEdgeMap Ac Af hs (Nf.targetSubsetFaceEdge0 Af f) e h0)
    | none =>
      match h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) with
      | some e => .edge (M.targetSubsetEdgeMap Ac Af hs (Nf.targetSubsetFaceEdge1 Af f) e h1)
      | none => .chart (chart M Ac Af hs
          (Nf.targetSubsetEdgeLeft Af (Nf.targetSubsetFaceEdge0 Af f)))

/-- 全セルのcarrier対象値。 -/
def obj : Inc Nf Af → Inc Nc Ac
  | .chart c => .chart (chart M Ac Af hs c)
  | .edge e => edge M Ac Af hs e
  | .face f => face M Ac Af hs f

/-- mapped辺のcarrierは同じ支持輸送辺である。 -/
@[simp] theorem edge_of_some (e : Nf.EdgeInTargetSubset Af) (a : Nc.nerve.EdgeComponent)
    (he : M.edgeMap e.1 = some a) :
    edge M Ac Af hs e = .edge (M.targetSubsetEdgeMap Ac Af hs e a he) := by
  unfold edge
  split <;> simp_all
  apply Subtype.ext
  rename_i a' ha
  exact Option.some.inj (ha.symm.trans he)

/-- 退化辺のcarrierは左端点のchartである。 -/
@[simp] theorem edge_of_none (e : Nf.EdgeInTargetSubset Af) (he : M.edgeMap e.1 = none) :
    edge M Ac Af hs e = .chart (chart M Ac Af hs (Nf.targetSubsetEdgeLeft Af e)) := by
  unfold edge
  split <;> simp_all

/-- mapped面のcarrierは同じ支持輸送面である。 -/
@[simp] theorem face_of_some (f : Nf.FaceInTargetSubset Af) (a : Nc.nerve.FaceComponent)
    (hf : M.faceMap f.1 = some a) :
    face M Ac Af hs f = .face (M.targetSubsetFaceMap Ac Af hs f a hf) := by
  unfold face
  split <;> simp_all
  apply Subtype.ext
  rename_i a' ha
  exact Option.some.inj (ha.symm.trans hf)

/-- 垂直面のcarrierの公開計算式。 -/
theorem face_of_vertical (f : Nf.FaceInTargetSubset Af) (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = none) :
    face M Ac Af hs f = .chart (chart M Ac Af hs
      (Nf.targetSubsetEdgeLeft Af (Nf.targetSubsetFaceEdge0 Af f))) := by
  unfold face
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- 左辺が退化する混在面のcarrierの公開計算式。 -/
theorem face_of_mixed_left (f : Nf.FaceInTargetSubset Af) (hf : M.faceMap f.1 = none)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = none) (e : Nc.nerve.EdgeComponent)
    (h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some e) :
    face M Ac Af hs f = .edge (M.targetSubsetEdgeMap Ac Af hs
      (Nf.targetSubsetFaceEdge1 Af f) e h1) := by
  unfold face
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  apply Subtype.ext
  rename_i e' he
  exact Option.some.inj (he.symm.trans h1)

/-- 第三辺が退化する混在面のcarrierの公開計算式。 -/
theorem face_of_mixed_right (f : Nf.FaceInTargetSubset Af) (hf : M.faceMap f.1 = none)
    (e : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1) = some e) :
    face M Ac Af hs f = .edge (M.targetSubsetEdgeMap Ac Af hs
      (Nf.targetSubsetFaceEdge0 Af f) e h0) := by
  unfold face
  split <;> simp_all
  split <;> simp_all
  apply Subtype.ext
  rename_i e' he
  exact Option.some.inj (he.symm.trans h0)

/-- 支持chartの像の原始セル名。 -/
@[simp] theorem chart_val (c : Nf.ChartInTargetSubset Af) :
    (chart M Ac Af hs c).1 = M.chartMap c.1 := rfl

/-- 原始端点のcarrier incidence射。mapped辺では左右の出現を保つ。 -/
def endpointHom (e : Nf.EdgeInTargetSubset Af) (s : Bool) :
    Inc.chart (chart M Ac Af hs (edgeEndpoint Nf Af e s)) ⟶ edge M Ac Af hs e := by
  cases he : M.edgeMap e.1 with
  | none =>
    rw [edge_of_none M Ac Af hs e he]
    apply eqToHom
    apply congrArg Inc.chart
    cases s
    · rfl
    · exact (M.targetSubsetChartMap_edgeLeft_eq_right_of_none Ac Af hs e he).symm
  | some a =>
    rw [edge_of_some M Ac Af hs e a he]
    apply IncHom.chartEdge _ _ s
    cases s
    · exact M.targetSubsetChartMap_edgeLeft Ac Af hs e a he
    · exact M.targetSubsetChartMap_edgeRight Ac Af hs e a he

end Carrier
end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.degenerate_face_cases
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.chart
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edge
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.face
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.obj
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edge_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.edge_of_none
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.face_of_some
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.face_of_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.face_of_mixed_left
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.face_of_mixed_right
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.chart_val
#print axioms AAT.AG.AtlasCoefficientFiber.Carrier.endpointHom
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
