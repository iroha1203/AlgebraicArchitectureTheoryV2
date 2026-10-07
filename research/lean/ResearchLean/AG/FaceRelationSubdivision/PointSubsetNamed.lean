import ResearchLean.AG.FaceRelationSubdivision.FullSupportSubset
import Formal.Util.AssertStandardAxioms

/-!
# 共通支持点を持つ singleton subset の原始名付き表

## Implementation notes

全 target 台を仮定せず、指定点が全 chart に属する証拠から K1 の全セルを選ぶ。
別ラベルが同じ選択を持つという仮定へ置き換える方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
/-- singleton subset がセルを選ぶ条件は、その同じ点の支持 membership。 -/
theorem singleton_selected_iff {T : Type u} (s : Set T) (a : T) :
    (∃ t, t∈s ∧ t∈({a} : Set T)) ↔ a∈s := by
  constructor
  · rintro ⟨t,ht,ha⟩
    have he : t=a := ha
    subst t
    exact ht
  · intro h
    exact ⟨a,h,rfl⟩
/-- 指定点から同じ選択セルを作る。 -/
def pointSelected {T I : Type u} (s : I → Set T) (a : T) (h : ∀ i, a∈s i) (i : I) :
    {i : I // ∃ t, t∈s i ∧ t∈({a} : Set T)} := ⟨i,⟨a,h i,rfl⟩⟩
/-- 共通支持点の選択はセル名を保つ。 -/
@[simp] theorem pointSelected_val {T I : Type u} (s : I → Set T) (a : T) (h : ∀ i, a∈s i) (i : I) :
    (pointSelected s a h i).val=i := rfl
/-- 全セルを選ぶ singleton cochain と原始セル関数の両逆。 -/
def pointSelectedCochain {T I : Type u} (s : I → Set T) (a : T) (h : ∀ i, a∈s i) :
    ({i : I // ∃ t, t∈s i ∧ t∈({a} : Set T)} → ℚ) ≃ₗ[ℚ] (I → ℚ) where
  toFun z i := z (pointSelected s a h i)
  invFun z i := z i.val
  left_inv z := by funext i; congr 1
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable {Source : Type u} {q : Reading Source} (N : TargetSupportedNerve q)
variable (a : q.Target) (h : ∀ v, a∈N.chartSupport v)
include h in
/-- 共通 chart 点は同じ K1 辺台に属する。 -/
theorem commonPoint_edge (e : N.nerve.EdgeComponent) : a∈N.edgeSupport e :=
  (N.mem_edgeSupport_iff e a).mpr ⟨h _,h _⟩
include h in
/-- 共通 chart 点は同じ K1 面台に属する。 -/
theorem commonPoint_face (f : N.nerve.FaceComponent) : a∈N.faceSupport f :=
  (N.mem_faceSupport_iff f a).mpr ⟨commonPoint_edge N a h _,commonPoint_edge N a h _,commonPoint_edge N a h _⟩
/-- 共通点の実 subset 複体と同じ原始名付き表の全三成分同型。 -/
def pointSubsetNamedEquiv : ThreeCochainComplex.CochainEquiv (N.targetSubsetComplex {a}) (namedComplex N) where
  e0 := pointSelectedCochain N.chartSupport a h
  e1 := pointSelectedCochain N.edgeSupport a (commonPoint_edge N a h)
  e2 := pointSelectedCochain N.faceSupport a (commonPoint_face N a h)
  comm0 z := by
    funext e
    rw [namedComplex_d0_apply]
    change (N.targetSubsetComplex {a}).d0 z (pointSelected N.edgeSupport a (commonPoint_edge N a h) e)=
      z (pointSelected N.chartSupport a h (N.nerve.edgeRight e))-
        z (pointSelected N.chartSupport a h (N.nerve.edgeLeft e))
    rw [N.targetSubsetComplex_d0_apply]
    congr 1
  comm1 z := by
    funext f
    rw [namedComplex_d1_apply]
    change (N.targetSubsetComplex {a}).d1 z (pointSelected N.faceSupport a (commonPoint_face N a h) f)=
      z (pointSelected N.edgeSupport a (commonPoint_edge N a h) (N.nerve.faceEdge0 f))-
        z (pointSelected N.edgeSupport a (commonPoint_edge N a h) (N.nerve.faceEdge1 f))+
        z (pointSelected N.edgeSupport a (commonPoint_edge N a h) (N.nerve.faceEdge2 f))
    rw [N.targetSubsetComplex_d1_apply]
    congr 1
/-- 同じ singleton 次数1同定は共通点で生成したセルを読む。 -/
@[simp] theorem pointSubsetNamedEquiv_e1 (z) (e) : (pointSubsetNamedEquiv N a h).e1 z e=
    z (pointSelected N.edgeSupport a (commonPoint_edge N a h) e) := rfl
/-- 同じ singleton 同定の逆は、元の支持セル名で cochain を読む。 -/
@[simp] theorem pointSubsetNamedEquiv_symm_e1 (z) (e : N.EdgeInTargetSubset {a}) :
    (pointSubsetNamedEquiv N a h).e1.symm z e=z e.val := rfl
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
