import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationGeometry
import ResearchLean.AG.AtlasDefectComposition.FullSupportIncidence
import Mathlib.Data.Fin.VecNotation
import Formal.Util.AssertStandardAxioms

/-!
# W2aとW3の連結した原始面

## Implementation notes

セル名v,w,uとe,a,b,kをFinで符号化し、chart台だけをパラメータにする。
W3は全台、W2aはwだけ片台として同じ原始セル表を共有する。
期待微分行列や相同型を入力する方式は採らず、supported nerveを先に作る。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness
open CanonicalResolution ResolutionInvariance Cohomology AtlasDefectComposition

/-- W2/W3の二点Sourceをそのまま読む全射reading。 -/
abbrev q : Reading Bool where
  Target := Bool
  read := id
  surjective := Function.surjective_id
/-- 一つの非定数identity Law。 -/
def laws : FiniteLawFamily Bool where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Bool
  valueDecidableEq _ := inferInstance
  eval _ := id
/-- identity readingへのadequacyを原始評価から得る。 -/
theorem adequate : laws.Adequate q := fun _ => ⟨id, fun _ => rfl⟩
/-- 同じ原始Lawの二つの評価は異なる。 -/
theorem law_nonconstant : laws.eval () false ≠ laws.eval () true := Bool.false_ne_true
/-- 二ラベルはSourceの二値から発生する。 -/
def label (a : Bool) : LawValueLabel laws := LawValueLabel.ofSource laws () a
/-- 二つの発生ラベルは別物。 -/
theorem labels_distinct : label false ≠ label true := by
  intro h
  exact Bool.false_ne_true (congrArg (fun l : LawValueLabel laws => l.value) h)
/-- 全発生ラベルをBoolの二値で尽くす。 -/
def labelEquiv : LawValueLabel laws ≃ Bool where
  toFun l := l.value
  invFun := label
  left_inv l := by cases l with | mk l v h => cases l; apply LawValueLabel.ext <;> rfl
  right_inv _ := rfl
/-- Bool同定の逆は同じSource発生ラベル。 -/
@[simp] theorem labelEquiv_symm (a : Bool) : labelEquiv.symm a = label a := rfl
/-- 同じSource発生ラベルをBool値へ戻す。 -/
@[simp] theorem labelEquiv_label (a : Bool) : labelEquiv (label a) = a := rfl
/-- 3頂点v,w,u、辺e,a,b,k、面F=(e,a,b)の原始表。 -/
abbrev nerve : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 4
  FaceComponent := Unit
  edgeLeft := ![0,0,1,0]
  edgeRight := ![1,2,2,0]
  faceEdge0 _ := 0
  faceEdge1 _ := 1
  faceEdge2 _ := 2
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent _ := True
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds _ := trivial
/-- chart台からK1と実微分を生成する同じセル表。 -/
abbrev supported (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) : TargetSupportedNerve q where
  nerve := nerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := S
  chartSupport_nonempty := hS
  faceEdge0_left _ := rfl
  faceEdge0_right _ := rfl
  faceEdge1_right _ := rfl
/-- 原始各辺の始点の公開評価。 -/
@[simp] theorem edgeLeft (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) (e : Fin 4) :
    (supported S hS).nerve.edgeLeft e = ![0,0,1,0] e := rfl
/-- 原始各辺の終点の公開評価。 -/
@[simp] theorem edgeRight (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) (e : Fin 4) :
    (supported S hS).nerve.edgeRight e = ![1,2,2,0] e := rfl
/-- 原始Fの第0辺。 -/
@[simp] theorem faceEdge0 (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) (f : Unit) :
    (supported S hS).nerve.faceEdge0 f = 0 := rfl
/-- 原始Fの第1辺。 -/
@[simp] theorem faceEdge1 (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) (f : Unit) :
    (supported S hS).nerve.faceEdge1 f = 1 := rfl
/-- 原始Fの第2辺。 -/
@[simp] theorem faceEdge2 (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) (f : Unit) :
    (supported S hS).nerve.faceEdge2 f = 2 := rfl
/-- chart台の公開評価。 -/
@[simp] theorem chartSupport (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) (v : Fin 3) :
    (supported S hS).chartSupport v = S v := rfl
/-- loop kはvを始終点とし、e,aと同じ頂点に接続する。 -/
theorem loop_attached (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) :
    (supported S hS).nerve.edgeLeft 3 = (supported S hS).nerve.edgeRight 3 ∧
    (supported S hS).nerve.edgeLeft 3 = (supported S hS).nerve.edgeLeft 0 ∧
    (supported S hS).nerve.edgeLeft 3 = (supported S hS).nerve.edgeLeft 1 := ⟨rfl,rfl,rfl⟩
/-- 原始グラフのv,w,uは辺e,aで同じ連結成分にある具体道。 -/
theorem connecting_edges (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) :
    (supported S hS).nerve.edgeLeft 0 = 0 ∧ (supported S hS).nerve.edgeRight 0 = 1 ∧
    (supported S hS).nerve.edgeLeft 1 = 0 ∧ (supported S hS).nerve.edgeRight 1 = 2 := ⟨rfl,rfl,rfl,rfl⟩
/-- 全頂点がv自身、またはvを始点とする原始辺の終点である。 -/
theorem every_vertex_connected (S : Fin 3 → Set Bool) (hS : ∀ v, (S v).Nonempty) (v : Fin 3) :
    v = 0 ∨ ∃ e : Fin 4, (supported S hS).nerve.edgeLeft e = 0 ∧
      (supported S hS).nerve.edgeRight e = v := by
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr ⟨0,rfl,rfl⟩
  · exact Or.inr ⟨1,rfl,rfl⟩

end AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness
