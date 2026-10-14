import ResearchLean.AG.ResolutionInvariance.SupportedNerveMorphism
import Mathlib.Data.Setoid.Basic
import Formal.Util.AssertStandardAxioms

/-!
# G-137 の有限原始入力と全分割対

T0 の全射 reading、有向単純辺、非空 chart 台から面なし nerve を生成する。
分割対は mathlib の `Setoid` の積であり、関係包含の complete lattice を用いる。

## Implementation notes

辺は原始順序対の subtype とする。同じ向きの重複を持たず、逆向きは別セルとなる。
有限性・非空性は入力集合の instance、対角除外と台の非空性は T0 の入力条件である。
安全性や比較同型を入力 field に置かない。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance Cohomology

variable (S T V : Type)

/-- T0 の原始表。有限集合の instance は型の引数から得る。 -/
structure PrimitiveInput where
  /-- 元の reading。 -/
  read : S → T
  /-- T0 の全射条件。 -/
  read_surjective : Function.Surjective read
  /-- 有向辺の存在表。 -/
  edge : V → V → Prop
  /-- T0 の対角除外。 -/
  edge_ne : ∀ v w, edge v w → v ≠ w
  /-- 元 chart の台。 -/
  support : V → Set T
  /-- T0 の chart 台の非空性。 -/
  support_nonempty : ∀ v, (support v).Nonempty

/-- T0 の全粗化。両分割は独立に量化する。 -/
abbrev Coarsening := Setoid T × Setoid V

namespace PrimitiveInput
variable {S T V}
variable (M : PrimitiveInput S T V)

/-- 原始全射から既存 reading を生成する。 -/
def reading : Reading S := ⟨T, M.read, M.read_surjective⟩

/-- 原始有向辺セル。同方向の多重辺を入力しない。 -/
abbrev Edge := {e : V × V // M.edge e.1 e.2}

/-- 原始有向単純 nerve。面型は空であり、辺存在命題は True。 -/
def nerve : CoverNerve where
  Chart := V
  EdgeComponent := M.Edge
  FaceComponent := Empty
  edgeLeft e := e.1.1
  edgeRight e := e.1.2
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent _ := True
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds _ := trivial
  faceTripleOverlapComponent_holds f := f.elim

variable [Fintype V]

/-- T0 の K1 支持 nerve への接続。面端点条件は空型から放電する。 -/
def supported : TargetSupportedNerve M.reading where
  nerve := M.nerve
  chartFintype := by change Fintype V; infer_instance
  edgeFintype := by classical change Fintype M.Edge; infer_instance
  faceFintype := by change Fintype Empty; infer_instance
  chartSupport := M.support
  chartSupport_nonempty := M.support_nonempty
  faceEdge0_left f := f.elim
  faceEdge0_right f := f.elim
  faceEdge1_right f := f.elim

/-- 原始 K1 辺台の公開評価式。 -/
@[simp] theorem mem_edgeSupport (e : M.Edge) (t : T) :
    t ∈ M.supported.edgeSupport e ↔ t ∈ M.support e.1.1 ∧ t ∈ M.support e.1.2 :=
  Iff.rfl

omit [Fintype V] in
/-- 原始辺セルは必ず異なる両端を持つ。 -/
theorem edge_endpoints_ne (e : M.Edge) : e.1.1 ≠ e.1.2 := M.edge_ne _ _ e.2

end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
