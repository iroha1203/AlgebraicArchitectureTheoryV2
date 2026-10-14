import ResearchLean.AG.SafeCoarseningOrder.Factorization

/-!
# G-137 の原始入力同型

A の二段商と恒等商の同定に用いる、元 S/T/V の全単射と q/有向辺/台の保存。
C の同型輸送もこの同じ型を用いる。

## Implementation notes

同型条件は原始表の保存だけとし、cochain/H¹同型や安全性を field に入れない。
辺の全単射を有向端点対と辺保存から誘導し、重複のない元セルへ戻す。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
variable {S T V S' T' V' S'' T'' V'' : Type}

/-- T0 入力同型。S/T/Vを同時に再添字づけし原始表を保存する。 -/
structure PrimitiveIso (M : PrimitiveInput S T V) (N : PrimitiveInput S' T' V') where
  /-- Source全単射。 -/
  source : S ≃ S'
  /-- Target全単射。 -/
  target : T ≃ T'
  /-- Chart全単射。 -/
  chart : V ≃ V'
  /-- Readingの可換性。 -/
  read_comm : ∀ s, N.read (source s) = target (M.read s)
  /-- 有向辺保存の両方向。 -/
  edge_iff : ∀ v w, M.edge v w ↔ N.edge (chart v) (chart w)
  /-- 支持点保存の両方向。 -/
  support_iff : ∀ v t, t ∈ M.support v ↔ target t ∈ N.support (chart v)

namespace PrimitiveIso
variable {M : PrimitiveInput S T V} {N : PrimitiveInput S' T' V'}
  {O : PrimitiveInput S'' T'' V''}

/-- 原始表の恒等同型。 -/
def refl (M : PrimitiveInput S T V) : PrimitiveIso M M where
  source := Equiv.refl S
  target := Equiv.refl T
  chart := Equiv.refl V
  read_comm _ := rfl
  edge_iff _ _ := Iff.rfl
  support_iff _ _ := Iff.rfl

/-- 原始同型の合成。保存条件は同じ元表で合成する。 -/
def trans (a : PrimitiveIso M N) (b : PrimitiveIso N O) : PrimitiveIso M O where
  source := a.source.trans b.source
  target := a.target.trans b.target
  chart := a.chart.trans b.chart
  read_comm s := by rw [Equiv.trans_apply, b.read_comm, a.read_comm]; rfl
  edge_iff v w := (a.edge_iff v w).trans (b.edge_iff (a.chart v) (a.chart w))
  support_iff v t := (a.support_iff v t).trans (b.support_iff (a.chart v) (a.target t))

/-- 原始同型の逆。全単射と原始保存の両方向から生成する。 -/
def symm (a : PrimitiveIso M N) : PrimitiveIso N M where
  source := a.source.symm
  target := a.target.symm
  chart := a.chart.symm
  read_comm s := by
    apply a.target.injective
    simpa only [Equiv.apply_symm_apply] using (a.read_comm (a.source.symm s)).symm
  edge_iff v w := by
    simpa only [Equiv.apply_symm_apply] using
      (a.edge_iff (a.chart.symm v) (a.chart.symm w)).symm
  support_iff v t := by
    simpa only [Equiv.apply_symm_apply] using
      (a.support_iff (a.chart.symm v) (a.target.symm t)).symm

/-- 有向辺の全単射は chart の全単射から誘導する。 -/
def edgeEquiv (a : PrimitiveIso M N) : M.Edge ≃ N.Edge where
  toFun e := ⟨(a.chart e.1.1, a.chart e.1.2), (a.edge_iff _ _).mp e.2⟩
  invFun e := ⟨(a.chart.symm e.1.1, a.chart.symm e.1.2),
    a.symm.edge_iff _ _ |>.mp e.2⟩
  left_inv e := by apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  right_inv e := by apply Subtype.ext; simp only [Equiv.apply_symm_apply]

/-- 誘導された辺同型の左端は同じ chart 同型で輸送される。 -/
@[simp] theorem edgeEquiv_left (a : PrimitiveIso M N) (e : M.Edge) :
    (a.edgeEquiv e).1.1 = a.chart e.1.1 := rfl

/-- 誘導された辺同型の右端も同じ chart 同型で輸送される。 -/
@[simp] theorem edgeEquiv_right (a : PrimitiveIso M N) (e : M.Edge) :
    (a.edgeEquiv e).1.2 = a.chart e.1.2 := rfl

/-- 原始同型 record の全 data 成分を含む ext API。 -/
@[ext] theorem ext {a b : PrimitiveIso M N}
    (hs : a.source = b.source) (ht : a.target = b.target) (hv : a.chart = b.chart) : a = b := by
  cases a
  cases b
  cases hs
  cases ht
  cases hv
  rfl

/-- 逆同型との合成は全 record で恒等になる。 -/
@[simp] theorem trans_symm (a : PrimitiveIso M N) : a.trans a.symm = refl M := by
  apply ext <;> ext x <;> exact Equiv.symm_apply_apply _ x

/-- 逆向きの両側逆も全 record で示す。 -/
@[simp] theorem symm_trans (a : PrimitiveIso M N) : a.symm.trans a = refl N := by
  apply ext <;> ext x <;> exact Equiv.apply_symm_apply _ x

end PrimitiveIso
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
