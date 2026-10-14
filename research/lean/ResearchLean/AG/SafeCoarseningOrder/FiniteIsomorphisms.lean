import ResearchLean.AG.SafeCoarseningOrder.IsomorphismActionInstances
import Mathlib.Data.Fintype.Perm
/-!
# 原始同型の全有限表

S/T/Vの全単射表をすべて生成し、q・有向辺・支持台の保存検査を通る表から全原始同型を得る。
自己同型をchart置換だけに限定せず、全S/T/Vを独立に検査する。

## Implementation notes

mathlibの有限Equiv一覧の積をfilterする。保存条件を検査してからPrimitiveIsoの全fieldを生成する。
H¹同型や安全性によるfilterは用いない。元同型の三全単射表を戻すことで完全性を証明し、
特定の生成元だけを列挙する方法は全Autを覆わないため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
variable {S T V S' T' V' : Type}
variable (M : PrimitiveInput S T V) (N : PrimitiveInput S' T' V')
/-- 元source/target/chartの独立な三全単射表。 -/
abbrev IsoTable := (S ≃ S') × (T ≃ T') × (V ≃ V')
/-- 三全単射表が元q・有向辺・台を保つ条件。 -/
def isoTableOK (p : IsoTable (S := S) (T := T) (V := V) (S' := S') (T' := T') (V' := V')) : Prop :=
  (∀ s, N.read (p.1 s) = p.2.1 (M.read s)) ∧
  (∀ v w, M.edge v w ↔ N.edge (p.2.2 v) (p.2.2 w)) ∧
  (∀ v t, t ∈ M.support v ↔ p.2.1 t ∈ N.support (p.2.2 v))
/-- 原始保存検査の公開特徴づけ。 -/
theorem isoTableOK_iff (p : IsoTable (S := S) (T := T) (V := V) (S' := S') (T' := T') (V' := V')) :
    isoTableOK M N p ↔ (∀ s, N.read (p.1 s) = p.2.1 (M.read s)) ∧
      (∀ v w, M.edge v w ↔ N.edge (p.2.2 v) (p.2.2 w)) ∧
      (∀ v t, t ∈ M.support v ↔ p.2.1 t ∈ N.support (p.2.2 v)) := Iff.rfl
/-- 全検査を通る表から原始同型の全fieldを生成。 -/
def fromIsoTable (p : IsoTable (S := S) (T := T) (V := V) (S' := S') (T' := T') (V' := V'))
    (h : isoTableOK M N p) : PrimitiveIso M N where
  source := p.1
  target := p.2.1
  chart := p.2.2
  read_comm := h.1
  edge_iff := h.2.1
  support_iff := h.2.2
/-- 表から生成した原始同型の元source評価。 -/
@[simp] theorem fromIsoTable_source
    (p : IsoTable (S := S) (T := T) (V := V) (S' := S') (T' := T') (V' := V'))
    (h : isoTableOK M N p) : (fromIsoTable M N p h).source = p.1 := rfl
/-- 表から生成した原始同型の元target評価。 -/
@[simp] theorem fromIsoTable_target
    (p : IsoTable (S := S) (T := T) (V := V) (S' := S') (T' := T') (V' := V'))
    (h : isoTableOK M N p) : (fromIsoTable M N p h).target = p.2.1 := rfl
/-- 表から生成した原始同型の元chart評価。 -/
@[simp] theorem fromIsoTable_chart
    (p : IsoTable (S := S) (T := T) (V := V) (S' := S') (T' := T') (V' := V'))
    (h : isoTableOK M N p) : (fromIsoTable M N p h).chart = p.2.2 := rfl
variable [Fintype S] [Fintype T] [Fintype V] [Fintype S'] [Fintype T'] [Fintype V']
/-- 全三全単射表から原始保存条件を通る全同型を列挙する。 -/
def allPrimitiveIsos : Finset (PrimitiveIso M N) := by
  classical
  exact ((Finset.univ : Finset (IsoTable (S := S) (T := T) (V := V)
    (S' := S') (T' := T') (V' := V'))).filter (isoTableOK M N)).attach.image
      (fun p => fromIsoTable M N p.1 (Finset.mem_filter.mp p.2).2)
/-- 任意の原始同型は全有限表一覧に現れる。 -/
theorem mem_allPrimitiveIsos (a : PrimitiveIso M N) : a ∈ allPrimitiveIsos M N := by
  classical
  let p : IsoTable (S := S) (T := T) (V := V) (S' := S') (T' := T') (V' := V') :=
    (a.source,a.target,a.chart)
  have hp : isoTableOK M N p := ⟨a.read_comm,a.edge_iff,a.support_iff⟩
  have hm : p ∈ (Finset.univ : Finset (IsoTable (S := S) (T := T) (V := V)
      (S' := S') (T' := T') (V' := V'))).filter (isoTableOK M N) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  apply Finset.mem_image.mpr
  refine ⟨⟨p,hm⟩,Finset.mem_attach _ _,?_⟩
  apply PrimitiveIso.ext <;> rfl
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
