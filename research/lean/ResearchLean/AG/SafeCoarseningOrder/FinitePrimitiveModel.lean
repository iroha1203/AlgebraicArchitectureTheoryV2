import ResearchLean.AG.SafeCoarseningOrder.SafeIsomorphism
import Mathlib.CategoryTheory.Groupoid

/-!
# 全非空有限原始入力のgroupoid

T0の原始集合と有限・非空instanceを束ね、全S/T/V原始同型を射とするgroupoidを作る。
対象を特定の型名・chart置換・自己同型軌道に制限しない。

## Implementation notes

集合型をdataとして保持し、有限符号化による任意の代表選択を要求しない。
射は既存PrimitiveIsoそのものであり、q/有向辺/支持の保存だけを条件にする。
圏と逆の法則は全原始同型recordのextから生成し、H¹同型や安全性を射のfieldに追加しない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.SafeCoarseningOrder
/-- T0全体の入力。有限・非空集合と原始表だけを保持する。 -/
structure FinitePrimitiveModel where
  /-- 原始source集合。 -/
  Source : Type
  /-- 原始target集合。 -/
  Target : Type
  /-- 原始chart集合。 -/
  Chart : Type
  /-- Sourceの有限性。 -/
  sourceFintype : Fintype Source
  /-- Targetの有限性。 -/
  targetFintype : Fintype Target
  /-- Chartの有限性。 -/
  chartFintype : Fintype Chart
  /-- Sourceの非空性。 -/
  sourceNonempty : Nonempty Source
  /-- Targetの非空性。 -/
  targetNonempty : Nonempty Target
  /-- Chartの非空性。 -/
  chartNonempty : Nonempty Chart
  /-- 全射q、有向非対角辺、非空台の原始入力。 -/
  input : PrimitiveInput Source Target Chart
attribute [instance] FinitePrimitiveModel.sourceFintype FinitePrimitiveModel.targetFintype
  FinitePrimitiveModel.chartFintype FinitePrimitiveModel.sourceNonempty
  FinitePrimitiveModel.targetNonempty FinitePrimitiveModel.chartNonempty
namespace FinitePrimitiveModel
/-- 任意の非空有限原始入力を全入力の束へ埋め込む。 -/
def ofInput {S T V : Type} [Fintype S] [Fintype T] [Fintype V]
    [Nonempty S] [Nonempty T] [Nonempty V] (M : PrimitiveInput S T V) : FinitePrimitiveModel where
  Source := S
  Target := T
  Chart := V
  sourceFintype := inferInstance
  targetFintype := inferInstance
  chartFintype := inferInstance
  sourceNonempty := inferInstance
  targetNonempty := inferInstance
  chartNonempty := inferInstance
  input := M
/-- 束への埋め込みは元原始入力を保持する。 -/
@[simp] theorem ofInput_input {S T V : Type} [Fintype S] [Fintype T] [Fintype V]
    [Nonempty S] [Nonempty T] [Nonempty V] (M : PrimitiveInput S T V) :
    (ofInput M).input = M := rfl
/-- 全原始同型をそのまま射とするgroupoid。全法則は元recordから生成する。 -/
instance primitiveGroupoid : CategoryTheory.Groupoid FinitePrimitiveModel where
  Hom M N := PrimitiveIso M.input N.input
  id M := PrimitiveIso.refl M.input
  comp a b := a.trans b
  id_comp := by intro M N a; apply PrimitiveIso.ext <;> rfl
  comp_id := by intro M N a; apply PrimitiveIso.ext <;> rfl
  assoc := by intro M N O P a b c; apply PrimitiveIso.ext <;> rfl
  inv a := a.symm
  inv_comp a := a.symm_trans
  comp_inv a := a.trans_symm
/-- groupoidの射型は全原始同型型と等しい。 -/
theorem hom_eq (M N : FinitePrimitiveModel) :
    (M ⟶ N) = PrimitiveIso M.input N.input := rfl
/-- groupoid恒等射は元原始恒等同型。 -/
theorem identity_eq (M : FinitePrimitiveModel) :
    (𝟙 M : M ⟶ M) = PrimitiveIso.refl M.input := rfl
/-- groupoid合成は元原始同型合成。 -/
theorem composition_eq {M N O : FinitePrimitiveModel} (a : M ⟶ N) (b : N ⟶ O) :
    a ≫ b = PrimitiveIso.trans a b := rfl
/-- 全T0入力のうち、元Mと原始同型な全入力からなる同型類。 -/
abbrev IsoClass (M : FinitePrimitiveModel) :=
  {N : FinitePrimitiveModel // Nonempty (PrimitiveIso M.input N.input)}
/-- 同型類の元の入力自身。恒等原始同型で所属を証明する。 -/
def base (M : FinitePrimitiveModel) : M.IsoClass := ⟨M,⟨PrimitiveIso.refl M.input⟩⟩
/-- 同型類の元の入力はMそのもの。 -/
@[simp] theorem base_val (M : FinitePrimitiveModel) : M.base.1 = M := rfl
/-- 同型類への全原始同型の一つを選ぶ。自然性は後に選び方独立で証明する。 -/
def isoTo {M : FinitePrimitiveModel} (N : M.IsoClass) : PrimitiveIso M.input N.1.input :=
  Classical.choice N.2
end FinitePrimitiveModel
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
