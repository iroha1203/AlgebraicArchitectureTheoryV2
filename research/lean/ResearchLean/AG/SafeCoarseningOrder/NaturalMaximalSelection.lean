import ResearchLean.AG.SafeCoarseningOrder.FinitePrimitiveModel
import ResearchLean.AG.SafeCoarseningOrder.FixedMaximalDecision

/-!
# 固定極大元と同型類全体の自然選択

全T0入力と全原始同型のgroupoidで、同型類全体への極大安全元の自然選択を定義する。
全自己同型が固定する元分割Rから輸送し、同型の選び方への独立性を証明する。

## Implementation notes

選択の出力は元分割Rであり、自己同型軌道ではない。同型類の各入力への原始同型を
一つ選ぶが、二つの選択の差は元入力の自己同型なので固定性から同じ出力になる。
辞書順の極大元をそのまま自然選択とする方法は固定性を与えないため用いない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.FinitePrimitiveModel
/-- 同型類の全入力に元分割を選び、全原始同型と整合させる。 -/
structure NaturalMaximalSelection (M : FinitePrimitiveModel) where
  /-- 同型な各入力で選ぶ元target/chart分割。 -/
  select : (N : M.IsoClass) → Coarsening N.1.Target N.1.Chart
  /-- 各出力は元安全集合の極大元。 -/
  maximal : ∀ N, Maximal N.1.input.Safe (select N)
  /-- 同型類内の全原始同型に対する自然性。 -/
  natural : ∀ N O (a : PrimitiveIso N.1.input O.1.input),
    a.coarseningOrderIso (select N) = select O
/-- 固定元の輸送はMから同じNへの原始同型の選び方に依存しない。 -/
theorem transport_independent {M N : FinitePrimitiveModel} (R : Coarsening M.Target M.Chart)
    (hf : ∀ g : PrimitiveIso M.input M.input, g.coarseningOrderIso R = R)
    (a b : PrimitiveIso M.input N.input) : a.coarseningOrderIso R = b.coarseningOrderIso R := by
  have hh := hf (a.trans b.symm)
  rw [PrimitiveIso.coarseningOrderIso_trans,PrimitiveIso.coarseningOrderIso_symm] at hh
  have ht := congrArg b.coarseningOrderIso hh
  simpa only [OrderIso.trans_apply,OrderIso.apply_symm_apply] using ht
/-- 元固定極大分割から同型類全体の自然選択を生成。 -/
def selectionFromFixed (M : FinitePrimitiveModel) (R : Coarsening M.Target M.Chart)
    (hm : Maximal M.input.Safe R)
    (hf : ∀ g : PrimitiveIso M.input M.input, g.coarseningOrderIso R = R) :
    NaturalMaximalSelection M where
  select N := (isoTo N).coarseningOrderIso R
  maximal N := (isoTo N).maximal_forward hm
  natural N O a := by
    have hh := transport_independent R hf ((isoTo N).trans a) (isoTo O)
    simpa only [PrimitiveIso.coarseningOrderIso_trans,OrderIso.trans_apply] using hh
/-- 固定元から生成した選択の各入力出力は同じ原始同型によるRの輸送。 -/
theorem selectionFromFixed_select (M : FinitePrimitiveModel) (R : Coarsening M.Target M.Chart)
    (hm : Maximal M.input.Safe R)
    (hf : ∀ g : PrimitiveIso M.input M.input, g.coarseningOrderIso R = R) (N : M.IsoClass) :
    (selectionFromFixed M R hm hf).select N = (isoTo N).coarseningOrderIso R := rfl
/-- 自然選択は元入力で全自己同型が固定する極大分割を返す。 -/
theorem selection_fixed (M : FinitePrimitiveModel) (s : NaturalMaximalSelection M) :
    Maximal M.input.Safe (s.select M.base) ∧
      ∀ g : PrimitiveIso M.input M.input, g.coarseningOrderIso (s.select M.base) = s.select M.base :=
  ⟨s.maximal M.base,fun g => s.natural M.base M.base g⟩
/-- 固定元から生成した選択の元入力出力は同じRそのもの。 -/
theorem selectionFromFixed_base (M : FinitePrimitiveModel) (R : Coarsening M.Target M.Chart)
    (hm : Maximal M.input.Safe R)
    (hf : ∀ g : PrimitiveIso M.input M.input, g.coarseningOrderIso R = R) :
    (selectionFromFixed M R hm hf).select M.base = R := hf (isoTo M.base)
/-- 同型類全体の全同型に自然な極大分割選択と全固定極大表非空は必要十分。 -/
theorem naturalSelection_iff_fixed (M : FinitePrimitiveModel) :
    Nonempty (NaturalMaximalSelection M) ↔ M.input.fixedMaximalCoarsenings.Nonempty := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.select M.base,(M.input.mem_fixedMaximalCoarsenings _).mpr (selection_fixed M s)⟩
  · rintro ⟨R,hR⟩
    obtain ⟨hm,hf⟩ := (M.input.mem_fixedMaximalCoarsenings R).mp hR
    exact ⟨selectionFromFixed M R hm hf⟩
/-- 原始表からの固定極大有限Boolは自然選択存在を必要十分に決定する。 -/
theorem naturalSelection_iff_decision (M : FinitePrimitiveModel) :
    Nonempty (NaturalMaximalSelection M) ↔ M.input.fixedMaximalDecision = true :=
  (naturalSelection_iff_fixed M).trans M.input.fixedMaximalDecision_eq_true.symm
/-- 正の原始有限判定から同型類全体の自然選択を出力する。 -/
def selectionFromDecision (M : FinitePrimitiveModel) (h : M.input.fixedMaximalDecision = true) :
    NaturalMaximalSelection M :=
  let w := M.input.fixedMaximalWitness h
  selectionFromFixed M w.coarsening w.maximal w.fixed
/-- 有限正判定からの自然選択は元入力で同じ有限producerの分割を返す。 -/
theorem selectionFromDecision_base (M : FinitePrimitiveModel) (h : M.input.fixedMaximalDecision = true) :
    (selectionFromDecision M h).select M.base = (M.input.fixedMaximalWitness h).coarsening :=
  selectionFromFixed_base M (M.input.fixedMaximalWitness h).coarsening
    (M.input.fixedMaximalWitness h).maximal (M.input.fixedMaximalWitness h).fixed
end AAT.AG.SafeCoarseningOrder.FinitePrimitiveModel
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
