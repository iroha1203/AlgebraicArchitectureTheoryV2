import ResearchLean.AG.SafeCoarseningOrder.W1Symmetry
import ResearchLean.AG.SafeCoarseningOrder.NaturalMaximalSelection

/-! # W1 同型類全体の自然な元分割選択

## Implementation notes

元全Max/全Autから証明した固定極大を同じ一般C producerへ渡す。
全同型類・全原始同型で自然性を保持し、元入力の出力は交互分割Rそのものに戻す。
軌道選択は元分割を返す要求を満たさないため用いない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
open FinitePrimitiveModel
/-- 元指定Bool/id有向四角形を全T0入力groupoidへ束ねる。 -/
def model : FinitePrimitiveModel := ofInput input
/-- 束の元原始表を保持する基本API。 -/
@[simp] theorem model_input : model.input=input := rfl
/-- 明示された元固定極大から同型類全体の自然選択を構成する。 -/
def specifiedNaturalSelection : NaturalMaximalSelection model :=
  selectionFromFixed model (candidate ⊤ 6) (binary_maximal 6 (by decide +kernel)) alternating_fixed
/-- 明示自然選択は元入力で同じ交互分割そのものを返す。 -/
theorem specifiedNaturalSelection_base : specifiedNaturalSelection.select model.base=candidate ⊤ 6 :=
  selectionFromFixed_base model (candidate ⊤ 6) (binary_maximal 6 (by decide +kernel)) alternating_fixed
/-- 同じ有限trueから自然選択の一般producerを発火させる。 -/
def generatedNaturalSelection : NaturalMaximalSelection model :=
  selectionFromDecision model fixedMaximalDecision_true
/-- 生成自然選択も元入力で同じ固定極大を返す。 -/
theorem generatedNaturalSelection_base : generatedNaturalSelection.select model.base=candidate ⊤ 6 := by
  have hh := selection_fixed model generatedNaturalSelection
  exact (fixed_maximal_iff _).mp hh
/-- W1同型類の全入力と全同型に自然な元極大選択が実在する。 -/
theorem natural_selection_exists : Nonempty (NaturalMaximalSelection model) := ⟨generatedNaturalSelection⟩
/-- 同じ固定Rの輸送は同型の選び方に依存しない。 -/
theorem transport_choice_independent (N : FinitePrimitiveModel)
    (a b : PrimitiveIso input N.input) :
    a.coarseningOrderIso (candidate ⊤ 6)=b.coarseningOrderIso (candidate ⊤ 6) :=
  transport_independent (M := model) (N := N) (candidate ⊤ 6) alternating_fixed a b
end AAT.AG.SafeCoarseningOrder.W1

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
