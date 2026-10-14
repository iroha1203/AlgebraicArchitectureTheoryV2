import ResearchLean.AG.SafeCoarseningOrder.UniformDecisions

/-!
# 固定極大有限判定と自然選択の原始正負発火

W0の全固定極大表は元topだけで、有限正出力と同型類全体の自然選択を生成する。
三角形は全固定点を排除し、有限負出力と自然選択不存在を同じ原始入力で発火させる。

## Implementation notes

全一覧の所属必要十分と受理済み最大元/原始回転を使用する。
producerの型があるだけで発火とせず、同じ入力で成立・不成立と出力の再検証を示す。
全一様主張の負の結果はUniformDecisionsの原始証拠へ接続し、W1–W3の指定評価は後続する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open FinitePrimitiveModel
open scoped Classical
/-- 原始同型表の保存述語は、W0の元恒等三表で成立する。 -/
theorem w0_identity_isoTableOK : isoTableOK w0 w0
    (Equiv.refl Unit,Equiv.refl Unit,Equiv.refl Bool) :=
  ⟨fun _ => rfl,fun _ _ => Iff.rfl,fun _ _ => Iff.rfl⟩
/-- 同じ三角形を辺なし表へ送る元三全単射表は保存検査を通らない。 -/
theorem triangle_edgeless_isoTable_not_ok
    (p : IsoTable (S := Unit) (T := Unit) (V := Fin 3)
      (S' := Unit) (T' := Unit) (V' := Fin 3)) : ¬ isoTableOK Triangle.input triangleEdgeless p :=
  fun h => triangle_not_iso_edgeless ⟨fromIsoTable Triangle.input triangleEdgeless p h⟩
/-- W0の全固定極大表は、元の最大全関係だけ。 -/
theorem w0_fixedMaximalCoarsenings : w0.fixedMaximalCoarsenings = {⊤} := by
  apply Finset.ext; intro R
  rw [w0.mem_fixedMaximalCoarsenings,Finset.mem_singleton]
  constructor
  · intro h
    exact le_antisymm le_top (h.1.2 (w0_safe ⊤) le_top)
  · rintro rfl
    exact ⟨w0_top_maximal,w0_top_fixed⟩
/-- W0の原始有限固定極大判定はtrue。 -/
theorem w0_fixedMaximalDecision_true : w0.fixedMaximalDecision = true := by
  apply w0.fixedMaximalDecision_eq_true.mpr
  rw [w0_fixedMaximalCoarsenings]
  exact Finset.singleton_nonempty _
/-- 指定W0の元topと全固定極大証拠を明示出力する。 -/
def w0SpecifiedFixedOutput : w0.FixedMaximalWitness := ⟨⊤,w0_top_maximal,w0_top_fixed⟩
/-- 同じ原始trueから一般の正有限producerを発火させる。 -/
def w0GeneratedFixedOutput : w0.FixedMaximalWitness := w0.fixedMaximalWitness w0_fixedMaximalDecision_true
/-- W0の一般正出力は同じ全固定極大表に所属する。 -/
theorem w0GeneratedFixedOutput_mem : w0GeneratedFixedOutput.coarsening ∈ w0.fixedMaximalCoarsenings :=
  w0GeneratedFixedOutput.coarsening_mem w0
/-- 一般の有限正producerも元の同じtopを返す。 -/
theorem w0GeneratedFixedOutput_eq_top : w0GeneratedFixedOutput.coarsening = ⊤ := by
  have hm := w0GeneratedFixedOutput_mem
  rw [w0_fixedMaximalCoarsenings,Finset.mem_singleton] at hm
  exact hm
/-- W0の全自己同型軌道表は同じtopだけ。 -/
theorem w0_top_orbit : w0.orbit ⊤ = {⊤} := (w0.fixed_iff_orbit_singleton ⊤).mp w0_top_fixed
/-- W0のtop安定化集合は全原始自己同型表そのもの。 -/
theorem w0_top_stabilizer : w0.stabilizer ⊤ = w0.allAut := by
  apply Finset.ext; intro a
  rw [w0.mem_stabilizer]
  exact iff_of_true (w0_top_fixed a) (w0.mem_allAut a)
/-- 同じW0の正出力から同じtrueを再検証する。 -/
theorem w0GeneratedFixedOutput_decision : w0.fixedMaximalDecision = true :=
  w0GeneratedFixedOutput.decision_true w0
/-- W0には全極大移動の負証拠は存在しない。 -/
theorem w0_no_negative_fixed_output : ¬ Nonempty w0.NoFixedMaximalWitness := by
  rintro ⟨w⟩
  exact w.decision_not_true w0 w0_fixedMaximalDecision_true
/-- 三角形には固定極大正出力が存在しない。 -/
theorem triangle_no_positive_fixed_output : ¬ Nonempty Triangle.input.FixedMaximalWitness := by
  rintro ⟨w⟩
  have hh := w.decision_true Triangle.input
  rw [Triangle.fixedMaximalDecision_false] at hh
  exact Bool.false_ne_true hh
/-- 三角形の一般負producerから全極大移動を再検証する。 -/
theorem triangleGeneratedNoFixed_moves (R : Coarsening Unit (Fin 3)) (hm : Maximal Triangle.input.Safe R) :
    (Triangle.generatedNoFixedOutput.move R hm).1.coarseningOrderIso R ≠ R :=
  (Triangle.generatedNoFixedOutput.move R hm).2.2
/-- 原始W0を全T0入力束へ埋め込む。 -/
def w0Model : FinitePrimitiveModel := ofInput w0
/-- W0束の原始入力は元の同じW0。 -/
@[simp] theorem w0Model_input : w0Model.input = w0 := rfl
/-- W0同型類の全入力・全原始同型への自然極大選択を原始trueから生成する。 -/
def w0NaturalSelection : NaturalMaximalSelection w0Model := selectionFromDecision w0Model w0_fixedMaximalDecision_true
/-- W0の全同型類に対する自然選択存在は実際に成立する。 -/
theorem w0_natural_selection_exists : Nonempty (NaturalMaximalSelection w0Model) := ⟨w0NaturalSelection⟩
/-- W0の自然選択は元入力で同じtopを返す。 -/
theorem w0NaturalSelection_base : w0NaturalSelection.select w0Model.base = ⊤ := by
  have hh := (selection_fixed w0Model w0NaturalSelection).1
  exact le_antisymm le_top (hh.2 (w0_safe ⊤) le_top)
/-- W0の明示topからも同じ全同型類の自然選択を生成できる。 -/
def w0SpecifiedNaturalSelection : NaturalMaximalSelection w0Model :=
  selectionFromFixed w0Model ⊤ w0_top_maximal w0_top_fixed
/-- 明示固定元からの元入力出力は同じtopそのもの。 -/
theorem w0SpecifiedNaturalSelection_base : w0SpecifiedNaturalSelection.select w0Model.base = ⊤ :=
  selectionFromFixed_base w0Model ⊤ w0_top_maximal w0_top_fixed
/-- 三角形同型類には全原始同型に自然な極大選択が存在しない。 -/
theorem triangle_no_natural_selection : ¬ Nonempty (NaturalMaximalSelection triangleModel) := by
  intro h
  have hh := (naturalSelection_iff_decision triangleModel).mp h
  rw [triangleModel_input,Triangle.fixedMaximalDecision_false] at hh
  exact Bool.false_ne_true hh
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
