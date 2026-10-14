import ResearchLean.AG.SafeCoarseningOrder.NaturalMaximalSelection
import ResearchLean.AG.SafeCoarseningOrder.TriangleMaximalClassification

/-!
# 三つの全T0一様主張の確定

全非空有限原始入力について最大元、join閉性、全groupoidでの自然maximal選択を述べる。
P_J⇒P_G⇒P_Nを入力生成経路で証明し、三角形原始モデルにより各一様主張を反証する。

## Implementation notes

全T0の束を量化し、型名や同型類の代表を固定しない。最大元からの自然選択は
各入力の最大元を選び、全原始同型による最大性保存と一意性で自然性を生成する。
負の結果は元比較の安全cut/全共通上界失敗と全極大固定点排除を使う。
排中律の未評価分岐や、反証済み主張からの矛盾消去だけで相互含意を証明する方法は用いない。
P_G/P_J/P_Nは全T0の一様命題であり、このmoduleの各原始反証から満たすinstanceは存在しない。
GlobalNaturalMaximalChoiceも全極大固定点排除によって不存在である。条件付き相互含意の
producerは一般構成を示す。固定極大証拠と同型類上NaturalMaximalSelectionの成立・不成立は
W0と三角形でそれぞれ示し、全一様命題の不成立と局所の正例を区別する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.FinitePrimitiveModel
/-- 全T0入力に対し元分割を選ぶ、全原始同型に自然な極大安全元の一様選択。 -/
structure GlobalNaturalMaximalChoice where
  /-- 全入力で選ぶ元target/chart分割。 -/
  select : (M : FinitePrimitiveModel) → Coarsening M.Target M.Chart
  /-- 各入力の元安全集合における極大性。 -/
  maximal : ∀ M, Maximal M.input.Safe (select M)
  /-- 全原始同型に対する同じ元分割の自然性。 -/
  natural : ∀ M N (a : PrimitiveIso M.input N.input), a.coarseningOrderIso (select M) = select N
/-- 全非空有限原始入力に最大安全元が存在する一様主張。 -/
def P_G : Prop := ∀ M : FinitePrimitiveModel, ∃ R, IsGreatest {W | M.input.Safe W} R
/-- 全非空有限原始入力の全安全対が同じjoinで安全である一様主張。 -/
def P_J : Prop := ∀ (M : FinitePrimitiveModel) (R Q : Coarsening M.Target M.Chart),
  M.input.Safe R → M.input.Safe Q → M.input.Safe (R ⊔ Q)
/-- 全T0 groupoidでの元極大分割の自然選択が存在する一様主張。 -/
def P_N : Prop := Nonempty GlobalNaturalMaximalChoice
/-- 全最大元存在の仮定から最大性保存と一意性により自然な元分割選択を生成。 -/
def globalFromGreatest (hg : P_G) : GlobalNaturalMaximalChoice where
  select M := Classical.choose (hg M)
  maximal M := ⟨(Classical.choose_spec (hg M)).1,fun _ hW _ => (Classical.choose_spec (hg M)).2 hW⟩
  natural M N a := (a.greatest_forward (Classical.choose_spec (hg M))).unique (Classical.choose_spec (hg N))
/-- 一様最大元から生成した選択は同じ元最大元を返す。 -/
theorem globalFromGreatest_select (hg : P_G) (M : FinitePrimitiveModel) :
    (globalFromGreatest hg).select M = Classical.choose (hg M) := rfl
/-- 一様join閉性は有限非空安全posetの最大元を構成する。 -/
theorem P_J_implies_P_G (hj : P_J) : P_G := by
  intro M
  exact M.input.greatest_of_join_closed ⟨⊥,M.input.safe_bot⟩ (hj M)
/-- 一様最大元存在から全原始同型に自然な極大元選択を構成する。 -/
theorem P_G_implies_P_N (hg : P_G) : P_N := ⟨globalFromGreatest hg⟩
/-- 原始三角形を同じT0全入力束に埋め込む。 -/
def triangleModel : FinitePrimitiveModel := ofInput Triangle.input
/-- 三角形モデルの原始入力は元の同じ三角形。 -/
@[simp] theorem triangleModel_input : triangleModel.input = Triangle.input := rfl
/-- 一様最大元存在は不成立。原始二Safe元の全共通上界排除へ戻す。 -/
theorem not_P_G : ¬ P_G := fun h => Triangle.no_greatest (h triangleModel)
/-- 一様join閉性は不成立。同じ原始Safe対のjoin実比較が失敗する。 -/
theorem not_P_J : ¬ P_J := by
  intro h
  have hh := h triangleModel (Triangle.cut 0) (Triangle.cut 1) (Triangle.cut_safe 0) (Triangle.cut_safe 1)
  rw [Triangle.cut_join_top] at hh
  exact triangle_top_not_safe hh
/-- 一様自然maximal選択は不成立。元三角形の全極大元を原始回転が動かす。 -/
theorem not_P_N : ¬ P_N := by
  rintro ⟨s⟩
  exact Triangle.rotation_moves_all_maximal (s.select triangleModel) (s.maximal triangleModel)
    (s.natural triangleModel triangleModel Triangle.rotation)
end AAT.AG.SafeCoarseningOrder.FinitePrimitiveModel
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
