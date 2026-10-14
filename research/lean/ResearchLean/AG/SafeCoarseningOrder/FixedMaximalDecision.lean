import ResearchLean.AG.SafeCoarseningOrder.FiniteIsomorphisms

/-!
# 全自己同型による固定極大元の有限判定

全S/T/V自己同型を全極大元に作用させ、固定極大元を漏れなく列挙する。
正の出力は元分割Rそのもの、負の出力は各極大元を動かす原始自己同型である。

## Implementation notes

元の全同型表をそのまま使い、chart回転だけを検査する方法は採用しない。
軌道と安定化集合も同じ全表で列挙し、Rの選択を軌道の選択へ置換しない。
非計算的選択は証明済み有限候補から証拠付き出力を取り出すためにのみ用いる。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
variable {S T V : Type} [Fintype S] [Fintype T] [Fintype V]
namespace PrimitiveInput
variable (M : PrimitiveInput S T V)
/-- 全原始自己同型。source/target/chartの全置換保存検査から生成する。 -/
def allAut : Finset (PrimitiveIso M M) := allPrimitiveIsos M M
/-- 全自己同型一覧は任意の原始自己同型を含む。 -/
theorem mem_allAut (a : PrimitiveIso M M) : a ∈ M.allAut := mem_allPrimitiveIsos M M a
/-- 元分割Rの全自己同型軌道を有限表として列挙する。 -/
def orbit (R : Coarsening T V) : Finset (Coarsening T V) := by
  classical
  exact M.allAut.image (fun a => a.coarseningOrderIso R)
/-- 軌道表所属は全原始自己同型による同じRの像であることと必要十分。 -/
theorem mem_orbit (R Q : Coarsening T V) : Q ∈ M.orbit R ↔
    ∃ a : PrimitiveIso M M, a.coarseningOrderIso R = Q := by
  classical
  simp only [orbit,Finset.mem_image]
  exact ⟨fun ⟨a,_,h⟩ => ⟨a,h⟩,fun ⟨a,h⟩ => ⟨a,M.mem_allAut a,h⟩⟩
/-- 全自己同型のうち同じRを固定する安定化集合。 -/
def stabilizer (R : Coarsening T V) : Finset (PrimitiveIso M M) := by
  classical
  exact M.allAut.filter (fun a => a.coarseningOrderIso R = R)
/-- 安定化集合は全自己同型について元Rの固定性と必要十分。 -/
theorem mem_stabilizer (R : Coarsening T V) (a : PrimitiveIso M M) :
    a ∈ M.stabilizer R ↔ a.coarseningOrderIso R = R := by
  classical
  simp only [stabilizer,Finset.mem_filter,M.mem_allAut,true_and]
/-- 安定化集合は原始恒等同型を含む。 -/
theorem stabilizer_identity (R : Coarsening T V) : PrimitiveIso.refl M ∈ M.stabilizer R := by
  apply (M.mem_stabilizer R _).mpr
  rw [PrimitiveIso.coarseningOrderIso_refl]
  rfl
/-- 安定化集合は原始同型合成で閉じる。 -/
theorem stabilizer_composition (R : Coarsening T V) (a b : PrimitiveIso M M)
    (ha : a ∈ M.stabilizer R) (hb : b ∈ M.stabilizer R) : a.trans b ∈ M.stabilizer R := by
  apply (M.mem_stabilizer R _).mpr
  rw [PrimitiveIso.coarseningOrderIso_trans,OrderIso.trans_apply,
    (M.mem_stabilizer R a).mp ha,(M.mem_stabilizer R b).mp hb]
/-- 安定化集合は原始逆同型で閉じる。 -/
theorem stabilizer_inverse (R : Coarsening T V) (a : PrimitiveIso M M)
    (ha : a ∈ M.stabilizer R) : a.symm ∈ M.stabilizer R := by
  apply (M.mem_stabilizer R _).mpr
  rw [PrimitiveIso.coarseningOrderIso_symm]
  have hh := congrArg a.coarseningOrderIso.symm ((M.mem_stabilizer R a).mp ha)
  simpa only [OrderIso.symm_apply_apply] using hh.symm
/-- 全極大元の軌道表の各元は同じ全安全集合の極大元。 -/
theorem orbit_maximal (R Q : Coarsening T V) (hR : Maximal M.Safe R) (hQ : Q ∈ M.orbit R) :
    Maximal M.Safe Q := by
  obtain ⟨a,ha⟩ := (M.mem_orbit R Q).mp hQ
  exact ha ▸ a.maximal_forward hR
/-- 全自己同型が元Rを固定することは全軌道表が同じR一元だけであることと必要十分。 -/
theorem fixed_iff_orbit_singleton (R : Coarsening T V) :
    (∀ a : PrimitiveIso M M, a.coarseningOrderIso R = R) ↔ M.orbit R = {R} := by
  classical
  constructor
  · intro h
    apply Finset.ext; intro Q
    rw [M.mem_orbit,Finset.mem_singleton]
    constructor
    · rintro ⟨a,ha⟩
      exact ha.symm.trans (h a)
    · rintro rfl
      refine ⟨PrimitiveIso.refl M,?_⟩
      rw [PrimitiveIso.coarseningOrderIso_refl]
      rfl
  · intro h a
    have hm := (M.mem_orbit R (a.coarseningOrderIso R)).mpr ⟨a,rfl⟩
    rw [h,Finset.mem_singleton] at hm
    exact hm
/-- 全固定極大元を全極大表と全自己同型表から生成する。 -/
def fixedMaximalCoarsenings : Finset (Coarsening T V) := by
  classical
  exact M.maximalCoarsenings.filter (fun R => ∀ a ∈ M.allAut, a.coarseningOrderIso R = R)
/-- 固定極大表は全原始自己同型が固定する全極大元と必要十分。 -/
theorem mem_fixedMaximalCoarsenings (R : Coarsening T V) : R ∈ M.fixedMaximalCoarsenings ↔
    Maximal M.Safe R ∧ ∀ a : PrimitiveIso M M, a.coarseningOrderIso R = R := by
  classical
  simp only [fixedMaximalCoarsenings,Finset.mem_filter,M.mem_maximalCoarsenings]
  exact and_congr_right fun _ => ⟨fun h a => h a (M.mem_allAut a),fun h a _ => h a⟩
/-- 全固定極大表の非空性を決定する有限Bool。 -/
def fixedMaximalDecision : Bool := by
  classical
  exact decide M.fixedMaximalCoarsenings.Nonempty
/-- 有限Boolは入力生成された全固定極大表の非空性と必要十分。 -/
theorem fixedMaximalDecision_eq_true : M.fixedMaximalDecision = true ↔ M.fixedMaximalCoarsenings.Nonempty := by
  classical
  simp only [fixedMaximalDecision,decide_eq_true_eq]
/-- 正の有限判定から出力する元分割と全極大・固定証拠。 -/
structure FixedMaximalWitness where
  /-- 元target/chart分割対。軌道ではなく元そのもの。 -/
  coarsening : Coarsening T V
  /-- 元安全集合における極大性。 -/
  maximal : Maximal M.Safe coarsening
  /-- 全原始自己同型による固定性。 -/
  fixed : ∀ a : PrimitiveIso M M, a.coarseningOrderIso coarsening = coarsening
/-- 正の有限判定から元分割と全証拠を生成する。 -/
theorem fixedMaximalWitness_exists (h : M.fixedMaximalDecision = true) : Nonempty M.FixedMaximalWitness := by
  obtain ⟨R,hR⟩ := (M.fixedMaximalDecision_eq_true).mp h
  obtain ⟨hm,hf⟩ := (M.mem_fixedMaximalCoarsenings R).mp hR
  exact ⟨⟨R,hm,hf⟩⟩
/-- 正の有限表から証拠付き元分割を選ぶ。 -/
def fixedMaximalWitness (h : M.fixedMaximalDecision = true) : M.FixedMaximalWitness :=
  Classical.choice (M.fixedMaximalWitness_exists h)
/-- 負の有限判定から全極大元それぞれを動かす原始自己同型を出力する。 -/
structure NoFixedMaximalWitness where
  /-- 各極大Rに、全有限表に現れる原始自己同型と移動証拠を与える。 -/
  move : ∀ R : Coarsening T V, Maximal M.Safe R →
    {a : PrimitiveIso M M // a ∈ M.allAut ∧ a.coarseningOrderIso R ≠ R}
/-- 負の有限表から各極大元の原始移動証拠を生成する。 -/
theorem noFixedMaximalWitness_exists (h : M.fixedMaximalDecision ≠ true) : Nonempty M.NoFixedMaximalWitness := by
  classical
  have hn := (M.fixedMaximalDecision_eq_true).not.mp h
  have hmoves : ∀ R : Coarsening T V, Maximal M.Safe R →
      ∃ a ∈ M.allAut, a.coarseningOrderIso R ≠ R := by
    intro R hR
    have hf : ¬ ∀ a ∈ M.allAut, a.coarseningOrderIso R = R := by
      intro hall
      have hmem := (M.mem_fixedMaximalCoarsenings R).mpr
        ⟨hR,fun a => hall a (M.mem_allAut a)⟩
      exact hn ⟨R,hmem⟩
    push_neg at hf
    exact hf
  refine ⟨⟨fun R hR => ?_⟩⟩
  exact ⟨Classical.choose (hmoves R hR),Classical.choose_spec (hmoves R hR)⟩
/-- 負の有限表から全極大元に対する移動証拠を選ぶ。 -/
def noFixedMaximalWitness (h : M.fixedMaximalDecision ≠ true) : M.NoFixedMaximalWitness :=
  Classical.choice (M.noFixedMaximalWitness_exists h)
/-- 正の出力が返す元分割は同じ全固定極大表に所属する。 -/
theorem FixedMaximalWitness.coarsening_mem (w : M.FixedMaximalWitness) :
    w.coarsening ∈ M.fixedMaximalCoarsenings :=
  (M.mem_fixedMaximalCoarsenings w.coarsening).mpr ⟨w.maximal,w.fixed⟩
/-- 正の証拠から同じ有限判定のtrueを再検証できる。 -/
theorem FixedMaximalWitness.decision_true (w : M.FixedMaximalWitness) : M.fixedMaximalDecision = true :=
  M.fixedMaximalDecision_eq_true.mpr ⟨w.coarsening,w.coarsening_mem M⟩
/-- 負の出力は全固定極大表が空であることを再検証する。 -/
theorem NoFixedMaximalWitness.fixed_empty (w : M.NoFixedMaximalWitness) : M.fixedMaximalCoarsenings = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  obtain ⟨hm,hf⟩ := (M.mem_fixedMaximalCoarsenings R).mp hR
  exact (w.move R hm).2.2 (hf _)
/-- 負の証拠から同じ有限判定がtrueではないことを再検証する。 -/
theorem NoFixedMaximalWitness.decision_not_true (w : M.NoFixedMaximalWitness) : M.fixedMaximalDecision ≠ true := by
  intro h
  obtain ⟨R,hR⟩ := M.fixedMaximalDecision_eq_true.mp h
  rw [w.fixed_empty M] at hR
  exact Finset.notMem_empty _ hR
end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
