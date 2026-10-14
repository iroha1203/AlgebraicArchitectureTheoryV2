import ResearchLean.AG.SafeCoarseningOrder.Factorization

/-!
# G-137 原始商生成の発火例

E の W0 の原始表を生成し、内部辺縮約と恒等分割での保持を評価する。
H¹ と安全半順序の W0 全評価は後続義務である。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance

/-- W0 の一辺、二 chart、Unit reading、全台の原始入力。 -/
def w0 : PrimitiveInput Unit Unit Bool where
  read := id
  read_surjective := Function.surjective_id
  edge v w := v = false ∧ w = true
  edge_ne v w h := by rcases h with ⟨rfl, rfl⟩; decide
  support _ := Set.univ
  support_nonempty _ := Set.univ_nonempty

/-- W0 の指定有向辺。 -/
def w0Edge : w0.Edge := ⟨(false, true), rfl, rfl⟩

/-- W0 全関係商で指定辺は内部辺として縮約される。 -/
theorem w0_top_edge_none : w0.quotientEdgeMap (⊤ : Coarsening Unit Bool) w0Edge = none := by
  apply (w0.quotientEdgeMap_eq_none _ _).mpr
  exact True.intro

/-- W0 恒等分割商では指定辺を縮約しない。 -/
theorem w0_bot_edge_not_none :
    w0.quotientEdgeMap (⊥ : Coarsening Unit Bool) w0Edge ≠ none := by
  intro h
  have he := (w0.quotientEdgeMap_eq_none _ _).mp h
  exact Bool.false_ne_true he

/-- T0 の対角除外が実質的制限であることを原始入力から示す。 -/
theorem primitive_no_diagonal {S T V : Type} (M : PrimitiveInput S T V) (v : V) :
    ¬ M.edge v v := by
  intro h
  exact M.edge_ne v v h rfl

end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
