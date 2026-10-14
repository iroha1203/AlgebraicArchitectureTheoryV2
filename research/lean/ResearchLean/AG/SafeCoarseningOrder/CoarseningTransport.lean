import ResearchLean.AG.SafeCoarseningOrder.IsomorphismCochains

/-!
# 原始同型による分割対と商入力の輸送

全S/T/V原始同型から関係包含の順序同型を作り、元の商写像を保つ商入力同型を生成する。
有向辺の部分像は内部化を含め同じ同型で可換になる。

## Implementation notes

分割は逆全単射によるSetoid.comap、商全単射はQuotient.congrを用いる。
元分割対を自己同型軌道で同一視せず、target/chartを独立に輸送する。
H¹同型や安全性を輸送条件にせず、原始q/辺/台から全fieldを証明する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
variable {X Y : Type}
/-- 全単射に沿う同値関係の輸送は包含順序の同型。 -/
def transportSetoid (e : X ≃ Y) : Setoid X ≃o Setoid Y where
  toFun P := Setoid.comap e.symm P
  invFun Q := Setoid.comap e Q
  left_inv P := by
    apply Setoid.ext; intro x y
    simp only [Setoid.comap_rel,Equiv.symm_apply_apply]
  right_inv Q := by
    apply Setoid.ext; intro x y
    simp only [Setoid.comap_rel,Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro P Q
    constructor
    · intro h x y hP
      have hx := h (show (Setoid.comap e.symm P).r (e x) (e y) from by simpa only [Setoid.comap_rel,Equiv.symm_apply_apply] using hP)
      simpa only [Setoid.comap_rel,Equiv.symm_apply_apply] using hx
    · intro h x y hP
      exact h hP
/-- 輸送した関係の公開評価は逆全単射による元関係。 -/
theorem transportSetoid_rel (e : X ≃ Y) (P : Setoid X) (x y : Y) :
    (transportSetoid e P).r x y ↔ P.r (e.symm x) (e.symm y) := Setoid.comap_rel _ _ _ _
/-- 元全単射と輸送関係から生成する商全単射。 -/
def transportQuotient (e : X ≃ Y) (P : Setoid X) : Quotient P ≃ Quotient (transportSetoid e P) :=
  Quotient.congr e (by
    intro x y
    rw [transportSetoid_rel]
    simp only [Equiv.symm_apply_apply])
/-- 商全単射は元の商写像と可換。 -/
@[simp] theorem transportQuotient_mk (e : X ≃ Y) (P : Setoid X) (x : X) :
    transportQuotient e P (Quotient.mk P x) = Quotient.mk (transportSetoid e P) (e x) := rfl
variable {S T V S' T' V' : Type}
variable {M : PrimitiveInput S T V} {N : PrimitiveInput S' T' V'}
namespace PrimitiveIso
/-- 全原始同型による独立target/chart分割対の順序同型。 -/
def coarseningOrderIso (a : PrimitiveIso M N) : Coarsening T V ≃o Coarsening T' V' where
  toFun R := (transportSetoid a.target R.1,transportSetoid a.chart R.2)
  invFun R := ((transportSetoid a.target).symm R.1,(transportSetoid a.chart).symm R.2)
  left_inv R := Prod.ext ((transportSetoid a.target).left_inv R.1)
    ((transportSetoid a.chart).left_inv R.2)
  right_inv R := Prod.ext ((transportSetoid a.target).right_inv R.1)
    ((transportSetoid a.chart).right_inv R.2)
  map_rel_iff' := by
    intro R Q
    exact and_congr (transportSetoid a.target).map_rel_iff (transportSetoid a.chart).map_rel_iff
/-- 順序輸送のtarget関係を元関係へ戻す公開API。 -/
theorem coarseningOrderIso_target_rel (a : PrimitiveIso M N) (R : Coarsening T V)
    (t u : T') : (a.coarseningOrderIso R).1.r t u ↔ R.1.r (a.target.symm t) (a.target.symm u) :=
  transportSetoid_rel a.target R.1 t u
/-- 順序輸送のchart関係を元関係へ戻す公開API。 -/
theorem coarseningOrderIso_chart_rel (a : PrimitiveIso M N) (R : Coarsening T V)
    (v w : V') : (a.coarseningOrderIso R).2.r v w ↔ R.2.r (a.chart.symm v) (a.chart.symm w) :=
  transportSetoid_rel a.chart R.2 v w
/-- 原始恒等同型の作用は全順序同型として恒等。 -/
theorem coarseningOrderIso_refl (M : PrimitiveInput S T V) :
    (refl M).coarseningOrderIso = OrderIso.refl (Coarsening T V) := by
  apply OrderIso.ext
  funext R
  apply Prod.ext <;> apply Setoid.ext <;> intro x y <;> rfl
/-- 原始同型の合成作用は全順序同型の合成。 -/
theorem coarseningOrderIso_trans {S'' T'' V'' : Type} {O : PrimitiveInput S'' T'' V''}
    (a : PrimitiveIso M N) (b : PrimitiveIso N O) :
    (a.trans b).coarseningOrderIso = a.coarseningOrderIso.trans b.coarseningOrderIso := by
  apply OrderIso.ext
  funext R
  apply Prod.ext <;> apply Setoid.ext <;> intro x y <;> rfl
/-- 原始逆同型の作用は全順序同型の逆。 -/
theorem coarseningOrderIso_symm (a : PrimitiveIso M N) :
    a.symm.coarseningOrderIso = a.coarseningOrderIso.symm := by
  apply OrderIso.ext
  funext R
  apply Prod.ext <;> apply Setoid.ext <;> intro x y <;> rfl

/-- 順序輸送したtarget商への元同型からの全単射。 -/
def quotientTarget (a : PrimitiveIso M N) (R : Coarsening T V) :
    Quotient R.1 ≃ Quotient (a.coarseningOrderIso R).1 := transportQuotient a.target R.1
/-- 順序輸送したchart商への元同型からの全単射。 -/
def quotientChart (a : PrimitiveIso M N) (R : Coarsening T V) :
    Quotient R.2 ≃ Quotient (a.coarseningOrderIso R).2 := transportQuotient a.chart R.2
/-- target商全単射は同じ元target商写像を保つ。 -/
@[simp] theorem quotientTarget_mk (a : PrimitiveIso M N) (R : Coarsening T V) (t : T) :
    a.quotientTarget R (Quotient.mk R.1 t) = Quotient.mk (a.coarseningOrderIso R).1 (a.target t) := rfl
/-- chart商全単射は同じ元chart商写像を保つ。 -/
@[simp] theorem quotientChart_mk (a : PrimitiveIso M N) (R : Coarsening T V) (v : V) :
    a.quotientChart R (Quotient.mk R.2 v) = Quotient.mk (a.coarseningOrderIso R).2 (a.chart v) := rfl
/-- 内部辺除外と有向原辺の存在を保ち商有向辺を両方向に輸送。 -/
theorem quotient_edge_iff (a : PrimitiveIso M N) (R : Coarsening T V)
    (b c : Quotient R.2) : M.quotientEdge R b c ↔
      N.quotientEdge (a.coarseningOrderIso R) (a.quotientChart R b) (a.quotientChart R c) := by
  rw [M.quotientEdge_iff,N.quotientEdge_iff]
  constructor
  · rintro ⟨hne,v,w,he,hl,hr⟩
    refine ⟨fun h => hne ((a.quotientChart R).injective h),a.chart v,a.chart w,
      (a.edge_iff v w).mp he,?_,?_⟩
    · rw [← quotientChart_mk,hl]
    · rw [← quotientChart_mk,hr]
  · rintro ⟨hne,v,w,he,hl,hr⟩
    refine ⟨fun h => hne (congrArg (a.quotientChart R) h),a.chart.symm v,a.chart.symm w,
      (a.symm.edge_iff v w).mp he,?_,?_⟩
    · apply (a.quotientChart R).injective
      simpa only [quotientChart_mk,Equiv.apply_symm_apply] using hl
    · apply (a.quotientChart R).injective
      simpa only [quotientChart_mk,Equiv.apply_symm_apply] using hr
/-- chart fiberの台の合併の像は原始台の輸送と可換。 -/
theorem quotient_support_iff (a : PrimitiveIso M N) (R : Coarsening T V)
    (b : Quotient R.2) (t : Quotient R.1) : t ∈ M.quotientSupport R b ↔
      a.quotientTarget R t ∈ N.quotientSupport (a.coarseningOrderIso R) (a.quotientChart R b) := by
  rw [M.mem_quotientSupport,N.mem_quotientSupport]
  constructor
  · rintro ⟨v,u,hv,hs,hu⟩
    refine ⟨a.chart v,a.target u,?_,(a.support_iff v u).mp hs,?_⟩
    · rw [← quotientChart_mk,hv]
    · rw [← quotientTarget_mk,hu]
  · rintro ⟨v,u,hv,hs,hu⟩
    refine ⟨a.chart.symm v,a.target.symm u,?_,(a.symm.support_iff v u).mp hs,?_⟩
    · apply (a.quotientChart R).injective
      simpa only [quotientChart_mk,Equiv.apply_symm_apply] using hv
    · apply (a.quotientTarget R).injective
      simpa only [quotientTarget_mk,Equiv.apply_symm_apply] using hu
/-- 元sourceを含む商原始入力の全同型をq/辺/台から生成。 -/
def quotientIso (a : PrimitiveIso M N) (R : Coarsening T V) :
    PrimitiveIso (M.quotientInput R) (N.quotientInput (a.coarseningOrderIso R)) where
  source := a.source
  target := a.quotientTarget R
  chart := a.quotientChart R
  read_comm s := congrArg (Quotient.mk (a.coarseningOrderIso R).1) (a.read_comm s)
  edge_iff b c := by
    rw [M.quotientInput_edge,N.quotientInput_edge]
    exact a.quotient_edge_iff R b c
  support_iff b t := by
    rw [M.quotientInput_support,N.quotientInput_support]
    exact a.quotient_support_iff R b t
/-- 商入力同型のsourceは元のsource全単射そのもの。 -/
@[simp] theorem quotientIso_source (a : PrimitiveIso M N) (R : Coarsening T V) :
    (a.quotientIso R).source = a.source := rfl
/-- 商入力同型のtargetは元商写像を保つ生成全単射。 -/
@[simp] theorem quotientIso_target (a : PrimitiveIso M N) (R : Coarsening T V) :
    (a.quotientIso R).target = a.quotientTarget R := rfl
/-- 商入力同型のchartは元商写像を保つ生成全単射。 -/
@[simp] theorem quotientIso_chart (a : PrimitiveIso M N) (R : Coarsening T V) :
    (a.quotientIso R).chart = a.quotientChart R := rfl
/-- 有向部分辺像の自然性。noneとsomeの双方を同じ生成式で保つ。 -/
theorem quotientEdgeMap_naturality (a : PrimitiveIso M N) (R : Coarsening T V) (e : M.Edge) :
    Option.map (a.quotientIso R).edgeEquiv (M.quotientEdgeMap R e) =
      N.quotientEdgeMap (a.coarseningOrderIso R) (a.edgeEquiv e) := by
  cases hm : M.quotientEdgeMap R e with
  | none =>
    simp only [Option.map_none]
    symm
    apply (N.quotientEdgeMap_eq_none _ _).mpr
    have hr := (M.quotientEdgeMap_eq_none R e).mp hm
    rw [coarseningOrderIso_chart_rel,edgeEquiv_left,edgeEquiv_right,
      Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact hr
  | some f =>
    simp only [Option.map_some]
    symm
    apply (N.quotientEdgeMap_eq_some _ _ _).mpr
    have hf := (M.quotientEdgeMap_eq_some R e f).mp hm
    constructor
    · rw [edgeEquiv_left,edgeEquiv_left,quotientIso_chart,← quotientChart_mk,hf.1]
    · rw [edgeEquiv_right,edgeEquiv_right,quotientIso_chart,← quotientChart_mk,hf.2]
end PrimitiveIso
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
