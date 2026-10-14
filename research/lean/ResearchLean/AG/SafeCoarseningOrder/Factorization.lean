import ResearchLean.AG.SafeCoarseningOrder.QuotientNerve
import ResearchLean.AG.AtlasDefectComposition.ComparisonComposition

/-!
# G-137 の分割包含と商因子

A の因子化を、元の target と chart からの商写像と可換な二因子として特徴づける。
Setoid の標準順序・商写像を用い、原始商の支持と辺も同じ因子で輸送する。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance Cohomology AtlasDefectComposition
variable {S T V : Type}

namespace Coarsening
variable {X : Type} {P Q U : Setoid X}

/-- 分割包含からの標準商因子。 -/
def factor (h : P ≤ Q) : Quotient P → Quotient Q := Setoid.map_of_le h

/-- 元の写像と商因子の可換性。 -/
@[simp] theorem factor_mk (h : P ≤ Q) (x : X) :
    factor h (Quotient.mk P x) = Quotient.mk Q x := rfl

/-- 商因子の一意性は全射商写像から得る。 -/
theorem factor_unique (h : P ≤ Q) (f : Quotient P → Quotient Q)
    (hf : ∀ x, f (Quotient.mk P x) = Quotient.mk Q x) : f = factor h := by
  funext a
  induction a using Quotient.inductionOn with
  | _ x => exact hf x

/-- 分割包含と元からの可換な因子の存在は同値。 -/
theorem le_iff_factor : P ≤ Q ↔
    ∃ f : Quotient P → Quotient Q, ∀ x, f (Quotient.mk P x) = Quotient.mk Q x := by
  constructor
  · intro h
    exact ⟨factor h, factor_mk h⟩
  · rintro ⟨f, hf⟩ x y hxy
    apply Quotient.exact
    rw [← hf x, ← hf y, Quotient.sound hxy]

/-- 恒等分割包含の因子は恒等写像。 -/
@[simp] theorem factor_refl : factor (le_refl P) = id := by
  symm
  apply factor_unique
  intro x
  rfl

/-- 三分割の標準因子の合成。 -/
theorem factor_comp (h : P ≤ Q) (k : Q ≤ U) :
    factor (le_trans h k) = factor k ∘ factor h := by
  symm
  apply factor_unique
  intro x
  rfl

/-- target と chart の二可換因子が分割対の順序を完全に特徴づける。 -/
theorem le_iff_factors {R R' : Coarsening T V} : R ≤ R' ↔
    (∃ f : Quotient R.1 → Quotient R'.1,
      ∀ t, f (Quotient.mk R.1 t) = Quotient.mk R'.1 t) ∧
    (∃ f : Quotient R.2 → Quotient R'.2,
      ∀ v, f (Quotient.mk R.2 v) = Quotient.mk R'.2 v) := by
  exact and_congr le_iff_factor le_iff_factor

end Coarsening

namespace PrimitiveInput
variable (M : PrimitiveInput S T V) {R R' : Coarsening T V} (h : R ≤ R')

include h in
/-- 分割包含から商 reading 間の coarse-reading 順序を生成する。 -/
theorem factor_coarser : (M.quotientReading R').CoarserThan (M.quotientReading R) := by
  intro x y hxy
  exact Quotient.sound (h.1 (Quotient.exact hxy))

/-- 既存の canonical target factor と標準商因子の一致。 -/
theorem factor_comparisonFactor :
    comparisonFactor (M.quotientReading R') (M.quotientReading R) (M.factor_coarser h) =
      Coarsening.factor h.1 := by
  symm
  apply comparisonFactor_unique (M.quotientReading R') (M.quotientReading R)
    (M.factor_coarser h)
  intro s
  rfl

/-- chart と target の商因子に沿う支持輸送。 -/
theorem factor_support (b : Quotient R.2) {x : Quotient R.1}
    (hx : x ∈ M.quotientSupport R b) :
    Coarsening.factor h.1 x ∈ M.quotientSupport R' (Coarsening.factor h.2 b) := by
  obtain ⟨v, t, hv, ht, htx⟩ := (M.mem_quotientSupport R b x).mp hx
  exact ⟨v, t, by rw [← hv]; rfl, ht, by rw [← htx]; rfl⟩

/-- 残る商辺を次の商へ送る。内部になった辺は none。 -/
def factorEdgeMap (e : M.QuotientEdge R) : Option (M.QuotientEdge R') := by
  classical
  exact if hn : Coarsening.factor h.2 e.1.1 = Coarsening.factor h.2 e.1.2 then none else
    some ⟨(Coarsening.factor h.2 e.1.1, Coarsening.factor h.2 e.1.2), hn, by
      obtain ⟨v, w, he, hv, hw⟩ := e.2.2
      exact ⟨v, w, he, by rw [← hv]; rfl, by rw [← hw]; rfl⟩⟩

/-- factorEdgeMap の内部辺条件。 -/
@[simp] theorem factorEdgeMap_eq_none (e : M.QuotientEdge R) :
    M.factorEdgeMap h e = none ↔
      Coarsening.factor h.2 e.1.1 = Coarsening.factor h.2 e.1.2 := by
  classical
  simp [factorEdgeMap]

/-- factorEdgeMap の残存辺の両端評価。 -/
theorem factorEdgeMap_some_endpoints (e : M.QuotientEdge R) (f : M.QuotientEdge R')
    (he : M.factorEdgeMap h e = some f) :
    Coarsening.factor h.2 e.1.1 = f.1.1 ∧ Coarsening.factor h.2 e.1.2 = f.1.2 := by
  classical
  unfold factorEdgeMap at he
  split_ifs at he with hn
  cases Option.some.inj he
  exact ⟨rfl, rfl⟩

variable [Fintype V]

/-- A の任意 R≤R' に対する原始比較。全 incidence と支持条件を生成する。 -/
def factorMorphism : TargetSupportedNerveMorphism
    (M.quotientReading R') (M.quotientReading R) (M.factor_coarser h)
    (M.quotientSupported R') (M.quotientSupported R) where
  chartMap := Coarsening.factor h.2
  edgeMap := M.factorEdgeMap h
  faceMap := Empty.elim
  edge_some_left e f he := (M.factorEdgeMap_some_endpoints h e f he).1
  edge_some_right e f he := (M.factorEdgeMap_some_endpoints h e f he).2
  edge_none_fiber e he := (M.factorEdgeMap_eq_none h e).mp he
  face_some_edge0 f := f.elim
  face_some_edge1 f := f.elim
  face_some_edge2 f := f.elim
  face_none_edge0 f := f.elim
  face_none_edge1 f := f.elim
  face_none_edge2 f := f.elim
  chartSupport_compatible b x hx := by
    rw [M.factor_comparisonFactor h]
    exact M.factor_support h b hx

omit [Fintype V] in
/-- 任意商辺の次段部分像も両端によって特徴づけられる。 -/
theorem factorEdgeMap_eq_some (e : M.QuotientEdge R) (f : M.QuotientEdge R') :
    M.factorEdgeMap h e = some f ↔
      Coarsening.factor h.2 e.1.1 = f.1.1 ∧ Coarsening.factor h.2 e.1.2 = f.1.2 := by
  classical
  constructor
  · exact M.factorEdgeMap_some_endpoints h e f
  · rintro ⟨hl, hr⟩
    have hn : Coarsening.factor h.2 e.1.1 ≠ Coarsening.factor h.2 e.1.2 := by
      rw [hl, hr]
      exact f.2.1
    simp only [factorEdgeMap, dif_neg hn]
    congr 1
    apply Subtype.ext
    exact Prod.ext hl hr

omit [Fintype V] in
/-- fine からの直接部分辺像と二段の Option.bind は一致する。 -/
theorem quotientEdgeMap_factor (e : M.Edge) :
    M.quotientEdgeMap R' e = (M.quotientEdgeMap R e).bind (M.factorEdgeMap h) := by
  cases he : M.quotientEdgeMap R e with
  | none =>
    have hf : M.quotientEdgeMap R' e = none :=
      (M.quotientEdgeMap_eq_none R' e).mpr (h.2 ((M.quotientEdgeMap_eq_none R e).mp he))
    simp only [Option.bind_none, hf]
  | some f =>
    rcases M.quotientEdgeMap_some_endpoints R e f he with ⟨hl, hr⟩
    cases hf : M.factorEdgeMap h f with
    | none =>
      have hn := (M.factorEdgeMap_eq_none h f).mp hf
      have hn' : Quotient.mk R'.2 e.1.1 = Quotient.mk R'.2 e.1.2 := by
        simpa only [← hl, ← hr, Coarsening.factor_mk] using hn
      have hg := (M.quotientEdgeMap_eq_none R' e).mpr (Quotient.exact hn')
      simp only [Option.bind_some, hf, hg]
    | some g =>
      rcases M.factorEdgeMap_some_endpoints h f g hf with ⟨hfl, hfr⟩
      have hg : M.quotientEdgeMap R' e = some g :=
        (M.quotientEdgeMap_eq_some R' e g).mpr ⟨by
          simpa only [← hl, Coarsening.factor_mk] using hfl, by
          simpa only [← hr, Coarsening.factor_mk] using hfr⟩
      simp only [Option.bind_some, hf, hg]

omit [Fintype V] in
/-- 同じ原始部分セル写像なら hereditary 比較の全 record が等しい。 -/
theorem morphism_ext {qc qf : Reading S} {hc : qc.CoarserThan qf}
    {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
    {m n : TargetSupportedNerveMorphism qc qf hc Nc Nf}
    (hchart : m.chartMap = n.chartMap) (hedge : m.edgeMap = n.edgeMap)
    (hface : m.faceMap = n.faceMap) : m = n := by
  cases m
  cases n
  cases hchart
  cases hedge
  cases hface
  rfl

/-- 原始 direct 比較と既存 G-133 比較合成の全 record の一致。 -/
theorem quotientMorphism_factor :
    M.quotientMorphism R' =
      comparisonComp (M.factorMorphism h) (M.quotientMorphism R) := by
  apply morphism_ext
  · funext v
    rfl
  · funext e
    exact M.quotientEdgeMap_factor h e
  · funext f
    exact f.elim

omit [Fintype V] in
/-- 三分割間の原始部分辺像の合成。 -/
theorem factorEdgeMap_comp {R'' : Coarsening T V} (k : R' ≤ R'')
    (e : M.QuotientEdge R) :
    M.factorEdgeMap (le_trans h k) e =
      (M.factorEdgeMap h e).bind (M.factorEdgeMap k) := by
  have hcomp : Coarsening.factor (le_trans h.2 k.2) =
      Coarsening.factor k.2 ∘ Coarsening.factor h.2 := Coarsening.factor_comp h.2 k.2
  cases he : M.factorEdgeMap h e with
  | none =>
    have hn := (M.factorEdgeMap_eq_none h e).mp he
    have hg : M.factorEdgeMap (le_trans h k) e = none :=
      (M.factorEdgeMap_eq_none (le_trans h k) e).mpr (by
        rw [hcomp]
        exact congrArg (Coarsening.factor k.2) hn)
    simp only [Option.bind_none, hg]
  | some f =>
    rcases M.factorEdgeMap_some_endpoints h e f he with ⟨hl, hr⟩
    cases hf : M.factorEdgeMap k f with
    | none =>
      have hn := (M.factorEdgeMap_eq_none k f).mp hf
      have hg : M.factorEdgeMap (le_trans h k) e = none :=
        (M.factorEdgeMap_eq_none (le_trans h k) e).mpr (by
          rw [hcomp]
          simpa only [Function.comp_apply, hl, hr] using hn)
      simp only [Option.bind_some, hf, hg]
    | some g =>
      rcases M.factorEdgeMap_some_endpoints k f g hf with ⟨hfl, hfr⟩
      have hg : M.factorEdgeMap (le_trans h k) e = some g :=
        (M.factorEdgeMap_eq_some (le_trans h k) e g).mpr ⟨by
          rw [hcomp]
          simpa only [Function.comp_apply, hl] using hfl, by
          rw [hcomp]
          simpa only [Function.comp_apply, hr] using hfr⟩
      simp only [Option.bind_some, hf, hg]

/-- 三分割間の direct 比較と合成の全 record 等号。 -/
theorem factorMorphism_comp {R'' : Coarsening T V} (k : R' ≤ R'') :
    M.factorMorphism (le_trans h k) =
      comparisonComp (M.factorMorphism k) (M.factorMorphism h) := by
  apply morphism_ext
  · exact Coarsening.factor_comp h.2 k.2
  · funext e
    exact M.factorEdgeMap_comp h k e
  · funext f
    exact f.elim

/-- 恒等包含の原始 chart 写像は恒等写像。 -/
@[simp] theorem factorMorphism_refl_chart (b : Quotient R.2) :
    (M.factorMorphism (le_refl R)).chartMap b = b := by
  exact congrFun Coarsening.factor_refl b

/-- 恒等包含の原始辺写像は全辺をそのまま保持する。 -/
@[simp] theorem factorMorphism_refl_edge (e : M.QuotientEdge R) :
    (M.factorMorphism (le_refl R)).edgeMap e = some e := by
  apply (M.factorEdgeMap_eq_some (le_refl R) e e).mpr
  exact ⟨congrFun Coarsening.factor_refl e.1.1, congrFun Coarsening.factor_refl e.1.2⟩

end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
