import ResearchLean.AG.SafeCoarseningOrder.PrimitiveIsomorphism

/-!
# G-137 の二段商と直接商

A の二段商は初段の quotient primitive input をさらに商にして生成する。
標準商因子の核を次段分割とし、実際の target/chart/辺/台の同型を構成する。

## Implementation notes

二段商を直接商から定義せず、quotientSupport と quotientEdge の存在式を再適用する。
同型は mathlib の商第一同型定理から作り、全元商写像の可換性を保つ。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance
variable {S T V X : Type}
namespace Coarsening
variable {P Q : Setoid X} (h : P ≤ Q)

/-- 恒等関係の商は元集合の名前だけを変える全単射。 -/
def botEquiv (X : Type) : X ≃ Quotient (⊥ : Setoid X) :=
  Equiv.ofBijective (Quotient.mk (⊥ : Setoid X)) ⟨by
    intro x y h
    exact Quotient.exact h, by
    intro x
    induction x using Quotient.inductionOn with
    | _ x => exact ⟨x, rfl⟩⟩

/-- 恒等商全単射の評価は同じ元の商写像。 -/
@[simp] theorem botEquiv_apply (x : X) : botEquiv X x = Quotient.mk (⊥ : Setoid X) x := rfl

/-- 標準商因子は全射。全商点を同じ原始元で表示する。 -/
theorem factor_surjective : Function.Surjective (factor h) := by
  intro x
  induction x using Quotient.inductionOn with
  | _ x => exact ⟨Quotient.mk P x, rfl⟩

/-- 二段目の分割は生成因子の核である。 -/
def factorKernel : Setoid (Quotient P) := Setoid.ker (factor h)

/-- 二段商から直接商への標準全単射。 -/
def iteratedEquiv : Quotient (factorKernel h) ≃ Quotient Q :=
  Setoid.quotientKerEquivOfSurjective (factor h) (factor_surjective h)

/-- 二段商全単射の、初段商点に対する評価式。 -/
@[simp] theorem iteratedEquiv_mk (x : Quotient P) :
    iteratedEquiv h (Quotient.mk (factorKernel h) x) = factor h x := rfl

end Coarsening
namespace PrimitiveInput
variable (M : PrimitiveInput S T V) (R : Coarsening T V)

/-- 商の原始表を生成する。次の商では同じ生成式をこの表へ再適用する。 -/
def quotientInput : PrimitiveInput S (Quotient R.1) (Quotient R.2) where
  read := (M.quotientReading R).read
  read_surjective := (M.quotientReading R).surjective
  edge := M.quotientEdge R
  edge_ne _ _ h := h.1
  support := M.quotientSupport R
  support_nonempty := M.quotientSupport_nonempty R

/-- 商原始表の reading は独立に作った quotientReading と一致。 -/
@[simp] theorem quotientInput_reading : (M.quotientInput R).reading = M.quotientReading R := rfl

/-- 商原始表の支持 API。 -/
@[simp] theorem quotientInput_support (b : Quotient R.2) :
    (M.quotientInput R).support b = M.quotientSupport R b := rfl

/-- 商原始表の辺 API。 -/
@[simp] theorem quotientInput_edge (b c : Quotient R.2) :
    (M.quotientInput R).edge b c ↔ M.quotientEdge R b c := Iff.rfl

/-- 商原始表から再生成した nerve は独立商の全セル・incidence record と等しい。 -/
@[simp] theorem quotientInput_nerve : (M.quotientInput R).nerve = M.quotientNerve R := rfl

/-- 同じ生成を既存 supported nerve の全recordへ接続する。有限instanceも保持。 -/
theorem quotientInput_supported [Fintype V] :
    letI : Fintype (Quotient R.2) := (M.quotientSupported R).chartFintype
    (M.quotientInput R).supported = M.quotientSupported R := by
  classical
  rfl

/-- 元の原始入力と恒等分割の商の、全S/T/Vと辺・台を保つ同型。 -/
def botIso : PrimitiveIso M (M.quotientInput (⊥ : Coarsening T V)) where
  source := Equiv.refl S
  target := Coarsening.botEquiv T
  chart := Coarsening.botEquiv V
  read_comm _ := rfl
  edge_iff v w := by
    constructor
    · intro he
      exact ⟨fun h => M.edge_ne v w he ((Coarsening.botEquiv V).injective h),
        v,w,he,rfl,rfl⟩
    · rintro ⟨hne,v',w',he,hv,hw⟩
      have hv' : v' = v := (Coarsening.botEquiv V).injective hv
      have hw' : w' = w := (Coarsening.botEquiv V).injective hw
      exact hv' ▸ hw' ▸ he
  support_iff v t := by
    constructor
    · exact M.quotientSupport_mk (⊥ : Coarsening T V) v
    · rintro ⟨v',t',hv,ht,htt⟩
      have hv' : v' = v := (Coarsening.botEquiv V).injective hv
      have ht' : t' = t := (Coarsening.botEquiv T).injective htt
      exact hv' ▸ ht' ▸ ht

variable {R} {R' : Coarsening T V} (h : R ≤ R')

/-- 二段目の target/chart 分割対を各標準因子の核から生成。 -/
def iteratedRelation : Coarsening (Quotient R.1) (Quotient R.2) :=
  (Coarsening.factorKernel h.1, Coarsening.factorKernel h.2)

/-- 二段商の chart 支持点を直接商に輸送する必要十分。 -/
theorem iterated_support (b : Quotient (Coarsening.factorKernel h.2))
    (x : Quotient (Coarsening.factorKernel h.1)) :
    x ∈ (M.quotientInput R).quotientSupport (iteratedRelation h) b ↔
      Coarsening.iteratedEquiv h.1 x ∈
        M.quotientSupport R' (Coarsening.iteratedEquiv h.2 b) := by
  induction b using Quotient.inductionOn with
  | _ b =>
    induction x using Quotient.inductionOn with
    | _ x =>
      constructor
      · rintro ⟨c, t, hcb, ht, htx⟩
        obtain ⟨v, a, hvc, ha, hat⟩ := ht
        have hcb' := Quotient.exact hcb
        have htx' := Quotient.exact htx
        exact ⟨v, a, by
          change Quotient.mk R'.2 v = Coarsening.factor h.2 b
          rw [← Coarsening.factor_mk h.2, hvc]
          exact hcb', ha, by
          change Quotient.mk R'.1 a = Coarsening.factor h.1 x
          rw [← Coarsening.factor_mk h.1, hat]
          exact htx'⟩
      · rintro ⟨v, a, hv, ha, hax⟩
        refine ⟨Quotient.mk R.2 v, Quotient.mk R.1 a, ?_,
          M.quotientSupport_mk R v ha, ?_⟩
        · apply Quotient.sound
          exact hv
        · apply Quotient.sound
          exact hax

/-- 二段商の有向辺を直接商へ輸送する必要十分。内部化した辺は復活しない。 -/
theorem iterated_edge (b c : Quotient (Coarsening.factorKernel h.2)) :
    (M.quotientInput R).quotientEdge (iteratedRelation h) b c ↔
      M.quotientEdge R' (Coarsening.iteratedEquiv h.2 b) (Coarsening.iteratedEquiv h.2 c) := by
  constructor
  · rintro ⟨hne, v, w, he, hv, hw⟩
    obtain ⟨a, d, had, hav, hdw⟩ := he.2
    refine ⟨fun heq => hne ((Coarsening.iteratedEquiv h.2).injective heq), a, d, had, ?_, ?_⟩
    · calc
        Quotient.mk R'.2 a = Coarsening.factor h.2 v := by rw [← hav]; rfl
        _ = Coarsening.iteratedEquiv h.2 b := by rw [← hv]; rfl
    · calc
        Quotient.mk R'.2 d = Coarsening.factor h.2 w := by rw [← hdw]; rfl
        _ = Coarsening.iteratedEquiv h.2 c := by rw [← hw]; rfl
  · rintro ⟨hne, v, w, he, hv, hw⟩
    have hneq : Quotient.mk R.2 v ≠ Quotient.mk R.2 w := by
      intro hsame
      apply hne
      rw [← hv, ← hw]
      exact congrArg (Coarsening.factor h.2) hsame
    refine ⟨fun heq => hne (congrArg (Coarsening.iteratedEquiv h.2) heq),
      Quotient.mk R.2 v, Quotient.mk R.2 w, ⟨hneq, v, w, he, rfl, rfl⟩, ?_, ?_⟩
    · apply (Coarsening.iteratedEquiv h.2).injective
      exact hv
    · apply (Coarsening.iteratedEquiv h.2).injective
      exact hw

/-- A の二段商と直接商の全原始入力同型。Sourceは同じ、二商写像は可換。 -/
def iteratedIso : PrimitiveIso
    ((M.quotientInput R).quotientInput (iteratedRelation h)) (M.quotientInput R') where
  source := Equiv.refl S
  target := Coarsening.iteratedEquiv h.1
  chart := Coarsening.iteratedEquiv h.2
  read_comm _ := rfl
  edge_iff := M.iterated_edge h
  support_iff := M.iterated_support h

/-- 二段商同型は元 T からの商写像と可換。 -/
@[simp] theorem iteratedIso_target_mk (t : T) :
    (M.iteratedIso h).target
      (Quotient.mk (Coarsening.factorKernel h.1) (Quotient.mk R.1 t)) =
        Quotient.mk R'.1 t := rfl

/-- 二段商同型は元 V からの商写像とも可換。 -/
@[simp] theorem iteratedIso_chart_mk (v : V) :
    (M.iteratedIso h).chart
      (Quotient.mk (Coarsening.factorKernel h.2) (Quotient.mk R.2 v)) =
        Quotient.mk R'.2 v := rfl

end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
