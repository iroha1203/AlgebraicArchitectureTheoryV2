import Formal.AG.SemanticRepair.Saga.Presentation
import Formal.AG.SemanticRepair.Saga.EquationLift

/-!
# Part X §4: affine semantic repair system and the semantic residual

* `AffineSemanticRepairSystem` (Part X Definition 4.1, Theorem 1.1 input 5,
  R0 §4.5): a sitewide semantic state presheaf with an `F_sem` action; the
  three material conditions (relation soundness, stabilizer completeness,
  local transitivity) are required over `Int_{≤2}(𝒰)` contexts.
* `mact`: the action descends to `M_sem` (relation soundness); the
  `M_sem`-torsor structure — freeness (`mact_free`), transitivity
  (`mact_transitive`) — and semantic faithfulness (`mact_faithful`,
  `x+p = y+p → x = y` in `M_sem`) are **derived theorems**, not fields.
* `SemanticRepairAtlas` (Definition 4.2, input 5b) and the generated semantic
  residual: `semanticResidual` / Lemma 4.3 (`semanticResidual_cocycle`) /
  Theorem 4.4 (`semanticResidual_choice`,
  `semanticResidualClass_choice_independent`) / Corollary 4.5
  (`semanticResidualClass_isZero_iff_coboundary`,
  `semanticResidualClass_isZero_iff_matching_correction`) — instantiating the
  generic residual engine of
  `Formal.AG.SemanticRepair.Saga.EquationLift` at the descended
  `M_sem`-affine system, exactly as the text derives Lemma 5.4 by the same
  computation.

`r_sem` is generated from atlas differences; it is never supplied as a
selected 1-cocycle, and no torsor conclusion is a structure field.
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory

universe u v x

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {R : AtomOccurrenceReading S}

/--
X.定義4.1(R0 §4.5): `F_sem` 作用つき semantic local repair state。
torsor 3条件は `Int_{≤2}(𝒰)` の context 上で要求する。
-/
structure AffineSemanticRepairSystem (P : SemanticRepairPresentation.{u, v} S R)
    (𝒰 : MonomorphicOrderedCover S) where
  State : S.category -> Type x
  restrictState : ∀ {V' V : S.category}, (V' ⟶ V) -> State V -> State V'
  restrictState_id : ∀ (V : S.category) (p : State V), restrictState (𝟙 V) p = p
  restrictState_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (p : State V),
        restrictState (f ≫ g) p = restrictState f (restrictState g p)
  act : ∀ V : S.category, P.atomData.SupportedWord V -> State V -> State V
  act_zero : ∀ (V : S.category) (p : State V), act V 0 p = p
  act_add : ∀ (V : S.category) (x y : P.atomData.SupportedWord V) (p : State V),
      act V (x + y) p = act V x (act V y p)
  act_restrict : ∀ {V' V : S.category} (f : V' ⟶ V)
      (x : P.atomData.SupportedWord V) (p : State V),
      restrictState f (act V x p) =
        act V' (P.atomData.wordRestrict f x) (restrictState f p)
  relation_sound : ∀ V : S.category, IsIntersectionCtx 𝒰 V ->
      ∀ x ∈ P.relSpan V, ∀ p : State V, act V x p = p
  stabilizer_complete : ∀ V : S.category, IsIntersectionCtx 𝒰 V ->
      ∀ (p : State V) (x : P.atomData.SupportedWord V),
        act V x p = p -> x ∈ P.relSpan V
  transitive : ∀ V : S.category, IsIntersectionCtx 𝒰 V ->
      ∀ p q : State V, ∃ x : P.atomData.SupportedWord V, q = act V x p

/-- X.定義4.2(定理1.1 入力5b): selected local repair atlas。 -/
structure SemanticRepairAtlas {P : SemanticRepairPresentation.{u, v} S R}
    {𝒰 : MonomorphicOrderedCover S}
    (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰) where
  localRepair : ∀ i : 𝒰.Index, Psem.State (𝒰.chart i)

namespace AffineSemanticRepairSystem

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {𝒰 : MonomorphicOrderedCover S}
variable (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰)

/--
X.定義4.1: relation soundness により作用は `M_sem` の作用へ降りる
(intersection context 上)。
-/
def mact (σ : IntersectionIndex 𝒰) (m : P.MSem σ.ctx)
    (p : Psem.State σ.ctx) : Psem.State σ.ctx :=
  Quotient.liftOn m (fun x => Psem.act σ.ctx x p)
    (by
      intro a b hab
      have hd : -a + b ∈ P.relSpan σ.ctx := QuotientAddGroup.leftRel_apply.mp hab
      show Psem.act σ.ctx a p = Psem.act σ.ctx b p
      have hb : b = a + (-a + b) := by abel
      rw [hb, Psem.act_add,
        Psem.relation_sound σ.ctx ⟨σ, rfl⟩ (-a + b) hd p])

@[simp]
theorem mact_mk (σ : IntersectionIndex 𝒰) (x : P.atomData.SupportedWord σ.ctx)
    (p : Psem.State σ.ctx) :
    Psem.mact σ (P.mSemMk σ.ctx x) p = Psem.act σ.ctx x p :=
  rfl

theorem mact_zero (σ : IntersectionIndex 𝒰) (p : Psem.State σ.ctx) :
    Psem.mact σ 0 p = p := by
  show Psem.act σ.ctx 0 p = p
  exact Psem.act_zero σ.ctx p

theorem mact_add (σ : IntersectionIndex 𝒰) (m m' : P.MSem σ.ctx)
    (p : Psem.State σ.ctx) :
    Psem.mact σ (m + m') p = Psem.mact σ m (Psem.mact σ m' p) := by
  refine QuotientAddGroup.induction_on m ?_
  intro a
  refine QuotientAddGroup.induction_on m' ?_
  intro b
  show Psem.act σ.ctx (a + b) p = Psem.act σ.ctx a (Psem.act σ.ctx b p)
  exact Psem.act_add σ.ctx a b p

theorem mact_restrict {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    (m : P.MSem τ.ctx) (p : Psem.State τ.ctx) :
    Psem.restrictState f.hom (Psem.mact τ m p) =
      Psem.mact σ (P.mSemRestrict f.hom m) (Psem.restrictState f.hom p) := by
  refine QuotientAddGroup.induction_on m ?_
  intro a
  show Psem.restrictState f.hom (Psem.act τ.ctx a p) =
    Psem.act σ.ctx (P.atomData.wordRestrict f.hom a)
      (Psem.restrictState f.hom p)
  exact Psem.act_restrict f.hom a p

/-- X.定義4.1: stabilizer completeness により `M_sem` 作用は free である(導出)。 -/
theorem mact_free (σ : IntersectionIndex 𝒰) (p : Psem.State σ.ctx)
    (m : P.MSem σ.ctx) (h : Psem.mact σ m p = p) : m = 0 := by
  revert h
  refine QuotientAddGroup.induction_on m ?_
  intro a ha
  have hact : Psem.act σ.ctx a p = p := ha
  have hmem : a ∈ P.relSpan σ.ctx :=
    Psem.stabilizer_complete σ.ctx ⟨σ, rfl⟩ p a hact
  exact (QuotientAddGroup.eq_zero_iff a).mpr hmem

/-- X.定義4.1: local transitivity により `M_sem` 作用は transitive である(導出)。 -/
theorem mact_transitive (σ : IntersectionIndex 𝒰)
    (p q : Psem.State σ.ctx) : ∃ m : P.MSem σ.ctx, q = Psem.mact σ m p := by
  rcases Psem.transitive σ.ctx ⟨σ, rfl⟩ p q with ⟨x, hx⟩
  exact ⟨P.mSemMk σ.ctx x, by rw [mact_mk]; exact hx⟩

/--
X.定義4.1 注記: semantic faithfulness `x + p = y + p → x = y` は
relation と作用から導かれる定理である(仮定 field ではない)。
-/
theorem mact_faithful (σ : IntersectionIndex 𝒰) (p : Psem.State σ.ctx)
    {m m' : P.MSem σ.ctx} (h : Psem.mact σ m p = Psem.mact σ m' p) :
    m = m' := by
  have h2 : Psem.mact σ (-m' + m) p = p := by
    rw [Psem.mact_add, h, ← Psem.mact_add, neg_add_cancel, Psem.mact_zero]
  have := Psem.mact_free σ p (-m' + m) h2
  have h3 : m = m' + (-m' + m) := by abel
  rw [h3, this, add_zero]

/--
X.定義4.1 の帰結: 降下した `M_sem` 作用は intersection 上の affine
local-state system(`AffineCoefficientLiftSystem`)をなす。
generic residual engine をこの instance で使う。
-/
def toLiftSystem :
    AffineCoefficientLiftSystem.{u, v, x}
      (P.mSemPresheaf.onIntersections 𝒰) where
  State := Psem.State
  restrictState := Psem.restrictState
  restrictState_id := Psem.restrictState_id
  restrictState_comp := Psem.restrictState_comp
  act := Psem.mact
  act_zero := Psem.mact_zero
  act_add σ m m' p := (Psem.mact_add σ m m' p)
  act_restrict f m p := Psem.mact_restrict f m p
  free σ p m := Psem.mact_free σ p m
  transitive := Psem.mact_transitive

end AffineSemanticRepairSystem

namespace SemanticRepairAtlas

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {𝒰 : MonomorphicOrderedCover S}
variable {Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰}

/-- semantic atlas の generic engine 用の読み。 -/
def toLiftAtlas (atlas : SemanticRepairAtlas Psem) :
    CoefficientLiftAtlas Psem.toLiftSystem :=
  ⟨atlas.localRepair⟩

/-- X.定義4.2: atlas の差から生成される semantic residual cochain `r_sem`。 -/
def semanticResidual (atlas : SemanticRepairAtlas Psem) :
    Cochain1 (P.mSemPresheaf.onIntersections 𝒰) :=
  atlas.toLiftAtlas.residual

/-- X.補題4.3: `δ¹ r_sem = 0`。 -/
theorem semanticResidual_cocycle (atlas : SemanticRepairAtlas Psem) :
    delta1 (P.mSemPresheaf.onIntersections 𝒰) atlas.semanticResidual = 0 :=
  atlas.toLiftAtlas.residual_cocycle

/-- X.定理4.4(cochain 水準): atlas 取り替えは `r_sem` を `δ⁰`-像だけ動かす。 -/
theorem semanticResidual_choice (atlas atlas' : SemanticRepairAtlas Psem) :
    atlas'.semanticResidual =
      atlas.semanticResidual +
        delta0 (P.mSemPresheaf.onIntersections 𝒰)
          (atlas.toLiftAtlas.gauge atlas'.toLiftAtlas) :=
  atlas.toLiftAtlas.residual_choice atlas'.toLiftAtlas

/-- X.定理4.4: 生成 residual class `[r_sem] ∈ H¹_sem(𝒰)`。 -/
def semanticResidualClass (atlas : SemanticRepairAtlas Psem) :
    P.SemanticH1 𝒰 :=
  atlas.toLiftAtlas.residualClass

/-- X.定理4.4: `[r_sem]` は local atlas の選択に依存しない。 -/
theorem semanticResidualClass_choice_independent
    (atlas atlas' : SemanticRepairAtlas Psem) :
    atlas'.semanticResidualClass = atlas.semanticResidualClass :=
  atlas.toLiftAtlas.residualClass_choice_independent atlas'.toLiftAtlas

/-- X.系4.5(1⟺2): `[r_sem] = 0` と `r_sem = δ⁰ a` の同値。 -/
theorem semanticResidualClass_isZero_iff_coboundary
    (atlas : SemanticRepairAtlas Psem) :
    (P.semanticComplex 𝒰).H1IsZero atlas.semanticResidualClass ↔
      ∃ b : Cochain0 (P.mSemPresheaf.onIntersections 𝒰),
        atlas.semanticResidual =
          delta0 (P.mSemPresheaf.onIntersections 𝒰) b :=
  atlas.toLiftAtlas.residualClass_isZero_iff_coboundary

/-- X.系4.5(1⟺3): `[r_sem] = 0` と corrected local repairs の
全 kept pairwise overlap 上の一致の同値。 -/
theorem semanticResidualClass_isZero_iff_matching_correction
    (atlas : SemanticRepairAtlas Psem) :
    (P.semanticComplex 𝒰).H1IsZero atlas.semanticResidualClass ↔
      ∃ b : Cochain0 (P.mSemPresheaf.onIntersections 𝒰),
        (atlas.toLiftAtlas.corrected b).MatchingOnKeptPairs :=
  atlas.toLiftAtlas.residualClass_isZero_iff_matching_correction

end SemanticRepairAtlas

end Saga
end SemanticRepair
end AAT.AG
