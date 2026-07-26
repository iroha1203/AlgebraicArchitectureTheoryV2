import Formal.AG.SemanticRepair.Saga.TrueSheafDescent
import Formal.AG.SemanticRepair.Saga.CircleWitness
import Formal.Util.AssertStandardAxioms

/-!
# Issue #3803 (C7.5): zero-class descent witness on the four-chart circle

This file constructs the zero-class dual of the C7 circle witness: the same
Boolean-lattice 4-cycle context geometry, but with the **zero twist** and a
non-uniform local atlas `(1, 0, 0, 0)`, so both generated residual cochains
are not identically zero while their classes vanish, and the §8 true-sheaf
descent conclusions fire on an actual global repair.

Role separation against C7 (`CircleWitness`): C7 fixes the nonzero-class side
(`[r_sem] ≠ 0`, obstruction transfer; it does not construct a
`TopologicalMonomorphicCover`); this file fixes the zero-class side
(`[r_sem] = 0`, actual descent) and does not re-implement the C7 non-identity
comparison instance or negative conditions.

The three previously statement-only surfaces fired here (PR #3801 review):

1. **Theorem 8.2 / Corollary 8.3 nonvacuity**: `descentSite` selects coverage
   requirements whose required-support clause rules out the empty admissible
   family, so the generated topology is classifiable
   (`descent_topology_classify`) and the Definition 8.1 sheaf condition
   becomes satisfiable and is proved on the whole topology for both state
   presheaves; the 4-chart cover is realized as an admissible family and
   `mem_topology` is constructed (`descentTopologicalCover`).
2. **`SagaEquationPacket.ofProduction` concrete instance**: `descentPacket`
   is assembled through the production constructor; its equation-side fields
   are `SupportAtomEquationSelection.realization` and
   `LiftFiberData.equationLiftSystem` applied to concrete data (#3734 route).
3. **Definition 5.3 typical-example nondegenerate firing**:
   `descentLiftFiber` carries the nonzero base reading `B_E = F₂`, `b ≡ 1`
   (`descentLiftFiber_base_ne_zero`), the selected base reading genuinely
   constrains the state fiber — the fiber is nonempty and the zero section
   of `L_E` is not a state (`descentLiftFiber_state_nonempty`,
   `descentLiftFiber_zero_not_in_fiber`) — and the generated equation
   residual cochain is not identically zero while its class is a coboundary
   (`descent_equationResidual_ne_zero`,
   `descent_equationResidualClass_isZero`).

Context-lattice, equation-system, occurrence and coefficient computations are
reused term-level from `CircleWitness` (they are site-independent or
definitionally transferable); only the coverage requirements, the untwisted
state systems, the production fiber, and the descent theorems are new.

Implementation notes (`lean_quality_standard.md` §2.5 申告):

(i) **coverage requirements の役割**: C7 の all-`False` requirements の下でも
任意の family は admissible であり(可視性条件はすべて空虚、
`boundaryVisibleOn` は `True`)、4-chart cover sieve 自体は C7 site の
topology にも入る。しかし **空 family も admissible** になるため底 sieve が
全対象の covering sieve となり、2値の状態 presheaf に対する X.定義8.1 条件1
(sheaf condition)が原理的に充足不能になる。`descentRequirements` の
required-support 条項は admissible family に4 chart patch を強制することで
空 family を排除し、条件1を成立可能にするためのものである(条件3 の
topology 所属のためではない)。`supportVisibleOn` を context の**等号**で
定義するのは、admissible family の patch 集合を分類可能にする
target-fitting であり、`FiniteModel` の Atom support の観測とは独立の
selected datum である。C7 requirements 側の観察は named 化してある:
空 family の admissibility は `circleEmptyCoverageFamily`、底 sieve の
covering 性は `circle_bot_mem_topology`、その帰結としての切断の
subsingleton 強制と2値 presheaf の充足不能性は
`circle_sheafCondition_subsingleton` / `circle_constant_not_sheafCondition`。

(ii) **twist の移動**: C7 は restriction に twist `t = (1,0,0,0)` を置き
atlas を零に取った(→ 非零 class)。本 witness は restriction を零 twist
(kept 上で値恒等)にし、同じ `(1,0,0,0)` を atlas 値 `atlasVal` へ移した
(→ residual は非恒等零だが構成的に coboundary)。両者は同じ 4-cycle 上の
双対な selected data である。零 twist の帰結として、この状態系では
**任意の** atlas の residual class が零になる
(`descent_every_atlas_residualClass_isZero` — atlas 選択が買っているのは
cochain の非零性だけ)。atlas 独立性の一般化を named するのは semantic 側
のみで、equation 側は選択 atlas の class 零
(`descent_equationResidualClass_isZero`)を named する。一方で複体の
`H¹` 自体は 4-cycle の edge sum により非自明であり
(named witness: `descent_semanticH1_nontrivial`)、class 零は複体の
自明性によるものではない。

(iii) **lift fiber の分裂性**: `descentLiftFiber` の short exact sequence
`0 → Q_E → Q_E × B_E → B_E → 0` は**分裂積**であり(`incl = inl`,
`proj = snd`)、exactness / injectivity は積の構造から自明に充足される。
非零 base reading `b ≡ 1` は lift 状態を affine fiber
`{(q, 1)}`(`Q_E`-torsor)へ制限し、lift problem の選択規律を発火させる。
residual が `Q_E` 値であることは一般的性質(同じ base reading の2つの
lift の差は `Q_E` に入る)だが、一般の定義5.3 典型例では `[r_E]` は
まさに base reading の大域 lift 可能性の障害であり、base reading は
obstruction が測る当のものである。**本 fixture では**拡大が分裂している
ため base reading の obstruction への寄与が消える(`(0, b)` が大域切断を
与える)— class 零の一部は分裂性の帰結である。
`descentLiftFiber_zero_not_in_fiber`
は `descentLiftFiber_base_ne_zero` と同内容(`(0 : F₂) ≠ 1`)の fiber 側の
言い換えであり、独立の証拠ではない。非分裂拡大(例: `ℤ/4` 型)は生成
`Q_E` の modulus 設計の全面改修を要し、定義5.3 典型例の発火に非分裂性は
要求されないため退けた。**非分裂性は主張しない**。

(iv) **`Nonempty P_sem(W)` の自明性**: `descentSpec` は全 context に零状態
`⟨0⟩` を与えるため、`Nonempty (GlobalRepair …)` は descent 論証と独立に
構成から真である(零 class fixture では定理8.2 により大域状態の存在自体は
必然)。したがって「修復の実在」の非自明な内容は bare な `Nonempty` では
なく、系4.5 correction による corrected family の**一意な** amalgamation
(`descent_globalRepair_of_h1IsZero`)と零 class 同値
(`descent_globalRepair_nonempty_iff`)が担う。総括
`descent_zero_class_repair` はこの構成的形を成分に取る。

(v) **cover 補題の再証明**: `descentCover` は `circleCover` と同一引数の
`ofOverlapPackage` 適用だが、`MonomorphicOrderedCover` の site parameter が
異なり(`descentSite` と `CircleWitness.site` は requirements field が
異なるため defeq でない)、C7 の cover 水準補題は型不一致で `exact` 再利用
できない。そのため同形の証明を descent 側で再演している。
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga
namespace DescentWitness

open CategoryTheory
open Opposite
open CircleWitness

/-! ## Coverage requirements admitting the four-chart cover -/

/-- C7.5: chart ごとの selected marker atom(chart 可視性を coverage
requirement として書くための単射な割り当て)。 -/
def chartAtom : Fin 4 -> FiniteModel.FiniteAtom
  | 0 => FiniteModel.FiniteAtom.componentA
  | 1 => FiniteModel.FiniteAtom.componentB
  | 2 => FiniteModel.FiniteAtom.dependsAB
  | 3 => FiniteModel.FiniteAtom.dependsBC

theorem chartAtom_injective : Function.Injective chartAtom := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/--
C7.5: descent witness の coverage requirements。required support は4つの
chart marker atom で、その可視性は対応する chart context でのみ成立する。
これにより admissible family は4 chart をすべて patch に含むことを強制され
(特に**空 family が admissible でなくなり**、底 sieve が covering sieve に
なることを防ぐ)、生成 topology は `descent_topology_classify` の形に分類
できて2値状態 presheaf の sheaf condition が成立可能になる。C7 の
all-`False` requirements では任意の family(空 family を含む)が admissible
であり、底 sieve が全対象を覆うため X.定義8.1 条件1 が充足不能だった —
requirements 新設の役割は条件1の成立可能化であって、cover sieve の
topology 所属(条件3)自体は C7 site でも成立する(module header の
Implementation notes (i) を見よ)。
-/
def descentRequirements :
    Site.CoverageRequirements FiniteModel.object circleEquationSystem
      FiniteModel.signature where
  requiredSupport atom := ∃ i : Fin 4, atom = chartAtom i
  requiredEquationCoordinate _ := False
  selectedViolationWitness _ := False
  requiredAxis _ := False
  supportVisibleOn W atom := ∃ i : Fin 4, atom = chartAtom i ∧ W = context {i}
  equationCoordinateVisibleOn _ _ := False
  violationWitnessVisibleOn _ _ := False
  axisReadableOn _ _ := False
  boundaryVisibleOn _ _ := True

/--
C7.5: 零 class descent witness の AAT site。context preorder・equation
system・signature・overlap は C7 circle witness と同一の selected data を
共有し、coverage requirements だけを descent 用に選ぶ。
-/
noncomputable def descentSite : Site.AATSite FiniteModel.object where
  contextPreorder := CircleWitness.contextPreorder
  equationSystem := circleEquationSystem
  signature := FiniteModel.signature
  requirements := descentRequirements
  overlap := contextOverlap

/-- C7.5: descent site 上の monomorphic 4-cycle cover(C7 と同じ chart・
同じ kept 指定。base `W = context ∅`、chart `W_i = context {i}`)。 -/
@[reducible] noncomputable def descentCover : MonomorphicOrderedCover descentSite :=
  MonomorphicOrderedCover.ofOverlapPackage base (Fin 4) inferInstance
    chartObj chartInclusion
    (fun i => mono_of_contextHom (chartInclusion i))
    (fun i j => ({i, j} : ContextIndex) ∉ keptSets)
    (fun _ _ _ => False)

/-- descent cover の pairwise overlap は selected union context。 -/
theorem descentCover_pairCtx (i j : Fin 4) :
    descentCover.pairCtx i j =
      Site.ContextCategoryObject.of CircleWitness.contextPreorder
        (context ({i} ∪ {j})) := by
  show Site.ContextCategoryObject.of CircleWitness.contextPreorder
      (overlapContext (context ∅) (context {i}) (context {j})) = _
  rw [overlapContext_context]

/-- descent cover の pairwise overlap architecture context。 -/
theorem descentCover_pairCtx_ctx (i j : Fin 4) :
    (descentCover.pairCtx i j).ctx = context ({i} ∪ {j}) :=
  congrArg Site.ContextCategoryObject.ctx (descentCover_pairCtx i j)

/-- descent cover の triple overlap architecture context。 -/
theorem descentCover_tripleCtx_ctx (i j k : Fin 4) :
    (descentCover.tripleCtx i j k).ctx = context (({i} ∪ {j}) ∪ {k}) := by
  show (overlapContext (context ∅)
    (overlapContext (context ∅) (context {i}) (context {j}))
    (context {k})) = _
  rw [overlapContext_context, overlapContext_context]

/-- descent cover の kept pair はちょうど4-cycle の隣接辺。 -/
theorem descentCover_keptPair_mem (p : descentCover.KeptPair) :
    ({p.fst, p.snd} : ContextIndex) ∈ keptSets := by
  by_contra h
  exact p.kept h

/-- chart context は kept。 -/
theorem chartObj_keptCtx (i : Fin 4) : KeptCtx (chartObj i).ctx := by
  refine ⟨recognized_context _, ?_⟩
  rw [show (chartObj i).ctx = context {i} from rfl, indexOf_context]
  exact singleton_mem_keptSets i

/-- base context は kept(空 index は keptSets に属する)。 -/
theorem base_keptCtx : KeptCtx base.ctx := by
  refine ⟨recognized_context _, ?_⟩
  rw [show base.ctx = context ∅ from rfl, indexOf_context]
  decide

/-- descent cover の intersection-diagram context はすべて kept。 -/
theorem descent_keptCtx_of_intersection (σ : IntersectionIndex descentCover) :
    KeptCtx σ.ctx.ctx := by
  cases σ with
  | chart i => exact chartObj_keptCtx i
  | pair p =>
    show KeptCtx (descentCover.pairCtx p.fst p.snd).ctx
    rw [descentCover_pairCtx_ctx]
    refine ⟨recognized_context _, ?_⟩
    rw [indexOf_context, singleton_union_eq_pair]
    exact descentCover_keptPair_mem p
  | triple t =>
    exact absurd (by
      rcases exists_omitted_pair_of_triple t.fst t.snd t.trd t.lt₁ t.lt₂ with
        h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))) t.kept

/-- omitted pair の overlap context は kept でない。 -/
theorem descent_pairCtx_not_kept {i j : Fin 4}
    (h : descentCover.omittedPair i j) :
    ¬ KeptCtx (descentCover.pairCtx i j).ctx := by
  intro hk
  rw [descentCover_pairCtx_ctx] at hk
  have hk2 := hk.2
  rw [indexOf_context, singleton_union_eq_pair] at hk2
  exact h hk2

/-- omitted triple の overlap context は kept でない。 -/
theorem descent_tripleCtx_not_kept {i j k : Fin 4}
    (h : descentCover.omittedTriple i j k) :
    ¬ KeptCtx (descentCover.tripleCtx i j k).ctx := by
  intro hk
  rw [descentCover_tripleCtx_ctx] at hk
  have hk2 := hk.2
  rw [indexOf_context] at hk2
  obtain ⟨hij, hik, hjk⟩ := pairs_kept_of_triple_kept i j k hk2
  rcases h with hp | hp | hp | hfalse
  · exact hp hij
  · exact hp hik
  · exact hp hjk
  · exact hfalse

/-! ## The admissible four-chart family and `mem_topology` -/

/-- C7.5: 4-chart cover を descent requirements の admissible family として
構成する(`mem_topology` の生成源)。 -/
noncomputable def descentCoverageFamily :
    Site.AATCoverageFamily descentRequirements contextOverlap base where
  Index := Fin 4
  patch i := context {i}
  inclusion i := Or.inr ⟨{i}, ∅, rfl, rfl, Finset.empty_subset _⟩
  admissible := {
    atomSupportCoverage := by
      rintro atom ⟨i, rfl⟩
      exact ⟨i, i, rfl, rfl⟩
    equationCoordinateCoverage := fun c hc => hc.elim
    violationWitnessCoverage := fun w hw => hw.elim
    signatureAxisCoverage := fun a ha => ha.elim
    boundaryCoverage := fun _ _ => trivial
    nonGeneration := Site.AdmissibleCover.nonGenerating_from_inclusions }

/-- C7.5 AC1: 4-chart cover sieve は生成 topology に属する(実構成)。 -/
theorem descentCover_mem_topology :
    Sieve.generate (Presieve.ofArrows descentCover.chart descentCover.inclusion) ∈
      descentSite.topology base :=
  Site.AATGrothendieckTopology.generate_mem descentCoverageFamily

/-- C7.5 AC1: `mem_topology` を実構成した topological monomorphic cover。 -/
noncomputable def descentTopologicalCover : TopologicalMonomorphicCover descentSite :=
  { descentCover with mem_topology := descentCover_mem_topology }

/-! ## Classification of the generated descent topology -/

/-- thin category: 同じ context を持つ対象は等しい。 -/
theorem descent_obj_ext {X Y : descentSite.category} (h : X.ctx = Y.ctx) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

/-- admissible family の patch 制約: 各 chart marker atom の可視 patch は
対応する chart context に一致し、base より下にある。 -/
theorem descentFamily_patch {X : descentSite.category}
    (F : Site.AATCoverageFamily descentRequirements contextOverlap X)
    (i : Fin 4) :
    ∃ j : F.Index, F.patch j = context {i} := by
  rcases F.admissible.atomSupportCoverage (chartAtom i) ⟨i, rfl⟩ with ⟨j, i', hi', hj⟩
  cases chartAtom_injective hi'
  exact ⟨j, hj⟩

/-- admissible family を持つ base 対象は `context ∅` に限る。 -/
theorem descentFamily_base {X : descentSite.category}
    (F : Site.AATCoverageFamily descentRequirements contextOverlap X) :
    X.ctx = context ∅ := by
  rcases descentFamily_patch F 0 with ⟨j0, hj0⟩
  rcases descentFamily_patch F 1 with ⟨j1, hj1⟩
  have h0 : contextLe (context {0}) X.ctx := by
    have := F.inclusion j0
    rwa [hj0] at this
  have h1 : contextLe (context {1}) X.ctx := by
    have := F.inclusion j1
    rwa [hj1] at this
  rcases h0 with h0 | ⟨s, t, hs, ht, hts⟩
  · rcases h1 with h1 | ⟨s', t', hs', ht', hts'⟩
    · exact absurd (context_injective (h0.trans h1.symm)) (by decide)
    · have hteq : t' = ({0} : ContextIndex) :=
        context_injective (ht'.symm.trans h0.symm)
      have hseq : s' = ({1} : ContextIndex) := context_injective hs'.symm
      rw [hseq, hteq] at hts'
      exact absurd hts' (by decide)
  · rcases h1 with h1 | ⟨s', t', hs', ht', hts'⟩
    · have hteq : t = ({1} : ContextIndex) :=
        context_injective (ht.symm.trans h1.symm)
      have hseq : s = ({0} : ContextIndex) := context_injective hs.symm
      rw [hseq, hteq] at hts
      exact absurd hts (by decide)
    · have htt : t = t' := context_injective (ht.symm.trans ht')
      have hseq : s = ({0} : ContextIndex) := context_injective hs.symm
      have hseq' : s' = ({1} : ContextIndex) := context_injective hs'.symm
      have hempty : t = ∅ := by
        rw [htt] at hts
        rw [hseq] at hts
        rw [hseq'] at hts'
        have : t' ⊆ ({0} : ContextIndex) ∩ ({1} : ContextIndex) :=
          Finset.subset_inter (htt ▸ hts) hts'
      -- {0} ∩ {1} = ∅
        rw [show ({0} : ContextIndex) ∩ ({1} : ContextIndex) = ∅ from by decide,
          Finset.subset_empty] at this
        rw [htt, this]
      rw [ht, hempty]

/--
C7.5: descent topology の分類。base 以外の対象上の covering sieve は `⊤` に
限り、`context ∅` 上の covering sieve は4つの chart arrow をすべて含む。
sheaf condition(`descent_sheafCondition`)はこの分類だけを消費する。
-/
theorem descent_topology_classify {X : descentSite.category} {Sv : Sieve X}
    (h : Sv ∈ descentSite.topology X) :
    Sv = ⊤ ∨ (X.ctx = context ∅ ∧
      ∀ (i : Fin 4) (f : chartObj i ⟶ X), Sv f) := by
  have h' : (Site.admissiblePrecoverage descentRequirements
      contextOverlap).Saturate X Sv := h
  clear h
  induction h' with
  | of X S hS =>
    rcases hS with ⟨F, rfl⟩
    refine Or.inr ⟨descentFamily_base F, ?_⟩
    intro i f
    rcases descentFamily_patch F i with ⟨j, hj⟩
    refine ⟨Site.ContextCategoryObject.of CircleWitness.contextPreorder
      (F.patch j), ?_, homOfLE (F.inclusion j), Presieve.ofArrows.mk j, ?_⟩
    · exact homOfLE (by rw [hj]; exact contextLe_refl _)
    · exact Subsingleton.elim _ _
  | top X => exact Or.inl rfl
  | pullback X S hS Y f ih =>
    rcases ih with rfl | ⟨hX, hcharts⟩
    · exact Or.inl Sieve.pullback_top
    · have hXbase : X = base := descent_obj_ext hX
      subst hXbase
      have hY : Recognized Y.ctx := by
        rcases leOfHom f with hf | ⟨s, t, hs, ht, hts⟩
        · rw [hf]
          exact recognized_context ∅
        · exact ⟨s, hs⟩
      by_cases hYe : indexOf Y.ctx = ∅
      · refine Or.inr ⟨by rw [context_indexOf hY, hYe], ?_⟩
        intro i g
        show S (g ≫ f)
        exact hcharts i (g ≫ f)
      · left
        rw [← Sieve.id_mem_iff_eq_top]
        show S (𝟙 Y ≫ f)
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
        have hle : contextLe Y.ctx (context {i}) := by
          rw [context_indexOf hY]
          exact Or.inr ⟨indexOf Y.ctx, {i}, rfl, rfl,
            Finset.singleton_subset_iff.mpr hi⟩
        have hmem := S.downward_closed (hcharts i (chartInclusion i))
          (homOfLE hle : Y ⟶ chartObj i)
        have heq : (homOfLE hle : Y ⟶ chartObj i) ≫ chartInclusion i =
            𝟙 Y ≫ f := Subsingleton.elim _ _
        rwa [heq] at hmem
  | transitive X S R _hS hR ihS ihR =>
    rcases ihS with rfl | ⟨hX, hcharts⟩
    · have hid : (⊤ : Sieve X) (𝟙 X) := trivial
      have := ihR hid
      rwa [Sieve.pullback_id] at this
    · have hXbase : X = base := descent_obj_ext hX
      subst hXbase
      refine Or.inr ⟨hX, ?_⟩
      intro i f
      have hf : f = chartInclusion i := Subsingleton.elim _ _
      subst hf
      rcases ihR (hcharts i (chartInclusion i)) with htop | ⟨habs, _⟩
      · have hid : (R.pullback (chartInclusion i)) (𝟙 (chartObj i)) := by
          rw [htop]
          trivial
        show R (chartInclusion i)
        have : R (𝟙 (chartObj i) ≫ chartInclusion i) := hid
        rwa [Category.id_comp] at this
      · exfalso
        have : ({i} : ContextIndex) = ∅ := by
          have := context_injective
            ((show (chartObj i).ctx = context {i} from rfl).symm.trans habs)
          exact this
        exact absurd this (Finset.singleton_ne_empty i)

/-! ## Why the all-`False` C7 requirements cannot serve §8

Implementation notes (i) の観察の named 化(査読 Lean B lane 第2巡 N1):
C7 requirements の下では空 family が admissible で、底 sieve が covering
sieve になり、2値 presheaf は sheaf condition を満たし得ない。 -/

/-- C7 の all-`False` requirements の下では空 family も admissible である
(可視性条件はすべて空虚、boundary 条項は添字が空で空虚)。 -/
noncomputable def circleEmptyCoverageFamily (X : CircleWitness.site.category) :
    Site.AATCoverageFamily circleRequirements contextOverlap X where
  Index := PEmpty
  patch i := i.elim
  inclusion i := i.elim
  admissible := {
    atomSupportCoverage := fun _ h => h.elim
    equationCoordinateCoverage := fun _ h => h.elim
    violationWitnessCoverage := fun _ h => h.elim
    signatureAxisCoverage := fun _ h => h.elim
    boundaryCoverage := fun i => i.elim
    nonGeneration := fun i => i.elim }

/-- 空 family の生成 sieve は底 sieve。 -/
theorem circleEmpty_generate_eq_bot (X : CircleWitness.site.category) :
    Sieve.generate (circleEmptyCoverageFamily X).presieve = ⊥ := by
  ext Z f
  constructor
  · rintro ⟨W, g, hWX, hmem, _⟩
    cases hmem with
    | mk i => exact i.elim
  · intro hf
    exact hf.elim

/-- C7 site では底 sieve が全対象の covering sieve である。 -/
theorem circle_bot_mem_topology (X : CircleWitness.site.category) :
    (⊥ : Sieve X) ∈ CircleWitness.site.topology X := by
  have h := Site.AATGrothendieckTopology.generate_mem (circleEmptyCoverageFamily X)
  rwa [circleEmpty_generate_eq_bot X] at h

/-- 底 sieve が covering なら、C7 topology 上の sheaf の切断は全対象で
subsingleton になる。 -/
theorem circle_sheafCondition_subsingleton
    (F : Site.AATPresheaf CircleWitness.site)
    (h : Site.AATSheafCondition CircleWitness.site F)
    (X : CircleWitness.site.category) :
    Subsingleton (F.obj (op X)) := by
  have hbot := h (⊥ : Sieve X) (circle_bot_mem_topology X)
  rw [Site.AATSheafConditionFor] at hbot
  obtain ⟨t, _, huniq⟩ := hbot
    (by intro Y f hf; exact hf.elim)
    (by intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hc; exact h₁.elim)
  refine ⟨fun a b => ?_⟩
  rw [huniq a (by intro Y f hf; exact hf.elim),
    huniq b (by intro Y f hf; exact hf.elim)]

/-- Implementation notes (i) の「2値状態 presheaf」の最小代表(定数 `F₂`)。 -/
def circleConstantPresheaf : Site.AATPresheaf CircleWitness.site where
  obj _ := ZMod 2
  map _ := id

/-- 査読対応(Lean B lane 第2巡 N1): C7 の all-`False` requirements の下では
2値の presheaf は sheaf condition を満たし得ない — X.定義8.1 条件1 の
充足不能性の named witness(`descentRequirements` 新設の根拠)。 -/
theorem circle_constant_not_sheafCondition :
    ¬ Site.AATSheafCondition CircleWitness.site circleConstantPresheaf := by
  intro h
  have hsub := circle_sheafCondition_subsingleton circleConstantPresheaf h base
  have h01 : (0 : ZMod 2) = 1 := hsub.allEq (0 : ZMod 2) (1 : ZMod 2)
  exact absurd h01 (by decide)

/-! ## Presentation layer (term-level reuse of the C7 circle presentation) -/

/-- descent site の occurrence reading。restriction 関数と各則は C7 の
`CircleWitness.occurrenceReading` と項レベルで共有する(site は coverage
requirements しか違わないため、occurrence 層は definitionally 転用できる)。 -/
noncomputable def descentOccurrenceReading : AtomOccurrenceReading descentSite where
  occRestrict f o := occRestrictFun f o
  occRestrict_id := CircleWitness.occurrenceReading.occRestrict_id
  occRestrict_comp := CircleWitness.occurrenceReading.occRestrict_comp
  occRestrict_atom := CircleWitness.occurrenceReading.occRestrict_atom

/-- descent site の semantic atom data(B.9.2 と同一の1-Atom 構成)。 -/
noncomputable def descentAtomData :
    SemanticAtomData descentSite descentOccurrenceReading where
  SemanticAtom := CircleWitness.semanticAtomData.SemanticAtom
  restrictAtom := CircleWitness.semanticAtomData.restrictAtom
  restrictAtom_id := CircleWitness.semanticAtomData.restrictAtom_id
  restrictAtom_comp := CircleWitness.semanticAtomData.restrictAtom_comp
  projection := CircleWitness.semanticAtomData.projection
  projection_natural := CircleWitness.semanticAtomData.projection_natural
  supported := CircleWitness.semanticAtomData.supported
  supported_restrict := CircleWitness.semanticAtomData.supported_restrict

/-- descent site の semantic repair presentation(`M_sem = ℤ[σ]/(2σ)`、
relation set は C7 の `relSet` と共有)。 -/
noncomputable def descentPresentation :
    SemanticRepairPresentation descentSite descentOccurrenceReading where
  atomData := descentAtomData
  rel := relSet
  rel_restrict := CircleWitness.presentation.rel_restrict

/-! ## The untwisted local state carrier -/

/-- C7.5: descent 状態の membership。kept context では `F₂` 全域(base を
含む)、それ以外では零のみ。C7 の `stateSpec` と異なり base 状態は空でない
(零 class fixture では定理8.2 により大域状態の存在が必然のため)。この
構成の帰結として**任意の context で零状態 `⟨0⟩` が存在し、
`Nonempty (GlobalRepair …)` は descent 論証と独立に真**である — 修復の
実在の非自明な内容は corrected family の一意 amalgamation
(`descent_globalRepair_of_h1IsZero`)が担う(module header の
Implementation notes (iv))。 -/
def descentSpec (W : Site.ArchCtx FiniteModel.object) (x : ZMod 2) : Prop :=
  KeptCtx W ∨ x = 0

/-- C7.5: descent local state carrier。 -/
def DescentState (W : Site.ArchCtx FiniteModel.object) : Type :=
  {x : ZMod 2 // descentSpec W x}

/-- kept でない context の状態値は零。 -/
theorem descentState_val_eq_zero {W : Site.ArchCtx FiniteModel.object}
    (h : ¬ KeptCtx W) (e : DescentState W) : e.1 = 0 :=
  e.2.resolve_left h

/-- kept でない context の状態は subsingleton。 -/
theorem descentState_subsingleton {W : Site.ArchCtx FiniteModel.object}
    (h : ¬ KeptCtx W) : Subsingleton (DescentState W) :=
  ⟨fun e e' => Subtype.ext (by
    rw [descentState_val_eq_zero h e, descentState_val_eq_zero h e'])⟩

/-- C7.5: 零 twist state restriction。kept target では値恒等、それ以外は零
(C7 の `stateRestrict` の twist 成分を恒等的に零に置いた双対)。 -/
noncomputable def descentRestrict {V' V : descentSite.category} (_f : V' ⟶ V)
    (e : DescentState V.ctx) : DescentState V'.ctx := by
  classical
  exact if h' : KeptCtx V'.ctx then ⟨e.1, Or.inl h'⟩ else ⟨0, Or.inr rfl⟩

theorem descentRestrict_val_of_kept {V' V : descentSite.category} (f : V' ⟶ V)
    (e : DescentState V.ctx) (h' : KeptCtx V'.ctx) :
    (descentRestrict f e).1 = e.1 := by
  rw [descentRestrict]
  split
  · rfl
  · exact absurd h' (by assumption)

theorem descentRestrict_id (V : descentSite.category) (e : DescentState V.ctx) :
    descentRestrict (𝟙 V) e = e := by
  by_cases h : KeptCtx V.ctx
  · exact Subtype.ext (descentRestrict_val_of_kept _ e h)
  · haveI := descentState_subsingleton h
    exact Subsingleton.elim _ _

theorem descentRestrict_comp {V'' V' V : descentSite.category}
    (f : V'' ⟶ V') (g : V' ⟶ V) (e : DescentState V.ctx) :
    descentRestrict (f ≫ g) e = descentRestrict f (descentRestrict g e) := by
  by_cases h'' : KeptCtx V''.ctx
  · have h' : KeptCtx V'.ctx := keptCtx_of_le (leOfHom f) h''
    apply Subtype.ext
    rw [descentRestrict_val_of_kept _ e h'',
      descentRestrict_val_of_kept _ _ h'',
      descentRestrict_val_of_kept _ e h']
  · haveI := descentState_subsingleton h''
    exact Subsingleton.elim _ _

/-! ## The semantic repair system with the untwisted states -/

/-- C7.5: kept context 上の word evaluation による semantic 作用。 -/
noncomputable def descentAct (V : descentSite.category)
    (w : descentAtomData.SupportedWord V) (e : DescentState V.ctx) :
    DescentState V.ctx := by
  classical
  exact if h : KeptCtx V.ctx then
    ⟨e.1 + ((evalWord V h.1 w : ℤ) : ZMod 2), Or.inl h⟩
  else e

theorem descentAct_of_kept (V : descentSite.category)
    (w : descentAtomData.SupportedWord V) (e : DescentState V.ctx)
    (h : KeptCtx V.ctx) :
    descentAct V w e = ⟨e.1 + ((evalWord V h.1 w : ℤ) : ZMod 2), Or.inl h⟩ := by
  rw [descentAct]
  split
  · rfl
  · exact absurd h (by assumption)

theorem descentAct_val_of_kept (V : descentSite.category)
    (w : descentAtomData.SupportedWord V) (e : DescentState V.ctx)
    (h : KeptCtx V.ctx) :
    (descentAct V w e).1 = e.1 + ((evalWord V h.1 w : ℤ) : ZMod 2) := by
  rw [descentAct_of_kept V w e h]

theorem descentAct_of_not_kept (V : descentSite.category)
    (w : descentAtomData.SupportedWord V) (e : DescentState V.ctx)
    (h : ¬ KeptCtx V.ctx) : descentAct V w e = e := by
  rw [descentAct]
  split
  · exact absurd (by assumption) h
  · rfl

/-- C7.5: 零 twist の semantic local repair system `P_sem`(kept context 上で
`F₂` 全域、base に大域状態が存在する)。 -/
noncomputable def descentRepairSystem :
    AffineSemanticRepairSystem descentPresentation descentCover where
  State V := DescentState V.ctx
  restrictState f e := descentRestrict f e
  restrictState_id := descentRestrict_id
  restrictState_comp := descentRestrict_comp
  act := descentAct
  act_zero V e := by
    by_cases h : KeptCtx V.ctx
    · apply Subtype.ext
      rw [descentAct_val_of_kept V 0 e h]
      simp
    · rw [descentAct_of_not_kept V 0 e h]
  act_add V x y e := by
    by_cases h : KeptCtx V.ctx
    · apply Subtype.ext
      rw [descentAct_val_of_kept V (x + y) e h, descentAct_val_of_kept V x _ h,
        descentAct_val_of_kept V y e h, map_add]
      push_cast
      ring
    · rw [descentAct_of_not_kept V (x + y) e h, descentAct_of_not_kept V y e h,
        descentAct_of_not_kept V x e h]
  act_restrict {V' V} f x e := by
    by_cases h' : KeptCtx V'.ctx
    · have h : KeptCtx V.ctx := keptCtx_of_le (leOfHom f) h'
      apply Subtype.ext
      rw [descentRestrict_val_of_kept f _ h', descentAct_val_of_kept V x e h,
        descentAct_val_of_kept V' _ _ h', descentRestrict_val_of_kept f e h',
        show evalWord V' h'.1 ((descentPresentation.atomData.wordRestrict f) x) =
            evalWord V h.1 x from
          evalWord_wordRestrict f h.1 h'.1 x]
    · haveI := descentState_subsingleton h'
      exact Subsingleton.elim _ _
  relation_sound V hV x hx e := by
    obtain ⟨σ, rfl⟩ := hV
    have hkept : KeptCtx σ.ctx.ctx := descent_keptCtx_of_intersection σ
    apply Subtype.ext
    rw [descentAct_val_of_kept _ x e hkept]
    obtain ⟨k, hk⟩ := evalWord_relSpan_even σ.ctx hkept hx
    rw [show evalWord σ.ctx hkept.1 x = 2 * k from hk, Int.cast_mul,
      show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul, add_zero]
  stabilizer_complete V hV e x hx := by
    obtain ⟨σ, rfl⟩ := hV
    have hkept : KeptCtx σ.ctx.ctx := descent_keptCtx_of_intersection σ
    have hval := congrArg Subtype.val hx
    rw [descentAct_val_of_kept _ x e hkept] at hval
    have hcast : ((evalWord σ.ctx hkept.1 x : ℤ) : ZMod 2) = 0 := by
      have := add_left_cancel (a := e.1)
        (b := ((evalWord σ.ctx hkept.1 x : ℤ) : ZMod 2)) (c := 0)
      apply this
      rw [add_zero]
      exact hval
    have heven : (2 : ℤ) ∣ evalWord σ.ctx hkept.1 x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hcast
    rw [word_eq_single σ.ctx hkept.1 x]
    exact single_mem_relSpan_of_even σ.ctx hkept _ heven
  transitive V hV e e' := by
    obtain ⟨σ, rfl⟩ := hV
    have hkept : KeptCtx σ.ctx.ctx := descent_keptCtx_of_intersection σ
    refine ⟨Finsupp.single (sigma σ.ctx hkept.1)
      (((e'.1 - e.1).val : ℕ) : ℤ), ?_⟩
    apply Subtype.ext
    rw [descentAct_val_of_kept _ _ e hkept, evalWord_single, zmod_two_cast_val]
    ring

/-! ## The `(1,0,0,0)` atlas and the zero semantic residual class -/

/-- C7.5: atlas 値 `a = (1, 0, 0, 0)`(C7 の twist datum `t = (1,0,0,0)` の
零 class 側の双対: twist を状態でなく atlas に移す)。 -/
def atlasVal (i : Fin 4) : ZMod 2 :=
  if i = 0 then 1 else 0

/-- C7.5: 非一様 local repair atlas `p_i = a_i`。 -/
noncomputable def descentRepairAtlas : SemanticRepairAtlas descentRepairSystem where
  localRepair i := ⟨atlasVal i, Or.inl (chartObj_keptCtx i)⟩

/-- descent presentation の class 写像は circle presentation の class 写像と
定義的に一致する(relation 層を共有しているため)。 -/
theorem descentPresentation_mSemMk_eq (V : descentSite.category)
    (w : descentAtomData.SupportedWord V) :
    descentPresentation.mSemMk V w = CircleWitness.presentation.mSemMk V w :=
  rfl

/-- descent presentation の商 restriction は circle presentation のそれと
定義的に一致する。 -/
theorem descentPresentation_mSemRestrict_eq {V' V : descentSite.category}
    (f : V' ⟶ V) (m : descentPresentation.MSem V) :
    descentPresentation.mSemRestrict f m =
      CircleWitness.presentation.mSemRestrict f m :=
  rfl

/-- descend した `M_sem` 作用の `F₂` 値。 -/
theorem descent_mact_val (σ : IntersectionIndex descentCover)
    (m : descentPresentation.MSem σ.ctx) (e : descentRepairSystem.State σ.ctx) :
    (descentRepairSystem.mact σ m e).1 =
      e.1 + mSemToZMod σ.ctx (descent_keptCtx_of_intersection σ) m := by
  induction m using QuotientAddGroup.induction_on with
  | H w =>
  show (descentRepairSystem.mact σ (descentPresentation.mSemMk σ.ctx w) e).1 =
    e.1 + mSemToZMod σ.ctx (descent_keptCtx_of_intersection σ)
      (descentPresentation.mSemMk σ.ctx w)
  rw [show descentRepairSystem.mact σ (descentPresentation.mSemMk σ.ctx w) e =
      descentRepairSystem.act σ.ctx w e from descentRepairSystem.mact_mk σ w e]
  rw [show (descentRepairSystem.act σ.ctx w e).1 =
      e.1 + ((evalWord σ.ctx (descent_keptCtx_of_intersection σ).1 w : ℤ) :
        ZMod 2) from
    descentAct_val_of_kept σ.ctx w e (descent_keptCtx_of_intersection σ)]
  rfl

/-- kept pair の pair context は kept。 -/
theorem descent_pairCtx_keptCtx (p : descentCover.KeptPair) :
    KeptCtx (descentCover.pairCtx p.fst p.snd).ctx :=
  descent_keptCtx_of_intersection (.pair p)

/-- C7.5: 生成 semantic residual の `F₂` 値は atlas 値の差
`a_{p.snd} - a_{p.fst}`(零 twist なので twist 項は現れない)。 -/
theorem descent_semanticResidual_val (p : descentCover.KeptPair) :
    mSemToZMod (descentCover.pairCtx p.fst p.snd) (descent_pairCtx_keptCtx p)
      (descentRepairAtlas.semanticResidual p) =
    atlasVal p.snd - atlasVal p.fst := by
  have hact := AffineCoefficientLiftSystem.act_diffAt
    (L := descentRepairSystem.toLiftSystem) (.pair p)
    (descentRepairAtlas.toLiftAtlas.leftOn p)
    (descentRepairAtlas.toLiftAtlas.rightOn p)
  have h1 : (descentRepairAtlas.toLiftAtlas.rightOn p).1 =
      (descentRepairAtlas.toLiftAtlas.leftOn p).1 +
        mSemToZMod (descentCover.pairCtx p.fst p.snd) (descent_pairCtx_keptCtx p)
          (descentRepairAtlas.semanticResidual p) := by
    conv_lhs => rw [← hact]
    exact descent_mact_val (.pair p) (descentRepairAtlas.semanticResidual p)
      (descentRepairAtlas.toLiftAtlas.leftOn p)
  have hleft : (descentRepairAtlas.toLiftAtlas.leftOn p).1 = atlasVal p.fst := by
    show (descentRestrict (descentCover.pairFst p.fst p.snd)
        (descentRepairAtlas.localRepair p.fst)).1 = _
    rw [descentRestrict_val_of_kept _ _ (descent_pairCtx_keptCtx p)]
    rfl
  have hright : (descentRepairAtlas.toLiftAtlas.rightOn p).1 = atlasVal p.snd := by
    show (descentRestrict (descentCover.pairSnd p.fst p.snd)
        (descentRepairAtlas.localRepair p.snd)).1 = _
    rw [descentRestrict_val_of_kept _ _ (descent_pairCtx_keptCtx p)]
    rfl
  rw [show mSemToZMod (descentCover.pairCtx p.fst p.snd) (descent_pairCtx_keptCtx p)
      (descentRepairAtlas.semanticResidual p) =
    (descentRepairAtlas.toLiftAtlas.rightOn p).1 -
      (descentRepairAtlas.toLiftAtlas.leftOn p).1 from by rw [h1]; ring]
  rw [hleft, hright]

/-- 4-cycle の隣接辺 `(0, 1)`。 -/
def descentEdge01 : descentCover.KeptPair :=
  ⟨(0 : Fin 4), (1 : Fin 4), by decide, fun h => h (by decide)⟩

/-- C7.5 AC4(semantic 側): residual cochain は恒等的に零ではない
(辺 `(0,1)` で値 `1`)。 -/
theorem descent_semanticResidual_ne_zero :
    descentRepairAtlas.semanticResidual ≠ 0 := by
  intro h
  have hv := congrArg
    (mSemToZMod _ (descent_pairCtx_keptCtx descentEdge01)) (congrFun h descentEdge01)
  rw [descent_semanticResidual_val] at hv
  simp only [Pi.zero_apply, map_zero] at hv
  exact absurd hv (by decide)

/-- C7.5: 補正 0-cochain `b_i = [a_i σ]`(semantic residual を coboundary
として実現する gauge。atlas 値の `M_sem` 読み)。 -/
noncomputable def descentGauge :
    Cochain0 (descentPresentation.mSemPresheaf.onIntersections descentCover) :=
  fun i => descentPresentation.mSemMk (descentCover.chart i)
    (Finsupp.single (sigma (descentCover.chart i) (chartObj_keptCtx i).1)
      (((atlasVal i).val : ℕ) : ℤ))

theorem descentGauge_val (i : Fin 4) :
    mSemToZMod (descentCover.chart i) (chartObj_keptCtx i) (descentGauge i) =
      atlasVal i := by
  show mSemToZMod (descentCover.chart i) (chartObj_keptCtx i)
    (descentPresentation.mSemMk (descentCover.chart i) _) = _
  rw [descentPresentation_mSemMk_eq, mSemToZMod_mk, evalWord_single,
    zmod_two_cast_val]

/-- C7.5 AC2: semantic residual は補正 0-cochain の coboundary である
(`[r_sem] = 0` の witness computation)。 -/
theorem descent_semanticResidual_coboundary :
    descentRepairAtlas.semanticResidual =
      delta0 (descentPresentation.mSemPresheaf.onIntersections descentCover)
        descentGauge := by
  funext p
  have hkept := descent_pairCtx_keptCtx p
  apply mSemToZMod_injective _ hkept
  rw [descent_semanticResidual_val]
  have hR : mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairRight p).hom
        (descentGauge p.snd)) = atlasVal p.snd :=
    (mSemToZMod_restrict (Face.pairRight p).hom hkept
      (chartObj_keptCtx p.snd) (descentGauge p.snd)).trans (descentGauge_val p.snd)
  have hL : mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairLeft p).hom
        (descentGauge p.fst)) = atlasVal p.fst :=
    (mSemToZMod_restrict (Face.pairLeft p).hom hkept
      (chartObj_keptCtx p.fst) (descentGauge p.fst)).trans (descentGauge_val p.fst)
  show atlasVal p.snd - atlasVal p.fst =
    mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairRight p).hom
          (descentGauge p.snd) -
        descentPresentation.mSemRestrict (Face.pairLeft p).hom
          (descentGauge p.fst))
  rw [map_sub, hR, hL]

/-- C7.5 AC2: `[r_sem] = 0`。 -/
theorem descent_semanticResidualClass_isZero :
    (descentPresentation.semanticComplex descentCover).H1IsZero
      descentRepairAtlas.semanticResidualClass :=
  (descentRepairAtlas.semanticResidualClass_isZero_iff_coboundary).mpr
    ⟨descentGauge, descent_semanticResidual_coboundary⟩

/-- 零 twist の帰結(査読 Lean A lane の指摘による named 化): 任意の
semantic repair atlas の生成 residual の `F₂` 値は atlas 読みの差。 -/
theorem descent_semanticResidual_val_of_atlas
    (A : SemanticRepairAtlas descentRepairSystem) (p : descentCover.KeptPair) :
    mSemToZMod (descentCover.pairCtx p.fst p.snd) (descent_pairCtx_keptCtx p)
      (A.semanticResidual p) =
    (A.localRepair p.snd).1 - (A.localRepair p.fst).1 := by
  have hact := AffineCoefficientLiftSystem.act_diffAt
    (L := descentRepairSystem.toLiftSystem) (.pair p)
    (A.toLiftAtlas.leftOn p) (A.toLiftAtlas.rightOn p)
  have h1 : (A.toLiftAtlas.rightOn p).1 =
      (A.toLiftAtlas.leftOn p).1 +
        mSemToZMod (descentCover.pairCtx p.fst p.snd)
          (descent_pairCtx_keptCtx p) (A.semanticResidual p) := by
    conv_lhs => rw [← hact]
    exact descent_mact_val (.pair p) (A.semanticResidual p)
      (A.toLiftAtlas.leftOn p)
  have hleft : (A.toLiftAtlas.leftOn p).1 = (A.localRepair p.fst).1 := by
    show (descentRestrict (descentCover.pairFst p.fst p.snd)
        (A.localRepair p.fst)).1 = _
    rw [descentRestrict_val_of_kept _ _ (descent_pairCtx_keptCtx p)]
  have hright : (A.toLiftAtlas.rightOn p).1 = (A.localRepair p.snd).1 := by
    show (descentRestrict (descentCover.pairSnd p.fst p.snd)
        (A.localRepair p.snd)).1 = _
    rw [descentRestrict_val_of_kept _ _ (descent_pairCtx_keptCtx p)]
  rw [show mSemToZMod (descentCover.pairCtx p.fst p.snd)
      (descent_pairCtx_keptCtx p) (A.semanticResidual p) =
    (A.toLiftAtlas.rightOn p).1 - (A.toLiftAtlas.leftOn p).1 from by
    rw [h1]; ring]
  rw [hleft, hright]

/-- 任意の atlas の atlas 読み gauge。 -/
noncomputable def descentGaugeOf (A : SemanticRepairAtlas descentRepairSystem) :
    Cochain0 (descentPresentation.mSemPresheaf.onIntersections descentCover) :=
  fun i => descentPresentation.mSemMk (descentCover.chart i)
    (Finsupp.single (sigma (descentCover.chart i) (chartObj_keptCtx i).1)
      ((((A.localRepair i).1).val : ℕ) : ℤ))

theorem descentGaugeOf_val (A : SemanticRepairAtlas descentRepairSystem)
    (i : Fin 4) :
    mSemToZMod (descentCover.chart i) (chartObj_keptCtx i)
      (descentGaugeOf A i) = (A.localRepair i).1 := by
  show mSemToZMod (descentCover.chart i) (chartObj_keptCtx i)
    (descentPresentation.mSemMk (descentCover.chart i) _) = _
  rw [descentPresentation_mSemMk_eq, mSemToZMod_mk, evalWord_single,
    zmod_two_cast_val]

/--
C7.5(査読 Lean A lane の指摘による named 化): 零 twist の下では**任意の**
semantic repair atlas の residual class が零になる。すなわち AC2 の
`[r_sem] = 0` は atlas `(1,0,0,0)` の選択に依らない構造的帰結であり、atlas
選択が買っているのは residual **cochain** の非零性
(`descent_semanticResidual_ne_zero`)だけである。なお本 fixture の複体の
`H¹` 自体は非自明である(`descent_semanticH1_nontrivial` — 4-cycle の
edge sum が coboundary を消す)ため、この零化は複体の自明性によるもので
はない。
-/
theorem descent_every_atlas_residualClass_isZero
    (A : SemanticRepairAtlas descentRepairSystem) :
    (descentPresentation.semanticComplex descentCover).H1IsZero
      A.semanticResidualClass := by
  refine (A.semanticResidualClass_isZero_iff_coboundary).mpr
    ⟨descentGaugeOf A, ?_⟩
  funext p
  have hkept := descent_pairCtx_keptCtx p
  apply mSemToZMod_injective _ hkept
  rw [descent_semanticResidual_val_of_atlas]
  have hR : mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairRight p).hom
        (descentGaugeOf A p.snd)) = (A.localRepair p.snd).1 :=
    (mSemToZMod_restrict (Face.pairRight p).hom hkept
      (chartObj_keptCtx p.snd) (descentGaugeOf A p.snd)).trans
      (descentGaugeOf_val A p.snd)
  have hL : mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairLeft p).hom
        (descentGaugeOf A p.fst)) = (A.localRepair p.fst).1 :=
    (mSemToZMod_restrict (Face.pairLeft p).hom hkept
      (chartObj_keptCtx p.fst) (descentGaugeOf A p.fst)).trans
      (descentGaugeOf_val A p.fst)
  show (A.localRepair p.snd).1 - (A.localRepair p.fst).1 =
    mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairRight p).hom
          (descentGaugeOf A p.snd) -
        descentPresentation.mSemRestrict (Face.pairLeft p).hom
          (descentGaugeOf A p.fst))
  rw [map_sub, hR, hL]

/-! ## The 4-cycle edge sum and nontriviality of the descent `H¹` -/

/-- 4-cycle の残りの隣接辺 `(1,2)`。 -/
def descentEdge12 : descentCover.KeptPair :=
  ⟨(1 : Fin 4), (2 : Fin 4), by decide, fun h => h (by decide)⟩

/-- 4-cycle の残りの隣接辺 `(2,3)`。 -/
def descentEdge23 : descentCover.KeptPair :=
  ⟨(2 : Fin 4), (3 : Fin 4), by decide, fun h => h (by decide)⟩

/-- 4-cycle の残りの隣接辺 `(0,3)`。 -/
def descentEdge03 : descentCover.KeptPair :=
  ⟨(0 : Fin 4), (3 : Fin 4), by decide, fun h => h (by decide)⟩

/-- descent 1-cochain の `F₂` 辺読み。 -/
noncomputable def descentEdgeRead (p : descentCover.KeptPair)
    (c : Cochain1 (descentPresentation.mSemPresheaf.onIntersections
      descentCover)) : ZMod 2 :=
  mSemToZMod (descentCover.pairCtx p.fst p.snd) (descent_pairCtx_keptCtx p)
    (c p)

/-- B.9.5 と同形の向き付き辺和(descent 複体版)。 -/
noncomputable def descentEdgeSum :
    Cochain1 (descentPresentation.mSemPresheaf.onIntersections descentCover) →+
      ZMod 2 :=
  AddMonoidHom.mk'
    (fun c => descentEdgeRead descentEdge01 c + descentEdgeRead descentEdge12 c +
      descentEdgeRead descentEdge23 c + descentEdgeRead descentEdge03 c)
    (by
      intro c d
      simp only [descentEdgeRead]
      have hadd : ∀ p : descentCover.KeptPair,
          mSemToZMod (descentCover.pairCtx p.fst p.snd)
            (descent_pairCtx_keptCtx p) ((c + d) p) =
          mSemToZMod (descentCover.pairCtx p.fst p.snd)
              (descent_pairCtx_keptCtx p) (c p) +
            mSemToZMod (descentCover.pairCtx p.fst p.snd)
              (descent_pairCtx_keptCtx p) (d p) := by
        intro p
        exact map_add (mSemToZMod (descentCover.pairCtx p.fst p.snd)
          (descent_pairCtx_keptCtx p)) (c p) (d p)
      rw [hadd descentEdge01, hadd descentEdge12, hadd descentEdge23,
        hadd descentEdge03]
      ring)

/-- 辺和は coboundary を消す(`F₂` の符号退化による 4-cycle 相殺)。 -/
theorem descentEdgeSum_delta0
    (b : Cochain0 (descentPresentation.mSemPresheaf.onIntersections
      descentCover)) :
    descentEdgeSum (delta0
      (descentPresentation.mSemPresheaf.onIntersections descentCover) b) = 0 := by
  have hread : ∀ p : descentCover.KeptPair,
      descentEdgeRead p (delta0
        (descentPresentation.mSemPresheaf.onIntersections descentCover) b) =
      mSemToZMod (descentCover.chart p.snd) (chartObj_keptCtx p.snd) (b p.snd) -
        mSemToZMod (descentCover.chart p.fst) (chartObj_keptCtx p.fst)
          (b p.fst) := by
    intro p
    have hR : mSemToZMod _ (descent_pairCtx_keptCtx p)
        (descentPresentation.mSemRestrict (Face.pairRight p).hom (b p.snd)) =
        mSemToZMod (descentCover.chart p.snd) (chartObj_keptCtx p.snd)
          (b p.snd) :=
      mSemToZMod_restrict (Face.pairRight p).hom (descent_pairCtx_keptCtx p)
        (chartObj_keptCtx p.snd) (b p.snd)
    have hL : mSemToZMod _ (descent_pairCtx_keptCtx p)
        (descentPresentation.mSemRestrict (Face.pairLeft p).hom (b p.fst)) =
        mSemToZMod (descentCover.chart p.fst) (chartObj_keptCtx p.fst)
          (b p.fst) :=
      mSemToZMod_restrict (Face.pairLeft p).hom (descent_pairCtx_keptCtx p)
        (chartObj_keptCtx p.fst) (b p.fst)
    show mSemToZMod _ (descent_pairCtx_keptCtx p)
      (descentPresentation.mSemRestrict (Face.pairRight p).hom (b p.snd) -
        descentPresentation.mSemRestrict (Face.pairLeft p).hom (b p.fst)) = _
    rw [map_sub, hR, hL]
  show descentEdgeRead descentEdge01 _ + descentEdgeRead descentEdge12 _ +
    descentEdgeRead descentEdge23 _ + descentEdgeRead descentEdge03 _ = 0
  rw [hread descentEdge01, hread descentEdge12, hread descentEdge23,
    hread descentEdge03]
  have hcycle : ∀ x y z w : ZMod 2,
      (y - x) + (z - y) + (w - z) + (w - x) = 0 := by decide
  exact hcycle _ _ _ _

/-- 辺 `(0,1)` にのみ台を持つ単位 1-cochain。kept triple が空なので
すべての 1-cochain は cocycle である。 -/
noncomputable def descentUnitCochain :
    Cochain1 (descentPresentation.mSemPresheaf.onIntersections descentCover) :=
  fun p =>
    if @Eq (Fin 4) p.fst 0 ∧ @Eq (Fin 4) p.snd 1 then
      descentPresentation.mSemMk (descentCover.pairCtx p.fst p.snd)
        (Finsupp.single (sigma _ (descent_pairCtx_keptCtx p).1) 1)
    else 0

/-- descent cover は kept triple を持たない(`C² = 0`)。 -/
theorem descent_keptTriple_isEmpty : IsEmpty descentCover.KeptTriple :=
  ⟨fun t => t.kept (by
    rcases exists_omitted_pair_of_triple t.fst t.snd t.trd t.lt₁ t.lt₂ with
      h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h)))⟩

/-- 単位 1-cochain の descent `H¹` class。 -/
noncomputable def descentUnitClass :
    descentPresentation.SemanticH1 descentCover :=
  Quotient.mk (incComplex
      (descentPresentation.mSemPresheaf.onIntersections
        descentCover)).H1CoboundarySetoid
    ⟨descentUnitCochain, by
      funext t
      exact (descent_keptTriple_isEmpty.false t).elim⟩

/-- 単位 1-cochain の辺和は `1`。 -/
theorem descentEdgeSum_unitCochain : descentEdgeSum descentUnitCochain = 1 := by
  have h01 : descentEdgeRead descentEdge01 descentUnitCochain = 1 := by
    show mSemToZMod _ (descent_pairCtx_keptCtx descentEdge01)
      (descentUnitCochain descentEdge01) = 1
    rw [show descentUnitCochain descentEdge01 =
        descentPresentation.mSemMk
          (descentCover.pairCtx descentEdge01.fst descentEdge01.snd)
          (Finsupp.single
            (sigma _ (descent_pairCtx_keptCtx descentEdge01).1) 1) from by
      simp only [descentUnitCochain]
      rw [if_pos (by decide)]]
    rw [descentPresentation_mSemMk_eq, mSemToZMod_mk, evalWord_single]
    decide
  have hz : ∀ p : descentCover.KeptPair,
      ¬ (@Eq (Fin 4) p.fst 0 ∧ @Eq (Fin 4) p.snd 1) ->
      descentEdgeRead p descentUnitCochain = 0 := by
    intro p hp
    show mSemToZMod _ (descent_pairCtx_keptCtx p) (descentUnitCochain p) = 0
    rw [show descentUnitCochain p = 0 from by
      simp only [descentUnitCochain]
      rw [if_neg hp], map_zero]
  show descentEdgeRead descentEdge01 _ + descentEdgeRead descentEdge12 _ +
    descentEdgeRead descentEdge23 _ + descentEdgeRead descentEdge03 _ = 1
  rw [h01, hz descentEdge12 (by decide), hz descentEdge23 (by decide),
    hz descentEdge03 (by decide)]
  decide

/--
査読対応(数学B lane 第2巡 N1 の (a) 案): descent 複体の `H¹` は非自明で
ある — 4-cycle の辺和は coboundary を消すが、辺 `(0,1)` の単位 cochain の
辺和は `1`。`descent_every_atlas_residualClass_isZero` の零化が複体の
自明性によるものではないことの named witness。
-/
theorem descent_semanticH1_nontrivial :
    ¬ (descentPresentation.semanticComplex descentCover).H1IsZero
      descentUnitClass := by
  intro hzero
  obtain ⟨b, hb⟩ := Quotient.exact hzero
  have hcob : descentUnitCochain =
      delta0 (descentPresentation.mSemPresheaf.onIntersections descentCover)
        b := by
    have hsub : descentUnitCochain - 0 =
        delta0 (descentPresentation.mSemPresheaf.onIntersections descentCover)
          b := hb
    rwa [sub_zero] at hsub
  have hone := descentEdgeSum_unitCochain
  rw [hcob, descentEdgeSum_delta0 b] at hone
  exact absurd hone (by decide)

/-! ## Sheaf condition engine over the classified topology -/

/--
C7.5: 分類済み descent topology 上の sheaf condition engine。kept context で
`F₂` への値写像が単射・全射・restriction 不変で、kept でない context の値が
subsingleton な Type 値 presheaf は sheaf condition を満たす。`P_sem` と
`P_E` の両 state presheaf をこの engine で放電する。

分類の帰結として、base 以外の対象上の covering sieve は `⊤` に限られ
`Presieve.isSheafFor_top` で放電されるため、実質的な amalgamation 論証は
base 上の(4 chart arrow を含む)sieve のケースに集中する — これは選んだ
幾何の帰結であり、sheaf condition の量化域は topology の全 cover である。
-/
theorem descent_sheafCondition (F : Site.AATPresheaf descentSite)
    (val : ∀ (V : descentSite.category), KeptCtx V.ctx -> F.obj (op V) -> ZMod 2)
    (hinj : ∀ (V) (h : KeptCtx V.ctx), Function.Injective (val V h))
    (hsurj : ∀ (V) (h : KeptCtx V.ctx), Function.Surjective (val V h))
    (hrestrict : ∀ {V' V : descentSite.category} (f : V' ⟶ V)
      (h' : KeptCtx V'.ctx) (h : KeptCtx V.ctx) (x : F.obj (op V)),
      val V' h' (F.map f.op x) = val V h x)
    (hsub : ∀ (V : descentSite.category), ¬ KeptCtx V.ctx ->
      Subsingleton (F.obj (op V))) :
    Site.AATSheafCondition descentSite F := by
  intro X cover hcover
  rcases descent_topology_classify hcover with rfl | ⟨hX, hcharts⟩
  · rw [Site.AATSheafConditionFor]
    exact Presieve.isSheafFor_top F
  · have hXbase : X = base := descent_obj_ext hX
    subst hXbase
    rw [Site.AATSheafConditionFor]
    intro x hx
    set xi : ∀ i : Fin 4, F.obj (op (chartObj i)) :=
      fun i => x (chartInclusion i) (hcharts i (chartInclusion i)) with hxi
    have hadj : ∀ i j : Fin 4, ({i, j} : ContextIndex) ∈ keptSets ->
        val _ (chartObj_keptCtx i) (xi i) = val _ (chartObj_keptCtx j) (xi j) := by
      intro i j hkeptij
      have hPk : KeptCtx (Site.ContextCategoryObject.of
          CircleWitness.contextPreorder (context ({i} ∪ {j}))).ctx := by
        refine ⟨recognized_context _, ?_⟩
        rw [show (Site.ContextCategoryObject.of CircleWitness.contextPreorder
            (context ({i} ∪ {j}))).ctx = context ({i} ∪ {j}) from rfl,
          indexOf_context, singleton_union_eq_pair]
        exact hkeptij
      have g₁ : Site.ContextCategoryObject.of CircleWitness.contextPreorder
          (context ({i} ∪ {j})) ⟶ chartObj i :=
        homOfLE (Or.inr ⟨{i} ∪ {j}, {i}, rfl, rfl, Finset.subset_union_left⟩)
      have g₂ : Site.ContextCategoryObject.of CircleWitness.contextPreorder
          (context ({i} ∪ {j})) ⟶ chartObj j :=
        homOfLE (Or.inr ⟨{i} ∪ {j}, {j}, rfl, rfl, Finset.subset_union_right⟩)
      have hcompat := hx g₁ g₂ (hcharts i (chartInclusion i))
        (hcharts j (chartInclusion j)) (Subsingleton.elim _ _)
      calc val _ (chartObj_keptCtx i) (xi i)
          = val _ hPk (F.map g₁.op (xi i)) :=
            (hrestrict g₁ hPk (chartObj_keptCtx i) (xi i)).symm
        _ = val _ hPk (F.map g₂.op (xi j)) := congrArg _ hcompat
        _ = val _ (chartObj_keptCtx j) (xi j) :=
            hrestrict g₂ hPk (chartObj_keptCtx j) (xi j)
    set v := val _ (chartObj_keptCtx 0) (xi 0) with hv
    have hvi : ∀ i : Fin 4, val _ (chartObj_keptCtx i) (xi i) = v := by
      have hval01 := hadj 0 1 (by decide)
      have hval12 := hadj 1 2 (by decide)
      have hval23 := hadj 2 3 (by decide)
      intro i
      fin_cases i
      · rfl
      · exact hval01.symm
      · exact (hval01.trans hval12).symm
      · exact ((hval01.trans hval12).trans hval23).symm
    obtain ⟨t, ht⟩ := hsurj base base_keptCtx v
    refine ⟨t, ?_, ?_⟩
    · intro Y f hf
      by_cases hK : KeptCtx Y.ctx
      · apply hinj Y hK
        rw [hrestrict f hK base_keptCtx t, ht]
        by_cases hYe : indexOf Y.ctx = ∅
        · have hle : contextLe (context {0}) Y.ctx := by
            rw [context_indexOf hK.1, hYe]
            exact Or.inr ⟨{0}, ∅, rfl, rfl, Finset.empty_subset _⟩
          have g : chartObj 0 ⟶ Y := homOfLE hle
          have hcompat := hx g (𝟙 (chartObj 0)) hf
            (hcharts 0 (chartInclusion 0)) (Subsingleton.elim _ _)
          have hthis := congrArg (val (chartObj 0) (chartObj_keptCtx 0)) hcompat
          rw [hrestrict g (chartObj_keptCtx 0) hK (x f hf)] at hthis
          simp only [op_id, F.map_id, types_id_apply] at hthis
          exact hv.trans hthis.symm
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
          have hle : contextLe Y.ctx (context {i}) := by
            rw [context_indexOf hK.1]
            exact Or.inr ⟨indexOf Y.ctx, {i}, rfl, rfl,
              Finset.singleton_subset_iff.mpr hi⟩
          have g : Y ⟶ chartObj i := homOfLE hle
          have hcompat := hx (𝟙 Y) g hf (hcharts i (chartInclusion i))
            (Subsingleton.elim _ _)
          have hthis := congrArg (val Y hK) hcompat
          rw [hrestrict g hK (chartObj_keptCtx i) (xi i)] at hthis
          simp only [op_id, F.map_id, types_id_apply] at hthis
          rw [hvi i] at hthis
          exact hthis.symm
      · haveI := hsub Y hK
        exact Subsingleton.elim _ _
    · intro t' ht'
      apply hinj base base_keptCtx
      have h0 := ht' (chartInclusion 0) (hcharts 0 (chartInclusion 0))
      have hthis := congrArg (val (chartObj 0) (chartObj_keptCtx 0)) h0
      rw [hrestrict (chartInclusion 0) (chartObj_keptCtx 0) base_keptCtx t'] at hthis
      rw [hthis, ht]

/-- C7.5 AC1: `P_sem` の state presheaf は descent topology 上の sheaf。 -/
theorem descent_stateSheaf :
    Site.AATSheafCondition descentSite descentRepairSystem.statePresheaf := by
  refine descent_sheafCondition descentRepairSystem.statePresheaf
    (fun V _h e => e.1) ?_ ?_ ?_ ?_
  · intro V h e e' hee'
    exact Subtype.ext hee'
  · intro V h y
    exact ⟨⟨y, Or.inl h⟩, rfl⟩
  · intro V' V f h' h e
    exact descentRestrict_val_of_kept f e h'
  · intro V hV
    exact descentState_subsingleton hV

/-- C7.5 AC1: descent fixture の true semantic repair sheaf(X.定義8.1、
sheaf condition は `descent_sheafCondition` engine による実証明)。 -/
theorem descentTrueSheaf :
    TrueSemanticRepairSheaf descentCover descentRepairSystem where
  isSheaf := descent_stateSheaf
  psem_pair_subsingleton _i _j hom :=
    descentState_subsingleton (descent_pairCtx_not_kept hom)
  psem_triple_subsingleton _i _j _k hom :=
    descentState_subsingleton (descent_tripleCtx_not_kept hom)

/-! ## Production route: selection, realization, completeness (#3734) -/

/-- C7.5 (#3734 route): support-Atom selected 対応(唯一の required equation
と有限 model reading への定数選択)。 -/
noncomputable def descentSelection : SupportAtomEquationSelection descentSite where
  equationIndex _ := ⟨PUnit.unit, rfl⟩
  archReading _ := FiniteModel.object

/-- C7.5 AC3: production constructor による realization(equation 側入力の
生成物。手書きの `EquationSemanticRealization` は置かない)。 -/
noncomputable def descentRealization :
    EquationSemanticRealization descentPresentation descentCover :=
  descentSelection.realization descentPresentation descentCover

/-- produced `χ^E` の値は `[1]`(生成 chain の読み出し)。 -/
theorem descent_chiE_apply (σ : IntersectionIndex descentCover)
    (l : descentPresentation.atomData.SupportedAtom σ.ctx) :
    descentRealization.chiE.chi σ l =
      Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal σ.ctx)
        (1 : ZMod (modulus σ.ctx.ctx)) :=
  rfl

/-- `F₂` 読みでの produced `χ̃^E` は word evaluation。 -/
theorem descent_qEToZMod_chiHom (σ : IntersectionIndex descentCover)
    (x : descentPresentation.atomData.SupportedWord σ.ctx) :
    qEToZMod σ.ctx (descent_keptCtx_of_intersection σ)
        (descentRealization.chiE.chiHom σ x) =
      ((evalWord σ.ctx (descent_keptCtx_of_intersection σ).1 x : ℤ) :
        ZMod 2) := by
  conv_lhs => rw [show x = Finsupp.single
    (sigma σ.ctx (descent_keptCtx_of_intersection σ).1)
    (evalWord σ.ctx (descent_keptCtx_of_intersection σ).1 x) from
    word_eq_single σ.ctx (descent_keptCtx_of_intersection σ).1 x]
  rw [descentRealization.chiE.chiHom_single, map_zsmul, descent_chiE_apply,
    qEToZMod_mk, map_one, zsmul_one]

/-- X.定義6.2 repair-relation completeness(descent instance、有限計算)。 -/
theorem descentRelationComplete (σ : IntersectionIndex descentCover) :
    descentRealization.chiE.RelationComplete σ := by
  intro x hx
  have hz : ((evalWord σ.ctx (descent_keptCtx_of_intersection σ).1 x : ℤ) :
      ZMod 2) = 0 := by
    rw [← descent_qEToZMod_chiHom σ x, hx, map_zero]
  have heven : (2 : ℤ) ∣
      evalWord σ.ctx (descent_keptCtx_of_intersection σ).1 x :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  rw [show x = Finsupp.single
      (sigma σ.ctx (descent_keptCtx_of_intersection σ).1)
      (evalWord σ.ctx (descent_keptCtx_of_intersection σ).1 x) from
    word_eq_single σ.ctx (descent_keptCtx_of_intersection σ).1 x]
  exact single_mem_relSpan_of_even σ.ctx
    (descent_keptCtx_of_intersection σ) _ heven

/-- X.定義6.2 target-generator completeness(descent instance、有限計算)。 -/
theorem descentGeneratorComplete (σ : IntersectionIndex descentCover) :
    descentRealization.chiE.GeneratorComplete σ := by
  intro q
  induction q using Quotient.inductionOn with
  | h y =>
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective y
  refine ⟨Finsupp.single
    (sigma σ.ctx (descent_keptCtx_of_intersection σ).1) n, ?_⟩
  rw [descentRealization.chiE.chiHom_single, descent_chiE_apply, ← hn]
  rw [show n • (Ideal.Quotient.mk
        (circleEquationSystem.obstructionIdeal σ.ctx))
        (1 : ZMod (modulus σ.ctx.ctx)) =
      (Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal σ.ctx))
        (n • (1 : ZMod (modulus σ.ctx.ctx))) from (map_zsmul _ _ _).symm,
    zsmul_one]
  rfl

/-! ## X.定義5.3 典型例: the nonzero-base-reading lift fiber -/

/-- C7.5: base reading の値域 presheaf `B_E`(定数 `F₂`、恒等 restriction)。 -/
def descentBaseReadingPresheaf : SitePresheafData descentSite where
  carrier _ := ZMod 2
  addCommGroup _ := inferInstance
  restrict _ := AddMonoidHom.id _
  restrict_id _ _ := rfl
  restrict_comp _ _ _ := rfl

/-- C7.5: total presheaf `L_E := Q_E × B_E`(成分ごとの restriction)。 -/
def descentTotalPresheaf : SitePresheafData descentSite where
  carrier V := circleEquationSystem.ObstructionQuotient V × ZMod 2
  addCommGroup _ := inferInstance
  restrict f :=
    AddMonoidHom.prodMap ((equationSitePresheaf descentSite).restrict f)
      (AddMonoidHom.id _)
  restrict_id V x :=
    Prod.ext ((equationSitePresheaf descentSite).restrict_id V x.1) rfl
  restrict_comp f g x :=
    Prod.ext ((equationSitePresheaf descentSite).restrict_comp f g x.1) rfl

/-- C7.5 AC4: 非零 base reading の lift-fiber datum。short exact sequence
`0 → Q_E → Q_E × B_E → B_E → 0` は**分裂積**であり(`incl = inl`,
`proj = snd`)、exactness / injectivity は積の構造から自明に充足される
(申告: Implementation notes (iii)。非分裂性は主張しない)。
`equationSelfLiftFiber`(`B_E = 0` の退化 instance)と異なり、恒等的に `1`
の selected base reading が lift 状態を affine fiber `{(q, 1)}` へ制限し、
解くべき局所 equation-lift problem の選択が実際に行われる。residual の値は
`Q_E` 成分が担い、本 fixture では分裂性により base reading の obstruction
への寄与は消える(一般の典型例では base reading こそが obstruction の
測る対象である — Implementation notes (iii))。 -/
noncomputable def descentLiftFiber :
    LiftFiberData (equationSitePresheaf descentSite) descentTotalPresheaf
      descentBaseReadingPresheaf where
  incl _V := AddMonoidHom.inl _ _
  incl_natural _f _q := rfl
  proj _V := AddMonoidHom.snd _ _
  proj_natural _f _l := rfl
  incl_injective _V _q h := congrArg Prod.fst h
  exact_at_middle V l := by
    constructor
    · intro h
      exact ⟨l.1, Prod.ext rfl h.symm⟩
    · rintro ⟨q, hq⟩
      rw [← hq]
      rfl
  base _ := (1 : ZMod 2)
  base_natural _ := rfl

/-- C7.5 AC4: 選ばれた base reading は全 context で非零
(`B_E ≠ 0` の読みが実際に選ばれている)。 -/
theorem descentLiftFiber_base_ne_zero (V : descentSite.category) :
    descentLiftFiber.base V ≠ 0 := by
  show (1 : ZMod 2) ≠ 0
  decide

/-- C7.5 AC4: 非零 base reading は lift problem を実際に制約する — `L_E` の
零切断は fiber 状態に入らない(退化 self-lift では零切断が常に状態になる
のと対照的)。内容は `descentLiftFiber_base_ne_zero` と同じ事実
(`(0 : F₂) ≠ 1`)の fiber 側の言い換えであり、独立の証拠ではない
(Implementation notes (iii))。 -/
theorem descentLiftFiber_zero_not_in_fiber (V : descentSite.category) :
    descentLiftFiber.proj V 0 ≠ descentLiftFiber.base V := by
  show (0 : ZMod 2) ≠ 1
  decide

/-- companion(査読 Lean A lane の指摘による named 化): fiber は非空である。
`descentLiftFiber_zero_not_in_fiber` と併せて、選ばれた base reading が
`L_E` の切断の**非空な真部分集合**を切り出していることを固定する。 -/
theorem descentLiftFiber_state_nonempty (V : descentSite.category) :
    Nonempty ((descentLiftFiber.equationLiftSystem descentCover).State V) :=
  ⟨⟨(0, 1), rfl⟩⟩

/-- C7.5 AC3/AC4: production 経由の equation-side lift system(X.定義5.3
典型例経路 `equationLiftSystem` の非退化適用)。 -/
noncomputable def descentLiftSystem :
    AffineCoefficientLiftSystem (equationCoefficient descentSite descentCover) :=
  descentLiftFiber.equationLiftSystem descentCover

/-- `F₂` 値から `Q_E` 元への標準 section。 -/
noncomputable def qOfVal (W : descentSite.category) (x : ZMod 2) :
    circleEquationSystem.ObstructionQuotient W :=
  Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal W)
    ((x.val : ℤ) : ZMod (modulus W.ctx))

theorem qEToZMod_qOfVal (W : descentSite.category) (h : KeptCtx W.ctx)
    (x : ZMod 2) : qEToZMod W h (qOfVal W x) = x := by
  rw [qOfVal, qEToZMod_mk, map_intCast, zmod_two_cast_val]

/-- C7.5: 非一様 equation local lift atlas `e_i = ([a_i], 1)`。 -/
noncomputable def descentLiftAtlas : CoefficientLiftAtlas descentLiftSystem where
  localLift i := ⟨(qOfVal (descentCover.chart i) (atlasVal i), 1), rfl⟩

/-- lift 状態の `F₂` 値(第1成分の `Q_E` 読み)。 -/
noncomputable def liftStateVal (V : descentSite.category) (h : KeptCtx V.ctx)
    (e : descentLiftSystem.State V) : ZMod 2 :=
  qEToZMod V h e.1.1

theorem liftStateVal_injective (V : descentSite.category) (h : KeptCtx V.ctx) :
    Function.Injective (liftStateVal V h) := by
  intro e e' he
  apply Subtype.ext
  apply Prod.ext
  · exact qEToZMod_injective V h he
  · exact e.2.trans e'.2.symm

theorem liftStateVal_surjective (V : descentSite.category) (h : KeptCtx V.ctx) :
    Function.Surjective (liftStateVal V h) :=
  fun x => ⟨⟨(qOfVal V x, 1), rfl⟩, qEToZMod_qOfVal V h x⟩

theorem liftStateVal_restrict {V' V : descentSite.category} (f : V' ⟶ V)
    (h' : KeptCtx V'.ctx) (h : KeptCtx V.ctx) (e : descentLiftSystem.State V) :
    liftStateVal V' h' (descentLiftSystem.restrictState f e) =
      liftStateVal V h e :=
  qEToZMod_restrict f h' h e.1.1

/-- kept でない context の lift 状態は subsingleton(`Q_E` が零のため)。 -/
theorem descentLiftState_subsingleton (V : descentSite.category)
    (h : ¬ KeptCtx V.ctx) : Subsingleton (descentLiftSystem.State V) :=
  ⟨fun e e' => Subtype.ext (Prod.ext
    ((qE_trivial_of_not_kept V h e.1.1).trans
      (qE_trivial_of_not_kept V h e'.1.1).symm)
    (e.2.trans e'.2.symm))⟩

/-- lift 作用の `F₂` 値。 -/
theorem liftStateVal_act (σ : IntersectionIndex descentCover)
    (q : circleEquationSystem.ObstructionQuotient σ.ctx)
    (e : descentLiftSystem.State σ.ctx) :
    liftStateVal σ.ctx (descent_keptCtx_of_intersection σ)
        (descentLiftSystem.act σ q e) =
      liftStateVal σ.ctx (descent_keptCtx_of_intersection σ) e +
        qEToZMod σ.ctx (descent_keptCtx_of_intersection σ) q := by
  show qEToZMod σ.ctx (descent_keptCtx_of_intersection σ) (e.1.1 + q) = _
  rw [map_add]
  rfl

/-- C7.5: 生成 equation residual の `F₂` 値は atlas 値の差
`a_{p.snd} - a_{p.fst}`。 -/
theorem descent_equationResidual_val (p : descentCover.KeptPair) :
    qEToZMod (descentCover.pairCtx p.fst p.snd) (descent_pairCtx_keptCtx p)
      (descentLiftAtlas.residual p) =
    atlasVal p.snd - atlasVal p.fst := by
  have hact := descentLiftSystem.act_diffAt (.pair p)
    (descentLiftAtlas.leftOn p) (descentLiftAtlas.rightOn p)
  have h1 : liftStateVal _ (descent_pairCtx_keptCtx p) (descentLiftAtlas.rightOn p) =
      liftStateVal _ (descent_pairCtx_keptCtx p) (descentLiftAtlas.leftOn p) +
        qEToZMod _ (descent_pairCtx_keptCtx p) (descentLiftAtlas.residual p) := by
    conv_lhs => rw [← hact]
    exact liftStateVal_act (.pair p) _ _
  have hleft : liftStateVal _ (descent_pairCtx_keptCtx p) (descentLiftAtlas.leftOn p) =
      atlasVal p.fst :=
    (liftStateVal_restrict (descentCover.pairFst p.fst p.snd)
        (descent_pairCtx_keptCtx p) (chartObj_keptCtx p.fst)
        (descentLiftAtlas.localLift p.fst)).trans
      (qEToZMod_qOfVal _ (chartObj_keptCtx p.fst) (atlasVal p.fst))
  have hright : liftStateVal _ (descent_pairCtx_keptCtx p) (descentLiftAtlas.rightOn p) =
      atlasVal p.snd :=
    (liftStateVal_restrict (descentCover.pairSnd p.fst p.snd)
        (descent_pairCtx_keptCtx p) (chartObj_keptCtx p.snd)
        (descentLiftAtlas.localLift p.snd)).trans
      (qEToZMod_qOfVal _ (chartObj_keptCtx p.snd) (atlasVal p.snd))
  rw [show qEToZMod (descentCover.pairCtx p.fst p.snd) (descent_pairCtx_keptCtx p)
      (descentLiftAtlas.residual p) =
    liftStateVal _ (descent_pairCtx_keptCtx p) (descentLiftAtlas.rightOn p) -
      liftStateVal _ (descent_pairCtx_keptCtx p) (descentLiftAtlas.leftOn p) from by
    rw [h1]; ring]
  rw [hleft, hright]

/-- C7.5 AC4: equation residual cochain は恒等的に零ではない
(辺 `(0,1)` で値 `1`)。 -/
theorem descent_equationResidual_ne_zero : descentLiftAtlas.residual ≠ 0 := by
  intro h
  have hv := congrArg (qEToZMod _ (descent_pairCtx_keptCtx descentEdge01))
    (congrFun h descentEdge01)
  rw [descent_equationResidual_val] at hv
  simp only [Pi.zero_apply, map_zero] at hv
  exact absurd hv (by decide)

/-- C7.5: equation 側補正 0-cochain `b_i = [a_i]`。 -/
noncomputable def descentEquationGauge :
    Cochain0 (equationCoefficient descentSite descentCover) :=
  fun i => qOfVal (descentCover.chart i) (atlasVal i)

/-- C7.5 AC4: equation residual は補正 0-cochain の coboundary である
(class 零の witness computation)。 -/
theorem descent_equationResidual_coboundary :
    descentLiftAtlas.residual =
      delta0 (equationCoefficient descentSite descentCover)
        descentEquationGauge := by
  funext p
  have hkept := descent_pairCtx_keptCtx p
  apply qEToZMod_injective _ hkept
  rw [descent_equationResidual_val]
  have hR : qEToZMod _ hkept
      ((equationCoefficient descentSite descentCover).restrict
        (Face.pairRight p) (descentEquationGauge p.snd)) = atlasVal p.snd :=
    (qEToZMod_restrict (Face.pairRight p).hom hkept (chartObj_keptCtx p.snd)
      (descentEquationGauge p.snd)).trans
      (qEToZMod_qOfVal _ (chartObj_keptCtx p.snd) (atlasVal p.snd))
  have hL : qEToZMod _ hkept
      ((equationCoefficient descentSite descentCover).restrict
        (Face.pairLeft p) (descentEquationGauge p.fst)) = atlasVal p.fst :=
    (qEToZMod_restrict (Face.pairLeft p).hom hkept (chartObj_keptCtx p.fst)
      (descentEquationGauge p.fst)).trans
      (qEToZMod_qOfVal _ (chartObj_keptCtx p.fst) (atlasVal p.fst))
  show atlasVal p.snd - atlasVal p.fst =
    qEToZMod _ hkept
      ((equationCoefficient descentSite descentCover).restrict
          (Face.pairRight p) (descentEquationGauge p.snd) -
        (equationCoefficient descentSite descentCover).restrict
          (Face.pairLeft p) (descentEquationGauge p.fst))
  rw [map_sub, hR, hL]

/-- C7.5 AC4: `[r_E] = 0`。 -/
theorem descent_equationResidualClass_isZero :
    (incComplex (equationCoefficient descentSite descentCover)).H1IsZero
      descentLiftAtlas.residualClass :=
  (descentLiftAtlas.residualClass_isZero_iff_coboundary).mpr
    ⟨descentEquationGauge, descent_equationResidual_coboundary⟩

/-! ## The state correspondence and the empty-overlap normalization -/

/-- C7.5: 状態対応 `β`(`F₂` 値を保つ標準対応、produced `χ^E` に同変)。 -/
noncomputable def descentBeta :
    PrimaryStateCorrespondence descentRealization.chiE descentRepairSystem
      descentLiftSystem where
  beta σ p := ⟨(qOfVal σ.ctx p.1, 1), rfl⟩
  beta_natural {σ τ} f p := by
    apply Subtype.ext
    apply Prod.ext
    · apply qEToZMod_injective σ.ctx (descent_keptCtx_of_intersection σ)
      have hLHS : qEToZMod σ.ctx (descent_keptCtx_of_intersection σ)
          (circleEquationSystem.obstructionQuotientRestrict f.hom
            (qOfVal τ.ctx p.1)) = p.1 :=
        (qEToZMod_restrict f.hom (descent_keptCtx_of_intersection σ)
          (descent_keptCtx_of_intersection τ) (qOfVal τ.ctx p.1)).trans
          (qEToZMod_qOfVal τ.ctx (descent_keptCtx_of_intersection τ) p.1)
      have hRHS : qEToZMod σ.ctx (descent_keptCtx_of_intersection σ)
          (qOfVal σ.ctx (descentRestrict f.hom p).1) = p.1 := by
        rw [qEToZMod_qOfVal,
          descentRestrict_val_of_kept f.hom p (descent_keptCtx_of_intersection σ)]
      exact hLHS.trans hRHS.symm
    · rfl
  beta_equivariant σ l p := by
    have hkept := descent_keptCtx_of_intersection σ
    apply Subtype.ext
    apply Prod.ext
    · apply qEToZMod_injective σ.ctx hkept
      have hact : (descentAct σ.ctx (Finsupp.single l 1) p).1 = p.1 + 1 := by
        rw [descentAct_val_of_kept σ.ctx _ p hkept]
        congr 1
        rw [show evalWord σ.ctx hkept.1 (Finsupp.single l 1) = 1 from by
          rw [@Subsingleton.elim _ (supportedAtom_subsingleton σ.ctx) l
            (sigma σ.ctx hkept.1), evalWord_single]]
        decide
      show qEToZMod σ.ctx hkept
          (qOfVal σ.ctx (descentAct σ.ctx (Finsupp.single l 1) p).1) =
        qEToZMod σ.ctx hkept
          (qOfVal σ.ctx p.1 +
            Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal σ.ctx)
              (1 : ZMod (modulus σ.ctx.ctx)))
      rw [map_add, qEToZMod_qOfVal, qEToZMod_qOfVal, hact, qEToZMod_mk,
        map_one]
    · rfl

/-- X.§1 入力8: omitted overlap 上の empty-overlap normalization。
descent model に対する named input-8 witness。X.§7 のとおり comparison core
の仮定ではない(`SagaEquationPacket` の field ではない)ため packet には
束ねず、明示仮説として受ける消費先のために保持する。 -/
theorem descentNormalization :
    EmptyOverlapNormalization descentPresentation descentCover
      descentRepairSystem descentLiftSystem where
  msem_pair_trivial _i _j hom m :=
    mSem_trivial_of_not_kept _ (descent_pairCtx_not_kept hom) m
  msem_triple_trivial _i _j _k hom m :=
    mSem_trivial_of_not_kept _ (descent_tripleCtx_not_kept hom) m
  qE_pair_trivial _i _j hom q :=
    qE_trivial_of_not_kept _ (descent_pairCtx_not_kept hom) q
  qE_triple_trivial _i _j _k hom q :=
    qE_trivial_of_not_kept _ (descent_tripleCtx_not_kept hom) q
  psem_pair_subsingleton _i _j hom :=
    descentState_subsingleton (descent_pairCtx_not_kept hom)
  psem_triple_subsingleton _i _j _k hom :=
    descentState_subsingleton (descent_tripleCtx_not_kept hom)
  pE_pair_subsingleton _i _j hom :=
    descentLiftState_subsingleton _ (descent_pairCtx_not_kept hom)
  pE_triple_subsingleton _i _j _k hom :=
    descentLiftState_subsingleton _ (descent_tripleCtx_not_kept hom)

/-! ## The production packet and the descent firings -/

/-- C7.5 AC3: production route による定理1.1 入力束の組み立て
(`SagaEquationPacket.ofProduction` の初の具体 instance)。 -/
noncomputable def descentPacket : SagaEquationPacket descentSite :=
  SagaEquationPacket.ofProduction descentOccurrenceReading descentCover
    descentPresentation descentSelection descentRepairSystem descentRepairAtlas
    descentLiftFiber descentLiftAtlas descentBeta

/-- packet の realization は production selection の生成物(AC3 の宣言面)。 -/
theorem descentPacket_realization_eq :
    descentPacket.realization =
      descentSelection.realization descentPresentation descentCover :=
  rfl

/-- packet の lift system は非零 base reading fiber の `equationLiftSystem`
適用(AC3・AC4 の宣言面)。 -/
theorem descentPacket_liftSystem_eq :
    descentPacket.liftSystem =
      descentLiftFiber.equationLiftSystem descentCover :=
  rfl

/-- packet cover の cover sieve は topology に属する(定理8.2 の `hmem`)。 -/
theorem descentPacket_mem_topology :
    Sieve.generate (Presieve.ofArrows descentPacket.cover.chart
        descentPacket.cover.inclusion) ∈
      descentSite.topology descentPacket.cover.base :=
  descentCover_mem_topology

/-- packet の true semantic repair sheaf(定理8.2 の `htrue`)。 -/
theorem descentPacket_trueSheaf :
    TrueSemanticRepairSheaf descentPacket.cover descentPacket.repairSystem :=
  descentTrueSheaf

/-- C7.5 / X.定理8.2 発火: `Nonempty P_sem(W) ⟺ [r_sem] = 0`
(named instance)。 -/
theorem descent_globalRepair_nonempty_iff :
    Nonempty (GlobalRepair descentPacket.cover descentPacket.repairSystem) ↔
      (descentPacket.presentation.semanticComplex
        descentPacket.cover).H1IsZero
        descentPacket.repairAtlas.semanticResidualClass :=
  descentPacket.globalRepair_nonempty_iff descentPacket_mem_topology
    descentPacket_trueSheaf

/-- C7.5 / X.定理8.2 発火(sanity corollary): `[r_sem] = 0` から
`Nonempty P_sem(W)`。**この `Nonempty` 自体は状態担体の構成から自明に真**
(`⟨0, Or.inr rfl⟩`)であり、本定理の内容は同値
`descent_globalRepair_nonempty_iff` の実適用の記録にある。定理8.2 の
非自明な構成面は `descent_globalRepair_of_h1IsZero` を見よ(module header
の Implementation notes (iv))。 -/
theorem descent_globalRepair_nonempty :
    Nonempty (GlobalRepair descentPacket.cover descentPacket.repairSystem) :=
  descent_globalRepair_nonempty_iff.mpr descent_semanticResidualClass_isZero

/-- C7.5 / X.定理8.2 発火(順方向の構成面): 系4.5 correction による
corrected family の一意な amalgamation としての大域 repair。 -/
theorem descent_globalRepair_of_h1IsZero :
    ∃ b : Cochain0 (descentPacket.presentation.mSemPresheaf.onIntersections
        descentPacket.cover),
      ∃! t : GlobalRepair descentPacket.cover descentPacket.repairSystem,
        ∀ i, descentPacket.repairSystem.restrictState
            (descentPacket.cover.inclusion i) t =
          (descentPacket.repairAtlas.toLiftAtlas.corrected b).localLift i :=
  descentPacket.globalRepair_of_h1IsZero descentPacket_mem_topology
    descentPacket_trueSheaf descent_semanticResidualClass_isZero

/-- C7.5 / X.定理8.2(統合)発火: grounded gluing の両側の同値。 -/
theorem descent_sagaGroundedGluing :
    (Nonempty (GlobalRepair descentPacket.cover descentPacket.repairSystem) ↔
      (descentPacket.presentation.semanticComplex
        descentPacket.cover).H1IsZero
        descentPacket.repairAtlas.semanticResidualClass) ∧
    (Nonempty (GlobalRepair descentPacket.cover descentPacket.repairSystem) ↔
      (incComplex (equationCoefficient descentSite
        descentPacket.cover)).H1IsZero
        descentPacket.liftAtlas.residualClass) :=
  descentPacket.sagaGroundedGluing descentPacket_mem_topology
    descentPacket_trueSheaf descentRelationComplete descentGeneratorComplete

/-- C7.5 / X.系8.3: `P_E` の state presheaf も descent topology 上の sheaf
(系8.3 の sitewide 前提の実証明)。 -/
theorem descent_equationStateSheaf :
    Site.AATSheafCondition descentSite descentPacket.equationStatePresheaf := by
  refine descent_sheafCondition descentPacket.equationStatePresheaf
    (fun V h e => liftStateVal V h e) ?_ ?_ ?_ ?_
  · exact liftStateVal_injective
  · exact liftStateVal_surjective
  · intro V' V f h' h e
    exact liftStateVal_restrict f h' h e
  · exact descentLiftState_subsingleton

/-- C7.5 / X.系8.3: base 水準の状態対応 `β_W`。 -/
noncomputable def descentBetaBase :
    descentPacket.repairSystem.State descentPacket.cover.base ->
      descentPacket.liftSystem.State descentPacket.cover.base :=
  fun p => ⟨(qOfVal base p.1, 1), rfl⟩

/-- `β_W` の chart restriction 整合(系8.3 の `hbetaW`)。 -/
theorem descentBetaBase_compat (i : descentPacket.cover.Index)
    (p : descentPacket.repairSystem.State descentPacket.cover.base) :
    descentPacket.liftSystem.restrictState (descentPacket.cover.inclusion i)
        (descentBetaBase p) =
      descentPacket.stateCorrespondence.beta (.chart i)
        (descentPacket.repairSystem.restrictState
          (descentPacket.cover.inclusion i) p) := by
  apply Subtype.ext
  apply Prod.ext
  · apply qEToZMod_injective _ (chartObj_keptCtx i)
    have hLHS : qEToZMod _ (chartObj_keptCtx i)
        (circleEquationSystem.obstructionQuotientRestrict
          (descentPacket.cover.inclusion i) (qOfVal base p.1)) = p.1 :=
      (qEToZMod_restrict (descentPacket.cover.inclusion i)
        (chartObj_keptCtx i) base_keptCtx (qOfVal base p.1)).trans
        (qEToZMod_qOfVal base base_keptCtx p.1)
    have hRHS : qEToZMod _ (chartObj_keptCtx i)
        (qOfVal _ (descentRestrict (descentPacket.cover.inclusion i) p).1) =
          p.1 := by
      rw [qEToZMod_qOfVal,
        descentRestrict_val_of_kept _ p (chartObj_keptCtx i)]
    exact hLHS.trans hRHS.symm
  · rfl

/-- C7.5 / X.系8.3 発火: `β_W` は全単射である(sitewide 拡張前提を
すべて放電した実適用)。 -/
theorem descent_betaBase_bijective : Function.Bijective descentBetaBase :=
  descentPacket.betaBase_bijective descentPacket_mem_topology
    descentPacket_trueSheaf descentRelationComplete descentGeneratorComplete
    descentBetaBase descentBetaBase_compat descent_equationStateSheaf

/-- C7.5 / X.系8.3 発火:
`Nonempty P_sem(W) ⟺ Nonempty P_E(W) ⟺ [r_E] = 0`(sitewide 拡張前提込みの
実適用。大域 equation lift の実在は `descent_equationGlobalLift_nonempty` が
named theorem として固定する)。 -/
theorem descent_sagaEquationGlobalLift :
    (Nonempty (GlobalRepair descentPacket.cover descentPacket.repairSystem) ↔
      Nonempty (descentPacket.liftSystem.State descentPacket.cover.base)) ∧
    (Nonempty (descentPacket.liftSystem.State descentPacket.cover.base) ↔
      (incComplex (equationCoefficient descentSite
        descentPacket.cover)).H1IsZero
        descentPacket.liftAtlas.residualClass) :=
  descentPacket.sagaEquationGlobalLift descentPacket_mem_topology
    descentPacket_trueSheaf descentRelationComplete descentGeneratorComplete
    descentBetaBase descentBetaBase_compat descent_equationStateSheaf

/-- C7.5 / X.系8.3 発火(sanity corollary、査読 Lean A lane の指摘による
named 化): 大域 equation lift が存在する。`Nonempty P_E(W)` 自体は状態担体
の構成から自明に真であり(`⟨(0, 1)⟩`)、本定理の内容は系8.3 の同値の実適用
の記録にある(Implementation notes (iv) と同じ注意)。 -/
theorem descent_equationGlobalLift_nonempty :
    Nonempty (descentPacket.liftSystem.State descentPacket.cover.base) :=
  descent_sagaEquationGlobalLift.1.mp descent_globalRepair_nonempty

/-- C7.5 / X.定理1.1 発火: descent packet 上の SAGA 中心定理(結論束)。 -/
theorem descent_sagaCentralTheorem :
    descentPacket.SagaCentralTheoremConclusions descentRelationComplete
      descentGeneratorComplete := by
  haveI : Fintype descentPacket.cover.Index := inferInstanceAs (Fintype (Fin 4))
  exact descentPacket.sagaCentralTheorem descentRelationComplete
    descentGeneratorComplete

/--
C7.5 総括(C7 `circle_nonzero_class_transfer` の零 class 双対): descent
fixture 上で `κ_*[r_sem] = [r_E]`、両 residual cochain は恒等的には零で
ないが両 class は零であり、系4.5 correction による corrected family の
**一意な** amalgamation として大域 repair が構成的に得られる(修復の
実在)。bare な `Nonempty P_sem(W)` は状態担体の構成から自明なため
(Implementation notes (iv))、最終成分は定理8.2 順方向の構成的な形で
主張する。
-/
theorem descent_zero_class_repair :
    (descentPacket.kappaStar descentRelationComplete descentGeneratorComplete
        descentPacket.repairAtlas.semanticResidualClass =
      descentPacket.liftAtlas.residualClass) ∧
    descentPacket.repairAtlas.semanticResidual ≠ 0 ∧
    descentPacket.liftAtlas.residual ≠ 0 ∧
    (descentPacket.presentation.semanticComplex descentPacket.cover).H1IsZero
      descentPacket.repairAtlas.semanticResidualClass ∧
    (incComplex (equationCoefficient descentSite
      descentPacket.cover)).H1IsZero
      descentPacket.liftAtlas.residualClass ∧
    ∃ b : Cochain0 (descentPacket.presentation.mSemPresheaf.onIntersections
        descentPacket.cover),
      ∃! t : GlobalRepair descentPacket.cover descentPacket.repairSystem,
        ∀ i, descentPacket.repairSystem.restrictState
            (descentPacket.cover.inclusion i) t =
          (descentPacket.repairAtlas.toLiftAtlas.corrected b).localLift i :=
  ⟨descent_sagaCentralTheorem.residual_transfer,
    descent_semanticResidual_ne_zero, descent_equationResidual_ne_zero,
    descent_semanticResidualClass_isZero, descent_equationResidualClass_isZero,
    descent_globalRepair_of_h1IsZero⟩

end DescentWitness
end Saga
end SemanticRepair
end AAT.AG

#assert_standard_axioms_only AAT.AG.SemanticRepair.Saga.DescentWitness
