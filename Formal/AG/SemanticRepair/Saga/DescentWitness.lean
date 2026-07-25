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
(`[r_sem] ≠ 0`, obstruction transfer, no `TopologicalMonomorphicCover`); this
file fixes the zero-class side (`[r_sem] = 0`, actual descent) and does not
re-implement the C7 non-identity comparison instance or negative conditions.

The three previously statement-only surfaces fired here (PR #3801 review):

1. **Theorem 8.2 / Corollary 8.3 nonvacuity**: `descentSite` selects coverage
   requirements under which the 4-chart cover is an admissible family, so
   `mem_topology` is constructed (`descentTopologicalCover`), the generated
   topology is classified (`descent_topology_classify`), and the sheaf
   condition for both state presheaves is proved on the whole topology.
2. **`SagaEquationPacket.ofProduction` concrete instance**: `descentPacket`
   is assembled through the production constructor; its equation-side fields
   are `SupportAtomEquationSelection.realization` and
   `LiftFiberData.equationLiftSystem` applied to concrete data (#3734 route).
3. **Definition 5.3 typical-example nondegenerate firing**:
   `descentLiftFiber` carries the nonzero base reading `B_E = F₂`, `b ≡ 1`
   (`descentLiftFiber_base_ne_zero`), the selected lift problem genuinely
   constrains the state fiber (`descentLiftFiber_zero_not_in_fiber`), and the
   generated equation residual cochain is not identically zero while its
   class is a coboundary (`descent_equationResidual_ne_zero`,
   `descent_equationResidualClass_isZero`).

Context-lattice, equation-system, occurrence and coefficient computations are
reused term-level from `CircleWitness` (they are site-independent or
definitionally transferable); only the coverage requirements, the untwisted
state systems, the production fiber, and the descent theorems are new.
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
これにより admissible family は4 chart をすべて patch に含むことを強制され、
生成 topology は `descent_topology_classify` の形に分類できる(C7 の
all-`False` requirements とは異なり、cover sieve が実際に topology に入る)。
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
theorem chartObjKept (i : Fin 4) : KeptCtx (chartObj i).ctx := by
  refine ⟨recognized_context _, ?_⟩
  rw [show (chartObj i).ctx = context {i} from rfl, indexOf_context]
  exact singleton_mem_keptSets i

/-- base context は kept(空 index は keptSets に属する)。 -/
theorem baseKept : KeptCtx base.ctx := by
  refine ⟨recognized_context _, ?_⟩
  rw [show base.ctx = context ∅ from rfl, indexOf_context]
  decide

/-- descent cover の intersection-diagram context はすべて kept。 -/
theorem descent_keptCtx_of_intersection (σ : IntersectionIndex descentCover) :
    KeptCtx σ.ctx.ctx := by
  cases σ with
  | chart i => exact chartObjKept i
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
theorem obj_ext {X Y : descentSite.category} (h : X.ctx = Y.ctx) : X = Y := by
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
    · have hXbase : X = base := obj_ext hX
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
    · have hXbase : X = base := obj_ext hX
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
(大域 repair の実在が本 witness の主張であるため)。 -/
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
  localRepair i := ⟨atlasVal i, Or.inl (chartObjKept i)⟩

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
theorem descentPairKept (p : descentCover.KeptPair) :
    KeptCtx (descentCover.pairCtx p.fst p.snd).ctx :=
  descent_keptCtx_of_intersection (.pair p)

/-- C7.5: 生成 semantic residual の `F₂` 値は atlas 値の差
`a_{p.snd} - a_{p.fst}`(零 twist なので twist 項は現れない)。 -/
theorem descent_semanticResidual_val (p : descentCover.KeptPair) :
    mSemToZMod (descentCover.pairCtx p.fst p.snd) (descentPairKept p)
      (descentRepairAtlas.semanticResidual p) =
    atlasVal p.snd - atlasVal p.fst := by
  have hact := AffineCoefficientLiftSystem.act_diffAt
    (L := descentRepairSystem.toLiftSystem) (.pair p)
    (descentRepairAtlas.toLiftAtlas.leftOn p)
    (descentRepairAtlas.toLiftAtlas.rightOn p)
  have h1 : (descentRepairAtlas.toLiftAtlas.rightOn p).1 =
      (descentRepairAtlas.toLiftAtlas.leftOn p).1 +
        mSemToZMod (descentCover.pairCtx p.fst p.snd) (descentPairKept p)
          (descentRepairAtlas.semanticResidual p) := by
    conv_lhs => rw [← hact]
    exact descent_mact_val (.pair p) (descentRepairAtlas.semanticResidual p)
      (descentRepairAtlas.toLiftAtlas.leftOn p)
  have hleft : (descentRepairAtlas.toLiftAtlas.leftOn p).1 = atlasVal p.fst := by
    show (descentRestrict (descentCover.pairFst p.fst p.snd)
        (descentRepairAtlas.localRepair p.fst)).1 = _
    rw [descentRestrict_val_of_kept _ _ (descentPairKept p)]
    rfl
  have hright : (descentRepairAtlas.toLiftAtlas.rightOn p).1 = atlasVal p.snd := by
    show (descentRestrict (descentCover.pairSnd p.fst p.snd)
        (descentRepairAtlas.localRepair p.snd)).1 = _
    rw [descentRestrict_val_of_kept _ _ (descentPairKept p)]
    rfl
  rw [show mSemToZMod (descentCover.pairCtx p.fst p.snd) (descentPairKept p)
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
    (mSemToZMod _ (descentPairKept descentEdge01)) (congrFun h descentEdge01)
  rw [descent_semanticResidual_val] at hv
  simp only [Pi.zero_apply, map_zero] at hv
  exact absurd hv (by decide)

/-- C7.5: 補正 0-cochain `b_i = [a_i σ]`(semantic residual を coboundary
として実現する gauge。atlas 値の `M_sem` 読み)。 -/
noncomputable def descentGauge :
    Cochain0 (descentPresentation.mSemPresheaf.onIntersections descentCover) :=
  fun i => descentPresentation.mSemMk (descentCover.chart i)
    (Finsupp.single (sigma (descentCover.chart i) (chartObjKept i).1)
      (((atlasVal i).val : ℕ) : ℤ))

theorem descentGauge_val (i : Fin 4) :
    mSemToZMod (descentCover.chart i) (chartObjKept i) (descentGauge i) =
      atlasVal i := by
  show mSemToZMod (descentCover.chart i) (chartObjKept i)
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
  have hkept := descentPairKept p
  apply mSemToZMod_injective _ hkept
  rw [descent_semanticResidual_val]
  have hR : mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairRight p).hom
        (descentGauge p.snd)) = atlasVal p.snd :=
    (mSemToZMod_restrict (Face.pairRight p).hom hkept
      (chartObjKept p.snd) (descentGauge p.snd)).trans (descentGauge_val p.snd)
  have hL : mSemToZMod _ hkept
      (descentPresentation.mSemRestrict (Face.pairLeft p).hom
        (descentGauge p.fst)) = atlasVal p.fst :=
    (mSemToZMod_restrict (Face.pairLeft p).hom hkept
      (chartObjKept p.fst) (descentGauge p.fst)).trans (descentGauge_val p.fst)
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

/-! ## Sheaf condition engine over the classified topology -/

/--
C7.5: 分類済み descent topology 上の sheaf condition engine。kept context で
`F₂` への値写像が単射・全射・restriction 不変で、kept でない context の値が
subsingleton な Type 値 presheaf は sheaf condition を満たす。`P_sem` と
`P_E` の両 state presheaf をこの engine で放電する。
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
  · have hXbase : X = base := obj_ext hX
    subst hXbase
    rw [Site.AATSheafConditionFor]
    intro x hx
    set xi : ∀ i : Fin 4, F.obj (op (chartObj i)) :=
      fun i => x (chartInclusion i) (hcharts i (chartInclusion i)) with hxi
    have hadj : ∀ i j : Fin 4, ({i, j} : ContextIndex) ∈ keptSets ->
        val _ (chartObjKept i) (xi i) = val _ (chartObjKept j) (xi j) := by
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
      calc val _ (chartObjKept i) (xi i)
          = val _ hPk (F.map g₁.op (xi i)) :=
            (hrestrict g₁ hPk (chartObjKept i) (xi i)).symm
        _ = val _ hPk (F.map g₂.op (xi j)) := congrArg _ hcompat
        _ = val _ (chartObjKept j) (xi j) :=
            hrestrict g₂ hPk (chartObjKept j) (xi j)
    set v := val _ (chartObjKept 0) (xi 0) with hv
    have hvi : ∀ i : Fin 4, val _ (chartObjKept i) (xi i) = v := by
      have hval01 := hadj 0 1 (by decide)
      have hval12 := hadj 1 2 (by decide)
      have hval23 := hadj 2 3 (by decide)
      intro i
      fin_cases i
      · rfl
      · exact hval01.symm
      · exact (hval01.trans hval12).symm
      · exact ((hval01.trans hval12).trans hval23).symm
    obtain ⟨t, ht⟩ := hsurj base baseKept v
    refine ⟨t, ?_, ?_⟩
    · intro Y f hf
      by_cases hK : KeptCtx Y.ctx
      · apply hinj Y hK
        rw [hrestrict f hK baseKept t, ht]
        by_cases hYe : indexOf Y.ctx = ∅
        · have hle : contextLe (context {0}) Y.ctx := by
            rw [context_indexOf hK.1, hYe]
            exact Or.inr ⟨{0}, ∅, rfl, rfl, Finset.empty_subset _⟩
          have g : chartObj 0 ⟶ Y := homOfLE hle
          have hcompat := hx g (𝟙 (chartObj 0)) hf
            (hcharts 0 (chartInclusion 0)) (Subsingleton.elim _ _)
          have hthis := congrArg (val (chartObj 0) (chartObjKept 0)) hcompat
          rw [hrestrict g (chartObjKept 0) hK (x f hf)] at hthis
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
          rw [hrestrict g hK (chartObjKept i) (xi i)] at hthis
          simp only [op_id, F.map_id, types_id_apply] at hthis
          rw [hvi i] at hthis
          exact hthis.symm
      · haveI := hsub Y hK
        exact Subsingleton.elim _ _
    · intro t' ht'
      apply hinj base baseKept
      have h0 := ht' (chartInclusion 0) (hcharts 0 (chartInclusion 0))
      have hthis := congrArg (val (chartObj 0) (chartObjKept 0)) h0
      rw [hrestrict (chartInclusion 0) (chartObjKept 0) baseKept t'] at hthis
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
`0 → Q_E → Q_E × B_E → B_E → 0` と、恒等的に `1` の selected base reading。
`equationSelfLiftFiber`(`B_E = 0` の退化 instance)と異なり、解くべき局所
equation-lift problem の選択が実際に行われる。 -/
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
のと対照的)。 -/
theorem descentLiftFiber_zero_not_in_fiber (V : descentSite.category) :
    descentLiftFiber.proj V 0 ≠ descentLiftFiber.base V := by
  show (0 : ZMod 2) ≠ 1
  decide

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
    qEToZMod (descentCover.pairCtx p.fst p.snd) (descentPairKept p)
      (descentLiftAtlas.residual p) =
    atlasVal p.snd - atlasVal p.fst := by
  have hact := descentLiftSystem.act_diffAt (.pair p)
    (descentLiftAtlas.leftOn p) (descentLiftAtlas.rightOn p)
  have h1 : liftStateVal _ (descentPairKept p) (descentLiftAtlas.rightOn p) =
      liftStateVal _ (descentPairKept p) (descentLiftAtlas.leftOn p) +
        qEToZMod _ (descentPairKept p) (descentLiftAtlas.residual p) := by
    conv_lhs => rw [← hact]
    exact liftStateVal_act (.pair p) _ _
  have hleft : liftStateVal _ (descentPairKept p) (descentLiftAtlas.leftOn p) =
      atlasVal p.fst :=
    (liftStateVal_restrict (descentCover.pairFst p.fst p.snd)
        (descentPairKept p) (chartObjKept p.fst)
        (descentLiftAtlas.localLift p.fst)).trans
      (qEToZMod_qOfVal _ (chartObjKept p.fst) (atlasVal p.fst))
  have hright : liftStateVal _ (descentPairKept p) (descentLiftAtlas.rightOn p) =
      atlasVal p.snd :=
    (liftStateVal_restrict (descentCover.pairSnd p.fst p.snd)
        (descentPairKept p) (chartObjKept p.snd)
        (descentLiftAtlas.localLift p.snd)).trans
      (qEToZMod_qOfVal _ (chartObjKept p.snd) (atlasVal p.snd))
  rw [show qEToZMod (descentCover.pairCtx p.fst p.snd) (descentPairKept p)
      (descentLiftAtlas.residual p) =
    liftStateVal _ (descentPairKept p) (descentLiftAtlas.rightOn p) -
      liftStateVal _ (descentPairKept p) (descentLiftAtlas.leftOn p) from by
    rw [h1]; ring]
  rw [hleft, hright]

/-- C7.5 AC4: equation residual cochain は恒等的に零ではない
(辺 `(0,1)` で値 `1`)。 -/
theorem descent_equationResidual_ne_zero : descentLiftAtlas.residual ≠ 0 := by
  intro h
  have hv := congrArg (qEToZMod _ (descentPairKept descentEdge01))
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
  have hkept := descentPairKept p
  apply qEToZMod_injective _ hkept
  rw [descent_equationResidual_val]
  have hR : qEToZMod _ hkept
      ((equationCoefficient descentSite descentCover).restrict
        (Face.pairRight p) (descentEquationGauge p.snd)) = atlasVal p.snd :=
    (qEToZMod_restrict (Face.pairRight p).hom hkept (chartObjKept p.snd)
      (descentEquationGauge p.snd)).trans
      (qEToZMod_qOfVal _ (chartObjKept p.snd) (atlasVal p.snd))
  have hL : qEToZMod _ hkept
      ((equationCoefficient descentSite descentCover).restrict
        (Face.pairLeft p) (descentEquationGauge p.fst)) = atlasVal p.fst :=
    (qEToZMod_restrict (Face.pairLeft p).hom hkept (chartObjKept p.fst)
      (descentEquationGauge p.fst)).trans
      (qEToZMod_qOfVal _ (chartObjKept p.fst) (atlasVal p.fst))
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

/-- X.§1 入力8: omitted overlap 上の empty-overlap normalization。 -/
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
    descentLiftFiber descentLiftAtlas descentBeta descentNormalization

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

/-- C7.5 / X.定理8.2 発火: `[r_sem] = 0` から実際の大域 repair が存在する
(descent 結論の nonvacuity)。 -/
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
  · apply qEToZMod_injective _ (chartObjKept i)
    have hLHS : qEToZMod _ (chartObjKept i)
        (circleEquationSystem.obstructionQuotientRestrict
          (descentPacket.cover.inclusion i) (qOfVal base p.1)) = p.1 :=
      (qEToZMod_restrict (descentPacket.cover.inclusion i)
        (chartObjKept i) baseKept (qOfVal base p.1)).trans
        (qEToZMod_qOfVal base baseKept p.1)
    have hRHS : qEToZMod _ (chartObjKept i)
        (qOfVal _ (descentRestrict (descentPacket.cover.inclusion i) p).1) =
          p.1 := by
      rw [qEToZMod_qOfVal,
        descentRestrict_val_of_kept _ p (chartObjKept i)]
    exact hLHS.trans hRHS.symm
  · rfl

/-- C7.5 / X.系8.3 発火:
`Nonempty P_sem(W) ⟺ Nonempty P_E(W) ⟺ [r_E] = 0`(sitewide 拡張前提込みの
実適用。大域 equation lift の実在は `descent_globalRepair_nonempty` と併せて
従う)。 -/
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
ないが両 class は零であり、実際の大域 repair が存在する(修復の実在)。
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
    Nonempty (GlobalRepair descentPacket.cover descentPacket.repairSystem) :=
  ⟨descent_sagaCentralTheorem.residual_transfer,
    descent_semanticResidual_ne_zero, descent_equationResidual_ne_zero,
    descent_semanticResidualClass_isZero, descent_equationResidualClass_isZero,
    descent_globalRepair_nonempty⟩

end DescentWitness
end Saga
end SemanticRepair
end AAT.AG

#assert_standard_axioms_only AAT.AG.SemanticRepair.Saga.DescentWitness
