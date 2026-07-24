import Formal.AG.SemanticRepair.Saga.OrderedComparison
import Formal.AG.SemanticRepair.Saga.KappaComparison

/-!
# Part X §8: true sheaf descent and actual global repair

* `AffineSemanticRepairSystem.statePresheaf`: the Part II Type-valued
  presheaf reading of the semantic state carrier (the Part II sheaf surface
  is `Type u`-valued, so this section pins the state universes to the site
  universe, as the Part IV coefficient surface already does).
* `TrueSemanticRepairSheaf` (Definition 8.1): the sheaf condition for all
  covers of the selected topology, plus the omitted-intersection subsingleton
  clause.  Condition (2) of the text is carried by the
  `AffineSemanticRepairSystem` fields; condition (3) is taken by each theorem
  as an explicit `hmem` hypothesis (the same proposition as
  `TopologicalMonomorphicCover.mem_topology`); no per-cover amalgamation map
  is taken as data.
* `exists_unique_glue`: the sheaf condition is **used** — a family matching
  on all ordered pairwise overlaps amalgamates to a unique global section
  (`Presieve.isSheafFor_arrows_iff` on the generated cover sieve).
* Theorem 8.2 (`globalRepair_of_h1IsZero`, `h1IsZero_of_globalRepair`,
  `globalRepair_nonempty_iff` and the packet-level triple equivalence
  `sagaGroundedGluing`): zero class → Corollary 4.5 correction → Lemma 2.1A
  matching-family upgrade (`matchingFamily_iff`, **used**) → sheaf
  amalgamation gives the unique global section restricting to the corrected
  family; conversely a global repair trivializes the residual by the torsor
  difference computation.  Uniqueness is claimed only for the amalgamation of
  the fixed corrected matching family — no subsingleton claim on `P_sem(W)`
  (text remark after Theorem 8.2).
* Corollary 8.3 (`betaBase_bijective`, `sagaEquationGlobalLift`): with the
  sitewide extension premises (a base-level `β_W` compatible with the chart
  restrictions, and the equation-side sheaf condition), `β_W` is a bijection
  and `Nonempty P_sem(W) ⟺ Nonempty P_E(W) ⟺ [r_E] = 0`.
* Principle 8.4: no nonabelian-torsor / higher-coherence / stack statement is
  derived from the additive comparison (stated scope; nothing is formalized
  beyond the additive theorems).
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory
open Opposite

universe u v

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {R : AtomOccurrenceReading S}
variable {𝒰 : MonomorphicOrderedCover S}

namespace AffineSemanticRepairSystem

variable {P : SemanticRepairPresentation.{u, v} S R}
variable (Psem : AffineSemanticRepairSystem.{u, v, u} P 𝒰)

/-- thin site: 平行な射に沿った semantic state restriction は一致する。 -/
theorem restrictState_hom_congr {X Y : S.category} (h h' : X ⟶ Y)
    (p : Psem.State Y) : Psem.restrictState h p = Psem.restrictState h' p := by
  rw [Subsingleton.elim h h']

/-- X.定義8.1 の担体: semantic state の Part II Type 値 presheaf 読み。 -/
def statePresheaf : Site.AATPresheaf S where
  obj V := Psem.State V.unop
  map f x := Psem.restrictState f.unop x
  map_id V := by
    funext x
    exact Psem.restrictState_id V.unop x
  map_comp f g := by
    funext x
    exact Psem.restrictState_comp g.unop f.unop x

@[simp]
theorem statePresheaf_map {V' V : S.category} (f : V' ⟶ V) (x : Psem.State V) :
    Psem.statePresheaf.map f.op x = Psem.restrictState f x :=
  rfl

end AffineSemanticRepairSystem

/--
X.定義8.1: true semantic repair sheaf。条件(1)が `isSheaf`(topology の全 cover
に対する sheaf condition)、条件(4)が omitted subsingleton 条項。条件(2)
(`M_sem` 作用の restriction 可換・局所 free/transitive)は
`AffineSemanticRepairSystem` の field が担い、条件(3)(`𝒰` の topology 所属)は
各定理が明示仮説 `hmem` として受け取る(`TopologicalMonomorphicCover.mem_topology`
と同一命題)。per-cover amalgamation map を別データとして置かない。
-/
structure TrueSemanticRepairSheaf {P : SemanticRepairPresentation.{u, v} S R}
    (𝒰 : MonomorphicOrderedCover S)
    (Psem : AffineSemanticRepairSystem.{u, v, u} P 𝒰) : Prop where
  isSheaf : Site.AATSheafCondition S Psem.statePresheaf
  psem_pair_subsingleton : ∀ i j, 𝒰.omittedPair i j ->
      Subsingleton (Psem.State (𝒰.pairCtx i j))
  psem_triple_subsingleton : ∀ i j k, 𝒰.omittedTriple i j k ->
      Subsingleton (Psem.State (𝒰.tripleCtx i j k))

/-- X.定義8.1: global semantic repair `GlobalRepair_sem(W) := P_sem(W)`。 -/
abbrev GlobalRepair {P : SemanticRepairPresentation.{u, v} S R}
    (𝒰 : MonomorphicOrderedCover S)
    (Psem : AffineSemanticRepairSystem.{u, v, u} P 𝒰) : Type u :=
  Psem.State 𝒰.base

section Gluing

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {Psem : AffineSemanticRepairSystem.{u, v, u} P 𝒰}
variable (hmem : Sieve.generate (Presieve.ofArrows 𝒰.chart 𝒰.inclusion) ∈
    S.topology 𝒰.base)

include hmem in
/--
sheaf condition の実使用(分離性): 全 chart への restriction が一致する
2つの global section は等しい。
-/
theorem state_separated (hsheaf : Site.AATSheafCondition S Psem.statePresheaf)
    {t t' : Psem.State 𝒰.base}
    (h : ∀ i, Psem.restrictState (𝒰.inclusion i) t =
      Psem.restrictState (𝒰.inclusion i) t') : t = t' := by
  have hArr : Presieve.IsSheafFor Psem.statePresheaf
      (Presieve.ofArrows 𝒰.chart 𝒰.inclusion) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsheaf _ hmem)
  have hkey := (Presieve.isSheafFor_arrows_iff _ _).mp hArr
    (fun i => Psem.restrictState (𝒰.inclusion i) t)
    (by
      intro i j Z gi gj hg
      show Psem.restrictState gi (Psem.restrictState (𝒰.inclusion i) t) =
        Psem.restrictState gj (Psem.restrictState (𝒰.inclusion j) t)
      rw [← Psem.restrictState_comp, ← Psem.restrictState_comp,
        Subsingleton.elim (gi ≫ 𝒰.inclusion i) (gj ≫ 𝒰.inclusion j)])
  rcases hkey with ⟨s, _, huniq⟩
  have ht : t = s := huniq t (fun i => rfl)
  have ht' : t' = s := huniq t' (fun i => (h i).symm)
  rw [ht, ht']

include hmem in
/--
X.定理8.2 の amalgamation 段(sheaf condition の実使用): 全 ordered pairwise
overlap 上で一致する chart family は一意な global section へ貼り合う。
-/
theorem exists_unique_glue
    (hsheaf : Site.AATSheafCondition S Psem.statePresheaf)
    (c : ∀ i, Psem.State (𝒰.chart i))
    (hmatch : ∀ i j, Psem.restrictState (𝒰.pairFst i j) (c i) =
      Psem.restrictState (𝒰.pairSnd i j) (c j)) :
    ∃! t : Psem.State 𝒰.base,
      ∀ i, Psem.restrictState (𝒰.inclusion i) t = c i := by
  have hArr : Presieve.IsSheafFor Psem.statePresheaf
      (Presieve.ofArrows 𝒰.chart 𝒰.inclusion) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsheaf _ hmem)
  exact (Presieve.isSheafFor_arrows_iff _ _).mp hArr c
    (by
      intro i j Z gi gj hg
      show Psem.restrictState gi (c i) = Psem.restrictState gj (c j)
      have h1 : Psem.restrictState gi (c i) =
          Psem.restrictState (𝒰.pairLift gi gj)
            (Psem.restrictState (𝒰.pairFst i j) (c i)) := by
        rw [← Psem.restrictState_comp]
        exact Psem.restrictState_hom_congr _ _ _
      rw [h1, hmatch i j, ← Psem.restrictState_comp]
      exact Psem.restrictState_hom_congr _ _ _)

end Gluing

/-! ## X.定理8.2: Grounded Global Gluing -/

namespace SagaEquationPacket

variable (packet : SagaEquationPacket.{u, v, u, u} S)
variable (hmem : Sieve.generate
    (Presieve.ofArrows packet.cover.chart packet.cover.inclusion) ∈
    S.topology packet.cover.base)
variable (htrue : TrueSemanticRepairSheaf packet.cover packet.repairSystem)

/-- packet の semantic 状態の `SiteStateData` 読み(補題2.1A の担体)。 -/
def semanticStateData : SiteStateData.{u, u} S where
  State := packet.repairSystem.State
  restrictState := packet.repairSystem.restrictState
  restrictState_id := packet.repairSystem.restrictState_id
  restrictState_comp := packet.repairSystem.restrictState_comp

include hmem htrue in
/--
X.定理8.2(順方向): `[r_sem] = 0` なら、系4.5 の correction による
corrected family を restriction として持つ global section が一意に存在する。
補題2.1A の matching family 昇格(`matchingFamily_iff`)と sheaf amalgamation
を実使用する。一意性は固定した corrected matching family の amalgamation に
ついてであり、`P_sem(W)` の subsingleton 性は主張しない。
-/
theorem globalRepair_of_h1IsZero
    (h : (packet.presentation.semanticComplex packet.cover).H1IsZero
      packet.repairAtlas.semanticResidualClass) :
    ∃ b : Cochain0 (packet.presentation.mSemPresheaf.onIntersections
        packet.cover),
      ∃! t : GlobalRepair packet.cover packet.repairSystem,
        ∀ i, packet.repairSystem.restrictState (packet.cover.inclusion i) t =
          (packet.repairAtlas.toLiftAtlas.corrected b).localLift i := by
  rcases (packet.repairAtlas.semanticResidualClass_isZero_iff_matching_correction).mp
    h with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  -- kept pair 上の一致を補題2.1A で全 ordered pair へ昇格する。
  have hall : ∀ i j,
      packet.repairSystem.restrictState (packet.cover.pairFst i j)
        ((packet.repairAtlas.toLiftAtlas.corrected b).localLift i) =
      packet.repairSystem.restrictState (packet.cover.pairSnd i j)
        ((packet.repairAtlas.toLiftAtlas.corrected b).localLift j) := by
    have hkept : ∀ q : KeptPair packet.cover,
        (packet.semanticStateData).restrictState
          (packet.cover.pairFst q.fst q.snd)
          ((packet.repairAtlas.toLiftAtlas.corrected b).localLift q.fst) =
        (packet.semanticStateData).restrictState
          (packet.cover.pairSnd q.fst q.snd)
          ((packet.repairAtlas.toLiftAtlas.corrected b).localLift q.snd) := by
      intro q
      exact (hb q).symm
    exact ((packet.semanticStateData).matchingFamily_iff
      (fun i j hij => htrue.psem_pair_subsingleton i j hij)
      (fun i => (packet.repairAtlas.toLiftAtlas.corrected b).localLift i)).mpr
      hkept
  exact exists_unique_glue hmem htrue.isSheaf _ hall

/--
X.定理8.2(逆方向): global repair が存在すれば `[r_sem] = 0`。
global section の restriction family は residual 零の atlas をなし、
定理4.4 により選択 atlas の residual は `δ⁰`-像になる。
-/
theorem h1IsZero_of_globalRepair
    (h : Nonempty (GlobalRepair packet.cover packet.repairSystem)) :
    (packet.presentation.semanticComplex packet.cover).H1IsZero
      packet.repairAtlas.semanticResidualClass := by
  rcases h with ⟨t⟩
  -- global section の restriction family を atlas として読む。
  set gAtlas : SemanticRepairAtlas packet.repairSystem :=
    ⟨fun i => packet.repairSystem.restrictState (packet.cover.inclusion i) t⟩
    with hgAtlas
  -- その residual は零(同一 global section の restrictions は pair 上一致)。
  have hzero : gAtlas.toLiftAtlas.residual = 0 := by
    rw [gAtlas.toLiftAtlas.residual_eq_zero_iff_matching]
    intro p
    show packet.repairSystem.restrictState (packet.cover.pairSnd p.fst p.snd)
        (packet.repairSystem.restrictState (packet.cover.inclusion p.snd) t) =
      packet.repairSystem.restrictState (packet.cover.pairFst p.fst p.snd)
        (packet.repairSystem.restrictState (packet.cover.inclusion p.fst) t)
    rw [← packet.repairSystem.restrictState_comp,
      ← packet.repairSystem.restrictState_comp]
    exact packet.repairSystem.restrictState_hom_congr _ _ _
  -- 定理4.4: 選択 atlas の residual は gauge の δ⁰-像。
  have hchoice := gAtlas.toLiftAtlas.residual_choice
    packet.repairAtlas.toLiftAtlas
  rw [hzero, zero_add] at hchoice
  apply (packet.repairAtlas.semanticResidualClass_isZero_iff_coboundary).mpr
  exact ⟨gAtlas.toLiftAtlas.gauge packet.repairAtlas.toLiftAtlas, hchoice⟩

include hmem htrue in
/-- X.定理8.2: `Nonempty P_sem(W) ⟺ [r_sem] = 0`。 -/
theorem globalRepair_nonempty_iff :
    Nonempty (GlobalRepair packet.cover packet.repairSystem) ↔
      (packet.presentation.semanticComplex packet.cover).H1IsZero
        packet.repairAtlas.semanticResidualClass := by
  constructor
  · exact packet.h1IsZero_of_globalRepair
  · intro h
    rcases packet.globalRepair_of_h1IsZero hmem htrue h with ⟨b, t, ht, _⟩
    exact ⟨t⟩

variable (hcomplete : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.RelationComplete σ)
variable (hgen : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.GeneratorComplete σ)

include hmem htrue hcomplete hgen in
/--
X.定理8.2(統合): `Nonempty P_sem(W) ⟺ [r_sem] = 0 ⟺ [r_E] = 0`
(最後の同値は定理7.6 の residual class 対応から)。
-/
theorem sagaGroundedGluing :
    (Nonempty (GlobalRepair packet.cover packet.repairSystem) ↔
      (packet.presentation.semanticComplex packet.cover).H1IsZero
        packet.repairAtlas.semanticResidualClass) ∧
    (Nonempty (GlobalRepair packet.cover packet.repairSystem) ↔
      (incComplex (equationCoefficient S packet.cover)).H1IsZero
        packet.liftAtlas.residualClass) := by
  refine ⟨packet.globalRepair_nonempty_iff hmem htrue, ?_⟩
  rw [packet.globalRepair_nonempty_iff hmem htrue]
  exact packet.sagaComparison_zero_iff hcomplete hgen

end SagaEquationPacket

/-! ## X.系8.3: equation-side global lift -/

namespace SagaEquationPacket

variable (packet : SagaEquationPacket.{u, v, u, u} S)
variable (hmem : Sieve.generate
    (Presieve.ofArrows packet.cover.chart packet.cover.inclusion) ∈
    S.topology packet.cover.base)
variable (htrue : TrueSemanticRepairSheaf packet.cover packet.repairSystem)
variable (hcomplete : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.RelationComplete σ)
variable (hgen : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.GeneratorComplete σ)

/-- equation 状態の Part II Type 値 presheaf 読み(系8.3 の sheaf 前提の担体)。 -/
def equationStatePresheaf : Site.AATPresheaf S where
  obj V := packet.liftSystem.State V.unop
  map f x := packet.liftSystem.restrictState f.unop x
  map_id V := by
    funext x
    exact packet.liftSystem.restrictState_id V.unop x
  map_comp f g := by
    funext x
    exact packet.liftSystem.restrictState_comp g.unop f.unop x

section Corollary83

-- 系8.3 の sitewide 拡張前提: base 水準の `β_W` と chart restriction 整合。
variable (betaW : packet.repairSystem.State packet.cover.base ->
    packet.liftSystem.State packet.cover.base)
variable (hbetaW : ∀ (i : packet.cover.Index)
    (p : packet.repairSystem.State packet.cover.base),
    packet.liftSystem.restrictState (packet.cover.inclusion i) (betaW p) =
      packet.stateCorrespondence.beta (.chart i)
        (packet.repairSystem.restrictState (packet.cover.inclusion i) p))
variable (hPEsheaf : Site.AATSheafCondition S packet.equationStatePresheaf)

include hmem hPEsheaf in
/-- equation 側の分離性(sheaf condition の帰結)。 -/
theorem equationState_separated
    {t t' : packet.liftSystem.State packet.cover.base}
    (h : ∀ i, packet.liftSystem.restrictState (packet.cover.inclusion i) t =
      packet.liftSystem.restrictState (packet.cover.inclusion i) t') :
    t = t' := by
  have hArr : Presieve.IsSheafFor packet.equationStatePresheaf
      (Presieve.ofArrows packet.cover.chart packet.cover.inclusion) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hPEsheaf _ hmem)
  have hkey := (Presieve.isSheafFor_arrows_iff _ _).mp hArr
    (fun i => packet.liftSystem.restrictState (packet.cover.inclusion i) t)
    (by
      intro i j Z gi gj hg
      show packet.liftSystem.restrictState gi
          (packet.liftSystem.restrictState (packet.cover.inclusion i) t) =
        packet.liftSystem.restrictState gj
          (packet.liftSystem.restrictState (packet.cover.inclusion j) t)
      rw [← packet.liftSystem.restrictState_comp,
        ← packet.liftSystem.restrictState_comp,
        Subsingleton.elim (gi ≫ packet.cover.inclusion i)
          (gj ≫ packet.cover.inclusion j)])
  rcases hkey with ⟨s, _, huniq⟩
  have ht : t = s := huniq t (fun i => rfl)
  have ht' : t' = s := huniq t' (fun i => (h i).symm)
  rw [ht, ht']

include hmem htrue hcomplete hbetaW in
/-- X.系8.3: `β_W` は単射である(局所単射性 + semantic 分離性)。 -/
theorem betaBase_injective : Function.Injective betaW := by
  intro p q hpq
  apply state_separated hmem htrue.isSheaf
  intro i
  have hi := congrArg
    (packet.liftSystem.restrictState (packet.cover.inclusion i)) hpq
  rw [hbetaW i p, hbetaW i q] at hi
  exact packet.stateCorrespondence.beta_injective
    (equationRelationSound packet.realization packet.stateCorrespondence
      packet.repairAtlas)
    (.chart i) (hcomplete (.chart i)) hi

include hmem htrue hcomplete hgen hbetaW hPEsheaf in
/-- X.系8.3: `β_W` は全射である(局所 preimage + 貼り合わせ + equation 分離性)。 -/
theorem betaBase_surjective : Function.Surjective betaW := by
  intro e
  have hsound := equationRelationSound packet.realization
    packet.stateCorrespondence packet.repairAtlas
  -- 各 chart で一意 preimage を選ぶ。
  have hlocal : ∀ i : packet.cover.Index,
      ∃ p : packet.repairSystem.State (packet.cover.chart i),
        packet.stateCorrespondence.beta (.chart i) p =
          packet.liftSystem.restrictState (packet.cover.inclusion i) e :=
    fun i => packet.stateCorrespondence.beta_surjective hsound (.chart i)
      (hgen (.chart i)) (packet.repairAtlas.localRepair i) _
  set c : ∀ i, packet.repairSystem.State (packet.cover.chart i) :=
    fun i => Classical.choose (hlocal i) with hc
  have hcspec : ∀ i, packet.stateCorrespondence.beta (.chart i) (c i) =
      packet.liftSystem.restrictState (packet.cover.inclusion i) e :=
    fun i => Classical.choose_spec (hlocal i)
  -- preimages は kept pair 上で一致(β naturality + pair 単射性)。
  have hkept : ∀ q : KeptPair packet.cover,
      packet.repairSystem.restrictState
        (packet.cover.pairFst q.fst q.snd) (c q.fst) =
      packet.repairSystem.restrictState
        (packet.cover.pairSnd q.fst q.snd) (c q.snd) := by
    intro q
    apply packet.stateCorrespondence.beta_injective hsound (.pair q)
      (hcomplete (.pair q))
    show packet.stateCorrespondence.beta (.pair q)
        (packet.repairSystem.restrictState (Face.pairLeft q).hom (c q.fst)) =
      packet.stateCorrespondence.beta (.pair q)
        (packet.repairSystem.restrictState (Face.pairRight q).hom (c q.snd))
    rw [← packet.stateCorrespondence.beta_natural (Face.pairLeft q),
      ← packet.stateCorrespondence.beta_natural (Face.pairRight q),
      hcspec q.fst, hcspec q.snd,
      ← packet.liftSystem.restrictState_comp,
      ← packet.liftSystem.restrictState_comp]
    exact packet.liftSystem.restrictState_hom_congr _ _ _
  -- 全 ordered pair へ昇格して貼り合わせる。
  have hall := ((packet.semanticStateData).matchingFamily_iff
    (fun i j hij => htrue.psem_pair_subsingleton i j hij) c).mpr hkept
  rcases exists_unique_glue hmem htrue.isSheaf c hall with ⟨p, hp, _⟩
  refine ⟨p, ?_⟩
  -- β_W p と e は全 chart 上で一致 → equation 分離性。
  apply packet.equationState_separated hmem hPEsheaf
  intro i
  rw [hbetaW i p, hp i, hcspec i]

include hmem htrue hcomplete hgen hbetaW hPEsheaf in
/-- X.系8.3: `β_W` は全単射である。 -/
theorem betaBase_bijective : Function.Bijective betaW :=
  ⟨packet.betaBase_injective hmem htrue hcomplete betaW hbetaW,
    packet.betaBase_surjective hmem htrue hcomplete hgen betaW hbetaW hPEsheaf⟩

include hmem htrue hcomplete hgen hbetaW hPEsheaf in
/--
X.系8.3: `Nonempty P_sem(W) ⟺ Nonempty P_E(W) ⟺ [r_E] = 0`。
零類から構成した matching lifts は equation 側 sheaf condition により
actual global equation lift へ貼り合わされる(`β_W` 全射の帰結)。
-/
theorem sagaEquationGlobalLift :
    (Nonempty (GlobalRepair packet.cover packet.repairSystem) ↔
      Nonempty (packet.liftSystem.State packet.cover.base)) ∧
    (Nonempty (packet.liftSystem.State packet.cover.base) ↔
      (incComplex (equationCoefficient S packet.cover)).H1IsZero
        packet.liftAtlas.residualClass) := by
  have hbij := packet.betaBase_bijective hmem htrue hcomplete hgen
    betaW hbetaW hPEsheaf
  have h1 : Nonempty (GlobalRepair packet.cover packet.repairSystem) ↔
      Nonempty (packet.liftSystem.State packet.cover.base) := by
    constructor
    · rintro ⟨p⟩
      exact ⟨betaW p⟩
    · rintro ⟨e⟩
      rcases hbij.2 e with ⟨p, _⟩
      exact ⟨p⟩
  refine ⟨h1, ?_⟩
  rw [← h1, packet.globalRepair_nonempty_iff hmem htrue]
  exact packet.sagaComparison_zero_iff hcomplete hgen

end Corollary83

end SagaEquationPacket

/-! ## X.定理1.1: SAGA 中心定理の最終束ね(R0 §4.9) -/

namespace SagaEquationPacket

variable (packet : SagaEquationPacket.{u, v, u, u} S)
variable (hcomplete : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.RelationComplete σ)
variable (hgen : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.GeneratorComplete σ)

/--
X.定理1.1(R0 §4.9): SAGA 中心定理の結論束。residual class 対応(定理7.5)、
零/非零同値(定理7.6)、および true sheaf 前提の下での grounded gluing
(定理8.2、本文「さらに … true sheaf であり … ならば」の条件節)を束ねる。
係数同型(系6.7 `phiEquiv`)・複体/cochain 可換(定理7.2)・cohomology 両側逆
(定理7.4)は named theorem 群が担う(§7 の surface)。
-/
structure SagaCentralTheoremConclusions : Prop where
  residual_transfer :
    packet.kappaStar hcomplete hgen packet.repairAtlas.semanticResidualClass =
      packet.liftAtlas.residualClass
  zero_iff :
    (packet.presentation.semanticComplex packet.cover).H1IsZero
        packet.repairAtlas.semanticResidualClass ↔
      (incComplex (equationCoefficient S packet.cover)).H1IsZero
        packet.liftAtlas.residualClass
  grounded_gluing :
    ∀ (_ : Sieve.generate
        (Presieve.ofArrows packet.cover.chart packet.cover.inclusion) ∈
        S.topology packet.cover.base)
      (_ : TrueSemanticRepairSheaf packet.cover packet.repairSystem),
      Nonempty (GlobalRepair packet.cover packet.repairSystem) ↔
        (packet.presentation.semanticComplex packet.cover).H1IsZero
          packet.repairAtlas.semanticResidualClass

/--
X.定理1.1(SAGA 中心定理、最終束ね): completeness 二条件(入力4)の下で
中心定理の結論束が成立する。`[Fintype]` は本文 §1 の有限添字集合の忠実転写
(comparison core と gluing の証明は有限性を使わない)。
-/
theorem sagaCentralTheorem [Fintype packet.cover.Index] :
    packet.SagaCentralTheoremConclusions hcomplete hgen where
  residual_transfer := packet.residual_correspondence_class hcomplete hgen
  zero_iff := packet.sagaComparison_zero_iff hcomplete hgen
  grounded_gluing hmem htrue := packet.globalRepair_nonempty_iff hmem htrue

end SagaEquationPacket

end Saga
end SemanticRepair
end AAT.AG
