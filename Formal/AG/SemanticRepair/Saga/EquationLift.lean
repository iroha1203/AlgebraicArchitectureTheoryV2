import Formal.AG.SemanticRepair.Saga.CechThreeTerm
import Formal.AG.LawAlgebra.LawEquation

/-!
# Part X §5 and the generic affine residual engine

* `AffineCoefficientLiftSystem` (Part X Definition 5.3, R0 §4.6): a sitewide
  state presheaf on which an intersection coefficient `Q` acts freely and
  transitively over `Int_{≤2}(𝒰)`, with `CoefficientLiftAtlas` as the selected
  local lift atlas (Theorem 1.1 input 6).
* the residual engine: `diffAt` (unique torsor difference), the generated
  residual cochain `residual`, Lemma 5.4 (`residual_cocycle`,
  `residual_choice`), and the Corollary 4.5-shaped zero-class equivalences —
  proved once over a generic coefficient and instantiated by both the
  semantic side (`Formal.AG.SemanticRepair.Saga.RepairTorsor`) and the
  equation side, mirroring the mathematical text where the Lemma 5.4 proof is
  the Lemma 4.3 / Theorem 4.4 computation verbatim.
* Part X Definition 5.1 / 5.2: `equationSitePresheaf` reads the Part III
  Theorem 11.4 coefficient `Q_E` from `LawAlgebra/LawEquation.lean`
  (`ObstructionQuotient`, reused, not reimplemented), and `equationComplex`
  is the geometric Čech complex `C_E = C(𝒰, Q_E)` of Definition 2.1.
* `LiftFiberData`: the Definition 5.3 typical instance — the local lift fiber
  of an additive short exact sequence `0 → Q → L → B → 0` over a selected
  base reading.

The residual is generated from the atlas differences; it is never supplied
as a selected 1-cocycle.  The G-07 declarations
`LocalLiftData` / `localLiftDifferenceFor(_cocycle)` /
`connectingClass_choice_independent` are used as proof patterns only
(no `ResearchLean` import).
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory
open Opposite

universe u w y

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {𝒰 : MonomorphicOrderedCover S}

/--
X.定義5.3(R0 §4.6): `Q` が作用する equation-lift local state。
carrier は presheaf(定義5.3 前文・系8.3 の sheaf 使用)、作用と affine 条件
(freeness / transitivity)は `Int_{≤2}(𝒰)` 上でだけ要求する。
-/
structure AffineCoefficientLiftSystem
    (Q : IntersectionCoefficientData.{u, w} 𝒰) where
  State : S.category -> Type y
  restrictState : ∀ {V' V : S.category}, (V' ⟶ V) -> State V -> State V'
  restrictState_id : ∀ (V : S.category) (e : State V), restrictState (𝟙 V) e = e
  restrictState_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (e : State V),
        restrictState (f ≫ g) e = restrictState f (restrictState g e)
  act : ∀ σ : IntersectionIndex 𝒰, Q.carrier σ -> State σ.ctx -> State σ.ctx
  act_zero : ∀ (σ : IntersectionIndex 𝒰) (e : State σ.ctx), act σ 0 e = e
  act_add : ∀ (σ : IntersectionIndex 𝒰) (q q' : Q.carrier σ) (e : State σ.ctx),
      act σ (q + q') e = act σ q (act σ q' e)
  act_restrict : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (q : Q.carrier τ) (e : State τ.ctx),
      restrictState f.hom (act τ q e) =
        act σ (Q.restrict f q) (restrictState f.hom e)
  free : ∀ (σ : IntersectionIndex 𝒰) (e : State σ.ctx) (q : Q.carrier σ),
      act σ q e = e -> q = 0
  transitive : ∀ (σ : IntersectionIndex 𝒰) (e e' : State σ.ctx),
      ∃ q : Q.carrier σ, e' = act σ q e

/-- X.定義4.2 / 5.3(R0 §4.6): selected local lift atlas(定理1.1 入力6b)。 -/
structure CoefficientLiftAtlas {Q : IntersectionCoefficientData.{u, w} 𝒰}
    (L : AffineCoefficientLiftSystem.{u, w, y} Q) where
  localLift : ∀ i : 𝒰.Index, L.State (𝒰.chart i)

namespace AffineCoefficientLiftSystem

variable {Q : IntersectionCoefficientData.{u, w} 𝒰}
variable (L : AffineCoefficientLiftSystem.{u, w, y} Q)

/-- thin site: 平行な射に沿った state restriction は一致する。 -/
theorem restrictState_hom_congr {X Y : S.category} (h h' : X ⟶ Y)
    (e : L.State Y) : L.restrictState h e = L.restrictState h' e := by
  rw [Subsingleton.elim h h']

/-- 作用の左簡約(freeness の帰結)。 -/
theorem act_cancel (σ : IntersectionIndex 𝒰) {e : L.State σ.ctx}
    {q q' : Q.carrier σ} (h : L.act σ q e = L.act σ q' e) : q = q' := by
  have h3 := congrArg (L.act σ (-q')) h
  rw [← L.act_add, ← L.act_add, neg_add_cancel, L.act_zero] at h3
  have h4 : L.act σ (q - q') e = e := by
    calc L.act σ (q - q') e = L.act σ (-q' + q) e := by
          rw [sub_eq_add_neg, add_comm]
      _ = e := h3
  exact sub_eq_zero.mp (L.free σ e _ h4)

/-- torsor 差: `e' = diffAt e e' + e` を満たす一意な係数(選択で生成)。 -/
def diffAt (σ : IntersectionIndex 𝒰) (e e' : L.State σ.ctx) : Q.carrier σ :=
  Classical.choose (L.transitive σ e e')

/-- torsor 差の定義性質。 -/
theorem act_diffAt (σ : IntersectionIndex 𝒰) (e e' : L.State σ.ctx) :
    L.act σ (L.diffAt σ e e') e = e' :=
  (Classical.choose_spec (L.transitive σ e e')).symm

/-- torsor 差の一意性(差の生成が supplied でないことの根拠)。 -/
theorem diffAt_unique (σ : IntersectionIndex 𝒰) {e e' : L.State σ.ctx}
    {q : Q.carrier σ} (h : e' = L.act σ q e) : q = L.diffAt σ e e' :=
  L.act_cancel σ (by rw [L.act_diffAt, ← h])

@[simp]
theorem diffAt_self (σ : IntersectionIndex 𝒰) (e : L.State σ.ctx) :
    L.diffAt σ e e = 0 :=
  (L.diffAt_unique σ (by rw [L.act_zero])).symm

/-- torsor 差の合成則(cocycle 計算の中核)。 -/
theorem diffAt_comp (σ : IntersectionIndex 𝒰) (e e' e'' : L.State σ.ctx) :
    L.diffAt σ e e'' = L.diffAt σ e' e'' + L.diffAt σ e e' :=
  (L.diffAt_unique σ (by rw [L.act_add, L.act_diffAt, L.act_diffAt])).symm

/-- torsor 差は零のとき、かつそのときに限り両状態が一致する。 -/
theorem diffAt_eq_zero_iff (σ : IntersectionIndex 𝒰) (e e' : L.State σ.ctx) :
    L.diffAt σ e e' = 0 ↔ e' = e := by
  constructor
  · intro h
    have := L.act_diffAt σ e e'
    rw [h, L.act_zero] at this
    exact this.symm
  · intro h
    rw [h]
    exact L.diffAt_self σ e

/-- torsor 差は face restriction と可換する。 -/
theorem diffAt_restrict {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    (e e' : L.State τ.ctx) :
    Q.restrict f (L.diffAt τ e e') =
      L.diffAt σ (L.restrictState f.hom e) (L.restrictState f.hom e') := by
  refine L.diffAt_unique σ ?_
  rw [← L.act_restrict f, L.act_diffAt]

end AffineCoefficientLiftSystem

namespace CoefficientLiftAtlas

variable {Q : IntersectionCoefficientData.{u, w} 𝒰}
variable {L : AffineCoefficientLiftSystem.{u, w, y} Q}

/-- chart 状態の kept pair overlap への restriction(左)。 -/
def leftOn (atlas : CoefficientLiftAtlas L) (p : KeptPair 𝒰) :
    L.State (𝒰.pairCtx p.fst p.snd) :=
  L.restrictState (𝒰.pairFst p.fst p.snd) (atlas.localLift p.fst)

/-- chart 状態の kept pair overlap への restriction(右)。 -/
def rightOn (atlas : CoefficientLiftAtlas L) (p : KeptPair 𝒰) :
    L.State (𝒰.pairCtx p.fst p.snd) :=
  L.restrictState (𝒰.pairSnd p.fst p.snd) (atlas.localLift p.snd)

/--
X.定義4.2 / 5.3: atlas の差から生成される residual cochain
`e_j| = r_ij + e_i|`。selected 1-cocycle として供給されない。
-/
def residual (atlas : CoefficientLiftAtlas L) : Cochain1 Q :=
  fun p => L.diffAt (.pair p) (atlas.leftOn p) (atlas.rightOn p)

/--
X.補題4.3 / 補題5.4 前半: 生成 residual は 1-cocycle である。
三 chart の triple restriction の torsor 差へ collapse し、
`diffAt_comp` で相殺する(G-07 `localLiftDifferenceFor_cocycle` pattern)。
-/
theorem residual_cocycle (atlas : CoefficientLiftAtlas L) :
    delta1 Q atlas.residual = 0 := by
  funext t
  simp only [delta1, AddMonoidHom.mk'_apply, Pi.zero_apply]
  set T : IntersectionIndex 𝒰 := .triple t with hT
  set Ei : L.State (𝒰.tripleCtx t.fst t.snd t.trd) :=
    L.restrictState ((Face.tripleIJ t).hom ≫ 𝒰.pairFst t.fst t.snd)
      (atlas.localLift t.fst) with hEi
  set Ej : L.State (𝒰.tripleCtx t.fst t.snd t.trd) :=
    L.restrictState ((Face.tripleIJ t).hom ≫ 𝒰.pairSnd t.fst t.snd)
      (atlas.localLift t.snd) with hEj
  set Ek : L.State (𝒰.tripleCtx t.fst t.snd t.trd) :=
    L.restrictState ((Face.tripleIK t).hom ≫ 𝒰.pairSnd t.fst t.trd)
      (atlas.localLift t.trd) with hEk
  have cJK : Q.restrict (Face.tripleJK t) (atlas.residual t.pairJK) =
      L.diffAt T Ej Ek := by
    show Q.restrict (Face.tripleJK t)
        (L.diffAt (.pair t.pairJK) (atlas.leftOn t.pairJK)
          (atlas.rightOn t.pairJK)) = L.diffAt T Ej Ek
    rw [L.diffAt_restrict (Face.tripleJK t)]
    have h1 : L.restrictState (Face.tripleJK t).hom (atlas.leftOn t.pairJK) =
        Ej := by
      show L.restrictState (Face.tripleJK t).hom
        (L.restrictState (𝒰.pairFst t.snd t.trd) (atlas.localLift t.snd)) = Ej
      rw [← L.restrictState_comp, hEj]
      exact L.restrictState_hom_congr _ _ _
    have h2 : L.restrictState (Face.tripleJK t).hom (atlas.rightOn t.pairJK) =
        Ek := by
      show L.restrictState (Face.tripleJK t).hom
        (L.restrictState (𝒰.pairSnd t.snd t.trd) (atlas.localLift t.trd)) = Ek
      rw [← L.restrictState_comp, hEk]
      exact L.restrictState_hom_congr _ _ _
    rw [h1, h2]
  have cIK : Q.restrict (Face.tripleIK t) (atlas.residual t.pairIK) =
      L.diffAt T Ei Ek := by
    show Q.restrict (Face.tripleIK t)
        (L.diffAt (.pair t.pairIK) (atlas.leftOn t.pairIK)
          (atlas.rightOn t.pairIK)) = L.diffAt T Ei Ek
    rw [L.diffAt_restrict (Face.tripleIK t)]
    have h1 : L.restrictState (Face.tripleIK t).hom (atlas.leftOn t.pairIK) =
        Ei := by
      show L.restrictState (Face.tripleIK t).hom
        (L.restrictState (𝒰.pairFst t.fst t.trd) (atlas.localLift t.fst)) = Ei
      rw [← L.restrictState_comp, hEi]
      exact L.restrictState_hom_congr _ _ _
    have h2 : L.restrictState (Face.tripleIK t).hom (atlas.rightOn t.pairIK) =
        Ek := by
      show L.restrictState (Face.tripleIK t).hom
        (L.restrictState (𝒰.pairSnd t.fst t.trd) (atlas.localLift t.trd)) = Ek
      rw [← L.restrictState_comp, hEk]
    rw [h1, h2]
  have cIJ : Q.restrict (Face.tripleIJ t) (atlas.residual t.pairIJ) =
      L.diffAt T Ei Ej := by
    show Q.restrict (Face.tripleIJ t)
        (L.diffAt (.pair t.pairIJ) (atlas.leftOn t.pairIJ)
          (atlas.rightOn t.pairIJ)) = L.diffAt T Ei Ej
    rw [L.diffAt_restrict (Face.tripleIJ t)]
    have h1 : L.restrictState (Face.tripleIJ t).hom (atlas.leftOn t.pairIJ) =
        Ei := by
      show L.restrictState (Face.tripleIJ t).hom
        (L.restrictState (𝒰.pairFst t.fst t.snd) (atlas.localLift t.fst)) = Ei
      rw [← L.restrictState_comp, hEi]
    have h2 : L.restrictState (Face.tripleIJ t).hom (atlas.rightOn t.pairIJ) =
        Ej := by
      show L.restrictState (Face.tripleIJ t).hom
        (L.restrictState (𝒰.pairSnd t.fst t.snd) (atlas.localLift t.snd)) = Ej
      rw [← L.restrictState_comp, hEj]
    rw [h1, h2]
  rw [cJK, cIK, cIJ, L.diffAt_comp T Ei Ej Ek]
  abel

/-- 2つの atlas の chart ごとの torsor 差(定理4.4 の `a_i`)。 -/
def gauge (atlas atlas' : CoefficientLiftAtlas L) : Cochain0 Q :=
  fun i => L.diffAt (.chart i) (atlas.localLift i) (atlas'.localLift i)

/--
X.定理4.4 / 補題5.4 後半: atlas 取り替えは residual を `δ⁰`-像だけ動かす
(G-07 `connectingClass_choice_independent` pattern)。
-/
theorem residual_choice (atlas atlas' : CoefficientLiftAtlas L) :
    atlas'.residual = atlas.residual + delta0 Q (atlas.gauge atlas') := by
  funext p
  show atlas'.residual p =
    atlas.residual p +
      (Q.restrict (Face.pairRight p) (atlas.gauge atlas' p.snd) -
        Q.restrict (Face.pairLeft p) (atlas.gauge atlas' p.fst))
  have hr : atlas'.rightOn p =
      L.act (.pair p) (Q.restrict (Face.pairRight p) (atlas.gauge atlas' p.snd))
        (atlas.rightOn p) := by
    show L.restrictState (Face.pairRight p).hom (atlas'.localLift p.snd) =
      L.act (.pair p) (Q.restrict (Face.pairRight p)
        (L.diffAt (.chart p.snd) (atlas.localLift p.snd)
          (atlas'.localLift p.snd)))
        (L.restrictState (Face.pairRight p).hom (atlas.localLift p.snd))
    rw [L.diffAt_restrict (Face.pairRight p), L.act_diffAt]
  have hl : atlas'.leftOn p =
      L.act (.pair p) (Q.restrict (Face.pairLeft p) (atlas.gauge atlas' p.fst))
        (atlas.leftOn p) := by
    show L.restrictState (Face.pairLeft p).hom (atlas'.localLift p.fst) =
      L.act (.pair p) (Q.restrict (Face.pairLeft p)
        (L.diffAt (.chart p.fst) (atlas.localLift p.fst)
          (atlas'.localLift p.fst)))
        (L.restrictState (Face.pairLeft p).hom (atlas.localLift p.fst))
    rw [L.diffAt_restrict (Face.pairLeft p), L.act_diffAt]
  refine (L.diffAt_unique (.pair p) ?_).symm
  rw [hr, hl]
  set gj := Q.restrict (Face.pairRight p) (atlas.gauge atlas' p.snd)
  set gi := Q.restrict (Face.pairLeft p) (atlas.gauge atlas' p.fst)
  calc L.act (.pair p) gj (atlas.rightOn p) =
      L.act (.pair p) gj
        (L.act (.pair p) (atlas.residual p) (atlas.leftOn p)) := by
        rw [residual, L.act_diffAt]
    _ = L.act (.pair p) (gj + atlas.residual p) (atlas.leftOn p) := by
        rw [L.act_add]
    _ = L.act (.pair p)
          ((atlas.residual p + (gj - gi)) + gi) (atlas.leftOn p) := by
        congr 1
        abel
    _ = L.act (.pair p) (atlas.residual p + (gj - gi))
          (L.act (.pair p) gi (atlas.leftOn p)) := by
        rw [L.act_add]

/-- residual の cover-relative `H¹` class(生成)。 -/
def residualClass (atlas : CoefficientLiftAtlas L) : IncH1 Q :=
  Quotient.mk (incComplex Q).H1CoboundarySetoid
    ⟨atlas.residual, atlas.residual_cocycle⟩

/-- X.定理4.4 / 補題5.4: residual class は atlas の選択に依存しない。 -/
theorem residualClass_choice_independent
    (atlas atlas' : CoefficientLiftAtlas L) :
    atlas'.residualClass = atlas.residualClass := by
  apply Quotient.sound
  refine ⟨atlas.gauge atlas', ?_⟩
  show atlas'.residual - atlas.residual = delta0 Q (atlas.gauge atlas')
  rw [atlas.residual_choice atlas']
  abel

/-- X.系4.5(1⟺2): 零類と `δ⁰`-像性の同値。 -/
theorem residualClass_isZero_iff_coboundary (atlas : CoefficientLiftAtlas L) :
    (incComplex Q).H1IsZero atlas.residualClass ↔
      ∃ b : Cochain0 Q, atlas.residual = delta0 Q b := by
  constructor
  · intro h
    have h' := Quotient.exact h
    rcases h' with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have : atlas.residual - 0 = delta0 Q b := hb
    rw [sub_zero] at this
    exact this
  · intro ⟨b, hb⟩
    apply Quotient.sound
    refine ⟨b, ?_⟩
    show atlas.residual - 0 = delta0 Q b
    rw [sub_zero]
    exact hb

/-- 補正 atlas `e_i^corr = (-b_i) + e_i`(系4.5 条件3 の担体)。 -/
def corrected (atlas : CoefficientLiftAtlas L) (b : Cochain0 Q) :
    CoefficientLiftAtlas L :=
  ⟨fun i => L.act (.chart i) (-(b i)) (atlas.localLift i)⟩

/-- atlas が全 kept pairwise overlap 上で一致すること。 -/
def MatchingOnKeptPairs (atlas : CoefficientLiftAtlas L) : Prop :=
  ∀ p : KeptPair 𝒰, atlas.rightOn p = atlas.leftOn p

/-- residual が零 cochain であることと overlap 一致は同値。 -/
theorem residual_eq_zero_iff_matching (atlas : CoefficientLiftAtlas L) :
    atlas.residual = 0 ↔ atlas.MatchingOnKeptPairs := by
  constructor
  · intro h p
    have := congrFun h p
    rw [residual, Pi.zero_apply, L.diffAt_eq_zero_iff] at this
    exact this
  · intro h
    funext p
    rw [residual, Pi.zero_apply, L.diffAt_eq_zero_iff]
    exact h p

/-- 補正 atlas の residual は `δ⁰ b` だけずれる。 -/
theorem corrected_residual (atlas : CoefficientLiftAtlas L) (b : Cochain0 Q) :
    (atlas.corrected b).residual = atlas.residual - delta0 Q b := by
  have hg : atlas.gauge (atlas.corrected b) = -b := by
    funext i
    show L.diffAt (.chart i) (atlas.localLift i)
      (L.act (.chart i) (-(b i)) (atlas.localLift i)) = -b i
    exact (L.diffAt_unique (.chart i) rfl).symm
  rw [atlas.residual_choice (atlas.corrected b), hg, map_neg]
  abel

/-- X.系4.5(1⟺3): 零類と corrected matching family の存在は同値。 -/
theorem residualClass_isZero_iff_matching_correction
    (atlas : CoefficientLiftAtlas L) :
    (incComplex Q).H1IsZero atlas.residualClass ↔
      ∃ b : Cochain0 Q, (atlas.corrected b).MatchingOnKeptPairs := by
  rw [atlas.residualClass_isZero_iff_coboundary]
  constructor
  · intro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [← (atlas.corrected b).residual_eq_zero_iff_matching,
      atlas.corrected_residual, hb, sub_self]
  · intro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have h0 := ((atlas.corrected b).residual_eq_zero_iff_matching).mpr hb
    rw [atlas.corrected_residual] at h0
    have := sub_eq_zero.mp h0
    exact this

end CoefficientLiftAtlas

/-! ## X.定義5.1–5.2: `Q_E` の再利用と幾何側複体 `C_E` -/

/--
X.定義5.1: Part III 定理11.4 の `Q_E = O_E / I_Ob^E` を site 全域 presheaf
データとして読む。`LawAlgebra/LawEquation.lean` の `ObstructionQuotient` /
`obstructionQuotientRestrict` の再利用であり、再実装しない。
-/
def equationSitePresheaf (S : Site.AATSite A) : SitePresheafData.{u, u} S where
  carrier V := S.equationSystem.ObstructionQuotient V
  addCommGroup _ := inferInstance
  restrict f := (S.equationSystem.obstructionQuotientRestrict f).toAddMonoidHom
  restrict_id V x := S.equationSystem.obstructionQuotientRestrict_id_apply V x
  restrict_comp f g x :=
    S.equationSystem.obstructionQuotientRestrict_comp_apply f g x

/--
X.定義5.2: 幾何側 Čech complex `C_E^•(𝒰) = C^•(𝒰, Q_E)`(定義2.1 の適用)。
semantic atom・semantic relation・`M_sem` はこの定義に使われない。
-/
def equationComplex (S : Site.AATSite A) (𝒰 : MonomorphicOrderedCover S) :
    Cohomology.AdditiveThreeTermComplex
      (Cochain0 ((equationSitePresheaf S).onIntersections 𝒰))
      (Cochain1 ((equationSitePresheaf S).onIntersections 𝒰))
      (Cochain2 ((equationSitePresheaf S).onIntersections 𝒰)) :=
  incComplex ((equationSitePresheaf S).onIntersections 𝒰)

/-! ## X.定義5.3 の典型 instance: short exact sequence の lift fiber -/

/--
X.定義5.3 典型例: additive short exact sequence `0 → Q → L → B → 0` と
selected base reading の local lift fiber データ。
-/
structure LiftFiberData (Q L B : SitePresheafData.{u, w} S) where
  incl : ∀ V : S.category, Q.carrier V →+ L.carrier V
  incl_natural : ∀ {V' V : S.category} (f : V' ⟶ V) (q : Q.carrier V),
      L.restrict f (incl V q) = incl V' (Q.restrict f q)
  proj : ∀ V : S.category, L.carrier V →+ B.carrier V
  proj_natural : ∀ {V' V : S.category} (f : V' ⟶ V) (l : L.carrier V),
      B.restrict f (proj V l) = proj V' (L.restrict f l)
  incl_injective : ∀ (V : S.category) (q : Q.carrier V), incl V q = 0 -> q = 0
  exact_at_middle : ∀ (V : S.category) (l : L.carrier V),
      proj V l = 0 ↔ ∃ q : Q.carrier V, incl V q = l
  /-- selected global base reading の各 context 値。 -/
  base : ∀ V : S.category, B.carrier V
  base_natural : ∀ {V' V : S.category} (f : V' ⟶ V),
      B.restrict f (base V) = base V'

namespace LiftFiberData

variable {Q L B : SitePresheafData.{u, w} S}

/--
X.定義5.3 典型例: lift fiber は `Q` が free かつ transitive に作用する
affine local-state system をなす。
-/
def liftSystem (D : LiftFiberData Q L B) (𝒰 : MonomorphicOrderedCover S) :
    AffineCoefficientLiftSystem.{u, w, w} ((Q.onIntersections 𝒰)) where
  State V := {l : L.carrier V // D.proj V l = D.base V}
  restrictState {V' V} f l :=
    ⟨L.restrict f l.1, by rw [← D.proj_natural f, l.2, D.base_natural f]⟩
  restrictState_id V l := Subtype.ext (L.restrict_id V l.1)
  restrictState_comp f g l := Subtype.ext (L.restrict_comp f g l.1)
  act σ q l :=
    ⟨l.1 + D.incl σ.ctx q, by
      rw [map_add, l.2, (D.exact_at_middle σ.ctx (D.incl σ.ctx q)).mpr ⟨q, rfl⟩,
        add_zero]⟩
  act_zero σ l := Subtype.ext (by simp)
  act_add σ q q' l := Subtype.ext (by
    show l.1 + D.incl σ.ctx (q + q') = l.1 + D.incl σ.ctx q' + D.incl σ.ctx q
    rw [map_add]
    abel)
  act_restrict {σ τ} f q l := Subtype.ext (by
    show L.restrict f.hom (l.1 + D.incl τ.ctx q) =
      L.restrict f.hom l.1 + D.incl σ.ctx ((Q.onIntersections 𝒰).restrict f q)
    rw [map_add, D.incl_natural f.hom q]
    rfl)
  free σ l q h := by
    have h1 : l.1 + D.incl σ.ctx q = l.1 := congrArg Subtype.val h
    exact D.incl_injective σ.ctx q
      (add_left_cancel (h1.trans (add_zero l.1).symm))
  transitive σ l l' := by
    have hproj : D.proj σ.ctx (l'.1 - l.1) = 0 := by
      rw [map_sub, l.2, l'.2, sub_self]
    rcases (D.exact_at_middle σ.ctx (l'.1 - l.1)).mp hproj with ⟨q, hq⟩
    refine ⟨q, Subtype.ext ?_⟩
    show l'.1 = l.1 + D.incl σ.ctx q
    rw [hq]
    abel

end LiftFiberData

end Saga
end SemanticRepair
end AAT.AG
