import Formal.AG.SemanticRepair.Saga.Exactness

/-!
# Part X Proposition 6.1A / Corollary 6.7: equation semantic realization

* `equationCoefficient`: the `Int_{≤2}(𝒰)` reading of the Part III
  Theorem 11.4 coefficient `Q_E` (reusing the C2 `equationSitePresheaf`;
  no independent redefinition, per R0 R5).
* `EquationSemanticRealization` (R0 §4.9): the selected restriction-compatible
  assignment `λ ↦ (i_λ, A_λ)` of Proposition 6.1A; the support Atom is the
  carrier atom of the presentation's occurrence projection `π_V(λ)`.
* `chiE` (Proposition 6.1A): the generated interpretation
  `χ^E_V(λ) = [ε_{V,A_λ,i_λ,π_V(λ)}]`, built from the Theorem 11.4 surface
  (`Ideal.Quotient.mk` of `equationResidual`, the `interpret` pattern of
  `LawAlgebra/LawEquation.lean`); its restriction naturality is proved from
  `equationResidual_restrict` and `obstructionQuotientRestrict_mk`, so `χ^E`
  is a `PrimaryCoefficientCorrespondence` — Definition 6.1 is realized.
* `SemanticRepairAtlas.witness`: the §1 remark that restricting the selected
  atlas makes every intersection state nonempty (feeds Lemma 6.2A).
* Corollary 6.7 (`equationPhi` / `equationPhiEquiv` / `equationPhi_natural`):
  Theorem 6.3 is **used** (not re-proved, not supplied): soundness comes from
  Lemma 6.2A via the atlas witnesses, and the two completeness conditions are
  the only supplied hypotheses.
* `EmptyOverlapNormalization` (Theorem 1.1 input 8, R0 §4.8): the selected
  triviality of `M_sem` / `Q_E` and subsingleton property of `P_sem` / `P_E`
  on omitted intersections, with the derivation lemmas that later children
  (C4/C5) consume as the Lemma 2.1A hypotheses.
* `SagaEquationPacket` (R0 §4.9): the Theorem 1.1 input bundle for the
  equation realization, with the named equation-side residual surface
  (`equationResidualCochain`, Lemma 5.4 wrappers).

No `Law.holds`, manual witness-ideal core, supplied `Φ`, inverse, or cochain
equivalence is taken as input.  The frozen G-06 route is untouched.
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory

universe u v x y

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {R : AtomOccurrenceReading S}
variable {𝒰 : MonomorphicOrderedCover S}

/--
X.定義5.1 の `Int_{≤2}(𝒰)` 読み(R0 R5): C2 の `equationSitePresheaf` を
再利用し、独立再定義しない。
-/
abbrev equationCoefficient (S : Site.AATSite A) (𝒰 : MonomorphicOrderedCover S) :
    IntersectionCoefficientData.{u, u} 𝒰 :=
  (equationSitePresheaf S).onIntersections 𝒰

/--
X.命題6.1A(R0 §4.9): supported semantic atom への required equation index
`i_λ` と local architecture reading `A_λ` の restriction-compatible な selected
対応。support Atom は presentation の occurrence projection `π_V(λ)` の台 Atom。
-/
structure EquationSemanticRealization
    (P : SemanticRepairPresentation.{u, v} S R)
    (𝒰 : MonomorphicOrderedCover S) : Type (max (u + 1) v) where
  lawIndex : ∀ σ : IntersectionIndex 𝒰,
      P.atomData.SupportedAtom σ.ctx -> S.equationSystem.Index
  lawIndex_required : ∀ (σ : IntersectionIndex 𝒰)
      (l : P.atomData.SupportedAtom σ.ctx),
      S.equationSystem.Required (lawIndex σ l)
  lawIndex_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (l : P.atomData.SupportedAtom τ.ctx),
      lawIndex σ (P.atomData.restrictSupported f.hom l) = lawIndex τ l
  archReading : ∀ σ : IntersectionIndex 𝒰,
      P.atomData.SupportedAtom σ.ctx -> ArchitectureObject U
  archReading_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (l : P.atomData.SupportedAtom τ.ctx),
      archReading σ (P.atomData.restrictSupported f.hom l) = archReading τ l

namespace EquationSemanticRealization

variable {P : SemanticRepairPresentation.{u, v} S R}
variable (real : EquationSemanticRealization P 𝒰)

/--
X.命題6.1A: equation semantic realization は primary coefficient
correspondence `χ^E_V(λ) = [ε_{V,A_λ,i_λ,π_V(λ)}]` を構成する。
構成は第III部 定理11.4 の生成面(`interpret` pattern:
`Ideal.Quotient.mk` + `equationResidual`)であり、naturality は
`equationResidual_restrict` + `obstructionQuotientRestrict_mk` +
realization の naturality field + occurrence の台 Atom 保存から証明される。
-/
def chiE : PrimaryCoefficientCorrespondence P (equationCoefficient S 𝒰) where
  chi σ l :=
    Ideal.Quotient.mk (S.equationSystem.obstructionIdeal σ.ctx)
      (S.equationSystem.equationResidual σ.ctx (real.archReading σ l)
        (real.lawIndex σ l) (P.atomData.projection σ.ctx l.1).atom)
  chi_natural {σ τ} f l := by
    show (S.equationSystem.obstructionQuotientRestrict f.hom)
        (Ideal.Quotient.mk (S.equationSystem.obstructionIdeal τ.ctx)
          (S.equationSystem.equationResidual τ.ctx (real.archReading τ l)
            (real.lawIndex τ l) (P.atomData.projection τ.ctx l.1).atom)) =
      Ideal.Quotient.mk (S.equationSystem.obstructionIdeal σ.ctx)
        (S.equationSystem.equationResidual σ.ctx
          (real.archReading σ (P.atomData.restrictSupported f.hom l))
          (real.lawIndex σ (P.atomData.restrictSupported f.hom l))
          (P.atomData.projection σ.ctx
            (P.atomData.restrictSupported f.hom l).1).atom)
    have hatom : (P.atomData.projection σ.ctx
        (P.atomData.restrictSupported f.hom l).1).atom =
        (P.atomData.projection τ.ctx l.1).atom := by
      show (P.atomData.projection σ.ctx
        (P.atomData.restrictAtom f.hom l.1)).atom = _
      rw [P.atomData.projection_natural f.hom l.1, R.occRestrict_atom]
    rw [S.equationSystem.obstructionQuotientRestrict_mk,
      S.equationSystem.equationResidual_restrict,
      real.archReading_natural f l, real.lawIndex_natural f l, hatom]

/-- X.命題6.1A の restriction naturality(theorem 面)。 -/
theorem chiE_natural {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    (l : P.atomData.SupportedAtom τ.ctx) :
    (equationCoefficient S 𝒰).restrict f (real.chiE.chi τ l) =
      real.chiE.chi σ (P.atomData.restrictSupported f.hom l) :=
  real.chiE.chi_natural f l

end EquationSemanticRealization

/-! ## X.§1 の注記: selected atlas から各 intersection の非空 witness -/

namespace SemanticRepairAtlas

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰}

/--
X.§1: selected local atlas を各 intersection へ restriction することで
`P_sem(V)` の元が得られる(補題6.2A の非空 witness)。
-/
def witness (atlas : SemanticRepairAtlas Psem) :
    ∀ σ : IntersectionIndex 𝒰, Psem.State σ.ctx
  | .chart i => atlas.localRepair i
  | .pair p =>
      Psem.restrictState (𝒰.pairFst p.fst p.snd) (atlas.localRepair p.fst)
  | .triple t =>
      Psem.restrictState
        (𝒰.tripleFaceIJ t.fst t.snd t.trd ≫ 𝒰.pairFst t.fst t.snd)
        (atlas.localRepair t.fst)

end SemanticRepairAtlas

/-! ## X.系6.7: Equation Coefficient Comparison(定理6.3 の実使用) -/

section Corollary67

variable {P : SemanticRepairPresentation.{u, v} S R}
variable (real : EquationSemanticRealization P 𝒰)
variable {Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰}
variable {PQ : AffineCoefficientLiftSystem.{u, u, y} (equationCoefficient S 𝒰)}
variable (β : PrimaryStateCorrespondence real.chiE Psem PQ)
variable (atlas : SemanticRepairAtlas Psem)

include β atlas in
/--
X.系6.7 の soundness 前提: affine local-state data と `β` から補題6.2A が
repair-relation soundness を与える(atlas witness で非空性を放電)。
-/
theorem equationRelationSound (σ : IntersectionIndex 𝒰) :
    real.chiE.RelationSound σ := fun _ hx =>
  β.relationSound_of_stateCorrespondence σ (atlas.witness σ) hx

/-- X.系6.7: 定理6.3 の実使用による `Φ_E`(準同型面)。 -/
def equationPhi (σ : IntersectionIndex 𝒰) :
    P.MSem σ.ctx →+ (equationCoefficient S 𝒰).carrier σ :=
  real.chiE.phi (equationRelationSound real β atlas) σ

/--
X.系6.7: repair-relation completeness と equation-generator completeness の
下で `Φ_E : M_sem|_{Int} ≃ Q_E|_{Int}`(定理6.3 の実使用。supplied
certificate ではない)。
-/
def equationPhiEquiv (σ : IntersectionIndex 𝒰)
    (hcomplete : real.chiE.RelationComplete σ)
    (hgen : real.chiE.GeneratorComplete σ) :
    P.MSem σ.ctx ≃+ (equationCoefficient S 𝒰).carrier σ :=
  real.chiE.phiEquiv (equationRelationSound real β atlas) σ hcomplete hgen

/-- X.系6.7: `Φ_E` の intersection diagram 上の restriction naturality。 -/
theorem equationPhi_natural {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    (m : P.MSem τ.ctx) :
    (equationCoefficient S 𝒰).restrict f (equationPhi real β atlas τ m) =
      equationPhi real β atlas σ (P.mSemRestrict f.hom m) :=
  real.chiE.phi_natural (equationRelationSound real β atlas) f m

end Corollary67

/-! ## X.§1 入力8: empty-overlap normalization(R0 §4.8) -/

/--
X.§1 入力8(R0 §4.8): 積から除いた empty intersection 上の値の固定。
`M_sem` / `Q_E` の零化と `P_sem` / `P_E` の subsingleton 性の4条件を
selected datum として持つ。消費先は補題2.1A の instantiation(C4)と
定理8.2 の matching family 化(C5)。
-/
structure EmptyOverlapNormalization
    (P : SemanticRepairPresentation.{u, v} S R)
    (𝒰 : MonomorphicOrderedCover S)
    (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰)
    (PQ : AffineCoefficientLiftSystem.{u, u, y} (equationCoefficient S 𝒰)) :
    Prop where
  msem_pair_trivial : ∀ i j, 𝒰.omittedPair i j ->
      ∀ m : P.MSem (𝒰.pairCtx i j), m = 0
  msem_triple_trivial : ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ m : P.MSem (𝒰.tripleCtx i j k), m = 0
  qE_pair_trivial : ∀ i j, 𝒰.omittedPair i j ->
      ∀ q : S.equationSystem.ObstructionQuotient (𝒰.pairCtx i j), q = 0
  qE_triple_trivial : ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ q : S.equationSystem.ObstructionQuotient (𝒰.tripleCtx i j k), q = 0
  psem_pair_subsingleton : ∀ i j, 𝒰.omittedPair i j ->
      Subsingleton (Psem.State (𝒰.pairCtx i j))
  psem_triple_subsingleton : ∀ i j k, 𝒰.omittedTriple i j k ->
      Subsingleton (Psem.State (𝒰.tripleCtx i j k))
  pE_pair_subsingleton : ∀ i j, 𝒰.omittedPair i j ->
      Subsingleton (PQ.State (𝒰.pairCtx i j))
  pE_triple_subsingleton : ∀ i j k, 𝒰.omittedTriple i j k ->
      Subsingleton (PQ.State (𝒰.tripleCtx i j k))

namespace EmptyOverlapNormalization

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰}
variable {PQ : AffineCoefficientLiftSystem.{u, u, y} (equationCoefficient S 𝒰)}

/-- 補題2.1A の semantic 側 pair 仮定(`hpair`)を normalization から導出する。 -/
theorem msem_hpair
    (N : EmptyOverlapNormalization P 𝒰 Psem PQ) :
    ∀ i j, 𝒰.omittedPair i j ->
      ∀ v : (P.mSemPresheaf).carrier (𝒰.pairCtx i j), v = 0 :=
  N.msem_pair_trivial

/-- 補題2.1A の semantic 側 triple 仮定(`htriple`)を normalization から導出する。 -/
theorem msem_htriple
    (N : EmptyOverlapNormalization P 𝒰 Psem PQ) :
    ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ v : (P.mSemPresheaf).carrier (𝒰.tripleCtx i j k), v = 0 :=
  N.msem_triple_trivial

/-- 補題2.1A の equation 側 pair 仮定を normalization から導出する。 -/
theorem qE_hpair
    (N : EmptyOverlapNormalization P 𝒰 Psem PQ) :
    ∀ i j, 𝒰.omittedPair i j ->
      ∀ v : (equationSitePresheaf S).carrier (𝒰.pairCtx i j), v = 0 :=
  N.qE_pair_trivial

/-- 補題2.1A の equation 側 triple 仮定を normalization から導出する。 -/
theorem qE_htriple
    (N : EmptyOverlapNormalization P 𝒰 Psem PQ) :
    ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ v : (equationSitePresheaf S).carrier (𝒰.tripleCtx i j k), v = 0 :=
  N.qE_triple_trivial

end EmptyOverlapNormalization

/-! ## R0 §4.9: 定理1.1 入力 bundle(equation realization) -/

/--
R0 §4.9: 系6.7 / 定理7.6 用の packet。coefficient と correspondence は
選択せず、`E` と realization から生成する(`equationCoefficient` /
`chiE`)。入力4(completeness 対)は bundle に入れず定理仮定として受け取る。
-/
structure SagaEquationPacket (S : Site.AATSite A) where
  occurrenceReading : AtomOccurrenceReading S
  cover : MonomorphicOrderedCover S
  presentation : SemanticRepairPresentation.{u, v} S occurrenceReading
  realization : EquationSemanticRealization presentation cover
  repairSystem : AffineSemanticRepairSystem.{u, v, x} presentation cover
  repairAtlas : SemanticRepairAtlas repairSystem
  liftSystem : AffineCoefficientLiftSystem.{u, u, y} (equationCoefficient S cover)
  liftAtlas : CoefficientLiftAtlas liftSystem
  stateCorrespondence :
    PrimaryStateCorrespondence realization.chiE repairSystem liftSystem
  normalization :
    EmptyOverlapNormalization presentation cover repairSystem liftSystem

namespace SagaEquationPacket

variable (packet : SagaEquationPacket.{u, v, x, y} S)

/-- X.定義4.2: packet の semantic residual `r_sem`(生成)。 -/
def semanticResidualCochain :
    Cochain1 (packet.presentation.mSemPresheaf.onIntersections packet.cover) :=
  packet.repairAtlas.semanticResidual

/-- X.定義5.3: packet の equation residual `r_E`(生成)。 -/
def equationResidualCochain :
    Cochain1 (equationCoefficient S packet.cover) :=
  packet.liftAtlas.residual

/-- X.補題5.4 前半: `r_E` は 1-cocycle である(named equation surface)。 -/
theorem equationResidualCochain_cocycle :
    delta1 (equationCoefficient S packet.cover)
      packet.equationResidualCochain = 0 :=
  packet.liftAtlas.residual_cocycle

/-- X.補題5.4 後半: `[r_E]` は equation atlas の選択に依存しない。 -/
theorem equationResidualClass_choice_independent
    (liftAtlas' : CoefficientLiftAtlas packet.liftSystem) :
    liftAtlas'.residualClass = packet.liftAtlas.residualClass :=
  packet.liftAtlas.residualClass_choice_independent liftAtlas'

/-- X.系6.7(packet 面): 定理6.3 の実使用による `Φ_E`。 -/
def phiEquiv (σ : IntersectionIndex packet.cover)
    (hcomplete : packet.realization.chiE.RelationComplete σ)
    (hgen : packet.realization.chiE.GeneratorComplete σ) :
    packet.presentation.MSem σ.ctx ≃+
      (equationCoefficient S packet.cover).carrier σ :=
  equationPhiEquiv packet.realization packet.stateCorrespondence
    packet.repairAtlas σ hcomplete hgen

end SagaEquationPacket

end Saga
end SemanticRepair
end AAT.AG
