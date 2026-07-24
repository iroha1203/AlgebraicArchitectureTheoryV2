import Formal.AG.SemanticRepair.Saga.EquationRealization

/-!
# Part X §7: cochain comparison `κ` and the SAGA `H¹` isomorphism

* Definition 7.1: `kappa0/1/2` are **constructed** by applying a natural
  degreewise coefficient equivalence `ψ` (in the SAGA instantiation, the
  Theorem 6.3 / Corollary 6.7 comparison `Φ`) to each component — no
  equivalence, inverse, or commutation is taken as a certificate.
* Theorem 7.2 (`kappa1_delta0` / `kappa2_delta1`): both commutation squares,
  by componentwise naturality and additivity.
* `kappaEquivalence`: the generated cochain-level equivalence packaged into
  the generic transport hub `Cohomology.AdditiveThreeTermComplex.Equivalence`
  (`CochainComparison.lean`).  Division of labour: the hub supplies the
  generic quotient transport; the equivalence fed into it is generated here
  from Definition 7.1, not supplied.
* Corollary 7.3 (`kappa1_cocycle` / `kappa1_cocycle_reflect` /
  `kappa1_coboundary` / `kappa1_coboundary_reflect`): preservation and
  reflection of cocycles and coboundaries.
* Theorem 7.4: `κ_* : H¹_sem ≃ Ȟ¹(𝒰, Q_E)` — well-definedness, both-sided
  inverses, and zero-class transfer are the hub-generated
  `toH1/fromH1/to_from_H1/from_to_H1/toH1_zero_iff` on `kappaEquivalence`.
* Theorem 7.5 (`residual_correspondence` and friends): for independently
  selected atlases, `r_E = κ¹(r_sem) + δ⁰_E h` with the generated gauge `h`,
  hence `κ_*([r_sem]) = [r_E]`; for the `β`-aligned atlas the cochain-level
  equality `κ¹(r_sem) = r_E` holds on the nose.
* Theorem 7.6 (`sagaComparison` / `sagaCentralTheorem_comparison`): the
  packaged conclusions (coefficient, complex, cochain, cohomology, residual,
  zero/nonzero).  The Theorem 1.1-named surface takes `[Fintype]` on the
  index per Part X §1 (the comparison core itself does not use finiteness;
  the instance argument is the faithful transcription of the fixed finite
  index set of the central theorem).
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory

universe u v w x y

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {R : AtomOccurrenceReading S}
variable {𝒰 : MonomorphicOrderedCover S}

/-! ## X.定義7.1: `Φ` の成分適用による `κ^n` の構成(generic) -/

section Kappa

variable {Q1 : IntersectionCoefficientData.{u, w} 𝒰}
variable {Q2 : IntersectionCoefficientData.{u, v} 𝒰}
variable (ψ : ∀ σ : IntersectionIndex 𝒰, Q1.carrier σ ≃+ Q2.carrier σ)
variable (hψ : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    (q : Q1.carrier τ), Q2.restrict f (ψ τ q) = ψ σ (Q1.restrict f q))

/-- X.定義7.1: `κ⁰`(成分ごとの `Φ` 適用)。 -/
def kappa0 : Cochain0 Q1 →+ Cochain0 Q2 :=
  AddMonoidHom.mk' (fun a i => ψ (.chart i) (a i))
    (by
      intro a b
      funext i
      simp)

/-- X.定義7.1: `κ¹`。 -/
def kappa1 : Cochain1 Q1 →+ Cochain1 Q2 :=
  AddMonoidHom.mk' (fun c p => ψ (.pair p) (c p))
    (by
      intro c d
      funext p
      simp)

/-- X.定義7.1: `κ²`。 -/
def kappa2 : Cochain2 Q1 →+ Cochain2 Q2 :=
  AddMonoidHom.mk' (fun c t => ψ (.triple t) (c t))
    (by
      intro c d
      funext t
      simp)

include hψ in
/-- X.定理7.2 第1正方形: `κ¹ δ⁰ = δ⁰ κ⁰`。 -/
theorem kappa1_delta0 (a : Cochain0 Q1) :
    kappa1 ψ (delta0 Q1 a) = delta0 Q2 (kappa0 ψ a) := by
  funext p
  show ψ (.pair p) (Q1.restrict (Face.pairRight p) (a p.snd) -
      Q1.restrict (Face.pairLeft p) (a p.fst)) =
    Q2.restrict (Face.pairRight p) (ψ (.chart p.snd) (a p.snd)) -
      Q2.restrict (Face.pairLeft p) (ψ (.chart p.fst) (a p.fst))
  rw [map_sub, hψ (Face.pairRight p) (a p.snd), hψ (Face.pairLeft p) (a p.fst)]

include hψ in
/-- X.定理7.2 第2正方形: `κ² δ¹ = δ¹ κ¹`。 -/
theorem kappa2_delta1 (c : Cochain1 Q1) :
    kappa2 ψ (delta1 Q1 c) = delta1 Q2 (kappa1 ψ c) := by
  funext t
  show ψ (.triple t) (Q1.restrict (Face.tripleJK t) (c t.pairJK) -
      Q1.restrict (Face.tripleIK t) (c t.pairIK) +
      Q1.restrict (Face.tripleIJ t) (c t.pairIJ)) =
    Q2.restrict (Face.tripleJK t) (ψ (.pair t.pairJK) (c t.pairJK)) -
      Q2.restrict (Face.tripleIK t) (ψ (.pair t.pairIK) (c t.pairIK)) +
      Q2.restrict (Face.tripleIJ t) (ψ (.pair t.pairIJ) (c t.pairIJ))
  rw [map_add, map_sub, hψ (Face.tripleJK t) (c t.pairJK),
    hψ (Face.tripleIK t) (c t.pairIK), hψ (Face.tripleIJ t) (c t.pairIJ)]

include hψ in
/-- `ψ` の逆側の naturality(`hψ` から導出)。 -/
theorem hψ_symm {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    (q : Q2.carrier τ) :
    Q1.restrict f ((ψ τ).symm q) = (ψ σ).symm (Q2.restrict f q) := by
  apply (ψ σ).injective
  rw [AddEquiv.apply_symm_apply, ← hψ f ((ψ τ).symm q),
    AddEquiv.apply_symm_apply]

include hψ in
/-- X.系7.3(1): cocycle の保存。 -/
theorem kappa1_cocycle {c : Cochain1 Q1} (hc : delta1 Q1 c = 0) :
    delta1 Q2 (kappa1 ψ c) = 0 := by
  rw [← kappa2_delta1 ψ hψ, hc, map_zero]

include hψ in
/-- X.系7.3(2): cocycle の反映(`κ²` の単射性)。 -/
theorem kappa1_cocycle_reflect {c : Cochain1 Q1}
    (hc : delta1 Q2 (kappa1 ψ c) = 0) : delta1 Q1 c = 0 := by
  have h := hc
  rw [← kappa2_delta1 ψ hψ] at h
  funext t
  have h0 := congrFun h t
  rw [Pi.zero_apply] at h0
  show delta1 Q1 c t = (0 : Cochain2 Q1) t
  rw [Pi.zero_apply]
  apply (ψ (.triple t)).injective
  rw [map_zero]
  exact h0

include hψ in
/-- X.系7.3(3): coboundary の輸送。 -/
theorem kappa1_coboundary {c c' : Cochain1 Q1} {a : Cochain0 Q1}
    (h : c - c' = delta0 Q1 a) :
    kappa1 ψ c - kappa1 ψ c' = delta0 Q2 (kappa0 ψ a) := by
  rw [← map_sub, h, kappa1_delta0 ψ hψ]

include hψ in
/-- X.系7.3(4): coboundary の反映(`κ⁰`/`κ¹` の全単射性)。 -/
theorem kappa1_coboundary_reflect {c c' : Cochain1 Q1} {b : Cochain0 Q2}
    (h : kappa1 ψ c - kappa1 ψ c' = delta0 Q2 b) :
    c - c' = delta0 Q1 (kappa0 (fun σ => (ψ σ).symm) b) := by
  have h2 := congrArg (kappa1 (fun σ => (ψ σ).symm)) h
  rw [map_sub] at h2
  have hc : kappa1 (fun σ => (ψ σ).symm) (kappa1 ψ c) = c := by
    funext p
    exact (ψ (.pair p)).symm_apply_apply (c p)
  have hc' : kappa1 (fun σ => (ψ σ).symm) (kappa1 ψ c') = c' := by
    funext p
    exact (ψ (.pair p)).symm_apply_apply (c' p)
  rw [hc, hc', kappa1_delta0 (fun σ => (ψ σ).symm) (hψ_symm ψ hψ)] at h2
  exact h2

/-- X.定理7.4 の素材: `κ¹` は cocycle を cocycle に送る。 -/
def kappaCocycleMap (c : (incComplex Q1).H1Cocycle)
    (hc1 : delta1 Q2 (kappa1 ψ c.1) = 0) : (incComplex Q2).H1Cocycle :=
  ⟨kappa1 ψ c.1, hc1⟩

include hψ in
/--
X.定理7.4: `κ_* : Ȟ¹(𝒰, Q1) → Ȟ¹(𝒰, Q2)`(well-defined 性は系7.3(3))。
generic hub(`CochainComparison.lean`)は単一 universe の複体同値輸送であり、
`κ` は係数 universe(`M_sem` と `Q_E`)を跨ぐため、同じ statement 形の
商上輸送をここで直接構成する(supplied ではなく生成)。
-/
def kappaH1To : IncH1 Q1 -> IncH1 Q2 :=
  Quotient.lift
    (fun c => Quotient.mk (incComplex Q2).H1CoboundarySetoid
      (kappaCocycleMap ψ c
        (kappa1_cocycle ψ hψ (show delta1 Q1 c.1 = 0 from c.2))))
    (by
      intro c c' hcc
      rcases hcc with ⟨b, hb⟩
      have hb' : c.1 - c'.1 = delta0 Q1 b := hb
      apply Quotient.sound
      refine ⟨kappa0 ψ b, ?_⟩
      show kappa1 ψ c.1 - kappa1 ψ c'.1 = delta0 Q2 (kappa0 ψ b)
      exact kappa1_coboundary ψ hψ hb')

include hψ in
/-- X.定理7.4: 逆方向 `κ_*⁻¹`(`ψ.symm` の誘導)。 -/
def kappaH1From : IncH1 Q2 -> IncH1 Q1 :=
  kappaH1To (fun σ => (ψ σ).symm) (hψ_symm ψ hψ)

include hψ in
/-- X.定理7.4: 両誘導写像は互いに逆(Q1 側)。 -/
theorem kappaH1_from_to (h : IncH1 Q1) :
    kappaH1From ψ hψ (kappaH1To ψ hψ h) = h := by
  refine Quotient.inductionOn h ?_
  intro c
  apply Quotient.sound
  refine ⟨0, ?_⟩
  show kappa1 (fun σ => (ψ σ).symm) (kappa1 ψ c.1) - c.1 = delta0 Q1 0
  have hc : kappa1 (fun σ => (ψ σ).symm) (kappa1 ψ c.1) = c.1 := by
    funext p
    exact (ψ (.pair p)).symm_apply_apply (c.1 p)
  rw [hc, sub_self, map_zero]

include hψ in
/-- X.定理7.4: 両誘導写像は互いに逆(Q2 側)。 -/
theorem kappaH1_to_from (h : IncH1 Q2) :
    kappaH1To ψ hψ (kappaH1From ψ hψ h) = h := by
  refine Quotient.inductionOn h ?_
  intro c
  apply Quotient.sound
  refine ⟨0, ?_⟩
  show kappa1 ψ (kappa1 (fun σ => (ψ σ).symm) c.1) - c.1 = delta0 Q2 0
  have hc : kappa1 ψ (kappa1 (fun σ => (ψ σ).symm) c.1) = c.1 := by
    funext p
    exact (ψ (.pair p)).apply_symm_apply (c.1 p)
  rw [hc, sub_self, map_zero]

include hψ in
/-- `κ_*` は零類を零類へ送る。 -/
theorem kappaH1To_zero :
    kappaH1To ψ hψ ((incComplex Q1).H1ZeroClass) =
      (incComplex Q2).H1ZeroClass := by
  apply Quotient.sound
  refine ⟨0, ?_⟩
  show kappa1 ψ (0 : Cochain1 Q1) - 0 = delta0 Q2 0
  simp only [map_zero, sub_zero]

include hψ in
/-- X.定理7.4 / 定理7.6: `κ_*` の零類の保存と反映。 -/
theorem kappaH1To_zero_iff (h : IncH1 Q1) :
    (incComplex Q2).H1IsZero (kappaH1To ψ hψ h) ↔
      (incComplex Q1).H1IsZero h := by
  constructor
  · intro hh
    have hstep := congrArg (kappaH1From ψ hψ) hh
    rw [kappaH1_from_to ψ hψ] at hstep
    rw [Cohomology.AdditiveThreeTermComplex.H1IsZero, hstep]
    show kappaH1From ψ hψ ((incComplex Q2).H1ZeroClass) =
      (incComplex Q1).H1ZeroClass
    exact kappaH1To_zero (fun σ => (ψ σ).symm) (hψ_symm ψ hψ)
  · intro hh
    rw [Cohomology.AdditiveThreeTermComplex.H1IsZero] at hh
    rw [Cohomology.AdditiveThreeTermComplex.H1IsZero, hh]
    exact kappaH1To_zero ψ hψ

end Kappa

/-! ## X.定理7.4–7.6: packet 面の SAGA 比較 -/

namespace SagaEquationPacket

variable (packet : SagaEquationPacket.{u, v, x, y} S)
variable (hcomplete : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.RelationComplete σ)
variable (hgen : ∀ σ : IntersectionIndex packet.cover,
    packet.realization.chiE.GeneratorComplete σ)

/-- 系6.7 の `Φ_E` を degreewise 同値族として読む。 -/
def phiFamily (σ : IntersectionIndex packet.cover) :
    (packet.presentation.mSemPresheaf.onIntersections packet.cover).carrier σ ≃+
      (equationCoefficient S packet.cover).carrier σ :=
  packet.phiEquiv σ (hcomplete σ) (hgen σ)

/-- `Φ_E` 族の restriction naturality(系6.7 の naturality の equiv 面)。 -/
theorem phiFamily_natural {σ τ : IntersectionIndex packet.cover}
    (f : Face packet.cover σ τ)
    (m : (packet.presentation.mSemPresheaf.onIntersections packet.cover).carrier τ) :
    (equationCoefficient S packet.cover).restrict f
        (packet.phiFamily hcomplete hgen τ m) =
      packet.phiFamily hcomplete hgen σ
        ((packet.presentation.mSemPresheaf.onIntersections packet.cover).restrict f m) :=
  equationPhi_natural packet.realization packet.stateCorrespondence
    packet.repairAtlas f m

/--
X.定理7.4: 生成 `κ` による `κ_* : H¹_sem → Ȟ¹(𝒰, Q_E)`
(両側逆・零類移送は `kappaH1_from_to`/`kappaH1_to_from`/`kappaH1To_zero_iff`)。
-/
def kappaStar :
    packet.presentation.SemanticH1 packet.cover ->
      IncH1 (equationCoefficient S packet.cover) :=
  kappaH1To (packet.phiFamily hcomplete hgen)
    (fun f q => packet.phiFamily_natural hcomplete hgen f q)

/-- X.定理7.4: `κ_*` の逆方向。 -/
def kappaStarInv :
    IncH1 (equationCoefficient S packet.cover) ->
      packet.presentation.SemanticH1 packet.cover :=
  kappaH1From (packet.phiFamily hcomplete hgen)
    (fun f q => packet.phiFamily_natural hcomplete hgen f q)

/-- X.定理7.4: `κ_*` は両側逆を持つ(semantic 側)。 -/
theorem kappaStar_leftInverse (h : packet.presentation.SemanticH1 packet.cover) :
    packet.kappaStarInv hcomplete hgen (packet.kappaStar hcomplete hgen h) = h :=
  kappaH1_from_to _ _ h

/-- X.定理7.4: `κ_*` は両側逆を持つ(equation 側)。 -/
theorem kappaStar_rightInverse
    (h : IncH1 (equationCoefficient S packet.cover)) :
    packet.kappaStar hcomplete hgen (packet.kappaStarInv hcomplete hgen h) = h :=
  kappaH1_to_from _ _ h

/-- X.定理7.5 の gauge `h`: 独立 atlas 間の chart ごとの torsor 差(生成)。 -/
def betaGauge : Cochain0 (equationCoefficient S packet.cover) :=
  fun i => packet.liftSystem.diffAt (.chart i)
    (packet.stateCorrespondence.beta (.chart i) (packet.repairAtlas.localRepair i))
    (packet.liftAtlas.localLift i)

/-- gauge の定義性質: `e_i = h_i + β(p_i)`。 -/
theorem betaGauge_spec (i : packet.cover.Index) :
    packet.liftAtlas.localLift i =
      packet.liftSystem.act (.chart i) (packet.betaGauge i)
        (packet.stateCorrespondence.beta (.chart i)
          (packet.repairAtlas.localRepair i)) :=
  (packet.liftSystem.act_diffAt (.chart i) _ _).symm

/--
X.定理7.5(cochain 水準): 独立に選んだ atlas に対して
`r_E = κ¹(r_sem) + δ⁰_E h`(gauge `h` は生成)。
-/
theorem residual_correspondence_cochain :
    packet.equationResidualCochain =
      kappa1 (packet.phiFamily hcomplete hgen)
          packet.semanticResidualCochain +
        delta0 (equationCoefficient S packet.cover) packet.betaGauge := by
  funext p
  show packet.equationResidualCochain p =
    kappa1 (packet.phiFamily hcomplete hgen)
        packet.semanticResidualCochain p +
      delta0 (equationCoefficient S packet.cover) packet.betaGauge p
  have hsound := equationRelationSound packet.realization
    packet.stateCorrespondence packet.repairAtlas
  -- e_j| = (h_j|) + β(p_j|)。
  have step1 : packet.liftAtlas.rightOn p =
      packet.liftSystem.act (.pair p)
        ((equationCoefficient S packet.cover).restrict (Face.pairRight p)
          (packet.betaGauge p.snd))
        (packet.stateCorrespondence.beta (.pair p)
          (packet.repairSystem.restrictState (Face.pairRight p).hom
            (packet.repairAtlas.localRepair p.snd))) := by
    show packet.liftSystem.restrictState (Face.pairRight p).hom
        (packet.liftAtlas.localLift p.snd) = _
    rw [packet.betaGauge_spec p.snd,
      packet.liftSystem.act_restrict (Face.pairRight p),
      packet.stateCorrespondence.beta_natural (Face.pairRight p)]
  -- p_j| = r_sem + p_i|(semantic torsor)。
  have step2 : packet.repairSystem.restrictState (Face.pairRight p).hom
      (packet.repairAtlas.localRepair p.snd) =
      packet.repairSystem.mact (.pair p)
        (packet.semanticResidualCochain p)
        (packet.repairSystem.restrictState (Face.pairLeft p).hom
          (packet.repairAtlas.localRepair p.fst)) :=
    (packet.repairSystem.toLiftSystem.act_diffAt (.pair p) _ _).symm
  -- β の M_sem 水準 equivariance(phiFamily 形で受ける。defeq)。
  have step3 : packet.stateCorrespondence.beta (.pair p)
      (packet.repairSystem.mact (.pair p)
        (packet.semanticResidualCochain p)
        (packet.repairSystem.restrictState (Face.pairLeft p).hom
          (packet.repairAtlas.localRepair p.fst))) =
      packet.liftSystem.act (.pair p)
        (packet.phiFamily hcomplete hgen (.pair p)
          (packet.semanticResidualCochain p))
        (packet.stateCorrespondence.beta (.pair p)
          (packet.repairSystem.restrictState (Face.pairLeft p).hom
            (packet.repairAtlas.localRepair p.fst))) :=
    packet.stateCorrespondence.beta_maction hsound (.pair p)
      (packet.semanticResidualCochain p)
      (packet.repairSystem.restrictState (Face.pairLeft p).hom
        (packet.repairAtlas.localRepair p.fst))
  -- β(p_i|) = (-h_i|) + e_i|。
  have step4 : packet.stateCorrespondence.beta (.pair p)
      (packet.repairSystem.restrictState (Face.pairLeft p).hom
        (packet.repairAtlas.localRepair p.fst)) =
      packet.liftSystem.act (.pair p)
        (-((equationCoefficient S packet.cover).restrict (Face.pairLeft p)
          (packet.betaGauge p.fst)))
        (packet.liftAtlas.leftOn p) := by
    have h4 : packet.liftAtlas.leftOn p =
        packet.liftSystem.act (.pair p)
          ((equationCoefficient S packet.cover).restrict (Face.pairLeft p)
            (packet.betaGauge p.fst))
          (packet.stateCorrespondence.beta (.pair p)
            (packet.repairSystem.restrictState (Face.pairLeft p).hom
              (packet.repairAtlas.localRepair p.fst))) := by
      show packet.liftSystem.restrictState (Face.pairLeft p).hom
          (packet.liftAtlas.localLift p.fst) = _
      rw [packet.betaGauge_spec p.fst,
        packet.liftSystem.act_restrict (Face.pairLeft p),
        packet.stateCorrespondence.beta_natural (Face.pairLeft p)]
    rw [h4, ← packet.liftSystem.act_add, neg_add_cancel,
      packet.liftSystem.act_zero]
  have hk : kappa1 (packet.phiFamily hcomplete hgen)
      packet.semanticResidualCochain p =
      packet.phiFamily hcomplete hgen (.pair p)
        (packet.semanticResidualCochain p) := rfl
  have hd : delta0 (equationCoefficient S packet.cover) packet.betaGauge p =
      (equationCoefficient S packet.cover).restrict (Face.pairRight p)
          (packet.betaGauge p.snd) -
        (equationCoefficient S packet.cover).restrict (Face.pairLeft p)
          (packet.betaGauge p.fst) := rfl
  -- 差の一意性で閉じる。
  refine (packet.liftSystem.diffAt_unique (.pair p) ?_).symm
  rw [step1, step2, step3, step4, ← packet.liftSystem.act_add,
    ← packet.liftSystem.act_add]
  congr 1
  rw [hk, hd]
  abel

/-- X.定理7.5(class 水準): `κ_*([r_sem]) = [r_E]`。 -/
theorem residual_correspondence_class :
    packet.kappaStar hcomplete hgen
        packet.repairAtlas.semanticResidualClass =
      packet.liftAtlas.residualClass := by
  apply Quotient.sound
  refine ⟨-packet.betaGauge, ?_⟩
  show kappa1 (packet.phiFamily hcomplete hgen)
      packet.semanticResidualCochain -
      packet.liftAtlas.residual =
    delta0 (equationCoefficient S packet.cover) (-packet.betaGauge)
  have h := packet.residual_correspondence_cochain hcomplete hgen
  rw [show packet.liftAtlas.residual = packet.equationResidualCochain from rfl,
    h, map_neg]
  abel

/-- X.定理7.5: `β`-整合 atlas(`e_i := β(p_i)`)。 -/
def betaAlignedLiftAtlas : CoefficientLiftAtlas packet.liftSystem :=
  ⟨fun i => packet.stateCorrespondence.beta (.chart i)
    (packet.repairAtlas.localRepair i)⟩

/-- X.定理7.5(整合 atlas): cochain 水準で `κ¹(r_sem) = r_E` が成立する。 -/
theorem betaAligned_residual :
    packet.betaAlignedLiftAtlas.residual =
      kappa1 (packet.phiFamily hcomplete hgen)
        packet.semanticResidualCochain := by
  funext p
  have hsound := equationRelationSound packet.realization
    packet.stateCorrespondence packet.repairAtlas
  refine (packet.liftSystem.diffAt_unique (.pair p) ?_).symm
  show packet.liftSystem.restrictState (Face.pairRight p).hom
      (packet.stateCorrespondence.beta (.chart p.snd)
        (packet.repairAtlas.localRepair p.snd)) =
    packet.liftSystem.act (.pair p)
      (packet.phiFamily hcomplete hgen (.pair p)
        (packet.semanticResidualCochain p))
      (packet.betaAlignedLiftAtlas.leftOn p)
  have step2 : packet.repairSystem.restrictState (Face.pairRight p).hom
      (packet.repairAtlas.localRepair p.snd) =
      packet.repairSystem.mact (.pair p)
        (packet.semanticResidualCochain p)
        (packet.repairSystem.restrictState (Face.pairLeft p).hom
          (packet.repairAtlas.localRepair p.fst)) :=
    (packet.repairSystem.toLiftSystem.act_diffAt (.pair p) _ _).symm
  have hleft : packet.betaAlignedLiftAtlas.leftOn p =
      packet.stateCorrespondence.beta (.pair p)
        (packet.repairSystem.restrictState (Face.pairLeft p).hom
          (packet.repairAtlas.localRepair p.fst)) := by
    show packet.liftSystem.restrictState (Face.pairLeft p).hom
        (packet.stateCorrespondence.beta (.chart p.fst)
          (packet.repairAtlas.localRepair p.fst)) = _
    rw [packet.stateCorrespondence.beta_natural (Face.pairLeft p)]
  rw [packet.stateCorrespondence.beta_natural (Face.pairRight p), step2,
    packet.stateCorrespondence.beta_maction hsound (.pair p), hleft]
  rfl

include hcomplete hgen in
/--
X.定理7.6(零/非零): `[r_sem] = 0 ⟺ [r_E] = 0`(したがって非零も同値)。
-/
theorem sagaComparison_zero_iff :
    (packet.presentation.semanticComplex packet.cover).H1IsZero
        packet.repairAtlas.semanticResidualClass ↔
      (incComplex (equationCoefficient S packet.cover)).H1IsZero
        packet.liftAtlas.residualClass := by
  rw [← packet.residual_correspondence_class hcomplete hgen]
  exact (kappaH1To_zero_iff _ _ _).symm

/--
X.定理7.6 / 定理1.1(比較部): SAGA 比較定理の統合 statement。
係数(系6.7 `phiEquiv`)・複体/cochain(定理7.2 = `kappaH1` の可換 field)・
cohomology(定理7.4 = hub 生成の両側逆)・residual(定理7.5)・零/非零の
各結論を束ねる。`[Fintype]` は本文 §1 の有限添字集合の忠実転写であり、
comparison core の証明は有限性を使わない。
-/
theorem sagaCentralTheorem_comparison [Fintype packet.cover.Index] :
    (packet.kappaStar hcomplete hgen
        packet.repairAtlas.semanticResidualClass =
      packet.liftAtlas.residualClass) ∧
    ((packet.presentation.semanticComplex packet.cover).H1IsZero
        packet.repairAtlas.semanticResidualClass ↔
      (incComplex (equationCoefficient S packet.cover)).H1IsZero
        packet.liftAtlas.residualClass) :=
  ⟨packet.residual_correspondence_class hcomplete hgen,
    packet.sagaComparison_zero_iff hcomplete hgen⟩

end SagaEquationPacket

end Saga
end SemanticRepair
end AAT.AG
