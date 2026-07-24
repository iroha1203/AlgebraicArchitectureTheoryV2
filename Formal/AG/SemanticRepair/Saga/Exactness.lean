import Formal.AG.SemanticRepair.Saga.RepairTorsor
import Mathlib.Data.ZMod.Basic

/-!
# Part X §6: SAGA presentation exactness and the coefficient comparison `Φ`

* `PrimaryCoefficientCorrespondence` (Definition 6.1, Theorem 1.1 input 3,
  R0 §4.3): a restriction-natural map from supported semantic atoms into a
  generic intersection coefficient `Q`, with its free extension `chiHom`.
* `PrimaryStateCorrespondence` (Definition 6.1B, input 7, R0 §4.7):
  a restriction-natural, generator-equivariant map `β : P_sem → P_Q`.
* `RelationSound` / `RelationComplete` / `GeneratorComplete`
  (Definition 6.2, R0 §4.4): the three verifiable exactness conditions.
* Lemma 6.2A (`relationSound_of_stateCorrespondence`): soundness is derived
  from the affine state data and `β` — only the two completeness conditions
  are supplied, as in Theorem 1.1 input 4.
* Theorem 6.3: `phi` is constructed by descending `chiHom` (soundness),
  proved injective (`phi_injective`, relation completeness), surjective
  (`phi_surjective`, generator completeness), restriction-natural
  (`phi_natural`), and packaged as `phiEquiv : M_sem ≃+ Q`.  No inverse or
  equivalence is taken as input.  The intersection-diagram statement is the
  one the SAGA core consumes (Corollary 6.7, Theorem 7.6); the sitewide
  clause of the text enters only through the sitewide extension premises of
  Corollary 8.3 (C5).
* Corollary 6.4 (`imageComparison`): without generator completeness,
  `M_sem ≃+ range χ̃`.
* Corollary 6.5 (`beta_bijective`): `β` is a `Φ`-equivariant bijection on
  nonempty intersection states.
* Example 6.6: three concrete negative fixtures showing that each exactness
  condition carries distinct mathematical work (map existence, injectivity,
  surjectivity).

`SagaPresentationCore` (R0 §4.9) bundles the generic Theorem 6.3 inputs;
the equation realization (`Q = Q_E`, Proposition 6.1A, Corollary 6.7) is
C3a (#3771), which instantiates this generic API.
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

/--
X.定義6.1(R0 §4.3): supported semantic atom を係数へ送る
restriction-natural な一次写像(定理1.1 入力3)。量化域は `Int_{≤2}(𝒰)`。
-/
structure PrimaryCoefficientCorrespondence
    (P : SemanticRepairPresentation.{u, v} S R)
    (Q : IntersectionCoefficientData.{u, w} 𝒰) where
  chi : ∀ σ : IntersectionIndex 𝒰, P.atomData.SupportedAtom σ.ctx -> Q.carrier σ
  chi_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (l : P.atomData.SupportedAtom τ.ctx),
      Q.restrict f (chi τ l) =
        chi σ (P.atomData.restrictSupported f.hom l)

namespace PrimaryCoefficientCorrespondence

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {Q : IntersectionCoefficientData.{u, w} 𝒰}
variable (χ : PrimaryCoefficientCorrespondence P Q)

/-- X.定義6.1: free abelian group への一意延長 `χ̃`。 -/
def chiHom (σ : IntersectionIndex 𝒰) :
    P.atomData.SupportedWord σ.ctx →+ Q.carrier σ :=
  Finsupp.liftAddHom (fun l => zmultiplesHom (Q.carrier σ) (χ.chi σ l))

@[simp]
theorem chiHom_single (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) (n : ℤ) :
    χ.chiHom σ (Finsupp.single l n) = n • χ.chi σ l := by
  simp [chiHom]

/-- `χ̃` の restriction naturality(generator 上の naturality から)。 -/
theorem chiHom_natural {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    (x : P.atomData.SupportedWord τ.ctx) :
    Q.restrict f (χ.chiHom τ x) =
      χ.chiHom σ (P.atomData.wordRestrict f.hom x) := by
  have hext : (Q.restrict f).comp (χ.chiHom τ) =
      (χ.chiHom σ).comp (P.atomData.wordRestrict f.hom) := by
    apply Finsupp.addHom_ext
    intro l n
    simp only [AddMonoidHom.comp_apply, chiHom_single, map_zsmul,
      χ.chi_natural f l]
    rw [show P.atomData.wordRestrict f.hom (Finsupp.single l n) =
        Finsupp.single (P.atomData.restrictSupported f.hom l) n from by
          simp [SemanticAtomData.wordRestrict, Finsupp.mapDomain_single],
      chiHom_single]
  exact DFunLike.congr_fun hext x

end PrimaryCoefficientCorrespondence

/--
X.定義6.1B(R0 §4.7): restriction-natural かつ generator-equivariant な
`β : P_sem → P_Q`(定理1.1 入力7)。逆写像・全単射性は入力に含めない。
-/
structure PrimaryStateCorrespondence
    {P : SemanticRepairPresentation.{u, v} S R}
    {Q : IntersectionCoefficientData.{u, w} 𝒰}
    (χ : PrimaryCoefficientCorrespondence P Q)
    (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰)
    (PQ : AffineCoefficientLiftSystem.{u, w, y} Q) where
  beta : ∀ σ : IntersectionIndex 𝒰, Psem.State σ.ctx -> PQ.State σ.ctx
  beta_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (p : Psem.State τ.ctx),
      PQ.restrictState f.hom (beta τ p) =
        beta σ (Psem.restrictState f.hom p)
  beta_equivariant : ∀ (σ : IntersectionIndex 𝒰)
      (l : P.atomData.SupportedAtom σ.ctx) (p : Psem.State σ.ctx),
      beta σ (Psem.act σ.ctx (Finsupp.single l 1) p) =
        PQ.act σ (χ.chi σ l) (beta σ p)

namespace PrimaryStateCorrespondence

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {Q : IntersectionCoefficientData.{u, w} 𝒰}
variable {χ : PrimaryCoefficientCorrespondence P Q}
variable {Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰}
variable {PQ : AffineCoefficientLiftSystem.{u, w, y} Q}
variable (β : PrimaryStateCorrespondence χ Psem PQ)

/-- generator-level equivariance を満たす word の部分群。 -/
private def equivariantWords (σ : IntersectionIndex 𝒰) :
    AddSubgroup (P.atomData.SupportedWord σ.ctx) where
  carrier := {x | ∀ p : Psem.State σ.ctx,
    β.beta σ (Psem.act σ.ctx x p) = PQ.act σ (χ.chiHom σ x) (β.beta σ p)}
  zero_mem' := by
    intro p
    rw [Psem.act_zero, map_zero, PQ.act_zero]
  add_mem' := by
    intro a b ha hb p
    rw [Psem.act_add, ha (Psem.act σ.ctx b p), hb p, map_add, PQ.act_add]
  neg_mem' := by
    intro a ha p
    have key := ha (Psem.act σ.ctx (-a) p)
    rw [← Psem.act_add, add_neg_cancel, Psem.act_zero] at key
    have h2 := congrArg (PQ.act σ (-(χ.chiHom σ a))) key
    rw [← PQ.act_add, neg_add_cancel, PQ.act_zero] at h2
    show β.beta σ (Psem.act σ.ctx (-a) p) =
      PQ.act σ (χ.chiHom σ (-a)) (β.beta σ p)
    rw [map_neg]
    exact h2.symm

private theorem mem_equivariantWords {σ : IntersectionIndex 𝒰}
    {x : P.atomData.SupportedWord σ.ctx} :
    x ∈ equivariantWords β σ ↔
      ∀ p : Psem.State σ.ctx,
        β.beta σ (Psem.act σ.ctx x p) =
          PQ.act σ (χ.chiHom σ x) (β.beta σ p) :=
  Iff.rfl

/--
X.定義6.1B: 有限和と additive inverse への equivariance は作用則から従う
(word 水準の equivariance)。
-/
theorem beta_word (σ : IntersectionIndex 𝒰)
    (x : P.atomData.SupportedWord σ.ctx) (p : Psem.State σ.ctx) :
    β.beta σ (Psem.act σ.ctx x p) =
      PQ.act σ (χ.chiHom σ x) (β.beta σ p) := by
  have hx : x ∈ equivariantWords β σ := by
    induction x using Finsupp.induction with
    | zero => exact (equivariantWords β σ).zero_mem
    | single_add l n g _ _ ih =>
        refine (equivariantWords β σ).add_mem ?_ ih
        have hsingle : Finsupp.single l (1 : ℤ) ∈ equivariantWords β σ := by
          rw [mem_equivariantWords]
          intro p'
          rw [β.beta_equivariant σ l p']
          congr 1
          rw [χ.chiHom_single, one_zsmul]
        have hsmul : Finsupp.single l n = n • Finsupp.single l (1 : ℤ) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsmul]
        exact zsmul_mem hsingle n
  exact (mem_equivariantWords β).mp hx p

include β in
/--
X.補題6.2A: primary state interpretation は repair-relation soundness を
生成する。`P_sem(σ)` の非空性は witness `p` が担う。
-/
theorem relationSound_of_stateCorrespondence (σ : IntersectionIndex 𝒰)
    (p : Psem.State σ.ctx) {x : P.atomData.SupportedWord σ.ctx}
    (hx : x ∈ P.relSpan σ.ctx) : χ.chiHom σ x = 0 := by
  have hfix : Psem.act σ.ctx x p = p :=
    Psem.relation_sound σ.ctx ⟨σ, rfl⟩ x hx p
  have h := β.beta_word σ x p
  rw [hfix] at h
  exact PQ.free σ (β.beta σ p) (χ.chiHom σ x) h.symm

end PrimaryStateCorrespondence

/-! ## X.定義6.2: SAGA presentation exactness の三条件 -/

namespace PrimaryCoefficientCorrespondence

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {Q : IntersectionCoefficientData.{u, w} 𝒰}
variable (χ : PrimaryCoefficientCorrespondence P Q)

/-- X.定義6.2 第1条件: repair-relation soundness `R_rep ⊆ ker χ̃`。
入力にはせず、補題6.2A が導出する(定理1.1 入力4 の形)。 -/
def RelationSound (σ : IntersectionIndex 𝒰) : Prop :=
  ∀ x ∈ P.relSpan σ.ctx, χ.chiHom σ x = 0

/-- X.定義6.2 第2条件: repair-relation completeness `ker χ̃ ⊆ R_rep`。 -/
def RelationComplete (σ : IntersectionIndex 𝒰) : Prop :=
  ∀ x : P.atomData.SupportedWord σ.ctx, χ.chiHom σ x = 0 -> x ∈ P.relSpan σ.ctx

/-- X.定義6.2 第3条件: target-generator completeness `im χ̃ = Q`。 -/
def GeneratorComplete (σ : IntersectionIndex 𝒰) : Prop :=
  ∀ q : Q.carrier σ, ∃ x : P.atomData.SupportedWord σ.ctx, χ.chiHom σ x = q

/-! ## X.定理6.3: Coefficient Presentation Theorem -/

/-- X.定理6.3: soundness により `χ̃` は商を通り `Φ` を誘導する。 -/
def phi (hsound : ∀ σ : IntersectionIndex 𝒰, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) : P.MSem σ.ctx →+ Q.carrier σ :=
  QuotientAddGroup.lift (P.relSpan σ.ctx) (χ.chiHom σ) (hsound σ)

@[simp]
theorem phi_mk (hsound : ∀ σ, χ.RelationSound σ) (σ : IntersectionIndex 𝒰)
    (x : P.atomData.SupportedWord σ.ctx) :
    χ.phi hsound σ (P.mSemMk σ.ctx x) = χ.chiHom σ x :=
  rfl

/-- X.定理6.3: relation completeness により `Φ` は単射である。 -/
theorem phi_injective (hsound : ∀ σ, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) (hcomplete : χ.RelationComplete σ) :
    Function.Injective (χ.phi hsound σ) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro m hm
  refine QuotientAddGroup.induction_on m ?_ hm
  intro x hx
  exact (QuotientAddGroup.eq_zero_iff x).mpr (hcomplete x hx)

/-- X.定理6.3: generator completeness により `Φ` は全射である。 -/
theorem phi_surjective (hsound : ∀ σ, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) (hgen : χ.GeneratorComplete σ) :
    Function.Surjective (χ.phi hsound σ) := by
  intro q
  rcases hgen q with ⟨x, hx⟩
  exact ⟨P.mSemMk σ.ctx x, hx⟩

/-- X.定理6.3: `Φ` は intersection diagram 上 restriction-natural である。 -/
theorem phi_natural (hsound : ∀ σ, χ.RelationSound σ)
    {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ) (m : P.MSem τ.ctx) :
    Q.restrict f (χ.phi hsound τ m) =
      χ.phi hsound σ (P.mSemRestrict f.hom m) := by
  refine QuotientAddGroup.induction_on m ?_
  intro x
  show Q.restrict f (χ.chiHom τ x) = χ.phi hsound σ (P.mSemRestrict f.hom
    (P.mSemMk τ.ctx x))
  rw [P.mSemRestrict_mk, phi_mk, χ.chiHom_natural f x]

/-- X.定理6.3: exactness 三条件の下で `Φ : M_sem ≃+ Q`(逆写像は構成、入力にしない)。 -/
def phiEquiv (hsound : ∀ σ, χ.RelationSound σ) (σ : IntersectionIndex 𝒰)
    (hcomplete : χ.RelationComplete σ) (hgen : χ.GeneratorComplete σ) :
    P.MSem σ.ctx ≃+ Q.carrier σ :=
  AddEquiv.ofBijective (χ.phi hsound σ)
    ⟨χ.phi_injective hsound σ hcomplete, χ.phi_surjective hsound σ hgen⟩

@[simp]
theorem phiEquiv_apply (hsound : ∀ σ, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) (hcomplete : χ.RelationComplete σ)
    (hgen : χ.GeneratorComplete σ) (m : P.MSem σ.ctx) :
    χ.phiEquiv hsound σ hcomplete hgen m = χ.phi hsound σ m :=
  rfl

/-! ## X.系6.4: image comparison -/

/-- X.系6.4: generator completeness なしでは `M_sem ≃+ im χ̃`。 -/
def imageComparison (σ : IntersectionIndex 𝒰)
    (hsound : χ.RelationSound σ) (hcomplete : χ.RelationComplete σ) :
    P.MSem σ.ctx ≃+ (χ.chiHom σ).range :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
      ext x
      constructor
      · intro hx
        exact hsound x hx
      · intro hx
        exact hcomplete x hx)).trans
    (QuotientAddGroup.quotientKerEquivRange (χ.chiHom σ))

/-- X.系6.4: `im χ̃` は restriction で subpresheaf をなす(自然性)。 -/
theorem range_restrict_mem {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
    {q : Q.carrier τ} (hq : q ∈ (χ.chiHom τ).range) :
    Q.restrict f q ∈ (χ.chiHom σ).range := by
  rcases hq with ⟨x, hx⟩
  exact ⟨P.atomData.wordRestrict f.hom x, by rw [← χ.chiHom_natural f x, hx]⟩

end PrimaryCoefficientCorrespondence

/-! ## X.系6.5: local state comparison の同型性 -/

namespace PrimaryStateCorrespondence

variable {P : SemanticRepairPresentation.{u, v} S R}
variable {Q : IntersectionCoefficientData.{u, w} 𝒰}
variable {χ : PrimaryCoefficientCorrespondence P Q}
variable {Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰}
variable {PQ : AffineCoefficientLiftSystem.{u, w, y} Q}
variable (β : PrimaryStateCorrespondence χ Psem PQ)

/-- `β` の `M_sem` 水準の equivariance(relation による商を経て)。 -/
theorem beta_maction (hsound : ∀ σ, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) (m : P.MSem σ.ctx) (p : Psem.State σ.ctx) :
    β.beta σ (Psem.mact σ m p) =
      PQ.act σ (χ.phi hsound σ m) (β.beta σ p) := by
  refine QuotientAddGroup.induction_on m ?_
  intro x
  show β.beta σ (Psem.act σ.ctx x p) = _
  rw [β.beta_word σ x p]
  rfl

/-- X.系6.5: `β_σ` は単射である(freeness + `Φ` 単射)。 -/
theorem beta_injective (hsound : ∀ σ, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) (hcomplete : χ.RelationComplete σ) :
    Function.Injective (β.beta σ) := by
  intro p q hpq
  rcases Psem.mact_transitive σ p q with ⟨m, hm⟩
  have h := β.beta_maction hsound σ m p
  rw [← hm, hpq] at h
  have hzero : χ.phi hsound σ m = 0 :=
    PQ.free σ (β.beta σ q) (χ.phi hsound σ m) h.symm
  have hm0 : m = 0 := by
    have := χ.phi_injective hsound σ hcomplete (a₁ := m) (a₂ := 0)
    exact this (by rw [hzero, map_zero])
  rw [hm, hm0, Psem.mact_zero]

/-- X.系6.5: `β_σ` は全射である(transitivity + `Φ` 全射、witness `p₀`)。 -/
theorem beta_surjective (hsound : ∀ σ, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) (hgen : χ.GeneratorComplete σ)
    (p₀ : Psem.State σ.ctx) :
    Function.Surjective (β.beta σ) := by
  intro e
  rcases PQ.transitive σ (β.beta σ p₀) e with ⟨q, hq⟩
  rcases χ.phi_surjective hsound σ hgen q with ⟨m, hm⟩
  refine ⟨Psem.mact σ m p₀, ?_⟩
  rw [β.beta_maction hsound σ m p₀, hm, ← hq]

/-- X.系6.5: exactness の下で `β_σ` は `Φ`-equivariant 全単射である。 -/
theorem beta_bijective (hsound : ∀ σ, χ.RelationSound σ)
    (σ : IntersectionIndex 𝒰) (hcomplete : χ.RelationComplete σ)
    (hgen : χ.GeneratorComplete σ) (p₀ : Psem.State σ.ctx) :
    Function.Bijective (β.beta σ) :=
  ⟨β.beta_injective hsound σ hcomplete,
    β.beta_surjective hsound σ hgen p₀⟩

end PrimaryStateCorrespondence

/-! ## R0 §4.9: 定理6.3 用の generic bundle -/

/--
R0 §4.9: 定理6.3(Coefficient Presentation Theorem)用の generic bundle。
completeness 対は bundle に入れず定理仮定として受け取る。
-/
structure SagaPresentationCore (S : Site.AATSite A) where
  occurrenceReading : AtomOccurrenceReading S
  cover : MonomorphicOrderedCover S
  presentation : SemanticRepairPresentation.{u, v} S occurrenceReading
  coefficient : IntersectionCoefficientData.{u, w} cover
  correspondence :
    PrimaryCoefficientCorrespondence presentation coefficient

/-! ## X.例6.6: exactness 三条件の独立性(negative fixtures) -/

namespace ExactnessFixtures

/--
X.例6.6 soundness failure: `R = 2ℤ`, `Q = ℤ`, `χ̃ = id`。
relation `2 = 0` は `Q` で零にならず、写像は `F/R` へ降りない
(soundness が写像の存在を担う)。
-/
theorem soundness_failure :
    ¬ (AddSubgroup.closure {(2 : ℤ)} ≤ (AddMonoidHom.id ℤ).ker) := by
  intro h
  have h2 : (2 : ℤ) ∈ AddSubgroup.closure {(2 : ℤ)} :=
    AddSubgroup.subset_closure rfl
  have := h h2
  simp at this

/--
X.例6.6 completeness failure: `R = 0`, `Q = ℤ/(2)`, `χ̃ = cast`。
写像は降りて全射だが `2 ∈ ker` が `R` に残るため単射でない
(completeness が単射性を担う)。
-/
theorem completeness_failure :
    ¬ ((Int.castAddHom (ZMod 2)).ker ≤ (⊥ : AddSubgroup ℤ)) := by
  intro h
  have h2 : (2 : ℤ) ∈ (Int.castAddHom (ZMod 2)).ker := by
    rw [AddMonoidHom.mem_ker]
    decide
  have := h h2
  simp at this

/--
X.例6.6 generation failure: `R = 2ℤ`, `Q = ℤ/(4)`, `χ̃(n) = [2n]`。
kernel は `R` と一致するが image は `{0, [2]}` で `Q` 全体でない
(generation が全射性を担う)。
-/
theorem generation_failure :
    (1 : ZMod 4) ∉ (zmultiplesHom (ZMod 4) (2 : ZMod 4)).range := by
  rintro ⟨n, hn⟩
  have hval : ((zmultiplesHom (ZMod 4)) (2 : ZMod 4)) n = (n : ZMod 4) * 2 := by
    rw [zmultiplesHom_apply, zsmul_eq_mul]
  have hcast : (n : ZMod 4) * 2 = 1 := by
    rw [← hval, hn]
  have : ∀ m : ZMod 4, m * 2 ≠ 1 := by decide
  exact this (n : ZMod 4) hcast

end ExactnessFixtures

end Saga
end SemanticRepair
end AAT.AG
