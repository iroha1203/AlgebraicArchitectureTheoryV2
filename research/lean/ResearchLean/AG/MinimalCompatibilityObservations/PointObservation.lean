import Mathlib
import ResearchLean.AG.ComparisonInformationLoss.ObservationKernel
import Formal.Util.AssertStandardAxioms

/-!
# G-128: point observations of a group action

The observation records the action at each point of a finite set. The pointwise
stabilizer is the kernel of this observation in the sense of indistinguishability
from the identity; no normality or faithfulness is assumed.
-/

namespace AAT.AG.MinimalCompatibilityObservations

variable {G X : Type*} [Group G] [MulAction G X]

/-- The exact table observed on a finite set of points. -/
def observe (B : Finset X) (g : G) : {x : X // x ∈ B} → X :=
  fun x => g • x.1

/-- The subgroup fixing every point of the observation set. -/
def pointStabilizer (B : Finset X) : Subgroup G where
  carrier := {g | ∀ x ∈ B, g • x = x}
  one_mem' := by intro x hx; simp
  mul_mem' := by
    intro g h hg hh x hx
    rw [mul_smul, hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    have h := hg x hx
    have := congrArg (fun y => g⁻¹ • y) h
    simpa using this.symm

@[simp] theorem mem_pointStabilizer_iff (B : Finset X) (g : G) :
    g ∈ pointStabilizer B ↔ ∀ x ∈ B, g • x = x := Iff.rfl

/-- Equal observation tables are precisely left cosets of the point stabilizer. -/
theorem observe_eq_iff (B : Finset X) (g h : G) :
    observe B g = observe B h ↔ h⁻¹ * g ∈ pointStabilizer B := by
  constructor
  · intro heq x hx
    have hpoint := congrFun heq ⟨x, hx⟩
    change g • x = h • x at hpoint
    have := congrArg (fun y => h⁻¹ • y) hpoint
    simpa [mul_smul] using this
  · intro hfix
    funext x
    have hpoint := hfix x.1 x.2
    change (h⁻¹ * g) • x.1 = x.1 at hpoint
    have := congrArg (fun y => h • y) hpoint
    simpa [mul_smul] using this

/-- A finite set is sufficient when its pointwise stabilizer lies in the
compatible subgroup. -/
def Sufficient (Gamma : Subgroup G) (B : Finset X) : Prop :=
  pointStabilizer B ≤ Gamma

/-- The exact observation predicate can be constructed from the compatible
elements. Its existence is equivalent to pointwise stabilizer inclusion. -/
theorem exists_predicate_iff_sufficient (Gamma : Subgroup G) (B : Finset X) :
    (∃ P : (({x : X // x ∈ B} → X) → Prop),
      ∀ g : G, P (observe B g) ↔ g ∈ Gamma) ↔ Sufficient Gamma B := by
  constructor
  · rintro ⟨P, hP⟩ k hk
    have hobs : observe B k = observe B (1 : G) :=
      (observe_eq_iff B k 1).2 (by simpa using hk)
    exact (hP k).1 (hobs ▸ (hP 1).2 Gamma.one_mem)
  · intro hS
    refine ⟨fun t => ∃ gamma : G, gamma ∈ Gamma ∧ observe B gamma = t, ?_⟩
    intro g
    constructor
    · rintro ⟨gamma, hgamma, hobs⟩
      have hk : gamma⁻¹ * g ∈ Gamma := hS ((observe_eq_iff B g gamma).1
        hobs.symm)
      have hg : g = gamma * (gamma⁻¹ * g) := by simp
      rw [hg]
      exact Gamma.mul_mem hgamma hk
    · intro hg
      exact ⟨g, hg, rfl⟩

/-- The minimum size of a sufficient finite observation set, or infinity if
there is none. -/
noncomputable def minObservations (Gamma : Subgroup G) : ℕ∞ :=
  ⨅ B : {B : Finset X // Sufficient Gamma B}, (B.1.card : ℕ∞)

theorem minObservations_le (Gamma : Subgroup G) (B : Finset X)
    (hB : Sufficient Gamma B) : minObservations (X := X) Gamma ≤ (B.card : ℕ∞) := by
  exact iInf_le (fun B : {B : Finset X // Sufficient Gamma B} => (B.1.card : ℕ∞))
    ⟨B, hB⟩

theorem minObservations_eq_top_iff (Gamma : Subgroup G) :
    minObservations (X := X) Gamma = ⊤ ↔ ¬ ∃ B : Finset X, Sufficient Gamma B := by
  unfold minObservations
  rw [ENat.iInf_coe_eq_top]
  constructor
  · intro h ⟨B, hB⟩
    exact h.false ⟨B, hB⟩
  · intro h
    exact ⟨fun B => h ⟨B.1, B.2⟩⟩

theorem minObservations_attained (Gamma : Subgroup G)
    (h : minObservations (X := X) Gamma ≠ ⊤) :
    ∃ B : Finset X, Sufficient Gamma B ∧ (B.card : ℕ∞) = minObservations (X := X) Gamma := by
  have hne : ∃ B : Finset X, Sufficient Gamma B := by
    by_contra hn
    exact h ((minObservations_eq_top_iff (X := X) Gamma).2 hn)
  letI : Nonempty {B : Finset X // Sufficient Gamma B} :=
    let ⟨B, hB⟩ := hne
    ⟨⟨B, hB⟩⟩
  obtain ⟨B, hB⟩ := ENat.exists_eq_iInf
    (fun B : {B : Finset X // Sufficient Gamma B} => (B.1.card : ℕ∞))
  exact ⟨B.1, B.2, hB⟩

theorem sufficient_empty_iff (Gamma : Subgroup G) :
    Sufficient Gamma (∅ : Finset X) ↔ Gamma = ⊤ := by
  have hs : pointStabilizer (∅ : Finset X) = (⊤ : Subgroup G) := by
    ext g
    simp [pointStabilizer]
  simp [Sufficient, hs, top_le_iff]

theorem minObservations_eq_zero_iff (Gamma : Subgroup G) :
    minObservations (X := X) Gamma = 0 ↔ Gamma = ⊤ := by
  constructor
  · intro h
    obtain ⟨B, hB, hc⟩ := minObservations_attained (X := X) Gamma (by simp [h])
    have hzero : B.card = 0 := by exact_mod_cast hc.trans h
    have he : B = ∅ := Finset.card_eq_zero.mp hzero
    exact (sufficient_empty_iff Gamma).1 (he ▸ hB)
  · intro h
    have hB : Sufficient Gamma (∅ : Finset X) :=
      (sufficient_empty_iff Gamma).2 h
    exact le_antisymm (by simpa using minObservations_le (X := X) Gamma ∅ hB) bot_le

/-- For the trivial compatible subgroup, sufficient observation is exactly
identification of every group element. -/
theorem sufficient_bot_iff_injective (B : Finset X) :
    Sufficient (⊥ : Subgroup G) B ↔
      Function.Injective (observe B : G → ({x : X // x ∈ B} → X)) := by
  constructor
  · intro h g k heq
    have hmem : k⁻¹ * g ∈ (⊥ : Subgroup G) :=
      h ((observe_eq_iff B g k).1 heq)
    have hone : k⁻¹ * g = 1 := by simpa using hmem
    exact (inv_mul_eq_one.mp hone).symm
  · intro hinj g hg
    have heq : observe B g = observe B (1 : G) :=
      (observe_eq_iff B g 1).2 (by simpa using hg)
    have hone : g = 1 := hinj heq
    simpa [hone]

section HomObservation

variable {L : Type*} [Group L] (O : G →* L)

/-- Left multiplication through a homomorphism gives G-120's observation
as the value at the identity point. -/
theorem hom_observe_one (g : G) :
    letI : MulAction G L := MulAction.compHom L O
    observe ({1} : Finset L) g ⟨1, by simp⟩ = O g := by
  change O g * 1 = O g
  simp

/-- The point stabilizer of the identity under the homomorphism action is
exactly the observation kernel from G-120. -/
theorem hom_pointStabilizer_one :
    letI : MulAction G L := MulAction.compHom L O
    pointStabilizer ({1} : Finset L) = O.ker := by
  ext g
  change (∀ x ∈ ({1} : Finset L), O g * x = x) ↔ O g = 1
  simp

/-- The singleton point-observation criterion is G-120's kernel criterion,
with the same observed value and compatible subgroup. -/
theorem hom_predicate_iff_original (Gamma : Subgroup G) :
    letI : MulAction G L := MulAction.compHom L O
    (∃ P : (({x : L // x ∈ ({1} : Finset L)} → L) → Prop),
      ∀ g : G, P (observe ({1} : Finset L) g) ↔ g ∈ Gamma) ↔
    (∃ h : L → Prop, ∀ g : G, g ∈ Gamma ↔ h (O g)) := by
  letI : MulAction G L := MulAction.compHom L O
  rw [exists_predicate_iff_sufficient, Sufficient, hom_pointStabilizer_one]
  exact (AAT.AG.ComparisonInformationLoss.exists_observation_predicate_iff_ker_le
    O Gamma).symm

end HomObservation

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
