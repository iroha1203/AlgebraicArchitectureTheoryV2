import ResearchLean.AG.MinimalCompatibilityObservations.PointObservation
import ResearchLean.AG.ProtocolHolonomy.FiniteDirectDecision
import Formal.Util.AssertStandardAxioms

/-!
# G-128: finite search for observation-table extensions

The input enumeration is the concrete finite table of surrounding changes.
Each search is a terminating list recursion and returns an actual change.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy

variable {G : Type*}

/-- A finite scan returns the first candidate accepted by the Boolean test. -/
def scan (p : G → Bool) : List G → Option G
  | [] => none
  | g :: gs => if p g then some g else scan p gs

theorem scan_some (p : G → Bool) (l : List G) (g : G)
    (h : scan p l = some g) : p g = true ∧ g ∈ l := by
  induction l with
  | nil => simp [scan] at h
  | cons a as ih =>
      by_cases ha : p a = true
      · simp [scan, ha] at h
        subst g
        exact ⟨ha, by simp⟩
      · have hfalse : p a = false := Bool.eq_false_iff.mpr ha
        simp [scan, hfalse] at h
        obtain ⟨hp, hm⟩ := ih h
        exact ⟨hp, by simp [hm]⟩

theorem scan_none_iff (p : G → Bool) (l : List G) :
    scan p l = none ↔ ∀ g ∈ l, p g = false := by
  induction l with
  | nil => simp [scan]
  | cons a as ih =>
      by_cases ha : p a = true
      · simp [scan, ha]
      · have hfalse : p a = false := Bool.eq_false_iff.mpr ha
        simp [scan, hfalse, ih]

variable {X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- Equality of an observed table is decided by checking its finite domain. -/
def tableMatches (B : Finset X) (t : {x : X // x ∈ B} → X) (g : G) : Bool :=
  letI : Fintype {x : X // x ∈ B} := ⟨B.attach, by intro x; simp⟩
  decide (∀ x : {x : X // x ∈ B}, g • x.1 = t x)

theorem tableMatches_iff (B : Finset X) (t : {x : X // x ∈ B} → X) (g : G) :
    tableMatches B t g = true ↔ observe B g = t := by
  simp only [tableMatches, decide_eq_true_eq]
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

/-- Search all surrounding changes for an extension of an arbitrary table. -/
def findExtension (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) : Option G :=
  scan (tableMatches B t) EG.values

theorem findExtension_some (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) (g : G)
    (h : findExtension EG B t = some g) : observe B g = t := by
  exact (tableMatches_iff B t g).mp (scan_some _ _ _ h).1

theorem findExtension_none_iff (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) :
    findExtension EG B t = none ↔ ¬ ∃ g : G, observe B g = t := by
  rw [findExtension, scan_none_iff]
  constructor
  · intro h ⟨g, hg⟩
    have hf := h g (EG.complete g)
    have ht := (tableMatches_iff B t g).mpr hg
    simp [ht] at hf
  · intro h g hg
    by_cases ht : tableMatches B t g = true
    · exact (h ⟨g, (tableMatches_iff B t g).mp ht⟩).elim
    · exact Bool.eq_false_iff.mpr ht

theorem findExtension_isSome_iff (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) :
    (findExtension EG B t).isSome = true ↔ ∃ g : G, observe B g = t := by
  cases hfind : findExtension EG B t with
  | none =>
      have hn := (findExtension_none_iff EG B t).mp hfind
      simp [hn]
  | some g => exact iff_of_true (by simp) ⟨g, findExtension_some EG B t g hfind⟩

section Compatible

variable (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]

/-- Search the same finite table, accepting only compatible extensions. -/
def findCompatibleExtension (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) : Option G :=
  scan (fun g => tableMatches B t g && decide (g ∈ Gamma)) EG.values

theorem findCompatibleExtension_some (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) (g : G)
    (h : findCompatibleExtension Gamma EG B t = some g) :
    observe B g = t ∧ g ∈ Gamma := by
  obtain ⟨hp, _⟩ := scan_some _ _ _ h
  have hp' : tableMatches B t g = true ∧ decide (g ∈ Gamma) = true := by
    simpa [findCompatibleExtension] using hp
  exact ⟨(tableMatches_iff B t g).mp hp'.1, of_decide_eq_true hp'.2⟩

theorem findCompatibleExtension_none_iff (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) :
    findCompatibleExtension Gamma EG B t = none ↔
      ¬ ∃ g : G, g ∈ Gamma ∧ observe B g = t := by
  rw [findCompatibleExtension, scan_none_iff]
  constructor
  · intro h ⟨g, hg, ht⟩
    have hf := h g (EG.complete g)
    have hm := (tableMatches_iff B t g).mpr ht
    simp [hm, hg] at hf
  · intro h g hg
    by_cases hm : tableMatches B t g = true
    · by_cases hgamma : g ∈ Gamma
      · exact (h ⟨g, hgamma, (tableMatches_iff B t g).mp hm⟩).elim
      · simp [hm, hgamma]
    · simp [Bool.eq_false_iff.mpr hm]

theorem findCompatibleExtension_isSome_iff (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) :
    (findCompatibleExtension Gamma EG B t).isSome = true ↔
      ∃ g : G, g ∈ Gamma ∧ observe B g = t := by
  cases hfind : findCompatibleExtension Gamma EG B t with
  | none =>
      have hn := (findCompatibleExtension_none_iff Gamma EG B t).mp hfind
      simp [hn]
  | some g =>
      have h := findCompatibleExtension_some Gamma EG B t g hfind
      exact iff_of_true (by simp) ⟨g, h.2, h.1⟩

/-- The executable classifier reads only the observation table. -/
def classify (EG : ExplicitEnumeration G) (B : Finset X)
    (t : {x : X // x ∈ B} → X) : Bool :=
  (findCompatibleExtension Gamma EG B t).isSome

theorem classify_correct (EG : ExplicitEnumeration G) (B : Finset X)
    (hB : Sufficient Gamma B) (g : G) :
    classify Gamma EG B (observe B g) = true ↔ g ∈ Gamma := by
  rw [classify, findCompatibleExtension_isSome_iff]
  constructor
  · rintro ⟨gamma, hgamma, hobs⟩
    have hk : gamma⁻¹ * g ∈ Gamma :=
      hB ((observe_eq_iff B g gamma).1 hobs.symm)
    have hg : g = gamma * (gamma⁻¹ * g) := by simp
    rw [hg]
    exact Gamma.mul_mem hgamma hk
  · intro hg
    exact ⟨g, hg, rfl⟩

end Compatible

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
