import ResearchLean.AG.Basic

/-!
Cycle 1 evidence for `G-aat-quality-surface-01`.

The theorem package formalizes the support-local repair principle for a finite
atom vocabulary: an eliminating repair must hit every selected minimal atom
support for the obstruction certificate.
-/

namespace ResearchLean.AG
namespace QualitySurface

universe u v

/-- A repair support hits a certificate support when they share an atom. -/
def SupportHits {Atom : Type u} (H M : Set Atom) : Prop :=
  ∃ a, a ∈ H ∧ a ∈ M

/-- A repair support misses a certificate support when no atom lies in both. -/
def SupportDisjoint {Atom : Type u} (H M : Set Atom) : Prop :=
  ∀ a, a ∈ H -> a ∈ M -> False

/-- If no hit exists, the two supports are disjoint in the support calculus. -/
theorem supportDisjoint_of_not_hits {Atom : Type u} {H M : Set Atom}
    (h : ¬ SupportHits H M) : SupportDisjoint H M := by
  intro a haH haM
  exact h (Exists.intro a (And.intro haH haM))

/--
Finite support calculus for local repair.

`MinSupportFamily c` is the selected minimal atom-support family for an
obstruction certificate `c`. `AfterRepairFamily H c` records supports that
remain after a repair supported on `H`. The locality axiom says that a selected
support missed by `H` survives the local repair. `Eliminates H c` is certified
by the absence of every after-repair support. The nonempty / antichain fields
record that the selected supports behave as a minimal support family.
-/
structure LocalRepairSupportCalculus (Atom : Type u) [Fintype Atom]
    (ObstructionClass : Type v) where
  MinSupportFamily : ObstructionClass -> Set (Set Atom)
  AfterRepairFamily : Set Atom -> ObstructionClass -> Set (Set Atom)
  Eliminates : Set Atom -> ObstructionClass -> Prop
  minSupportFamilyNonempty :
    ∀ c : ObstructionClass, ∃ M : Set Atom, MinSupportFamily c M
  minSupportFamilyAntichain :
    ∀ {c : ObstructionClass} {M N : Set Atom},
      MinSupportFamily c M ->
        MinSupportFamily c N ->
          (∀ a, a ∈ M -> a ∈ N) ->
            ∀ a, a ∈ N -> a ∈ M
  repairLocalOutside :
    ∀ {H : Set Atom} {c : ObstructionClass} {M : Set Atom},
      MinSupportFamily c M -> SupportDisjoint H M -> AfterRepairFamily H c M
  eliminates_no_afterSupport :
    ∀ {H : Set Atom} {c : ObstructionClass} {M : Set Atom},
      Eliminates H c -> AfterRepairFamily H c M -> False

/--
A minimal support that is missed by the repair support survives, so the repair
does not eliminate the obstruction certificate.
-/
theorem missed_minSupport_survives {Atom : Type u} [Fintype Atom]
    {ObstructionClass : Type v}
    (Q : LocalRepairSupportCalculus Atom ObstructionClass)
    {H : Set Atom} {c : ObstructionClass} {M : Set Atom}
    (hM : Q.MinSupportFamily c M) (hmiss : SupportDisjoint H M) :
    ¬ Q.Eliminates H c := by
  intro helim
  exact Q.eliminates_no_afterSupport helim (Q.repairLocalOutside hM hmiss)

/--
Support-local repair hitting theorem.

If a local repair eliminates an obstruction certificate, then its repair
support hits every selected minimal atom support of that certificate.
-/
theorem hits_every_minSupport_of_eliminates {Atom : Type u} [Fintype Atom]
    {ObstructionClass : Type v}
    (Q : LocalRepairSupportCalculus Atom ObstructionClass)
    {H : Set Atom} {c : ObstructionClass}
    (helim : Q.Eliminates H c) :
    ∀ M : Set Atom, Q.MinSupportFamily c M -> SupportHits H M := by
  intro M hM
  by_contra hhit
  exact (missed_minSupport_survives Q hM (supportDisjoint_of_not_hits hhit)) helim

/-! ## A finite two-support certificate calculus -/

/-- A toy finite atom vocabulary with two disjoint support regions. -/
inductive ToyAtom where
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- A single obstruction certificate in the toy calculus. -/
inductive ToyObstruction where
  | omega
  deriving DecidableEq

namespace Toy

open ToyAtom ToyObstruction

/-- The first selected minimal atom support. -/
def supportAB : Set ToyAtom :=
  fun x => x = a ∨ x = b

/-- The second selected minimal atom support. -/
def supportC : Set ToyAtom :=
  fun x => x = c

/-- A repair touching only atom `a`. -/
def repairA : Set ToyAtom :=
  fun x => x = a

/-- A repair touching one atom in each selected minimal support. -/
def repairAC : Set ToyAtom :=
  fun x => x = a ∨ x = c

/-- The toy obstruction has two selected minimal atom supports. -/
def toyMinSupport : ToyObstruction -> Set (Set ToyAtom)
  | omega => fun M => M = supportAB ∨ M = supportC

/-- A support remains after local repair exactly when the repair misses it. -/
def toyAfterRepair (H : Set ToyAtom) (c : ToyObstruction) : Set (Set ToyAtom) :=
  fun M => toyMinSupport c M ∧ SupportDisjoint H M

/-- The toy repair eliminates the obstruction when no selected support remains. -/
def toyEliminates (H : Set ToyAtom) (c : ToyObstruction) : Prop :=
  ∀ M, ¬ toyAfterRepair H c M

/-- The toy finite certificate calculus used as cycle-1 evidence. -/
def toyCalculus : LocalRepairSupportCalculus ToyAtom ToyObstruction where
  MinSupportFamily := toyMinSupport
  AfterRepairFamily := toyAfterRepair
  Eliminates := toyEliminates
  minSupportFamilyNonempty := by
    intro c
    cases c
    exact Exists.intro supportAB (Or.inl rfl)
  minSupportFamilyAntichain := by
    intro obs M N hM hN hsub x hxN
    cases obs
    cases hM with
    | inl hMab =>
        cases hN with
        | inl hNab =>
            rw [hMab]
            rw [hNab] at hxN
            exact hxN
        | inr hNc =>
            have haM : ToyAtom.a ∈ M := by
              rw [hMab]
              exact Or.inl rfl
            have haN : ToyAtom.a ∈ N := hsub ToyAtom.a haM
            rw [hNc] at haN
            cases haN
    | inr hMc =>
        cases hN with
        | inl hNab =>
            have hcM : ToyAtom.c ∈ M := by
              rw [hMc]
              rfl
            have hcN : ToyAtom.c ∈ N := hsub ToyAtom.c hcM
            rw [hNab] at hcN
            cases hcN with
            | inl hcA => cases hcA
            | inr hcB => cases hcB
        | inr hNc =>
            rw [hMc]
            rw [hNc] at hxN
            exact hxN
  repairLocalOutside := by
    intro H c M hM hmiss
    exact And.intro hM hmiss
  eliminates_no_afterSupport := by
    intro H c M helim hafter
    exact helim M hafter

/-- The two selected minimal supports are distinct. -/
theorem toy_two_minSupports_distinct : supportAB ≠ supportC := by
  intro h
  have haC : ToyAtom.a ∈ supportC := by
    rw [← h]
    exact Or.inl rfl
  cases haC

/-- `{a,b}` is a selected minimal support of the toy obstruction. -/
theorem supportAB_minSupport :
    toyCalculus.MinSupportFamily omega supportAB := by
  exact Or.inl rfl

/-- `{c}` is a selected minimal support of the toy obstruction. -/
theorem supportC_minSupport :
    toyCalculus.MinSupportFamily omega supportC := by
  exact Or.inr rfl

/-- The toy obstruction has a nonempty selected minimal support family. -/
theorem toy_minSupportFamily_nonempty :
    ∃ M : Set ToyAtom, toyCalculus.MinSupportFamily omega M :=
  toyCalculus.minSupportFamilyNonempty omega

/-- The selected minimal supports form an antichain in the toy calculus. -/
theorem toy_minSupportFamily_antichain {M N : Set ToyAtom}
    (hM : toyCalculus.MinSupportFamily omega M)
    (hN : toyCalculus.MinSupportFamily omega N)
    (hsub : ∀ x, x ∈ M -> x ∈ N) :
    ∀ x, x ∈ N -> x ∈ M :=
  toyCalculus.minSupportFamilyAntichain hM hN hsub

/-- The repair `{a}` misses the selected minimal support `{c}`. -/
theorem repairA_misses_supportC : SupportDisjoint repairA supportC := by
  intro x hxA hxC
  cases hxA
  cases hxC

/-- A repair supported only at `a` does not eliminate the toy obstruction. -/
theorem repairA_does_not_eliminate_omega :
    ¬ toyCalculus.Eliminates repairA omega :=
  missed_minSupport_survives toyCalculus supportC_minSupport repairA_misses_supportC

/-- The repair `{a,c}` hits the selected minimal support `{a,b}`. -/
theorem repairAC_hits_supportAB : SupportHits repairAC supportAB := by
  exact Exists.intro ToyAtom.a (And.intro (Or.inl rfl) (Or.inl rfl))

/-- The repair `{a,c}` hits the selected minimal support `{c}`. -/
theorem repairAC_hits_supportC : SupportHits repairAC supportC := by
  exact Exists.intro ToyAtom.c (And.intro (Or.inr rfl) rfl)

/-- The repair `{a,c}` eliminates the toy obstruction. -/
theorem repairAC_eliminates_omega :
    toyCalculus.Eliminates repairAC omega := by
  intro M hafter
  rcases hafter with ⟨hmin, hdisj⟩
  cases hmin with
  | inl hM =>
      have hH : ToyAtom.a ∈ repairAC := Or.inl rfl
      have hS : ToyAtom.a ∈ M := by
        rw [hM]
        exact Or.inl rfl
      exact hdisj ToyAtom.a hH hS
  | inr hM =>
      have hH : ToyAtom.c ∈ repairAC := Or.inr rfl
      have hS : ToyAtom.c ∈ M := by
        rw [hM]
        rfl
      exact hdisj ToyAtom.c hH hS

/-- In the toy calculus, an eliminating repair hits every selected support. -/
theorem repairAC_hits_every_minSupport :
    ∀ M : Set ToyAtom, toyCalculus.MinSupportFamily omega M -> SupportHits repairAC M :=
  hits_every_minSupport_of_eliminates toyCalculus repairAC_eliminates_omega

end Toy

end QualitySurface
end ResearchLean.AG
