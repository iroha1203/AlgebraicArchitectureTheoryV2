import Formal.AG.Cohomology.CechComplex

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

/--
X.R1(c): a semantic-free three-term additive cochain complex.

Only degrees `0`, `1`, and `2` are recorded, because the R1(c) comparison
needs exactly the data required to form `H^1 = ker d¹ / im d⁰`.
-/
structure AdditiveThreeTermComplex (C0 C1 C2 : Type u)
    [AddCommGroup C0] [AddCommGroup C1] [AddCommGroup C2] where
  d0 : C0 →+ C1
  d1 : C1 →+ C2
  d_comp : ∀ c : C0, d1 (d0 c) = 0

namespace AdditiveThreeTermComplex

variable {C0 C1 C2 D0 D1 D2 : Type u}
variable [AddCommGroup C0] [AddCommGroup C1] [AddCommGroup C2]
variable [AddCommGroup D0] [AddCommGroup D1] [AddCommGroup D2]

/-- X.R1(c): degree-one cocycles of a three-term complex. -/
def H1Cocycle (K : AdditiveThreeTermComplex C0 C1 C2) : Type u :=
  { c : C1 // K.d1 c = 0 }

/-- X.R1(c): degree-one coboundary relation `x - y ∈ im d⁰`. -/
def H1CoboundarySetoid (K : AdditiveThreeTermComplex C0 C1 C2) :
    Setoid K.H1Cocycle :=
  {
    r x y := ∃ b : C0, x.1 - y.1 = K.d0 b
    iseqv := by
      refine ⟨?refl, ?symm, ?trans⟩
      · intro x
        refine ⟨0, ?_⟩
        simp
      · intro x y hxy
        rcases hxy with ⟨b, hb⟩
        refine ⟨-b, ?_⟩
        calc
          y.1 - x.1 = -(x.1 - y.1) := by abel
          _ = -(K.d0 b) := by rw [hb]
          _ = K.d0 (-b) := by simp
      · intro x y z hxy hyz
        rcases hxy with ⟨bxy, hbxy⟩
        rcases hyz with ⟨byz, hbyz⟩
        refine ⟨bxy + byz, ?_⟩
        rw [map_add, ← hbxy, ← hbyz]
        abel
  }

/-- X.R1(c): the semantic-free `H^1` quotient of a three-term complex. -/
abbrev H1 (K : AdditiveThreeTermComplex C0 C1 C2) : Type u :=
  Quotient K.H1CoboundarySetoid

/-- X.R1(c): zero class in semantic-free `H^1`. -/
def H1ZeroClass (K : AdditiveThreeTermComplex C0 C1 C2) : K.H1 :=
  Quotient.mk K.H1CoboundarySetoid ⟨0, by simp⟩

/-- X.R1(c): zero predicate for the semantic-free `H^1` quotient. -/
def H1IsZero (K : AdditiveThreeTermComplex C0 C1 C2) (h : K.H1) : Prop :=
  h = K.H1ZeroClass

/--
X.R1(c): cochain-level equivalence of three-term complexes.

The fields are deliberately cochain-level: degree-wise additive maps, inverse
laws in degrees `0`, `1`, and `2`, and differential compatibility in both
directions.  The quotient-level `H^1` maps below are generated from these
fields rather than supplied as assumptions.
-/
structure Equivalence (K : AdditiveThreeTermComplex C0 C1 C2)
    (L : AdditiveThreeTermComplex D0 D1 D2) where
  to0 : C0 →+ D0
  to1 : C1 →+ D1
  to2 : C2 →+ D2
  from0 : D0 →+ C0
  from1 : D1 →+ C1
  from2 : D2 →+ C2
  to0_from0 : ∀ c : D0, to0 (from0 c) = c
  from0_to0 : ∀ c : C0, from0 (to0 c) = c
  to1_from1 : ∀ c : D1, to1 (from1 c) = c
  from1_to1 : ∀ c : C1, from1 (to1 c) = c
  to2_from2 : ∀ c : D2, to2 (from2 c) = c
  from2_to2 : ∀ c : C2, from2 (to2 c) = c
  to_d0 : ∀ c : C0, to1 (K.d0 c) = L.d0 (to0 c)
  to_d1 : ∀ c : C1, to2 (K.d1 c) = L.d1 (to1 c)
  from_d0 : ∀ c : D0, from1 (L.d0 c) = K.d0 (from0 c)
  from_d1 : ∀ c : D1, from2 (L.d1 c) = K.d1 (from1 c)

namespace Equivalence

variable {K : AdditiveThreeTermComplex C0 C1 C2}
variable {L : AdditiveThreeTermComplex D0 D1 D2}

/-- X.R1(c): the forward cochain map sends degree-one cocycles to cocycles. -/
def toH1Cocycle (E : Equivalence K L) (c : K.H1Cocycle) : L.H1Cocycle :=
  ⟨E.to1 c.1, by
    calc
      L.d1 (E.to1 c.1) = E.to2 (K.d1 c.1) := by rw [E.to_d1 c.1]
      _ = 0 := by simp [c.2]⟩

/-- X.R1(c): the reverse cochain map sends degree-one cocycles to cocycles. -/
def fromH1Cocycle (E : Equivalence K L) (c : L.H1Cocycle) : K.H1Cocycle :=
  ⟨E.from1 c.1, by
    calc
      K.d1 (E.from1 c.1) = E.from2 (L.d1 c.1) := by rw [E.from_d1 c.1]
      _ = 0 := by simp [c.2]⟩

/-- X.R1(c): generated map on `H^1` from a cochain-level equivalence. -/
def toH1 (E : Equivalence K L) : K.H1 -> L.H1 :=
  Quotient.lift
    (fun c => Quotient.mk L.H1CoboundarySetoid (E.toH1Cocycle c))
    (by
      intro x y hxy
      rcases hxy with ⟨b, hb⟩
      apply Quotient.sound
      refine ⟨E.to0 b, ?_⟩
      calc
        (E.toH1Cocycle x).1 - (E.toH1Cocycle y).1 =
            E.to1 (x.1 - y.1) := by simp [toH1Cocycle]
        _ = E.to1 (K.d0 b) := by rw [hb]
        _ = L.d0 (E.to0 b) := E.to_d0 b)

/-- X.R1(c): generated inverse map on `H^1` from a cochain-level equivalence. -/
def fromH1 (E : Equivalence K L) : L.H1 -> K.H1 :=
  Quotient.lift
    (fun c => Quotient.mk K.H1CoboundarySetoid (E.fromH1Cocycle c))
    (by
      intro x y hxy
      rcases hxy with ⟨b, hb⟩
      apply Quotient.sound
      refine ⟨E.from0 b, ?_⟩
      calc
        (E.fromH1Cocycle x).1 - (E.fromH1Cocycle y).1 =
            E.from1 (x.1 - y.1) := by simp [fromH1Cocycle]
        _ = E.from1 (L.d0 b) := by rw [hb]
        _ = K.d0 (E.from0 b) := E.from_d0 b)

/-- X.R1(c): generated `H^1` maps are left inverses. -/
theorem to_from_H1 (E : Equivalence K L) (h : L.H1) :
    E.toH1 (E.fromH1 h) = h := by
  refine Quotient.inductionOn h ?_
  intro x
  apply Quotient.sound
  refine ⟨0, ?_⟩
  simp [toH1Cocycle, fromH1Cocycle, E.to1_from1]

/-- X.R1(c): generated `H^1` maps are right inverses. -/
theorem from_to_H1 (E : Equivalence K L) (h : K.H1) :
    E.fromH1 (E.toH1 h) = h := by
  refine Quotient.inductionOn h ?_
  intro x
  apply Quotient.sound
  refine ⟨0, ?_⟩
  simp [toH1Cocycle, fromH1Cocycle, E.from1_to1]

/-- X.R1(c): the generated forward `H^1` map preserves the zero class. -/
theorem toH1_zero (E : Equivalence K L) :
    E.toH1 K.H1ZeroClass = L.H1ZeroClass := by
  apply Quotient.sound
  refine ⟨0, ?_⟩
  simp [toH1Cocycle]

/-- X.R1(c): the generated reverse `H^1` map preserves the zero class. -/
theorem fromH1_zero (E : Equivalence K L) :
    E.fromH1 L.H1ZeroClass = K.H1ZeroClass := by
  apply Quotient.sound
  refine ⟨0, ?_⟩
  simp [fromH1Cocycle]

/-- X.R1(c): the generated forward map reflects and preserves zero classes. -/
theorem toH1_zero_iff (E : Equivalence K L) (h : K.H1) :
    L.H1IsZero (E.toH1 h) ↔ K.H1IsZero h := by
  constructor
  · intro hh
    calc
      h = E.fromH1 (E.toH1 h) := by rw [E.from_to_H1 h]
      _ = E.fromH1 L.H1ZeroClass := by rw [hh]
      _ = K.H1ZeroClass := E.fromH1_zero
  · intro hh
    rw [H1IsZero] at hh
    rw [hh]
    exact E.toH1_zero

/-- X.R1(c): the generated reverse map reflects and preserves zero classes. -/
theorem fromH1_zero_iff (E : Equivalence K L) (h : L.H1) :
    K.H1IsZero (E.fromH1 h) ↔ L.H1IsZero h := by
  constructor
  · intro hh
    calc
      h = E.toH1 (E.fromH1 h) := by rw [E.to_from_H1 h]
      _ = E.toH1 K.H1ZeroClass := by rw [hh]
      _ = L.H1ZeroClass := E.toH1_zero
  · intro hh
    rw [H1IsZero] at hh
    rw [hh]
    exact E.fromH1_zero

end Equivalence

end AdditiveThreeTermComplex

namespace CoverRelativeCechComplex

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}

/-- X.R1(c): expose the selected additive structure on Čech cochains. -/
instance instCnAddCommGroup (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    AddCommGroup (K.Cn n) :=
  K.cochainAddCommGroup n

/--
X.R1(c): the degree `0,1,2` additive spine of a cover-relative Čech complex.
-/
def degreeOneThreeTerm (K : CoverRelativeCechComplex 𝒰 Ob) :
    AdditiveThreeTermComplex (K.Cn 0) (K.Cn 1) (K.Cn 2) where
  d0 := K.d 0
  d1 := K.d 1
  d_comp := K.differential_comp 0

/--
X.R1(c): generated H¹ map to a finite-poset comparison target, once the
target's degree `0,1,2` cochains carry the pinned three-term additive complex
and cochain-level equivalence with the cover-relative spine.
-/
def FinitePosetComparisonTarget.generatedH1To
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (T : K.FinitePosetComparisonTarget)
    [AddCommGroup (T.finitePosetCochain 0)]
    [AddCommGroup (T.finitePosetCochain 1)]
    [AddCommGroup (T.finitePosetCochain 2)]
    (L : AdditiveThreeTermComplex
      (T.finitePosetCochain 0) (T.finitePosetCochain 1) (T.finitePosetCochain 2))
    (E : AdditiveThreeTermComplex.Equivalence K.degreeOneThreeTerm L)
    (_to0_eq_target : ∀ c : K.Cn 0, E.to0 c = T.toFinitePosetCochain 0 c)
    (_to1_eq_target : ∀ c : K.Cn 1, E.to1 c = T.toFinitePosetCochain 1 c)
    (_from0_eq_target : ∀ c : T.finitePosetCochain 0,
      E.from0 c = T.fromFinitePosetCochain 0 c)
    (_from1_eq_target : ∀ c : T.finitePosetCochain 1,
      E.from1 c = T.fromFinitePosetCochain 1 c)
    (_d0_eq_target : ∀ c : T.finitePosetCochain 0,
      L.d0 c = T.finitePosetDifferential 0 c)
    (_d1_eq_target : ∀ c : T.finitePosetCochain 1,
      L.d1 c = T.finitePosetDifferential 1 c) :
    K.CoverRelativeHn 1 -> L.H1 :=
  E.toH1

/--
X.R1(c): generated inverse H¹ map from a finite-poset comparison target.
-/
def FinitePosetComparisonTarget.generatedH1From
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (T : K.FinitePosetComparisonTarget)
    [AddCommGroup (T.finitePosetCochain 0)]
    [AddCommGroup (T.finitePosetCochain 1)]
    [AddCommGroup (T.finitePosetCochain 2)]
    (L : AdditiveThreeTermComplex
      (T.finitePosetCochain 0) (T.finitePosetCochain 1) (T.finitePosetCochain 2))
    (E : AdditiveThreeTermComplex.Equivalence K.degreeOneThreeTerm L)
    (_to0_eq_target : ∀ c : K.Cn 0, E.to0 c = T.toFinitePosetCochain 0 c)
    (_to1_eq_target : ∀ c : K.Cn 1, E.to1 c = T.toFinitePosetCochain 1 c)
    (_from0_eq_target : ∀ c : T.finitePosetCochain 0,
      E.from0 c = T.fromFinitePosetCochain 0 c)
    (_from1_eq_target : ∀ c : T.finitePosetCochain 1,
      E.from1 c = T.fromFinitePosetCochain 1 c)
    (_d0_eq_target : ∀ c : T.finitePosetCochain 0,
      L.d0 c = T.finitePosetDifferential 0 c)
    (_d1_eq_target : ∀ c : T.finitePosetCochain 1,
      L.d1 c = T.finitePosetDifferential 1 c) :
    L.H1 -> K.CoverRelativeHn 1 :=
  E.fromH1

/--
X.R1(c): generated finite-poset H¹ maps are inverse in the target direction.
-/
theorem FinitePosetComparisonTarget.generatedH1_to_from
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (T : K.FinitePosetComparisonTarget)
    [AddCommGroup (T.finitePosetCochain 0)]
    [AddCommGroup (T.finitePosetCochain 1)]
    [AddCommGroup (T.finitePosetCochain 2)]
    (L : AdditiveThreeTermComplex
      (T.finitePosetCochain 0) (T.finitePosetCochain 1) (T.finitePosetCochain 2))
    (E : AdditiveThreeTermComplex.Equivalence K.degreeOneThreeTerm L)
    (hto0 : ∀ c : K.Cn 0, E.to0 c = T.toFinitePosetCochain 0 c)
    (hto1 : ∀ c : K.Cn 1, E.to1 c = T.toFinitePosetCochain 1 c)
    (hfrom0 : ∀ c : T.finitePosetCochain 0,
      E.from0 c = T.fromFinitePosetCochain 0 c)
    (hfrom1 : ∀ c : T.finitePosetCochain 1,
      E.from1 c = T.fromFinitePosetCochain 1 c)
    (hd0 : ∀ c : T.finitePosetCochain 0,
      L.d0 c = T.finitePosetDifferential 0 c)
    (hd1 : ∀ c : T.finitePosetCochain 1,
      L.d1 c = T.finitePosetDifferential 1 c)
    (h : L.H1) :
    FinitePosetComparisonTarget.generatedH1To K T L E hto0 hto1 hfrom0 hfrom1 hd0 hd1
      (FinitePosetComparisonTarget.generatedH1From K T L E hto0 hto1 hfrom0 hfrom1 hd0 hd1 h) =
        h :=
  E.to_from_H1 h

/--
X.R1(c): generated finite-poset H¹ maps are inverse in the cover-relative
direction.
-/
theorem FinitePosetComparisonTarget.generatedH1_from_to
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (T : K.FinitePosetComparisonTarget)
    [AddCommGroup (T.finitePosetCochain 0)]
    [AddCommGroup (T.finitePosetCochain 1)]
    [AddCommGroup (T.finitePosetCochain 2)]
    (L : AdditiveThreeTermComplex
      (T.finitePosetCochain 0) (T.finitePosetCochain 1) (T.finitePosetCochain 2))
    (E : AdditiveThreeTermComplex.Equivalence K.degreeOneThreeTerm L)
    (hto0 : ∀ c : K.Cn 0, E.to0 c = T.toFinitePosetCochain 0 c)
    (hto1 : ∀ c : K.Cn 1, E.to1 c = T.toFinitePosetCochain 1 c)
    (hfrom0 : ∀ c : T.finitePosetCochain 0,
      E.from0 c = T.fromFinitePosetCochain 0 c)
    (hfrom1 : ∀ c : T.finitePosetCochain 1,
      E.from1 c = T.fromFinitePosetCochain 1 c)
    (hd0 : ∀ c : T.finitePosetCochain 0,
      L.d0 c = T.finitePosetDifferential 0 c)
    (hd1 : ∀ c : T.finitePosetCochain 1,
      L.d1 c = T.finitePosetDifferential 1 c)
    (h : K.CoverRelativeHn 1) :
    FinitePosetComparisonTarget.generatedH1From K T L E hto0 hto1 hfrom0 hfrom1 hd0 hd1
      (FinitePosetComparisonTarget.generatedH1To K T L E hto0 hto1 hfrom0 hfrom1 hd0 hd1 h) =
        h :=
  E.from_to_H1 h

/--
X.R1(c): generated finite-poset H¹ comparison preserves and reflects the zero
predicate.
-/
theorem FinitePosetComparisonTarget.generatedH1_zero_iff
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (T : K.FinitePosetComparisonTarget)
    [AddCommGroup (T.finitePosetCochain 0)]
    [AddCommGroup (T.finitePosetCochain 1)]
    [AddCommGroup (T.finitePosetCochain 2)]
    (L : AdditiveThreeTermComplex
      (T.finitePosetCochain 0) (T.finitePosetCochain 1) (T.finitePosetCochain 2))
    (E : AdditiveThreeTermComplex.Equivalence K.degreeOneThreeTerm L)
    (hto0 : ∀ c : K.Cn 0, E.to0 c = T.toFinitePosetCochain 0 c)
    (hto1 : ∀ c : K.Cn 1, E.to1 c = T.toFinitePosetCochain 1 c)
    (hfrom0 : ∀ c : T.finitePosetCochain 0,
      E.from0 c = T.fromFinitePosetCochain 0 c)
    (hfrom1 : ∀ c : T.finitePosetCochain 1,
      E.from1 c = T.fromFinitePosetCochain 1 c)
    (hd0 : ∀ c : T.finitePosetCochain 0,
      L.d0 c = T.finitePosetDifferential 0 c)
    (hd1 : ∀ c : T.finitePosetCochain 1,
      L.d1 c = T.finitePosetDifferential 1 c)
    (h : K.CoverRelativeHn 1) :
    L.H1IsZero
        (FinitePosetComparisonTarget.generatedH1To K T L E hto0 hto1 hfrom0 hfrom1 hd0 hd1 h) ↔
      K.degreeOneThreeTerm.H1IsZero h :=
  E.toH1_zero_iff h

/--
X.R1(c): rebuild a finite-poset comparison target with the degree-one
cohomology fields generated from a cochain-level equivalence.

All cochain fields and all non-`H^1` cohomology fields are inherited from the
input target.  Only the `n = 1` cohomology object and maps are replaced by the
semantic-free quotient generated above.  The extra equality hypotheses pin the
cochain-level equivalence and its three-term differential to the inherited
target fields; they prevent using this constructor to attach an unrelated
degree-one quotient to the target.
-/
def FinitePosetComparisonTarget.withGeneratedH1
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (T : K.FinitePosetComparisonTarget)
    [AddCommGroup (T.finitePosetCochain 0)]
    [AddCommGroup (T.finitePosetCochain 1)]
    [AddCommGroup (T.finitePosetCochain 2)]
    (L : AdditiveThreeTermComplex
      (T.finitePosetCochain 0) (T.finitePosetCochain 1) (T.finitePosetCochain 2))
    (E : AdditiveThreeTermComplex.Equivalence K.degreeOneThreeTerm L)
    (_to0_eq_target : ∀ c : K.Cn 0, E.to0 c = T.toFinitePosetCochain 0 c)
    (_to1_eq_target : ∀ c : K.Cn 1, E.to1 c = T.toFinitePosetCochain 1 c)
    (_from0_eq_target : ∀ c : T.finitePosetCochain 0,
      E.from0 c = T.fromFinitePosetCochain 0 c)
    (_from1_eq_target : ∀ c : T.finitePosetCochain 1,
      E.from1 c = T.fromFinitePosetCochain 1 c)
    (_d0_eq_target : ∀ c : T.finitePosetCochain 0,
      L.d0 c = T.finitePosetDifferential 0 c)
    (_d1_eq_target : ∀ c : T.finitePosetCochain 1,
      L.d1 c = T.finitePosetDifferential 1 c) :
    K.FinitePosetComparisonTarget where
  finitePosetCochain := T.finitePosetCochain
  finitePosetDifferential := T.finitePosetDifferential
  toFinitePosetCochain := T.toFinitePosetCochain
  fromFinitePosetCochain := T.fromFinitePosetCochain
  to_from_finitePosetCochain := T.to_from_finitePosetCochain
  from_to_finitePosetCochain := T.from_to_finitePosetCochain
  differential_compat_toFinitePoset := T.differential_compat_toFinitePoset
  finitePosetCohomology := fun
    | 0 => T.finitePosetCohomology 0
    | 1 => L.H1
    | n + 2 => T.finitePosetCohomology (n + 2)
  toFinitePosetCohomology := fun
    | 0 => T.toFinitePosetCohomology 0
    | 1 => E.toH1
    | n + 2 => T.toFinitePosetCohomology (n + 2)
  fromFinitePosetCohomology := fun
    | 0 => T.fromFinitePosetCohomology 0
    | 1 => E.fromH1
    | n + 2 => T.fromFinitePosetCohomology (n + 2)
  to_from_finitePosetCohomology := by
    intro n
    cases n with
    | zero =>
        exact T.to_from_finitePosetCohomology 0
    | succ n =>
        cases n with
        | zero =>
            exact E.to_from_H1
        | succ n =>
            exact T.to_from_finitePosetCohomology (n + 2)
  from_to_finitePosetCohomology := by
    intro n
    cases n with
    | zero =>
        exact T.from_to_finitePosetCohomology 0
    | succ n =>
        cases n with
        | zero =>
            exact E.from_to_H1
        | succ n =>
            exact T.from_to_finitePosetCohomology (n + 2)

end CoverRelativeCechComplex

end Cohomology
end AAT.AG
