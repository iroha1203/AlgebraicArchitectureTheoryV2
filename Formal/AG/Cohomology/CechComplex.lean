import Formal.AG.Cohomology.ObstructionSheaf
import Mathlib.Tactic

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

open CategoryTheory
open Opposite

/--
IV.定義3.1: cover-relative input for the general AAT Čech complex.

The cover is recorded over a selected base object of the AAT site.  The
overlap object for each simplex degree is explicit data, so later finite-poset
comparison can instantiate this surface with the PRD-2 overlap construction.
-/
structure CoverRelativeCechCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  base : S.category
  Index : Type u
  chart : Index -> S.category
  inclusion : ∀ i : Index, chart i ⟶ base
  simplex : Nat -> Type u
  overlap : ∀ n : Nat, simplex n -> S.category
  face : ∀ n : Nat, Fin (n + 2) -> simplex (n + 1) -> simplex n
  faceRestriction :
    ∀ (n : Nat) (i : Fin (n + 2)) (σ : simplex (n + 1)),
      overlap (n + 1) σ ⟶ overlap n (face n i σ)

/-- IV.定義3.2: `C^n(𝒰, Ob_U)` as the selected section family over n-simplices. -/
def CoverRelativeCechCochain {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (𝒰 : CoverRelativeCechCover S) (Ob : ObstructionSheaf S)
    (n : Nat) : Type u :=
  (σ : 𝒰.simplex n) -> Ob.carrier.toPresheaf.obj (op (𝒰.overlap n σ))

/--
IV.定義3.3: general cover-relative Čech complex package.

The cochain object is the section product above.  The differential is supplied
as a selected alternating combination of the concrete face-restriction terms,
together with its `d ∘ d = 0` witness.  This keeps the proof surface concrete
while leaving the finite-poset comparison to the dedicated R2 theorem.
-/
structure CoverRelativeCechComplex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (𝒰 : CoverRelativeCechCover S) (Ob : ObstructionSheaf S) where
  cochainAddCommGroup :
    ∀ n : Nat, AddCommGroup (CoverRelativeCechCochain 𝒰 Ob n)
  alternatingFaceCombination :
    ∀ n : Nat,
      ((σ : 𝒰.simplex (n + 1)) -> Fin (n + 2) ->
        Ob.carrier.toPresheaf.obj (op (𝒰.overlap (n + 1) σ))) ->
      CoverRelativeCechCochain 𝒰 Ob (n + 1)
  differential :
    ∀ n : Nat, CoverRelativeCechCochain 𝒰 Ob n →+
      CoverRelativeCechCochain 𝒰 Ob (n + 1)
  differential_eq_alternatingFaceCombination :
    ∀ (n : Nat) (c : CoverRelativeCechCochain 𝒰 Ob n),
      differential n c =
        alternatingFaceCombination n
          (fun σ i =>
            Ob.carrier.toPresheaf.map (𝒰.faceRestriction n i σ).op
              (c (𝒰.face n i σ)))
  differential_comp :
    ∀ (n : Nat) (c : CoverRelativeCechCochain 𝒰 Ob n),
      differential (n + 1) (differential n c) = 0

attribute [instance] CoverRelativeCechComplex.cochainAddCommGroup

namespace CoverRelativeCechComplex

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}

/-- IV.定義3.2: readable notation for the n-th cochain group. -/
abbrev Cn (_K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) : Type u :=
  CoverRelativeCechCochain 𝒰 Ob n

/-- IV.定義3.3: the selected Čech differential. -/
def d (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :=
  K.differential n

/-- IV.定義3.3: the i-th face-restriction term used by the selected differential. -/
def faceRestrictionTerm (K : CoverRelativeCechComplex 𝒰 Ob)
    (n : Nat) (i : Fin (n + 2)) (c : K.Cn n)
    (σ : 𝒰.simplex (n + 1)) :
    Ob.carrier.toPresheaf.obj (op (𝒰.overlap (n + 1) σ)) :=
  Ob.carrier.toPresheaf.map (𝒰.faceRestriction n i σ).op
    (c (𝒰.face n i σ))

/--
IV.定義3.3: the selected differential is the selected alternating combination
of face-restriction terms.
-/
theorem d_eq_alternatingFaceCombination (K : CoverRelativeCechComplex 𝒰 Ob)
    (n : Nat) (c : K.Cn n) :
    K.d n c =
      K.alternatingFaceCombination n
        (fun σ i => K.faceRestrictionTerm n i c σ) :=
  K.differential_eq_alternatingFaceCombination n c

/-- IV.定義3.3: the selected Čech differential squares to zero. -/
theorem d_comp_d_eq_zero (K : CoverRelativeCechComplex 𝒰 Ob)
    (n : Nat) (c : K.Cn n) :
    letI := K.cochainAddCommGroup (n + 2)
    K.d (n + 1) (K.d n c) = 0 :=
  K.differential_comp n c

/-- IV.定義4.1: kernel of the n-th Čech differential. -/
def CechCocycle (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) : Type u :=
  letI := K.cochainAddCommGroup (n + 1)
  { c : K.Cn n // K.d n c = 0 }

/--
IV.定義4.1: coboundary relation on positive-degree cocycles.

Two `(n+1)`-cocycles are identified when their difference is in the image of
`d^n`.  The `d ∘ d = 0` field above is the reason that these images live in the
next cocycle kernel.
-/
def CechCoboundarySetoidSucc (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    Setoid (K.CechCocycle (n + 1)) :=
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  letI := K.cochainAddCommGroup (n + 2)
  {
    r x y := ∃ b : K.Cn n, x.1 - y.1 = K.d n b
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
          _ = -(K.d n b) := by rw [hb]
          _ = K.d n (-b) := by simp
      · intro x y z hxy hyz
        rcases hxy with ⟨bxy, hbxy⟩
        rcases hyz with ⟨byz, hbyz⟩
        refine ⟨bxy + byz, ?_⟩
        rw [map_add, ← hbxy, ← hbyz]
        abel
  }

/-- IV.定義4.1: positive-degree `H^(n+1)(𝒰, Ob_U) = ker d^(n+1) / im d^n`. -/
abbrev CechCohomologySucc (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    Type u :=
  Quotient (K.CechCoboundarySetoidSucc n)

/-- IV.定義4.1: degree-zero cover-relative cohomology is the zero-cocycle kernel. -/
abbrev CechCohomologyZero (K : CoverRelativeCechComplex 𝒰 Ob) : Type u :=
  K.CechCocycle 0

/-- IV.定義4.1: cover-relative `H^n(𝒰, Ob_U)`. -/
def CoverRelativeHn (K : CoverRelativeCechComplex 𝒰 Ob) : Nat -> Type u
  | 0 => K.CechCohomologyZero
  | n + 1 => K.CechCohomologySucc n

/-- IV.定義4.1: class of a positive-degree cocycle in cover-relative cohomology. -/
def cohomologyClassSucc (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat)
    (c : K.CechCocycle (n + 1)) : K.CechCohomologySucc n :=
  Quotient.mk (K.CechCoboundarySetoidSucc n) c

/--
R5 / IV-1: cochain type tagged by the selected complex so its additive
group instance is recoverable by typeclass search.
-/
def AdditiveCochain (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) : Type u :=
  K.Cn n

instance additiveCochainAddCommGroup (K : CoverRelativeCechComplex 𝒰 Ob)
    (n : Nat) : AddCommGroup (K.AdditiveCochain n) :=
  K.cochainAddCommGroup n

/--
R5 / IV-1: additive cocycle subgroup `Z^n = ker d^n` inside the selected
cover-relative cochain group.
-/
def CechCocycleSubgroup (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    AddSubgroup (K.AdditiveCochain n) :=
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  letI := K.additiveCochainAddCommGroup n
  letI := K.additiveCochainAddCommGroup (n + 1)
  {
    carrier := fun c => K.d n c = 0
    zero_mem' := by
      change K.d n (0 : K.Cn n) = 0
      simp [d]
    add_mem' := by
      intro x y hx hy
      change K.d n (x + y : K.Cn n) = 0
      rw [map_add, hx, hy, add_zero]
    neg_mem' := by
      intro x hx
      change K.d n (-x : K.Cn n) = 0
      rw [map_neg, hx, neg_zero]
  }

/--
R5 / IV-1: a coboundary `d^n b` is a cocycle in degree `n+1`.

This is the load-bearing use of the selected `d ∘ d = 0` witness.
-/
def coboundaryCocycle (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat)
    (b : K.Cn n) : K.CechCocycleSubgroup (n + 1) :=
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  letI := K.cochainAddCommGroup (n + 2)
  letI := K.additiveCochainAddCommGroup n
  letI := K.additiveCochainAddCommGroup (n + 1)
  letI := K.additiveCochainAddCommGroup (n + 2)
  ⟨K.d n b, by
    simpa [CechCocycleSubgroup] using K.d_comp_d_eq_zero n b⟩

/--
R5 / IV-1: additive coboundary subgroup `B^(n+1) = im d^n` inside
`Z^(n+1)`.
-/
def CechCoboundarySubgroupSucc (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    AddSubgroup (K.CechCocycleSubgroup (n + 1)) :=
  letI := K.cochainAddCommGroup n
  letI := K.cochainAddCommGroup (n + 1)
  letI := K.cochainAddCommGroup (n + 2)
  letI := K.additiveCochainAddCommGroup n
  letI := K.additiveCochainAddCommGroup (n + 1)
  letI := K.additiveCochainAddCommGroup (n + 2)
  {
    carrier := fun c => ∃ b : K.Cn n, c = K.coboundaryCocycle n b
    zero_mem' := by
      refine ⟨0, ?_⟩
      ext
      simp [coboundaryCocycle, CechCocycleSubgroup]
    add_mem' := by
      intro x y hx hy
      rcases hx with ⟨bx, rfl⟩
      rcases hy with ⟨by', rfl⟩
      refine ⟨bx + by', ?_⟩
      ext
      simp [coboundaryCocycle, CechCocycleSubgroup, map_add]
    neg_mem' := by
      intro x hx
      rcases hx with ⟨b, rfl⟩
      refine ⟨-b, ?_⟩
      ext
      simp [coboundaryCocycle, CechCocycleSubgroup, map_neg]
  }

/--
R5 / IV-1: additive cover-relative `H^1(𝒰, Ob_U) = Z^1 / B^1`.

The legacy `CechCohomologySucc 0` quotient surface remains unchanged; this is
the additive group reading of the same selected degree-one relation.
-/
abbrev AdditiveCechH1 (K : CoverRelativeCechComplex 𝒰 Ob) : Type u :=
  letI := K.additiveCochainAddCommGroup 0
  letI := K.additiveCochainAddCommGroup 1
  letI := K.additiveCochainAddCommGroup 2
  K.CechCocycleSubgroup 1 ⧸ K.CechCoboundarySubgroupSucc 0

/-- R5 / IV-1: the additive H1 surface carries its quotient abelian group. -/
instance additiveCechH1AddCommGroup (K : CoverRelativeCechComplex 𝒰 Ob) :
    AddCommGroup K.AdditiveCechH1 := by
  dsimp [AdditiveCechH1]
  infer_instance

/-- R5 / IV-1: class of a degree-one cocycle in additive cover-relative H1. -/
def additiveH1Class (K : CoverRelativeCechComplex 𝒰 Ob)
    (c : K.CechCocycle 1) : K.AdditiveCechH1 :=
  letI := K.additiveCochainAddCommGroup 0
  letI := K.additiveCochainAddCommGroup 1
  letI := K.additiveCochainAddCommGroup 2
  ((⟨c.1, c.2⟩ :
      K.CechCocycleSubgroup 1) : K.AdditiveCechH1)

/--
R5 / IV-1: a degree-one additive class vanishes exactly when the selected
cocycle is a degree-zero coboundary.
-/
theorem additiveH1Class_eq_zero_iff (K : CoverRelativeCechComplex 𝒰 Ob)
    (c : K.CechCocycle 1) :
    K.additiveH1Class c = 0 ↔ ∃ b : K.Cn 0, c.1 = K.d 0 b := by
  letI := K.additiveCochainAddCommGroup 0
  letI := K.additiveCochainAddCommGroup 1
  letI := K.additiveCochainAddCommGroup 2
  change
    ((⟨c.1, c.2⟩ :
        K.CechCocycleSubgroup 1) : K.AdditiveCechH1) = 0 ↔
      ∃ b : K.Cn 0, c.1 = K.d 0 b
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    exact congrArg Subtype.val hb
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    ext
    exact hb

/--
R5 / IV-1: the legacy degree-one setoid relation is the same relation read
as equality in the additive quotient.
-/
theorem additiveH1Class_eq_iff_legacy_setoid (K : CoverRelativeCechComplex 𝒰 Ob)
    (x y : K.CechCocycle 1) :
    K.additiveH1Class x = K.additiveH1Class y ↔
      (K.CechCoboundarySetoidSucc 0).r x y := by
  letI := K.additiveCochainAddCommGroup 0
  letI := K.additiveCochainAddCommGroup 1
  letI := K.additiveCochainAddCommGroup 2
  change
    ((⟨x.1, x.2⟩ :
        K.CechCocycleSubgroup 1) : K.AdditiveCechH1) =
      ((⟨y.1, y.2⟩ :
          K.CechCocycleSubgroup 1) : K.AdditiveCechH1) ↔
      (K.CechCoboundarySetoidSucc 0).r x y
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    exact congrArg Subtype.val hb
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    ext
    exact hb

/--
R5 / IV-1: equality of legacy `CechCohomologySucc 0` classes is equivalent
to equality of their additive H1 quotient classes.
-/
theorem cohomologyClassSucc_eq_iff_additiveH1Class_eq
    (K : CoverRelativeCechComplex 𝒰 Ob) (x y : K.CechCocycle 1) :
    K.cohomologyClassSucc 0 x = K.cohomologyClassSucc 0 y ↔
      K.additiveH1Class x = K.additiveH1Class y := by
  change Quotient.mk (K.CechCoboundarySetoidSucc 0) x =
      Quotient.mk (K.CechCoboundarySetoidSucc 0) y ↔
    K.additiveH1Class x = K.additiveH1Class y
  rw [Quotient.eq]
  exact (K.additiveH1Class_eq_iff_legacy_setoid x y).symm

/--
IV.R2 frontier: finite-poset comparison witness for a general Čech complex.

The actual PRD-2 comparison theorem is intentionally left for the R2 issue.
This package is only a typed target for that theorem and carries no claim that
an arbitrary general complex already agrees with the finite-poset surface.
-/
structure FinitePosetComparisonTarget (K : CoverRelativeCechComplex 𝒰 Ob) where
  finitePosetCochain : Nat -> Type u
  finitePosetDifferential : ∀ n : Nat, finitePosetCochain n -> finitePosetCochain (n + 1)
  toFinitePosetCochain : ∀ n : Nat, K.Cn n -> finitePosetCochain n
  fromFinitePosetCochain : ∀ n : Nat, finitePosetCochain n -> K.Cn n
  to_from_finitePosetCochain :
    ∀ (n : Nat) (c : finitePosetCochain n),
      toFinitePosetCochain n (fromFinitePosetCochain n c) = c
  from_to_finitePosetCochain :
    ∀ (n : Nat) (c : K.Cn n),
      fromFinitePosetCochain n (toFinitePosetCochain n c) = c
  differential_compat_toFinitePoset :
    ∀ (n : Nat) (c : K.Cn n),
      toFinitePosetCochain (n + 1) (K.d n c) =
        finitePosetDifferential n (toFinitePosetCochain n c)
  finitePosetCohomology : Nat -> Type u
  toFinitePosetCohomology : ∀ n : Nat, K.CoverRelativeHn n -> finitePosetCohomology n
  fromFinitePosetCohomology : ∀ n : Nat, finitePosetCohomology n -> K.CoverRelativeHn n
  to_from_finitePosetCohomology :
    ∀ (n : Nat) (h : finitePosetCohomology n),
      toFinitePosetCohomology n (fromFinitePosetCohomology n h) = h
  from_to_finitePosetCohomology :
    ∀ (n : Nat) (h : K.CoverRelativeHn n),
      fromFinitePosetCohomology n (toFinitePosetCohomology n h) = h

end CoverRelativeCechComplex

end Cohomology
end AAT.AG
