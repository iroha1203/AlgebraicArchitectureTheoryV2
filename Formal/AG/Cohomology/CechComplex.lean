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

end CoverRelativeCechComplex

end Cohomology
end AAT.AG
