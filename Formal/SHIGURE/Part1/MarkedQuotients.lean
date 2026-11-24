import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Canonical marked quotient modules

Equation (3.4) of SHIGURE Chapter 3 uses the quotient of a finite free module
by a specified kernel. Its marks are the images of the named coordinate
basis vectors.

## Implementation notes

Use mathlib submodules and their standard quotients, so an equality of
kernels determines a strict equality of the marked data. An arbitrary
isomorphic module with a chosen surjection would require additional
identifications to give that same strict restriction. The finite locally
free condition uses finite projectivity and the mathlib rank at each prime.
-/

universe u

namespace SHIGURE.Marked

variable {R : Type u} [CommRing R] {m n : ℕ}

/-- The coordinates of the `m` named generators in Equation (3.4). -/
abbrev Coordinates (R : Type u) (m : ℕ) := Fin m → R

/-- The actual relations among the generators in Equation (3.4). -/
abbrev Kernel (R : Type u) [CommRing R] (m : ℕ) := Submodule R (Coordinates R m)

/-- The canonical quotient carrier in Equation (3.4). -/
abbrev Quotient (K : Kernel R m) := Coordinates R m ⧸ K

/-- The canonical quotient map in Equation (3.4). -/
def projection (K : Kernel R m) : Coordinates R m →ₗ[R] Quotient K :=
  K.mkQ

/-- Every quotient point is represented by a vector of coordinates. -/
theorem projection_surjective (K : Kernel R m) : Function.Surjective (projection K) :=
  K.mkQ_surjective

/-- The kernel of the marked presentation's projection is the specified submodule. -/
theorem ker_projection (K : Kernel R m) : LinearMap.ker (projection K) = K :=
  K.ker_mkQ

/-- The named generators are the images of the coordinate basis. -/
def generator (K : Kernel R m) (i : Fin m) : Quotient K :=
  projection K (Pi.single i 1)

/-- The coordinate formula for a named generator uses no choice of representatives. -/
theorem projection_single (K : Kernel R m) (i : Fin m) :
    projection K (Pi.single i 1) = generator K i :=
  rfl

/-- A canonical quotient of the finite coordinate module is finite over the coefficient ring. -/
theorem module_finite (K : Kernel R m) : Module.Finite R (Quotient K) :=
  Module.Finite.of_surjective (projection K) (projection_surjective K)

/-- The additional quotient condition in Proposition 3.6. Finiteness is automatic. -/
structure FixedRank (K : Kernel R m) (n : ℕ) : Prop where
  /-- Projectivity gives local freeness for the finite quotient. -/
  projective : Module.Projective R (Quotient K)
  /-- Each prime stalk has the declared finite rank. -/
  atPrime (p : PrimeSpectrum R) : Module.rankAtStalk (R := R) (Quotient K) p = n

/-- The quotient is locally free in mathlib's free-locus sense at every prime. -/
theorem FixedRank.freeLocus_eq_univ {K : Kernel R m} (h : FixedRank K n) :
    Module.freeLocus R (Quotient K) = Set.univ := by
  letI := module_finite K
  letI := h.projective
  exact Module.freeLocus_eq_univ

/-- For a finitely presented quotient, the free locus and stalk ranks give the same condition. -/
theorem FixedRank.of_freeLocus {K : Kernel R m} [Module.FinitePresentation R (Quotient K)]
    (locallyFree : Module.freeLocus R (Quotient K) = Set.univ)
    (rank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (Quotient K) p = n) :
    FixedRank K n :=
  ⟨Module.freeLocus_eq_univ_iff.mp locallyFree, rank⟩

/-- A finite projective marked quotient is finitely presented over the fixed ring. -/
theorem FixedRank.finitePresentation {K : Kernel R m} (h : FixedRank K n) :
    Module.FinitePresentation R (Quotient K) := by
  letI := module_finite K
  letI := h.projective
  exact Module.finitePresentation_of_projective R (Quotient K)

/-- A mark-preserving equivalence intertwines the two coordinate projections. -/
theorem comp_projection_of_preserves {K L : Kernel R m} (e : Quotient K ≃ₗ[R] Quotient L)
    (marks : ∀ i, e (generator K i) = generator L i) :
    e.toLinearMap.comp (projection K) = projection L := by
  apply (Pi.basisFun R (Fin m)).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, projection_single] using marks i

/-- A mark-preserving linear equivalence can exist only when the presentation kernels are equal. -/
theorem kernel_eq_of_preserves {K L : Kernel R m} (e : Quotient K ≃ₗ[R] Quotient L)
    (marks : ∀ i, e (generator K i) = generator L i) : K = L := by
  rw [← ker_projection K, ← ker_projection L, ← comp_projection_of_preserves e marks]
  exact (e.ker_comp (projection K)).symm

end SHIGURE.Marked
