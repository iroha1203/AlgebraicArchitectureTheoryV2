import ResearchLean.AG.UniformInvariance.UniformityReduction
import Formal.Util.AssertStandardAxioms

/-!
# Defect semantics for uniform invariance

This module completes claim (i) of
`G-107-aat-uniform-invariance-characterization`.  For a finite-dimensional
rational linear map it records the exact kernel/cokernel defect
`(finrank ker, finrank (codomain / range))`, proves independently that this
defect vanishes exactly for bijective maps, and specializes the result to the
actual constant-rational A-subnerve H¹ comparison.

Combining that pointwise bridge with the Cycle 4 reduction characterizes
uniform invariance by zero defect on every nonempty target subset.  No inverse,
rank, defect, or bijectivity certificate is supplied as comparison data.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution TwoPhase

universe u

variable {Source : Type u}

/-! ## Finite-dimensional kernel/cokernel defect -/

/-- The exact rational defect of a linear map: kernel dimension followed by
the dimension of the literal cokernel quotient by its range. -/
def blockDefect {V W : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (f : V →ₗ[ℚ] W) : ℕ × ℕ :=
  (Module.finrank ℚ (LinearMap.ker f),
    Module.finrank ℚ (W ⧸ LinearMap.range f))

/-- For a finite-dimensional rational linear map, exact kernel/cokernel
defect vanishes if and only if the underlying map is bijective. -/
theorem blockDefect_eq_zero_iff_bijective
    {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (f : V →ₗ[ℚ] W) :
    blockDefect f = (0, 0) ↔ Function.Bijective f := by
  constructor
  · intro hzero
    have hkerZero : Module.finrank ℚ (LinearMap.ker f) = 0 :=
      congrArg Prod.fst hzero
    have hcokerZero : Module.finrank ℚ (W ⧸ LinearMap.range f) = 0 :=
      congrArg Prod.snd hzero
    have hker : LinearMap.ker f = ⊥ :=
      Submodule.finrank_eq_zero.mp hkerZero
    have hrangeFinrank :
        Module.finrank ℚ (LinearMap.range f) = Module.finrank ℚ W := by
      have hquotient := Submodule.finrank_quotient_add_finrank
        (LinearMap.range f)
      omega
    have hrange : LinearMap.range f = ⊤ :=
      Submodule.eq_top_of_finrank_eq hrangeFinrank
    exact ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  · intro hbijective
    have hker : LinearMap.ker f = ⊥ :=
      LinearMap.ker_eq_bot.mpr hbijective.1
    have hrange : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr hbijective.2
    have hkerZero : Module.finrank ℚ (LinearMap.ker f) = 0 :=
      Submodule.finrank_eq_zero.mpr hker
    have hcokerZero : Module.finrank ℚ (W ⧸ LinearMap.range f) = 0 := by
      have hquotient := Submodule.finrank_quotient_add_finrank
        (LinearMap.range f)
      rw [hrange]
      rw [hrange] at hquotient
      simpa using hquotient
    exact Prod.ext hkerZero hcokerZero

/-! ## Actual A-subnerve defect and uniformity -/

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-- The defect of the actual H¹ map on the constant-rational A-subnerve and
the canonical fine preimage of `A`. -/
def aSubnerveDefect
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target) : ℕ × ℕ :=
  blockDefect (M.aSubnerveComparisonHom A).h1Map

/-- The actual A-subnerve defect is zero exactly when the actual induced H¹
map is bijective. -/
theorem aSubnerveDefect_eq_zero_iff_bijective
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (A : Set coarseReading.Target) :
    M.aSubnerveDefect A = (0, 0) ↔
      Function.Bijective (M.aSubnerveComparisonHom A).h1Map :=
  blockDefect_eq_zero_iff_bijective
    (M.aSubnerveComparisonHom A).h1Map

/-- Uniform invariance is equivalent to exact zero kernel/cokernel defect for
every nonempty actual A-subnerve H¹ comparison. -/
theorem uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero
    [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine) :
    M.UniformInvariance ↔
      ∀ (A : Set coarseReading.Target), A.Nonempty →
        M.aSubnerveDefect A = (0, 0) := by
  rw [M.uniformInvariance_iff_allNonemptyASubnerveH1Bijective]
  constructor
  · intro hbijective A hA
    exact (M.aSubnerveDefect_eq_zero_iff_bijective A).2
      (hbijective A hA)
  · intro hzero A hA
    exact (M.aSubnerveDefect_eq_zero_iff_bijective A).1 (hzero A hA)

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
