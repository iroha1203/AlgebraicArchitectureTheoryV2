import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Stalk ranks of finite projective duals

Localization identifies the dual of a finite projective module with the
dual of its localized module.  The latter is finite free over the local ring,
so its rank agrees with the rank of the original localization.
-/

namespace SHIGURE.MinimalRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

/-- A finite projective module and its dual have the same rank at every prime. -/
theorem dual_rankAtStalk_eq (p : PrimeSpectrum R) :
    Module.rankAtStalk (Module.Dual R M) p = Module.rankAtStalk M p := by
  classical
  let U := p.asIdeal.primeCompl
  let A := Localization.AtPrime p.asIdeal
  let V := LocalizedModule U M
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  letI : Module.Free A V := Module.free_of_flat_of_isLocalRing
  let j : Module.Dual R M →ₗ[R] Module.Dual A V :=
    IsLocalizedModule.mapExtendScalars U (LocalizedModule.mkLinearMap U M)
      (Algebra.linearMap R A) A
  letI : IsLocalizedModule U j :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars U
      (LocalizedModule.mkLinearMap U M) (Algebra.linearMap R A) A
  let e : LocalizedModule U (Module.Dual R M) ≃ₗ[A] Module.Dual A V :=
    (IsLocalizedModule.linearEquiv U (LocalizedModule.mkLinearMap U (Module.Dual R M)) j)
      |>.extendScalarsOfIsLocalization U A
  change Module.finrank A (LocalizedModule U (Module.Dual R M)) = Module.finrank A V
  exact e.finrank_eq.trans (Module.Free.chooseBasis A V).toDualEquiv.symm.finrank_eq

end SHIGURE.MinimalRing
