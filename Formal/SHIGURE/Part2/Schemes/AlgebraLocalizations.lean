import Mathlib.RingTheory.Localization.Module

/-! # Algebra localization from the underlying module map

For a map of commutative algebras, localization of the underlying
module at a submonoid of the coefficient ring gives localization
of the algebra at the image of that submonoid.
-/

namespace SHIGURE.SchemeDescent

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Detect the algebra localization using the actual underlying scalar-linear map. -/
theorem isLocalization_of_isLocalizedModule (S : Submonoid R)
    (h : IsLocalizedModule S (IsScalarTower.toAlgHom R A B).toLinearMap) :
    IsLocalization (Algebra.algebraMapSubmonoid A S) B := by
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨s, hs, equal⟩ := y.property
    have unit := h.map_units ⟨s, hs⟩
    rw [Module.End.isUnit_iff] at unit
    obtain ⟨b, inverse⟩ := unit.2 (1 : B)
    change s • b = 1 at inverse
    apply IsUnit.of_mul_eq_one b
    rw [← equal, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
    exact inverse
  · intro b
    obtain ⟨⟨a, s⟩, equal⟩ := h.surj b
    refine ⟨⟨a, ⟨algebraMap R A s, ⟨s, s.property, rfl⟩⟩⟩, ?_⟩
    change b * algebraMap A B (algebraMap R A s) = algebraMap A B a
    rw [← IsScalarTower.algebraMap_apply, mul_comm, ← Algebra.smul_def]
    exact equal
  · intro a a' equal
    obtain ⟨s, equality⟩ := h.exists_of_eq equal
    refine ⟨⟨algebraMap R A s, ⟨s, s.property, rfl⟩⟩, ?_⟩
    change algebraMap R A s * a = algebraMap R A s * a'
    simpa only [Submonoid.smul_def, Algebra.smul_def] using equality

end SHIGURE.SchemeDescent
