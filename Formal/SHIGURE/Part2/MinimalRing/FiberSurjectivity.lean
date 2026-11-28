import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Detecting surjectivity on residue-field fibers

For a linear map with finite target, tensoring with every residue field
reflects surjectivity.  The proof uses the finite cokernel, its support, and
right exactness of tensor product.
-/

namespace SHIGURE.MinimalRing

open scoped TensorProduct

variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A map to a finite module is surjective if and only if all of its
residue-field tensors are surjective. -/
theorem surjective_iff_residueField_lTensor_surjective [Module.Finite R N]
    (f : M →ₗ[R] N) :
    Function.Surjective f ↔
      ∀ p : PrimeSpectrum R, Function.Surjective (f.lTensor p.asIdeal.ResidueField) := by
  constructor
  · intro hf p
    exact LinearMap.lTensor_surjective _ hf
  · intro hf
    let Q := N ⧸ LinearMap.range f
    haveI : Module.Finite R Q := Module.Finite.quotient R (LinearMap.range f)
    have hsupport : Module.support R Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have htop : LinearMap.range (f.lTensor p.asIdeal.ResidueField) = ⊤ :=
        LinearMap.range_eq_top.mpr (hf p)
      have hquot : Subsingleton
          ((p.asIdeal.ResidueField ⊗[R] N) ⧸
            LinearMap.range (f.lTensor p.asIdeal.ResidueField)) :=
        Submodule.Quotient.subsingleton_iff.mpr htop
      let e := lTensor.equiv p.asIdeal.ResidueField f.exact_map_mkQ_range
        (Submodule.mkQ_surjective (LinearMap.range f))
      have hsub : Subsingleton (p.asIdeal.ResidueField ⊗[R] Q) :=
        e.toEquiv.subsingleton_congr.mp hquot
      have hnontrivial : Nontrivial (p.asIdeal.ResidueField ⊗[R] Q) :=
        (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hp
      exact (not_nontrivial_iff_subsingleton.mpr hsub) hnontrivial
    haveI : Subsingleton Q := (Module.support_eq_empty_iff (R := R) (M := Q)).mp hsupport
    apply LinearMap.range_eq_top.mp
    exact Submodule.Quotient.subsingleton_iff.mp (inferInstance : Subsingleton Q)

end SHIGURE.MinimalRing
