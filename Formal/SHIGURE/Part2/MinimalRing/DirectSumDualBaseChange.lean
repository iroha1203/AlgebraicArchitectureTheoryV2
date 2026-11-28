import Formal.SHIGURE.Part2.MinimalRing.DualBaseChangeEquiv
import Formal.SHIGURE.Part2.MinimalRing.DirectSumBaseChange

/-! Scalar extension and dualization for maps out of arbitrary direct sums. -/

namespace SHIGURE.MinimalRing

open scoped DirectSum TensorProduct

variable {R T ι M : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable [AddCommGroup M] [Module R M]
variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- The direct sum of the canonical dual base-change maps intertwines
the direct-sum maps of a family and its scalar extension. -/
theorem dualBaseChange_toModule [DecidableEq ι] (f : ∀ i, M →ₗ[R] N i) :
    (dualBaseChangeMap (R := R) (T := T) M).comp
        (DirectSum.toModule T ι (T ⊗[R] Module.Dual R M)
          (fun i => (f i).dualMap.baseChange T)) =
      (DirectSum.toModule T ι (Module.Dual T (T ⊗[R] M))
        (fun i => ((f i).baseChange T).dualMap)).comp
          (DirectSum.lmap (fun i => dualBaseChangeMap (R := R) (T := T) (N i))) := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.toModule_lof, DirectSum.lmap_lof]
  exact LinearMap.congr_fun (dualBaseChangeMap_natural (T := T) (f i)) x

variable [Module.Finite R M] [Module.Projective R M]
variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Projective R (N i)]

/-- Scalar extension of an arbitrary direct sum of duals is canonically the
direct sum of the duals of the scalar-extended modules. -/
noncomputable def directSumDualBaseChangeEquiv :
    (T ⊗[R] (⨁ i, Module.Dual R (N i))) ≃ₗ[T]
      (⨁ i, Module.Dual T (T ⊗[R] N i)) :=
  (scalarDirectSumEquiv (R := R) (T := T) (M := fun i => Module.Dual R (N i))).trans
    (DirectSum.congrLinearEquiv (fun i => dualBaseChangeEquiv (R := R) (T := T) (M := N i)))

/-- The preceding equivalences make the direct-sum dual map commute with
scalar extension, with no finiteness assumption on the index type. -/
theorem toModule_dual_baseChange [DecidableEq ι] (f : ∀ i, M →ₗ[R] N i) :
    (dualBaseChangeEquiv (R := R) (T := T) (M := M)).toLinearMap.comp
      ((DirectSum.toModule R ι (Module.Dual R M) (fun i => (f i).dualMap)).baseChange T) =
    (DirectSum.toModule T ι (Module.Dual T (T ⊗[R] M))
      (fun i => ((f i).baseChange T).dualMap)).comp
        (directSumDualBaseChangeEquiv (R := R) (T := T) (N := N)).toLinearMap := by
  have hbase := toModule_baseChange (T := T) (fun i => (f i).dualMap)
  have hnatural := dualBaseChange_toModule (T := T) f
  change (dualBaseChangeMap (R := R) (T := T) M).comp
      ((DirectSum.toModule R ι (Module.Dual R M) (fun i => (f i).dualMap)).baseChange T) =
    (DirectSum.toModule T ι (Module.Dual T (T ⊗[R] M))
      (fun i => ((f i).baseChange T).dualMap)).comp
        ((DirectSum.lmap (fun i => dualBaseChangeMap (R := R) (T := T) (N i))).comp
          (scalarDirectSumEquiv (R := R) (T := T)
            (M := fun i => Module.Dual R (N i))).toLinearMap)
  rw [scalarDirectSumEquiv_eq_directSumRight, ← hbase, ← LinearMap.comp_assoc,
    hnatural, LinearMap.comp_assoc]

end SHIGURE.MinimalRing
