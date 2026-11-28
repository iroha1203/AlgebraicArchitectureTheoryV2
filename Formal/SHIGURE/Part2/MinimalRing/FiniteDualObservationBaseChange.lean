import Formal.SHIGURE.Part2.MinimalRing.ObservationBaseChange
import Formal.SHIGURE.Part2.MinimalRing.DualBaseChangeEquiv
import Formal.SHIGURE.Part2.MinimalRing.DualProduct

/-!
# Scalar extension of the dual of finite observation

The canonical comparison acts on the dual of the actual finite product;
`boundedObservationMap_dualMap_comp_equiv` identifies this dual with the
direct sum of the output duals.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped TensorProduct

variable {R T S : Type*} [CommRing R] [CommRing T] [Algebra R T] [Finite S]
variable {Op : S → S → Type*} [∀ s t, Finite (Op s t)]
variable {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]
variable [∀ s, Module.Finite R (E s)] [∀ s, Module.Projective R (E s)]
variable [∀ s, Module.Finite R (O s)] [∀ s, Module.Projective R (O s)]

/-- The canonical source equivalence for the dual of finite observation. -/
noncomputable def boundedObservationDualBaseChangeEquiv (s : S) (n : ℕ) :
    (T ⊗[R] Module.Dual R (∀ w : ShortOutputWord Op s n, O w.1.1)) ≃ₗ[T]
      Module.Dual T (∀ w : ShortOutputWord Op s n, T ⊗[R] O w.1.1) := by
  classical
  letI : Finite (ShortOutputWord Op s n) := finite_shortOutputWord s n
  letI : Fintype (ShortOutputWord Op s n) := Fintype.ofFinite _
  letI : ∀ w : ShortOutputWord Op s n, Module.Projective R (O w.1.1) :=
    fun w => inferInstanceAs (Module.Projective R (O w.1.1))
  letI : Module.Projective R (∀ w : ShortOutputWord Op s n, O w.1.1) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype
      (R := R) (M := fun w : ShortOutputWord Op s n => O w.1.1))
  exact (dualBaseChangeEquiv (R := R) (T := T)
    (M := ∀ w : ShortOutputWord Op s n, O w.1.1)).trans
      (observationProductEquiv (R := R) (T := T) (Op := Op) (O := O) s n).symm.dualMap

/-- The actual finite observation `dualMap` commutes with scalar extension
through the canonical dual and finite-product equivalences. -/
theorem boundedObservationMap_dualMap_baseChange
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s) (s : S) (n : ℕ) :
    (dualBaseChangeEquiv (R := R) (T := T) (M := E s)).toLinearMap.comp
      ((boundedObservationMap A observe s n).dualMap.baseChange T) =
    (boundedObservationMap
      (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
      (O := fun u => T ⊗[R] O u) (baseChangeSystem T A)
      (fun u => (observe u).baseChange T) s n).dualMap.comp
        (boundedObservationDualBaseChangeEquiv (R := R) (T := T) (Op := Op) (O := O) s n).toLinearMap := by
  classical
  letI : Finite (ShortOutputWord Op s n) := finite_shortOutputWord s n
  letI : Fintype (ShortOutputWord Op s n) := Fintype.ofFinite _
  letI : ∀ w : ShortOutputWord Op s n, Module.Projective R (O w.1.1) :=
    fun w => inferInstanceAs (Module.Projective R (O w.1.1))
  letI : Module.Projective R (∀ w : ShortOutputWord Op s n, O w.1.1) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype
      (R := R) (M := fun w : ShortOutputWord Op s n => O w.1.1))
  let e := observationProductEquiv (R := R) (T := T) (Op := Op) (O := O) s n
  have hn := dualBaseChangeMap_natural (T := T) (boundedObservationMap A observe s n)
  rw [boundedObservationMap_baseChange]
  apply LinearMap.ext
  intro x
  change dualBaseChangeMap (R := R) (T := T) (E s)
      ((boundedObservationMap A observe s n).dualMap.baseChange T x) =
    (e.toLinearMap.comp ((boundedObservationMap A observe s n).baseChange T)).dualMap
      (e.symm.dualMap (dualBaseChangeMap (R := R) (T := T)
        (∀ w : ShortOutputWord Op s n, O w.1.1) x))
  have hx := LinearMap.congr_fun hn x
  change dualBaseChangeMap (R := R) (T := T) (E s)
      ((boundedObservationMap A observe s n).dualMap.baseChange T x) =
    ((boundedObservationMap A observe s n).baseChange T).dualMap
      (dualBaseChangeMap (R := R) (T := T) (∀ w : ShortOutputWord Op s n, O w.1.1) x) at hx
  rw [hx]
  apply LinearMap.ext
  intro y
  change dualBaseChangeMap (R := R) (T := T) (∀ w : ShortOutputWord Op s n, O w.1.1) x
      ((boundedObservationMap A observe s n).baseChange T y) =
    dualBaseChangeMap (R := R) (T := T) (∀ w : ShortOutputWord Op s n, O w.1.1) x
      (e.symm (e ((boundedObservationMap A observe s n).baseChange T y)))
  rw [e.symm_apply_apply]

/-- The same comparison starting from the direct sum of the finite-word
output duals, using the canonical finite-product dual equivalence. -/
theorem boundedWordDualObservationMap_baseChange_via_product
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (s : S) (n : ℕ) [Fintype (ShortOutputWord Op s n)] :
    (dualBaseChangeEquiv (R := R) (T := T) (M := E s)).toLinearMap.comp
      ((boundedWordDualObservationMap A observe s n).baseChange T) =
    (boundedObservationMap
      (E := fun u => T ⊗[R] E u) (I := fun u => T ⊗[R] I u)
      (O := fun u => T ⊗[R] O u) (baseChangeSystem T A)
      (fun u => (observe u).baseChange T) s n).dualMap.comp
        ((boundedObservationDualBaseChangeEquiv (R := R) (T := T) (Op := Op) (O := O) s n).toLinearMap.comp
          ((finiteDualProductEquiv (fun w : ShortOutputWord Op s n => O w.1.1)).toLinearMap.baseChange T)) := by
  rw [← boundedObservationMap_dualMap_comp_equiv, LinearMap.baseChange_comp,
    ← LinearMap.comp_assoc, boundedObservationMap_dualMap_baseChange, LinearMap.comp_assoc]

end SHIGURE.MinimalRing
