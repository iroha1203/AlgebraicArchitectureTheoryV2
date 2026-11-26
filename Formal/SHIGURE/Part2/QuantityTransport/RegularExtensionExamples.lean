import Formal.SHIGURE.Part2.QuantityTransport.ExtensionColimit
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Nonuniqueness and nonexistence of regular extensions

Example 5.12 distinguishes equality on native inputs from equality
on every coefficient algebra.
-/

open scoped DualNumber

universe u

noncomputable section

namespace SHIGURE.Quantities.RegularExtensionExamples

/-- Encode a native scalar as a tuple in one variable. -/
private def singletonTuple {k : Type u} (x : k) : PUnit.{u + 1} → k := fun _ => x

section Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- The polynomial (t) extends the identity on the native prime-field inputs. -/
def linearExtension : ExtensionPolynomial (k := ZMod p) (C := ZMod p) singletonTuple id :=
  ⟨MvPolynomial.X PUnit.unit, fun x => by simp [singletonTuple]⟩

/-- The polynomial (t^p) extends exactly the same native values. -/
def frobeniusExtension : ExtensionPolynomial (k := ZMod p) (C := ZMod p) singletonTuple id :=
  ⟨MvPolynomial.X PUnit.unit ^ p, fun x => by
    simp [singletonTuple]⟩

/-- The two operations differ on the nilpotent direction of the dual numbers. -/
theorem extensions_differ_on_dualNumbers :
    (extensionPolynomialEquiv (k := ZMod p) singletonTuple id (linearExtension p)).val.run
      (R := DualNumber (ZMod p)) (singletonTuple ε) ≠
    (extensionPolynomialEquiv (k := ZMod p) singletonTuple id (frobeniusExtension p)).val.run
      (R := DualNumber (ZMod p)) (singletonTuple ε) := by
  change MvPolynomial.aeval (singletonTuple (ε : DualNumber (ZMod p))) (MvPolynomial.X PUnit.unit) ≠
    MvPolynomial.aeval (singletonTuple (ε : DualNumber (ZMod p))) (MvPolynomial.X PUnit.unit ^ p)
  simp only [map_pow, MvPolynomial.aeval_X, singletonTuple]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have vanished : (ε : DualNumber (ZMod p)) ^ p = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hp
    calc
      (ε : DualNumber (ZMod p)) ^ p = ε ^ (2 + n) :=
        congrArg (fun exponent => (ε : DualNumber (ZMod p)) ^ exponent) hn
      _ = 0 := by rw [pow_add, pow_two, DualNumber.eps_mul_eps, zero_mul]
  rw [vanished]
  intro h
  have h' := congrArg (fun z : DualNumber (ZMod p) => z.snd) h
  exact one_ne_zero h'

/-- The two native-compatible elements of the extension colimit are distinct. -/
theorem frobenius_two_extensions :
    (extensionColimitEquiv (k := ZMod p) singletonTuple id).symm (linearExtension p) ≠
      (extensionColimitEquiv (k := ZMod p) singletonTuple id).symm (frobeniusExtension p) := by
  intro eq
  have same := (extensionColimitEquiv (k := ZMod p) singletonTuple id).symm.injective eq
  exact extensions_differ_on_dualNumbers p (by rw [same])

end Frobenius

section Rational

/-- The required native value supported at the single rational input zero. -/
def rationalSpike (x : ℚ) : ℚ := if x = 0 then 1 else 0

/-- The one-variable change of presentation preserves evaluation at every scalar. -/
private theorem eval_pUnit (p : MvPolynomial PUnit ℚ) (x : ℚ) :
    ((MvPolynomial.pUnitAlgEquiv ℚ) p).eval x = MvPolynomial.eval (singletonTuple x) p := by
  let e := MvPolynomial.pUnitAlgEquiv ℚ
  have generator : e (MvPolynomial.X PUnit.unit) = Polynomial.X := MvPolynomial.eval₂_X _ _ _
  have same : (Polynomial.aeval x).comp e.toAlgHom = MvPolynomial.aeval (singletonTuple x) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨⟩
    change Polynomial.aeval x (e (MvPolynomial.X PUnit.unit)) =
      MvPolynomial.aeval (singletonTuple x) (MvPolynomial.X PUnit.unit)
    rw [generator, Polynomial.aeval_X, MvPolynomial.aeval_X]
    rfl
  have values := AlgHom.congr_fun same p
  change Polynomial.aeval x (e p) = MvPolynomial.aeval (singletonTuple x) p at values
  simpa only [Polynomial.coe_aeval_eq_eval, MvPolynomial.aeval_eq_eval] using values

/-- No ordinary polynomial gives the specified spike at the rational native inputs. -/
theorem rationalSpike_noExtensions :
    IsEmpty (ExtensionColimit (C := ℚ) singletonTuple rationalSpike) := by
  refine ⟨fun c => ?_⟩
  let p := extensionColimitEquiv singletonTuple rationalSpike c
  let P := (MvPolynomial.pUnitAlgEquiv ℚ) p.val
  have eval_eq (x : ℚ) : P.eval x = rationalSpike x := by
    rw [show P.eval x = MvPolynomial.eval (singletonTuple x) p.val from eval_pUnit p.val x]
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using p.property x
  have hz : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.finite_singleton (0 : ℚ)).infinite_compl.mono
    intro x hx
    change P.eval x = 0
    rw [eval_eq, rationalSpike, if_neg]
    exact hx
  have h := eval_eq 0
  rw [hz, Polynomial.eval_zero, rationalSpike, if_pos rfl] at h
  exact zero_ne_one h

end Rational

/-- Over an infinite field the identity native input map determines at most one extension. -/
theorem infiniteField_extension_unique {k X : Type u} [Field k] [Infinite k] (residual : (X → k) → k) :
    Subsingleton (ExtensionColimit (C := k) (D := X → k) (X := X) id residual) := by
  refine ⟨fun a b => (extensionColimitEquiv id residual).injective (Subtype.ext ?_)⟩
  apply MvPolynomial.funext
  intro x
  have ha := (extensionColimitEquiv id residual a).property x
  have hb := (extensionColimitEquiv id residual b).property x
  simpa only [Algebra.algebraMap_self, RingHom.id_apply, id_eq] using ha.trans hb.symm

section IntegerStage

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-- The native input records twice the input integer. -/
def doubleInput (n : ℤ) : PUnit → ℤ := singletonTuple (2 * n)

/-- The stage containing only the monomial t. -/
def linearStage : Finset (PUnit →₀ ℕ) := {Finsupp.single PUnit.unit 1}

/-- The only monomial index of the linear stage. -/
private def linearIndex : ↥linearStage := ⟨_, Finset.mem_singleton_self _⟩

/-- The linear stage has exactly the one coefficient b. -/
private theorem linearIndex_eq (i : ↥linearStage) : i = linearIndex :=
  Subtype.ext (Finset.mem_singleton.mp i.property)

/-- The left-hand side of a stage equation is the product of b and the doubled input. -/
private theorem linearStage_sum {C : Type} [CommRing C] [Algebra ℤ C] (b : ↥linearStage → C) (n : ℤ) :
    (∑ m : ↥linearStage, b m * algebraMap ℤ C (nativeMonomialValue (doubleInput n) m.val)) =
      b linearIndex * algebraMap ℤ C (2 * n) := by
  rw [Fintype.sum_eq_single linearIndex]
  · change b linearIndex * algebraMap ℤ C (MvPolynomial.eval (doubleInput n)
        (MvPolynomial.X PUnit.unit)) = _
    rw [MvPolynomial.eval_X]
    rfl
  · exact fun i ne => (ne (linearIndex_eq i)).elim

/-- Over each test algebra, the stage's equations are equivalent to 2b=1. -/
def integerStagePointEquiv {C : Type} [CommRing C] [Algebra ℤ C] :
    StagePoint (C := C) doubleInput id linearStage ≃ {b : C // algebraMap ℤ C 2 * b = 1} where
  toFun a := ⟨a.val linearIndex, by
    have h := a.property 1
    rw [linearStage_sum, mul_one, mul_comm] at h
    simpa only [id_eq, map_one] using h⟩
  invFun b := ⟨fun _ => b.val, fun n => by
    rw [linearStage_sum, id_eq, map_mul, ← mul_assoc, mul_comm b.val, b.property, one_mul]⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    exact congrArg a.val (linearIndex_eq i).symm
  right_inv b := Subtype.ext rfl

/-- The integer stage has no integer point, since two is not a unit in ℤ. -/
theorem integerStage_noIntegerPoint : IsEmpty (StagePoint (C := ℤ) doubleInput id linearStage) := by
  refine ⟨fun a => ?_⟩
  have h := (integerStagePointEquiv a).property
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  omega

/-- The coordinate algebra of the stage inverts two and has the universal property of that localization. -/
def integerStageAlgebraEquiv :
    StageAlgebra doubleInput id linearStage ≃ₐ[ℤ] Localization.Away (2 : ℤ) := by
  let A := StageAlgebra doubleInput id linearStage
  let B := Localization.Away (2 : ℤ)
  let inverseTwo : A := (universalStagePoint doubleInput id linearStage).val linearIndex
  have inverseTwo_spec : algebraMap ℤ A 2 * inverseTwo = 1 :=
    (integerStagePointEquiv (universalStagePoint doubleInput id linearStage)).property
  have twoUnit : IsUnit (algebraMap ℤ A 2) := IsUnit.of_mul_eq_one inverseTwo inverseTwo_spec
  let unitTwo : IsUnit (algebraMap ℤ B 2) := IsLocalization.Away.algebraMap_isUnit _
  let b := unitTwo.exists_right_inv.choose
  let forward : A →ₐ[ℤ] B := stagePointAlgHomEquiv doubleInput id linearStage
    (integerStagePointEquiv.symm ⟨b, unitTwo.exists_right_inv.choose_spec⟩)
  let backward : B →ₐ[ℤ] A :=
    { toRingHom := IsLocalization.Away.lift (2 : ℤ) (g := algebraMap ℤ A) twoUnit
      commutes' := IsLocalization.Away.lift_eq (2 : ℤ) twoUnit }
  refine AlgEquiv.ofAlgHom forward backward ?_ ?_
  · apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
    ext n
    exact (forward.comp backward).commutes n
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    rw [linearIndex_eq i]
    change backward (forward inverseTwo) = inverseTwo
    apply twoUnit.mul_left_cancel
    have eq := congrArg (backward.comp forward) inverseTwo_spec
    rw [map_mul, AlgHom.commutes, map_one] at eq
    exact eq.trans inverseTwo_spec.symm

/-- The stage scheme is Spec of ℤ with two inverted, over Spec ℤ. -/
def integerStageSchemeIso :
    extensionStage doubleInput id linearStage ≅ specOver (Localization.Away (2 : ℤ)) :=
  Over.isoMk (Scheme.Spec.mapIso integerStageAlgebraEquiv.symm.toRingEquiv.toCommRingCatIso.op)
    (Over.w (specOverMap integerStageAlgebraEquiv.symm.toAlgHom))

/-- The linear stage scheme is nonempty, witnessed by its rational coefficient point. -/
theorem integerStage_nonempty : Nonempty (extensionStage doubleInput id linearStage).left := by
  let rationalPoint : StagePoint (C := ℚ) doubleInput id linearStage :=
    integerStagePointEquiv.symm ⟨1 / 2, by norm_num⟩
  let f := stagePointAlgHomEquiv doubleInput id linearStage rationalPoint
  letI : Nontrivial (StageAlgebra doubleInput id linearStage) := f.toRingHom.domain_nontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

end IntegerStage

end SHIGURE.Quantities.RegularExtensionExamples
