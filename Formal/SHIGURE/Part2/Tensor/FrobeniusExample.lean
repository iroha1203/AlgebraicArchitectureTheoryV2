import Formal.SHIGURE.Part2.Tensor.CopyingComparison
import Formal.SHIGURE.Part2.Tensor.UniversalTerms
import Mathlib.Algebra.DualNumber
import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite-field points and infinitesimal directions

Example 4.11 compares the native finite-field equation with its polynomial
and dual-number substitutions. The copying point calculation uses the
trivial-idempotent case of Theorem 4.3.
-/

open AlgebraicGeometry CategoryTheory SHIGURE.Copying TensorProduct
open scoped BigOperators TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

/-- A dual number over a field is idempotent only when it equals zero or one. -/
theorem dualNumber_idempotent {k : Type u} [Field k] (z : DualNumber k)
    (hz : IsIdempotentElem z) : z = 0 ∨ z = 1 := by
  have hf : IsIdempotentElem z.fst := congrArg TrivSqZeroExt.fst hz
  have hs : z.fst * z.snd + z.snd * z.fst = z.snd := by
    simpa only [DualNumber.snd_mul] using congrArg TrivSqZeroExt.snd hz
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hf with h | h
  · have hzero : z.snd = 0 := by simpa [h, eq_comm] using hs
    exact Or.inl (TrivSqZeroExt.ext h hzero)
  · have hzero : z.snd = 0 := by
      have hh : z.snd + z.snd = z.snd + 0 := by simpa [h] using hs
      exact add_left_cancel hh
    exact Or.inr (TrivSqZeroExt.ext h hzero)

/-- The infinitesimal of the dual-number algebra is nonzero over a field. -/
theorem dualNumber_epsilon_ne_zero {k : Type u} [Field k] :
    (DualNumber.eps : DualNumber k) ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg TrivSqZeroExt.snd h : (1 : k) = 0)

/-- The infinitesimal state belongs to the tensor realization and lies outside the
image of the scalar comparison from the copying realization. -/
theorem dualNumber_epsilon_not_copying {k : Type u} [Field k] :
    (DualNumber.eps : DualNumber k) ∉ Set.range
      (compareScalarPoint : (CopyScheme (DualNumber k) PUnit ⟶ CopyScheme (DualNumber k) k) → DualNumber k) := by
  rintro ⟨x, hx⟩
  let e := stateSchemeMapsEquiv (R := DualNumber k) (X := PUnit) (Y := k) dualNumber_idempotent
  let a := e.symm x
  have ha : mapStateSchemes (Spec (CommRingCat.of (DualNumber k))) a = x := by
    rw [← copyingHomEquiv_mapStates]
    exact e.apply_symm_apply x
  have hε : algebraMap k (DualNumber k) (a PUnit.unit) = DualNumber.eps := by
    rw [← hx, ← ha]
    exact (compareScalarPoint_constant (a PUnit.unit)).symm
  have hz : (0 : k) = 1 := congrArg TrivSqZeroExt.snd hε
  exact zero_ne_one hz

variable (p : ℕ)

/-- The Frobenius equation holds at every native state of the prime field. -/
theorem zmod_frobenius [Fact p.Prime] (a : ZMod p) : a ^ p = a := ZMod.pow_card a

/-- Substituting the polynomial indeterminate into the Frobenius equation fails. -/
theorem polynomial_frobenius_fails [Fact p.Prime] :
    (Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X ≠ 0 :=
  FiniteField.X_pow_card_sub_X_ne_zero _ (Fact.out : Nat.Prime p).one_lt

/-- The nonzero square-zero direction also violates the Frobenius equation. -/
theorem dualNumber_frobenius_fails [Fact p.Prime] :
    (DualNumber.eps : DualNumber (ZMod p)) ^ p ≠ DualNumber.eps := by
  have h : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h
  have he : (DualNumber.eps : DualNumber (ZMod p)) ^ p = 0 := calc
    _ = (DualNumber.eps : DualNumber (ZMod p)) ^ (2 + n) :=
      congrArg (fun j : ℕ => (DualNumber.eps : DualNumber (ZMod p)) ^ j) hn
    _ = 0 := by rw [pow_add, pow_two, DualNumber.eps_mul_eps, zero_mul]
  rw [he]
  exact Ne.symm dualNumber_epsilon_ne_zero

/-- The relative affine points give the same exclusion for the comparison of Theorem 4.9. -/
theorem dualNumber_epsilon_not_relativeCopying {k : Type u} [Field k] :
    (DualNumber.eps : DualNumber k) ∉ Set.range
      (compareRelativeScalarPoint : (specOver (k := k) (DualNumber k) ⟶ CopyScheme k k) → DualNumber k) := by
  rintro ⟨x, hx⟩
  exact dualNumber_epsilon_not_copying ⟨relativeCopyingPointEquiv (algebraMap k (DualNumber k)) k x, hx⟩

/-- The scalar ring signature with a nullary unit and a binary product. -/
def scalarRingSignature : Signature.{0} where
  SortType := Unit
  Total := Bool
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity
    | false => ⟨[], ()⟩
    | true => ⟨[(), ()], ()⟩
  relInputs x := nomatch x
  partialArity x := nomatch x
  quantityArity x := nomatch x

/-- Interpret a finite product as a multilinear map of scalar modules. -/
private def scalarProduct (K : Type) [CommRing K] (Γ : List Unit) :
    TensorOperation K (fun _ => ModuleCat.of K K) ⟨Γ, ()⟩ :=
  letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
  MultilinearMap.mkPiRing K (TensorPosition Γ) (1 : K)

/-- The scalar carriers with their native unit and multiplication. -/
def scalarRingStructure (K : Type) [CommRing K] : TensorStructure K scalarRingSignature where
  carrier _ := ModuleCat.of K K
  total
    | false => scalarProduct K []
    | true => scalarProduct K [(), ()]
  quantity x := nomatch x

/-- Read the two distinct positions of the binary operation. -/
private def scalarPair {X : Type} (a b : X) : TensorPosition [(), ()] → X
  | ⟨_, .here⟩ => a
  | ⟨_, .there .here⟩ => b

/-- The product over the two typed argument positions is their ordinary binary product. -/
private theorem scalarPair_prod {K : Type} [CommRing K] (a b : K) :
    letI : Fintype (TensorPosition [(), ()]) := Fintype.ofFinite _
    ∏ i, scalarPair a b i = a * b := by
  classical
  letI : Fintype (TensorPosition [(), ()]) := Fintype.ofFinite _
  let i : TensorPosition [(), ()] := ⟨(), .here⟩
  let j : TensorPosition [(), ()] := ⟨(), .there .here⟩
  have h : (Finset.univ : Finset (TensorPosition [(), ()])) = {i, j} := by
    ext z
    rcases z with ⟨_, _ | _ | z⟩
    · exact ⟨fun _ => Finset.mem_insert_self _ _, fun _ => Finset.mem_univ _⟩
    · exact ⟨fun _ => Finset.mem_insert_of_mem (Finset.mem_singleton_self _), fun _ => Finset.mem_univ _⟩
    · exact nomatch z
  have hij : i ∉ ({j} : Finset (TensorPosition [(), ()])) := by
    intro hm
    have he := congrArg (scalarPair false true) (Finset.mem_singleton.mp hm)
    cases he
  rw [h, Finset.prod_insert hij, Finset.prod_singleton]
  rfl

/-- Put distinct typed subterms into the two argument positions of multiplication. -/
private def scalarProductTerms (a b : TensorTerm scalarRingSignature [()] ()) :
    (i : TensorPosition [(), ()]) → TensorTerm scalarRingSignature [()] i.1
  | ⟨_, .here⟩ => a
  | ⟨_, .there .here⟩ => b

/-- A finite term uses the one typed variable as often as the exponent requires. -/
def scalarPowerTerm : ℕ → TensorTerm scalarRingSignature [()] ()
  | 0 => TensorTerm.total (sig := scalarRingSignature) (false : Bool)
      (fun i : TensorPosition ([] : List Unit) => nomatch i.2)
  | n + 1 => TensorTerm.total (sig := scalarRingSignature) (true : Bool)
      (scalarProductTerms (scalarPowerTerm n) (.var .here))

/-- The evaluated native product is the actual product of its scalar arguments. -/
private theorem scalarProduct_apply (K : Type) [CommRing K] (Γ : List Unit)
    (x : TensorPosition Γ → K) : scalarProduct K Γ x =
      letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
      ∏ i, x i := by
  letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
  change (MultilinearMap.mkPiRing K (TensorPosition Γ) (1 : K)) x = ∏ i, x i
  rw [MultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one]

/-- The precise native interpretation of the typed power term. -/
theorem scalarPowerTerm_eval {K : Type} [CommRing K] (n : ℕ) (x : K) :
    (scalarPowerTerm n).eval (scalarRingStructure K) (fun _ => x) = x ^ n := by
  induction n with
  | zero =>
    letI : IsEmpty (TensorPosition ([] : List Unit)) := ⟨fun i => nomatch i.2⟩
    rw [scalarPowerTerm, TensorTerm.eval]
    change scalarProduct K [] _ = x ^ 0
    rw [scalarProduct_apply, Finset.prod_of_isEmpty, pow_zero]
  | succ n ih =>
    have h : (fun i : TensorPosition [(), ()] =>
        (scalarProductTerms (scalarPowerTerm n) (.var .here) i).eval (scalarRingStructure K) (fun _ => x)) =
        scalarPair (x ^ n) x := by
      funext i
      rcases i with ⟨_, _ | _ | i⟩
      · exact ih
      · rfl
      · exact nomatch i
    change scalarProduct K [(), ()] (fun i =>
      (scalarProductTerms (scalarPowerTerm n) (.var .here) i).eval (scalarRingStructure K) (fun _ => x)) = _
    rw [h, scalarProduct_apply, scalarPair_prod, pow_succ]

variable {K R : Type} [CommRing K] [CommRing R] [Algebra K R]

/-- Equation (4.3) extends the scalar product by multiplying the new coefficients. -/
private theorem scalarProduct_extended (Γ : List Unit) (r : TensorPosition Γ → R) :
    extendOperation K (fun _ : Unit => ModuleCat.of K K) R (N := ModuleCat.of K K)
      (scalarProduct K Γ) (fun i => r i ⊗ₜ[K] (1 : K)) =
        letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
        (∏ i, r i) ⊗ₜ[K] (1 : K) := by
  letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
  rw [extendOperation_tprod]
  have h : scalarProduct K Γ (fun _ => (1 : K)) = 1 :=
    (scalarProduct_apply K Γ (fun _ => (1 : K))).trans Finset.prod_const_one
  exact congrArg (fun a : K => (∏ i, r i) ⊗ₜ[K] a) h

/-- Scalar extension interprets the same term as the ordinary power in every coefficient ring. -/
theorem scalarPowerTerm_eval_extended (n : ℕ) (x : R) :
    (scalarPowerTerm n).eval (extendStructure K R (scalarRingStructure K))
      (fun _ => x ⊗ₜ[K] (1 : K)) = (x ^ n) ⊗ₜ[K] (1 : K) := by
  induction n with
  | zero =>
    letI : IsEmpty (TensorPosition ([] : List Unit)) := ⟨fun i => nomatch i.2⟩
    rw [scalarPowerTerm, TensorTerm.eval]
    change extendOperation K (fun _ : Unit => ModuleCat.of K K) R (N := ModuleCat.of K K)
      (scalarProduct K []) _ = _
    let r (i : TensorPosition ([] : List Unit)) : R := nomatch i.2
    have h := scalarProduct_extended (K := K) ([] : List Unit) r
    rw [Finset.prod_of_isEmpty] at h
    rw [pow_zero, ← h]
    congr 1
    funext i
    exact nomatch i.2
  | succ n ih =>
    have h : (fun i : TensorPosition [(), ()] =>
        (scalarProductTerms (scalarPowerTerm n) (.var .here) i).eval (extendStructure K R (scalarRingStructure K))
          (fun _ => x ⊗ₜ[K] (1 : K))) =
        fun i => scalarPair (x ^ n) x i ⊗ₜ[K] (1 : K) := by
      funext i
      rcases i with ⟨_, _ | _ | i⟩
      · exact ih
      · rfl
      · exact nomatch i
    change extendOperation K (fun _ : Unit => ModuleCat.of K K) R (N := ModuleCat.of K K)
      (scalarProduct K [(), ()]) (fun i =>
        (scalarProductTerms (scalarPowerTerm n) (.var .here) i).eval (extendStructure K R (scalarRingStructure K))
          (fun _ => x ⊗ₜ[K] (1 : K))) = _
    rw [h, scalarProduct_extended, scalarPair_prod, pow_succ]

/-- The written Frobenius term agrees with the input variable at every prime-field state. -/
theorem frobenius_term_native [Fact p.Prime] (x : ZMod p) :
    (scalarPowerTerm p).eval (scalarRingStructure (ZMod p)) (fun _ => x) =
      (TensorTerm.var Var.here : TensorTerm scalarRingSignature [()] ()).eval
        (scalarRingStructure (ZMod p)) (fun _ => x) :=
  (scalarPowerTerm_eval p x).trans (zmod_frobenius p x)

/-- A ring state violating the scalar equation also violates the extended equation of terms. -/
theorem frobenius_term_extended_ne [Algebra (ZMod p) R] (x : R) (h : x ^ p ≠ x) :
    (scalarPowerTerm p).eval (extendStructure (ZMod p) R (scalarRingStructure (ZMod p)))
      (fun _ => x ⊗ₜ[ZMod p] (1 : ZMod p)) ≠
    (TensorTerm.var Var.here : TensorTerm scalarRingSignature [()] ()).eval
      (extendStructure (ZMod p) R (scalarRingStructure (ZMod p)))
      (fun _ => x ⊗ₜ[ZMod p] (1 : ZMod p)) := by
  intro he
  rw [scalarPowerTerm_eval_extended] at he
  change (x ^ p) ⊗ₜ[ZMod p] (1 : ZMod p) = x ⊗ₜ[ZMod p] (1 : ZMod p) at he
  have hs := congrArg (extendScalarSort (k := ZMod p) R) he
  exact h (by simpa only [extendScalarSort_tmul, one_smul] using hs)

/-- In the polynomial algebra the extended Frobenius term disagrees with the variable at the indeterminate. -/
theorem frobenius_term_polynomial [Fact p.Prime] :
    (scalarPowerTerm p).eval (extendStructure (ZMod p) (Polynomial (ZMod p)) (scalarRingStructure (ZMod p)))
      (fun _ => Polynomial.X ⊗ₜ[ZMod p] (1 : ZMod p)) ≠
    (TensorTerm.var Var.here : TensorTerm scalarRingSignature [()] ()).eval
      (extendStructure (ZMod p) (Polynomial (ZMod p)) (scalarRingStructure (ZMod p)))
      (fun _ => Polynomial.X ⊗ₜ[ZMod p] (1 : ZMod p)) :=
  frobenius_term_extended_ne p Polynomial.X (sub_ne_zero.mp (polynomial_frobenius_fails p))

/-- The dual-number direction also violates the extended equation of written terms. -/
theorem frobenius_term_dualNumber [Fact p.Prime] :
    (scalarPowerTerm p).eval (extendStructure (ZMod p) (DualNumber (ZMod p)) (scalarRingStructure (ZMod p)))
      (fun _ => DualNumber.eps ⊗ₜ[ZMod p] (1 : ZMod p)) ≠
    (TensorTerm.var Var.here : TensorTerm scalarRingSignature [()] ()).eval
      (extendStructure (ZMod p) (DualNumber (ZMod p)) (scalarRingStructure (ZMod p)))
      (fun _ => DualNumber.eps ⊗ₜ[ZMod p] (1 : ZMod p)) :=
  frobenius_term_extended_ne p DualNumber.eps (dualNumber_frobenius_fails p)

/-- The single native summand equal to one gives a nonzero residual in equation (4.5). -/
theorem frobenius_formal_residual_ne [Fact p.Prime] :
    let A := scalarRingStructure (ZMod p)
    let n : TensorPosition ([()] : List Unit) → ℕ := fun _ => 1
    let P := MvPolynomial ((i : TensorPosition ([()] : List Unit)) × Fin (n i)) (ZMod p)
    let t : TensorTerm scalarRingSignature [()] () := .var .here
    let z := formalInput A n (fun _ _ => (1 : ZMod p))
    (scalarPowerTerm p).eval (extendStructure (ZMod p) P A) z -
      t.eval (extendStructure (ZMod p) P A) z ≠ 0 := by
  intro A n P t z h
  let f : P →ₐ[ZMod p] Polynomial (ZMod p) := MvPolynomial.aeval (fun _ => Polynomial.X)
  let y (i : TensorPosition ([()] : List Unit)) :
      (extendStructure (ZMod p) (Polynomial (ZMod p)) A).carrier i.1 :=
    Polynomial.X ⊗ₜ[ZMod p] (1 : ZMod p)
  have hz : (fun i => mapCoefficients f (z i)) = y := by
    funext i
    change mapCoefficients f
      (∑ j : Fin 1, MvPolynomial.X ⟨i, j⟩ ⊗ₜ[ZMod p] (1 : ZMod p)) = y i
    rw [Fin.sum_univ_one, mapCoefficients_tmul]
    let v : (j : TensorPosition ([()] : List Unit)) × Fin (n j) := ⟨i, 0⟩
    have hv : f (MvPolynomial.X v) = (Polynomial.X : Polynomial (ZMod p)) :=
      MvPolynomial.aeval_X (R := ZMod p) (fun _ => (Polynomial.X : Polynomial (ZMod p))) v
    exact congrArg (fun a : Polynomial (ZMod p) => a ⊗ₜ[ZMod p] (1 : ZMod p)) hv
  have he := congrArg (mapCoefficients f) (sub_eq_zero.mp h)
  rw [(scalarPowerTerm p).eval_mapCoefficients f A z, t.eval_mapCoefficients f A z, hz] at he
  exact frobenius_term_polynomial p he

end SHIGURE.TensorRealization
