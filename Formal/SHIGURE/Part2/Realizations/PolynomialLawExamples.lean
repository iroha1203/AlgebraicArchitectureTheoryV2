import Formal.SHIGURE.Part2.Realizations.PolynomialTerms
import Formal.SHIGURE.Part2.Tensor.FrobeniusExample

/-! # Written polynomial Laws tested over the two-element field -/

namespace SHIGURE.RealizationFamilies.Examples

open SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

private abbrev k := ZMod 2

private abbrev variableTerm : PolynomialTerm k scalarRingSignature [()] () := .var .here

/-- Supply the two terms for the two input positions of multiplication. -/
private def pairTerms (a b : PolynomialTerm k scalarRingSignature [()] ()) :
    (i : TensorPosition [(), ()]) → PolynomialTerm k scalarRingSignature [()] i.1
  | ⟨_, .here⟩ => a
  | ⟨_, .there .here⟩ => b

/-- Write a power using the designated unit and repeated multiplication. -/
private def polynomialPower : ℕ → PolynomialTerm k scalarRingSignature [()] ()
  | 0 => PolynomialTerm.total (sig := scalarRingSignature) (false : Bool)
      (fun i : TensorPosition ([] : List Unit) => nomatch i.2)
  | n + 1 => PolynomialTerm.total (sig := scalarRingSignature) (true : Bool)
      (pairTerms (polynomialPower n) variableTerm)

/-- The written power has the same evaluation as the existing tensor power term. -/
private theorem polynomialPower_eval {R : Type} [CommRing R] (c : k →+* R)
    (A : TensorStructure R scalarRingSignature) (x : ∀ i : TensorPosition ([()] : List Unit), A.carrier i.1)
    (n : ℕ) :
    (polynomialPower n).eval c A x = (scalarPowerTerm n).eval A x := by
  induction n with
  | zero =>
    dsimp only [polynomialPower, scalarPowerTerm, PolynomialTerm.eval, TensorTerm.eval]
    apply congrArg (A.total false)
    funext i
    exact nomatch i.2
  | succ n ih =>
    dsimp only [polynomialPower, scalarPowerTerm, PolynomialTerm.eval, TensorTerm.eval]
    apply congrArg (A.total true)
    funext i
    rcases i with ⟨_, _ | _ | i⟩
    · exact ih
    · rfl
    · exact nomatch i

/-- The written equation adding the same variable twice. -/
private def twoCopiesLaw : PolynomialLaw k scalarRingSignature [()] () :=
  ⟨.add variableTerm variableTerm,
    PolynomialTerm.zero (sig := scalarRingSignature) (Γ := [()]) ()⟩

/-- The written equation equating the square with the original variable. -/
private def frobeniusLaw : PolynomialLaw k scalarRingSignature [()] () :=
  ⟨polynomialPower 2, variableTerm⟩

/-- Two copies of an input sum to zero after every extension of the
two-element field, on the actual rank-one realization. -/
theorem twoCopiesLaw_holds :
    twoCopiesLaw.Holds (RingHom.id k) (scalarRingStructure k) := by
  intro S _ _ x
  let v := x ⟨(), .here⟩
  have two : (1 : S) + 1 = 0 := by
    have value : (1 : k) + 1 = 0 := by decide
    simpa only [map_add, map_one, map_zero] using congrArg (algebraMap k S) value
  change v + v = 0
  calc
    _ = ((1 : S) + 1) • v := by simp only [add_smul, one_smul]
    _ = 0 := by rw [two, zero_smul]

/-- The written Frobenius Law holds at every original field point. -/
theorem frobeniusLaw_originalPoints (x : k) :
    frobeniusLaw.left.eval (RingHom.id k) (scalarRingStructure k) (fun _ => x) =
      frobeniusLaw.right.eval (RingHom.id k) (scalarRingStructure k) (fun _ => x) :=
  (polynomialPower_eval _ _ _ 2).trans (frobenius_term_native 2 x)

/-- The same written Law fails over the polynomial test algebra, although it
holds at every original point of the two-element field. -/
theorem frobeniusLaw_not_holds :
    ¬ frobeniusLaw.Holds (RingHom.id k) (scalarRingStructure k) := by
  intro h
  let S := Polynomial k
  let x (i : TensorPosition ([()] : List Unit)) :
      (extendStructure k S (scalarRingStructure k)).carrier i.1 :=
    (Polynomial.X : S) ⊗ₜ[k] (1 : k)
  have value := h S x
  change (polynomialPower 2).eval _ _ x = _ at value
  rw [polynomialPower_eval] at value
  exact frobenius_term_polynomial 2 value

end

end SHIGURE.RealizationFamilies.Examples
