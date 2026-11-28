import Formal.SHIGURE.Part2.Families.AffineRealizations
import Mathlib.Tactic.NormNum

/-! # A rank-one affine realization and its arrows -/

open CategoryTheory SHIGURE.TensorRealization SHIGURE.CoefficientDescent
open scoped TensorProduct

noncomputable section

namespace SHIGURE.RealizationFamilies.Examples

/-- A single sort and no primitive operations. -/
def lineSignature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity := Empty.elim
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

/-- The empty Law families. -/
def lineLaws : AffineLawPresentation ℤ lineSignature where
  tensorIndex := Empty
  tensorLaw := Empty.elim
  polynomialIndex := Empty
  inputs := Empty.elim
  output := Empty.elim
  polynomialLaw i := nomatch i

def lineStructure : TensorStructure ℤ lineSignature where
  carrier _ := ModuleCat.of ℤ ℤ
  total p := nomatch p
  quantity q := nomatch q

/-- The free rank-one integer line is an affine realization. -/
def integerLine : AffineRealization lineLaws (fun _ => 1) (RingHom.id ℤ) :=
  ⟨lineStructure, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s
      change FiniteLocallyFree ℤ ℤ
      exact finiteLocallyFree_iff_finite_projective.mpr ⟨inferInstance, inferInstance⟩
    · intro s p
      change Module.rankAtStalk (R := ℤ) ℤ p = 1
      simp only [Module.rankAtStalk_self, Pi.one_apply]
    · intro i
      change Empty at i
      exact nomatch i
    · intro i
      change Empty at i
      exact nomatch i⟩

/-- The same integer line does not satisfy the rank-zero realization property:
its stalk at the zero prime has rank one. -/
theorem integerLine_not_rank_zero :
    ¬ affineProperty lineLaws (fun _ => 0) (RingHom.id ℤ) lineStructure := by
  intro h
  obtain ⟨_, ranks, _, _⟩ := h
  let p : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩
  have rankZero := ranks () p
  change Module.rankAtStalk (R := ℤ) ℤ p = 0 at rankZero
  have rankOne : Module.rankAtStalk (R := ℤ) ℤ p = 1 := by
    simp only [Module.rankAtStalk_self, Pi.one_apply]
  exact (by decide : (1 : ℕ) ≠ 0) (rankOne.symm.trans rankZero)

private def negateLineMap : lineStructure ⟶ lineStructure where
  onSort _ := (LinearEquiv.neg ℤ).toLinearMap
  preservesTotal p := nomatch p
  preservesQuantity q := nomatch q

/-- Negation defines a structured automorphism of the integer line. -/
def negateLine : integerLine ≅ integerLine :=
  ObjectProperty.isoMk _ (structureIsoOfCarrierEquiv negateLineMap
    (fun _ => LinearEquiv.neg ℤ) (fun _ => rfl))

/-- This automorphism is distinct from the identity. -/
theorem negateLine_ne_id : negateLine.hom ≠ 𝟙 integerLine := by
  intro h
  have value := congrArg (fun f : integerLine ⟶ integerLine => f.hom.onSort () (1 : ℤ)) h
  change -(1 : ℤ) = 1 at value
  exact (by decide : (-1 : ℤ) ≠ 1) value

/-- The zero map preserves all the operations of the line. -/
def zeroLine : integerLine ⟶ integerLine := ObjectProperty.homMk
  { onSort := fun _ => 0
    preservesTotal := fun p => nomatch p
    preservesQuantity := fun q => nomatch q }

/-- The zero structure-preserving arrow is not an isomorphism. -/
theorem zeroLine_not_isIso : ¬ IsIso zeroLine := by
  intro h
  letI : IsIso zeroLine := h
  have value := congrArg (fun f : integerLine ⟶ integerLine => f.hom.onSort () (1 : ℤ))
    (IsIso.hom_inv_id zeroLine)
  change (inv zeroLine).hom.onSort () 0 = (1 : ℤ) at value
  rw [map_zero] at value
  exact (by decide : (0 : ℤ) ≠ 1) value

/-- Negation remains an isomorphism after every coefficient extension. -/
def changedNegateLine (S : Type) [CommRing S] [Algebra ℤ S] :
    (affineBaseChange (S := S) lineLaws (fun _ => 1) (RingHom.id ℤ)).obj integerLine ≅
      (affineBaseChange (S := S) lineLaws (fun _ => 1) (RingHom.id ℤ)).obj integerLine :=
  (affineBaseChange (S := S) lineLaws (fun _ => 1) (RingHom.id ℤ)).mapIso negateLine

/-- Coefficient extension sends the zero arrow to the zero map on its carrier. -/
theorem changedZeroLine_onSort (S : Type) [CommRing S] [Algebra ℤ S] :
    ((affineBaseChange (S := S) lineLaws (fun _ => 1) (RingHom.id ℤ)).map zeroLine).hom.onSort () = 0 := by
  change (0 : ℤ →ₗ[ℤ] ℤ).baseChange S = 0
  exact LinearMap.baseChange_zero

/-- Over the rationals, the changed negation still differs from the identity. -/
theorem changedNegateLine_rational_ne_id :
    (changedNegateLine ℚ).hom ≠
      𝟙 ((affineBaseChange (S := ℚ) lineLaws (fun _ => 1) (RingHom.id ℤ)).obj integerLine) := by
  intro h
  let F := affineBaseChange (S := ℚ) lineLaws (fun _ => 1) (RingHom.id ℤ)
  let e := extendScalarSort (k := ℤ) ℚ
  let x : ℚ ⊗[ℤ] ℤ := (1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)
  have value := congrArg (fun f : F.obj integerLine ⟶ F.obj integerLine =>
    e (f.hom.onSort () x)) h
  change e (((LinearEquiv.neg ℤ).toLinearMap.baseChange ℚ) x) = e x at value
  have tensorEq := e.injective value
  change ((LinearEquiv.neg ℤ).toLinearMap.baseChange ℚ) ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)) =
    (1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ) at tensorEq
  rw [LinearMap.baseChange_tmul] at tensorEq
  change ((1 : ℚ) ⊗ₜ[ℤ] (-1 : ℤ)) = (1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ) at tensorEq
  have scalarEq := congrArg (extendScalarSort (k := ℤ) ℚ) tensorEq
  rw [extendScalarSort_tmul, extendScalarSort_tmul] at scalarEq
  norm_num at scalarEq

/-- The changed zero map is still noninvertible over the rationals. -/
theorem changedZeroLine_rational_not_isIso :
    ¬ IsIso ((affineBaseChange (S := ℚ) lineLaws (fun _ => 1) (RingHom.id ℤ)).map zeroLine) := by
  let F := affineBaseChange (S := ℚ) lineLaws (fun _ => 1) (RingHom.id ℤ)
  intro h
  letI : IsIso (F.map zeroLine) := h
  let e := extendScalarSort (k := ℤ) ℚ
  let x : ℚ ⊗[ℤ] ℤ := (1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)
  have value := congrArg (fun f : F.obj integerLine ⟶ F.obj integerLine =>
    e (f.hom.onSort () x)) (IsIso.hom_inv_id (F.map zeroLine))
  change e ((inv (F.map zeroLine)).hom.onSort () ((F.map zeroLine).hom.onSort () x)) = e x at value
  have zeroValue : (F.map zeroLine).hom.onSort () x = 0 := by
    change (0 : ℤ →ₗ[ℤ] ℤ).baseChange ℚ x = 0
    simp only [LinearMap.baseChange_zero, LinearMap.zero_apply]
  have tensorEq := e.injective value
  rw [zeroValue, map_zero] at tensorEq
  have scalarEq := congrArg (extendScalarSort (k := ℤ) ℚ) tensorEq
  change (extendScalarSort (k := ℤ) ℚ) 0 =
    (extendScalarSort (k := ℤ) ℚ) ((1 : ℚ) ⊗ₜ[ℤ] (1 : ℤ)) at scalarEq
  rw [map_zero, extendScalarSort_tmul, one_smul] at scalarEq
  exact (by norm_num : (0 : ℚ) ≠ 1) scalarEq

end SHIGURE.RealizationFamilies.Examples
