import Formal.SHIGURE.Part1.CoordinateRings
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Adding an inverse variable

Example 3.12 uses the inclusion of the declaration of x into the presentation
with x, y and the Law xy = 1. Its coordinate map is the localization map at x.
A reverse map that preserves the shared generator x would make x invertible
in the polynomial ring itself.

## Implementation notes

The option name type distinguishes the retained variable from the added
inverse. The nested polynomial representation identifies the retained
variable in the coefficients and the new variable as the outer generator.
This connects their quotient to AdjoinRoot and to the mathlib localization
equivalence. A direct presentation by fractions would require uniqueness
proofs for two separately constructed homomorphisms.
-/

namespace SHIGURE.PolynomialPresentation.InverseVariableExample

open MvPolynomial

noncomputable section

/-- The presentation with just the shared variable x. -/
def small : PolynomialPresentation.{0,0} ℚ where
  Variable := PUnit
  Law := PEmpty
  left := PEmpty.elim
  right := PEmpty.elim

/-- The enlarged presentation, with y at the new name and the Law xy = 1. -/
def large : PolynomialPresentation.{0,0} ℚ where
  Variable := Option PUnit
  Law := PUnit
  left _ := X (some PUnit.unit) * X none
  right _ := 1

/-- The small presentation has no Law relations. -/
theorem small_lawIdeal : small.lawIdeal = ⊥ := by
  letI : IsEmpty small.Law := inferInstanceAs (IsEmpty (PEmpty : Type))
  exact small.lawIdeal_eq_bot_of_isEmpty

/-- The large presentation cuts out precisely the relation xy - 1. -/
theorem large_lawIdeal : large.lawIdeal = Ideal.span
    {X (some PUnit.unit) * X none - (1 : MvPolynomial large.Variable ℚ)} := by
  letI : Subsingleton large.Law := inferInstanceAs (Subsingleton (PUnit : Type))
  exact large.lawIdeal_eq_span_singleton PUnit.unit

/-- The two variables equal to one satisfy the inverse Law. -/
def assignmentAtOne : large.Assignment ℚ where
  value _ := 1
  holds _ := by
    change aeval (fun _ : large.Variable => (1 : ℚ)) (X (some PUnit.unit) * X none) =
      aeval (fun _ : large.Variable => (1 : ℚ)) 1
    simp

/-- Assigning zero to the retained variable is incompatible with the inverse Law. -/
theorem no_assignment_at_x_zero :
    ¬ ∃ a : large.Assignment ℚ, a.value (some PUnit.unit) = 0 := by
  rintro ⟨a, xZero⟩
  have holds := a.holds PUnit.unit
  change aeval a.value (X (some PUnit.unit) * X none) = aeval a.value 1 at holds
  simp [xZero] at holds

/-- Keep both variable names with an empty family of Laws. -/
def freeTwoVariables : PolynomialPresentation.{0,0} ℚ where
  Variable := Option PUnit
  Law := PEmpty
  left := PEmpty.elim
  right := PEmpty.elim

/-- The two presentations have the same variable names. -/
def sameNames : large.Variable ↪ freeTwoVariables.Variable :=
  Function.Embedding.refl _

/-- The identical variable embedding fails to preserve the inverse Law ideal. -/
theorem sameNames_not_preserving :
    ¬ large.lawIdeal ≤ freeTwoVariables.lawIdeal.comap (rename sameNames) := by
  intro preserves
  let inclusion : large.Inclusion freeTwoVariables := ⟨sameNames, preserves⟩
  let zero : freeTwoVariables.Assignment ℚ := ⟨fun _ => 0, fun law => PEmpty.elim law⟩
  exact no_assignment_at_x_zero ⟨inclusion.forget zero, rfl⟩

/-- The inclusion preserves the name x and sends the zero Law ideal into the enlarged one. -/
def inclusion : small.Inclusion large where
  names := ⟨some, Option.some_injective _⟩
  preserves := by rw [small_lawIdeal]; exact bot_le

/-- The polynomial ring of the shared variable x. -/
abbrev LeftRing := Polynomial ℚ

/-- The small coordinate ring is the ordinary univariate polynomial ring. -/
def univariate : small.CoordinateRing ≃ₐ[ℚ] LeftRing :=
  (Ideal.quotientEquivAlg small.lawIdeal ⊥ (AlgEquiv.refl : MvPolynomial small.Variable ℚ ≃ₐ[ℚ] _)
    (by rw [small_lawIdeal, Ideal.map_bot])).trans
    ((AlgEquiv.quotientBot ℚ _).trans (MvPolynomial.pUnitAlgEquiv ℚ))

/-- Under the univariate identification the named generator is the polynomial X. -/
theorem univariate_generator : univariate (small.generator PUnit.unit) = Polynomial.X := by
  rw [generator_eq_quotient_mk]
  simp only [univariate, AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk,
    AlgEquiv.quotientBot_mk]
  change MvPolynomial.pUnitAlgEquiv ℚ (X (PUnit.unit : PUnit)) = Polynomial.X
  simp [MvPolynomial.pUnitAlgEquiv_apply]

/-- The class of x in the large Law quotient. -/
def barX : large.CoordinateRing := large.generator (some PUnit.unit)

/-- The class of y in the large Law quotient. -/
def barY : large.CoordinateRing := large.generator none

/-- Equation (3.9) uses the coordinate map induced by the same variable inclusion as in (3.8). -/
def declarationMap : LeftRing →ₐ[ℚ] large.CoordinateRing :=
  inclusion.coordinateMap.comp univariate.symm.toAlgHom

/-- Adding the inverse variable sends x to the shared generator in the larger quotient. -/
theorem declarationMap_X : declarationMap Polynomial.X = barX := by
  have h : univariate.symm Polynomial.X = small.generator PUnit.unit :=
    univariate.symm_apply_eq.mpr univariate_generator.symm
  change inclusion.coordinateMap (univariate.symm Polynomial.X) = _
  rw [h, Inclusion.coordinateMap_generator]
  rfl

/-- The images of the two variables multiply to one in the quotient. -/
theorem barX_mul_barY : barX * barY = 1 := by
  have rel : X (some PUnit.unit) * X none - 1 ∈ large.lawIdeal :=
    large.law_sub_mem PUnit.unit
  have zero : Ideal.Quotient.mk large.lawIdeal (X (some PUnit.unit) * X none - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr rel
  rw [map_sub, map_mul, map_one, sub_eq_zero] at zero
  simpa only [barX, barY, generator_eq_quotient_mk] using zero

/-- There is no reverse algebra map keeping the shared x. Evaluate a putative inverse relation at zero. -/
theorem no_reverse_preserving_X :
    ¬ ∃ f : large.CoordinateRing →ₐ[ℚ] LeftRing, f barX = Polynomial.X := by
  rintro ⟨f, keepsX⟩
  have relation := congrArg f barX_mul_barY
  rw [map_mul, map_one, keepsX] at relation
  have zero := congrArg (Polynomial.evalRingHom (0 : ℚ)) relation
  simp at zero

/-- Identify the shared variable in the coefficient ring and the inverse as the outer polynomial variable. -/
private def bivariate : MvPolynomial (Option PUnit.{1}) ℚ ≃ₐ[ℚ] Polynomial LeftRing :=
  (MvPolynomial.optionEquivLeft ℚ PUnit).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.pUnitAlgEquiv ℚ))

/-- Identify the shared variable as the constant polynomial with coefficient X. -/
private theorem bivariate_x :
    bivariate (X (some PUnit.unit)) = Polynomial.C (Polynomial.X : LeftRing) := by
  simp [bivariate, MvPolynomial.pUnitAlgEquiv_apply]

/-- Identify the inverse variable with the outer polynomial generator. -/
private theorem bivariate_y : bivariate (X none) = Polynomial.X := by
  simp [bivariate]

/-- Write the relation xy − 1 in the nested polynomial ring. -/
private abbrev inversionLaw : Polynomial LeftRing :=
  Polynomial.C (Polynomial.X : LeftRing) * Polynomial.X - 1

/-- Transport the generated inverse Law ideal along the bivariate equivalence. -/
private theorem mappedIdeal : Ideal.span {inversionLaw} = large.lawIdeal.map bivariate.toRingHom := by
  rw [large_lawIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {inversionLaw} =
    Ideal.span {bivariate (X (some PUnit.unit) * X none - 1)}
  rw [map_sub, map_mul, map_one, bivariate_x, bivariate_y]

/-- Pass the polynomial equivalence through the two equal Law ideals. -/
private def quotientEquiv : large.CoordinateRing ≃ₐ[ℚ] AdjoinRoot inversionLaw :=
  Ideal.quotientEquivAlg _ _ bivariate mappedIdeal

/-- The bivariate equivalence descends by taking the quotient class of its polynomial image. -/
private theorem quotientEquiv_mk (p : MvPolynomial large.Variable ℚ) :
    quotientEquiv (Ideal.Quotient.mk large.lawIdeal p) = AdjoinRoot.mk inversionLaw (bivariate p) :=
  rfl

/-- The exact coordinate ring of the large presentation is the localization away from x. -/
def localization : large.CoordinateRing ≃ₐ[ℚ] Localization.Away (Polynomial.X : LeftRing) :=
  quotientEquiv.trans ((Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm.restrictScalars ℚ)

/-- The localization identification preserves the shared generator x. -/
theorem localization_barX :
    localization barX = algebraMap LeftRing (Localization.Away (Polynomial.X : LeftRing)) Polynomial.X := by
  change (Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm
    (quotientEquiv (large.generator (some PUnit.unit))) = _
  rw [generator_eq_quotient_mk, quotientEquiv_mk, bivariate_x]
  exact (Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm.commutes _

/-- The localization identification sends the new generator y to the inverse of x. -/
theorem localization_barY :
    localization barY = IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : LeftRing))
      (Polynomial.X : LeftRing) := by
  change (Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm
    (quotientEquiv (large.generator none)) = _
  rw [generator_eq_quotient_mk, quotientEquiv_mk, bivariate_y]
  let L := Localization.Away (Polynomial.X : LeftRing)
  let inverse := IsLocalization.Away.invSelf (S := L) (Polynomial.X : LeftRing)
  have satisfies : Polynomial.eval₂ (Algebra.ofId LeftRing L) inverse inversionLaw = 0 := by
    simp [inversionLaw, inverse]
  exact AdjoinRoot.liftAlgHom_root inversionLaw (Algebra.ofId LeftRing L) inverse satisfies

/-- The entire arrow of (3.9) becomes the standard localization algebra map. -/
theorem declarationMap_eq_localization :
    localization.toAlgHom.comp declarationMap =
      IsScalarTower.toAlgHom ℚ LeftRing (Localization.Away (Polynomial.X : LeftRing)) := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, declarationMap_X, AlgEquiv.coe_algHom, localization_barX]
  rfl

end

end SHIGURE.PolynomialPresentation.InverseVariableExample
