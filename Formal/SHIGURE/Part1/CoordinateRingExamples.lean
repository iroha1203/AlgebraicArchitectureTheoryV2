import Formal.SHIGURE.Part1.CoordinateRings
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Adding an inverse variable

Example 3.12 uses the inclusion of the declaration of x into the presentation
with x, y and the Law xy = 1. Its coordinate map is the localization map at x.
A reverse map that preserves the shared generator x would make x invertible
in the polynomial ring itself.
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
  unfold lawIdeal
  have h : Set.range (fun l : small.Law => small.left l - small.right l) = ∅ := by
    ext p
    constructor
    · rintro ⟨l, _⟩
      exact PEmpty.elim l
    · exact False.elim
  rw [h, Ideal.span_empty]

/-- The large presentation cuts out precisely the relation xy - 1. -/
theorem large_lawIdeal : large.lawIdeal = Ideal.span
    {X (some PUnit.unit) * X none - (1 : MvPolynomial large.Variable ℚ)} := by
  unfold lawIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨⟨⟩, h⟩
    exact h.symm
  · intro h
    exact ⟨PUnit.unit, h.symm⟩

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
  change univariate (Ideal.Quotient.mk small.lawIdeal (X PUnit.unit)) = _
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
  let mk := Ideal.Quotient.mkₐ ℚ large.lawIdeal
  have rel : X (some PUnit.unit) * X none - 1 ∈ large.lawIdeal :=
    Ideal.subset_span ⟨PUnit.unit, rfl⟩
  have zero : mk (X (some PUnit.unit) * X none - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr rel
  change mk (X (some PUnit.unit)) * mk (X none) = 1
  rw [map_sub, map_mul, map_one, sub_eq_zero] at zero
  exact zero

/-- There is no reverse algebra map keeping the shared x. Evaluate a putative inverse relation at zero. -/
theorem no_reverse_preserving_X :
    ¬ ∃ f : large.CoordinateRing →ₐ[ℚ] LeftRing, f barX = Polynomial.X := by
  rintro ⟨f, keepsX⟩
  have relation := congrArg f barX_mul_barY
  rw [map_mul, map_one, keepsX] at relation
  have zero := congrArg (Polynomial.evalRingHom (0 : ℚ)) relation
  simp at zero

private def bivariate : MvPolynomial (Option PUnit.{1}) ℚ ≃ₐ[ℚ] Polynomial LeftRing :=
  (MvPolynomial.optionEquivLeft ℚ PUnit).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.pUnitAlgEquiv ℚ))

private theorem bivariate_x :
    bivariate (X (some PUnit.unit)) = Polynomial.C (Polynomial.X : LeftRing) := by
  simp [bivariate, MvPolynomial.pUnitAlgEquiv_apply]

private theorem bivariate_y : bivariate (X none) = Polynomial.X := by
  simp [bivariate]

private abbrev inversionLaw : Polynomial LeftRing :=
  Polynomial.C (Polynomial.X : LeftRing) * Polynomial.X - 1

private theorem mappedIdeal : Ideal.span {inversionLaw} = large.lawIdeal.map bivariate.toRingHom := by
  rw [large_lawIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {inversionLaw} =
    Ideal.span {bivariate (X (some PUnit.unit) * X none - 1)}
  rw [map_sub, map_mul, map_one, bivariate_x, bivariate_y]

private def quotientEquiv : large.CoordinateRing ≃ₐ[ℚ] AdjoinRoot inversionLaw :=
  Ideal.quotientEquivAlg _ _ bivariate mappedIdeal

/-- The exact coordinate ring of the large presentation is the localization away from x. -/
def localization : large.CoordinateRing ≃ₐ[ℚ] Localization.Away (Polynomial.X : LeftRing) :=
  quotientEquiv.trans ((Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm.restrictScalars ℚ)

/-- The localization identification preserves the shared generator x. -/
theorem localization_barX :
    localization barX = algebraMap LeftRing (Localization.Away (Polynomial.X : LeftRing)) Polynomial.X := by
  change (Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm
    (quotientEquiv (Ideal.Quotient.mk large.lawIdeal (X (some PUnit.unit)))) = _
  rw [show quotientEquiv (Ideal.Quotient.mk large.lawIdeal (X (some PUnit.unit))) =
      algebraMap LeftRing (AdjoinRoot inversionLaw) Polynomial.X by
    change Ideal.Quotient.mk (Ideal.span {inversionLaw}) (bivariate (X (some PUnit.unit))) = _
    rw [bivariate_x, AdjoinRoot.algebraMap_eq]
    rfl]
  exact (Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm.commutes _

/-- The localization identification sends the new generator y to the inverse of x. -/
theorem localization_barY :
    localization barY = IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : LeftRing))
      (Polynomial.X : LeftRing) := by
  change (Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm
    (quotientEquiv (Ideal.Quotient.mk large.lawIdeal (X none))) = _
  change (Localization.awayEquivAdjoin (Polynomial.X : LeftRing)).symm
    (Ideal.Quotient.mk (Ideal.span {inversionLaw}) (bivariate (X none))) = _
  rw [bivariate_y]
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
