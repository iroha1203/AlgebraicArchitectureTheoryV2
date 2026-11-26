import Formal.SHIGURE.Part2.QuantityTransport.AgreementQuotient
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The correspondence when a Law input is missing

Example 5.10 uses one source quantity and one target quantity.
The source requires its value to be zero. The target has an empty
set of Law inputs. Eliminating the source coordinate selects the
origin of the target affine line.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Quantities.MissingLawInput

variable (k : Type u) [CommRing k] {sig sig' : Signature.{u}}
variable (A : Structure sig) (B : Structure sig')

/-- One source quantity with its declared Law input. -/
def source : Presentation k A where
  Quantity := PUnit
  Domain _ := PUnit
  Law := PUnit
  Input _ := PUnit
  left _ _ := .quantity ⟨PUnit.unit, PUnit.unit⟩
  right _ _ := .scalar 0

/-- One target quantity with no input at which the Law must hold. -/
def target : Presentation k B where
  Quantity := PUnit
  Domain _ := PUnit
  Law := PUnit
  Input _ := PEmpty
  left _ _ := .quantity ⟨PUnit.unit, PUnit.unit⟩
  right _ _ := .scalar 0

/-- The sole source quantity input maps to the sole target quantity input. -/
def comparison : QuantityMap (source k A) (target k B) where
  name := id
  argument _ := id

/-- No Law map can act on the source's required input. -/
theorem noLawMap : ¬ Nonempty (LawMap (source k A) (target k B)) := by
  rintro ⟨h⟩
  exact PEmpty.elim (h.input PUnit.unit PUnit.unit)

/-- The free model with quantity value one is lawful at the target. -/
def targetOne : (target k B).Model k :=
  ⟨fun _ _ => 1, fun _ e => PEmpty.elim e⟩

/-- Over a nonzero ring the pullback of quantity one violates the source equation. -/
theorem targetOne_pullback_fails [Nontrivial k] :
    ¬ (source k A).Holds ((comparison k A B).candidate (targetOne k B).val) := by
  intro h
  have ht := h PUnit.unit PUnit.unit
  change (1 : k) = algebraMap k k 0 at ht
  rw [map_zero] at ht
  exact one_ne_zero ht

/-- When every quantity must be zero, the coefficient ring represents the models. -/
private def zeroModelAlgebra {S : Structure sig} (P : Presentation k S)
    (zeroLaw : ∀ (R : Type u) [CommRing R] [Algebra k R] (q : P.Candidate R),
      P.Holds q ↔ ∀ j x, q j x = 0) :
    P.LawAlgebra ≃ₐ[k] k := by
  let q : P.Model k := ⟨fun _ _ => 0, (zeroLaw _ _).mpr (fun _ _ => rfl)⟩
  let f := P.modelAlgHomEquiv q
  let g := Algebra.ofId k P.LawAlgebra
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AlgHom.ext
    exact f.commutes
  · change g.comp (P.modelAlgHomEquiv q) = _
    rw [← P.modelAlgHomEquiv_natural]
    have hg : P.map g q = P.universalModel := by
      apply Subtype.ext
      funext j x
      change g 0 = P.universalModel.val j x
      rw [map_zero]
      exact ((zeroLaw _ _).mp P.universalModel.property j x).symm
    rw [hg]
    exact P.modelAlgHomEquiv.apply_symm_apply _

/-- The source Law scheme is represented by the coefficient ring. -/
def sourceAlgebraEquiv : (source k A).LawAlgebra ≃ₐ[k] k :=
  zeroModelAlgebra k (source k A) (by
    intro R _ _ q
    constructor
    · intro h ⟨⟩ ⟨⟩
      have he := h PUnit.unit PUnit.unit
      change q PUnit.unit PUnit.unit = algebraMap k R 0 at he
      rwa [map_zero] at he
    · intro h l e
      change q PUnit.unit PUnit.unit = algebraMap k R 0
      rw [map_zero]
      exact h _ _)

/-- With no Law inputs the target residual ideal is zero. -/
theorem targetResidualIdeal_eq_bot : (target k B).residualIdeal = ⊥ := by
  apply le_antisymm _ bot_le
  exact ((target k B).residualIdeal_le_iff).mpr (fun _ e => PEmpty.elim e)

/-- The target Law scheme is the relative affine line. -/
def targetAlgebraEquiv : (target k B).LawAlgebra ≃ₐ[k] Polynomial k :=
  (Ideal.quotientEquivAlgOfEq k (targetResidualIdeal_eq_bot k B)).trans
    ((AlgEquiv.quotientBot k _).trans
      ((MvPolynomial.renameEquiv k
        (show (target k B).Coordinate ≃ PUnit.{u + 1} from
          { toFun := fun _ => PUnit.unit
            invFun := fun _ => ⟨PUnit.unit, PUnit.unit⟩
            left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
            right_inv := by rintro ⟨⟩; rfl })).trans (MvPolynomial.pUnitAlgEquiv k)))

/-- The matching equations leave one quantity forced to be zero. -/
def correspondenceAlgebraEquiv :
    (comparison k A B).correspondencePresentation.LawAlgebra ≃ₐ[k] k :=
  zeroModelAlgebra k (comparison k A B).correspondencePresentation (by
    intro R _ _ q
    constructor
    · intro h ⟨⟩ ⟨⟩
      have he := h (.inr PUnit.unit) PUnit.unit
      change q PUnit.unit PUnit.unit = algebraMap k R 0 at he
      rwa [map_zero] at he
    · intro h l e
      cases l with
      | inl _ => exact PEmpty.elim e
      | inr _ =>
        change q PUnit.unit PUnit.unit = algebraMap k R 0
        rw [map_zero]
        exact h _ _)

/-- Under the displayed identifications the second projection is the origin of the affine line. -/
theorem projection_eq_origin :
    (correspondenceAlgebraEquiv k A B).toAlgHom.comp (comparison k A B).targetQuotient =
      (Polynomial.aeval (0 : k)).comp (targetAlgebraEquiv k B).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨⟨⟩, ⟨⟩⟩
  change (correspondenceAlgebraEquiv k A B)
      (Ideal.Quotient.mk (comparison k A B).correspondencePresentation.residualIdeal
        (MvPolynomial.X ⟨PUnit.unit, PUnit.unit⟩)) =
    Polynomial.aeval (0 : k) ((targetAlgebraEquiv k B)
      (Ideal.Quotient.mk (target k B).residualIdeal (MvPolynomial.X ⟨PUnit.unit, PUnit.unit⟩)))
  have origin : (correspondenceAlgebraEquiv k A B)
      (Ideal.Quotient.mk (comparison k A B).correspondencePresentation.residualIdeal
        (MvPolynomial.X ⟨PUnit.unit, PUnit.unit⟩)) = 0 := by
    change MvPolynomial.aeval (fun _ => (0 : k))
      (MvPolynomial.X (⟨PUnit.unit, PUnit.unit⟩ : (target k B).Coordinate)) = 0
    rw [MvPolynomial.aeval_X]
  have variable_image : (targetAlgebraEquiv k B)
      (Ideal.Quotient.mk (target k B).residualIdeal (MvPolynomial.X ⟨PUnit.unit, PUnit.unit⟩)) =
      Polynomial.X := by
    change MvPolynomial.pUnitAlgEquiv k
      (MvPolynomial.rename (fun _ => PUnit.unit)
        (MvPolynomial.X (R := k) (⟨PUnit.unit, PUnit.unit⟩ : (target k B).Coordinate))) = _
    rw [MvPolynomial.rename_X]
    exact MvPolynomial.eval₂_X _ _ _
  rw [origin, variable_image, Polynomial.aeval_X]

/-- The second projection becomes the inclusion of the origin as a relative scheme map. -/
theorem schemeProjection_eq_origin :
    (specOverAlgEquiv (correspondenceAlgebraEquiv k A B)).hom ≫ (comparison k A B).targetProjection =
      specOverMap (Polynomial.aeval (0 : k)) ≫ (specOverAlgEquiv (targetAlgebraEquiv k B)).hom := by
  change specOverMap (correspondenceAlgebraEquiv k A B).toAlgHom ≫
      specOverMap (comparison k A B).targetQuotient =
    specOverMap (Polynomial.aeval (0 : k)) ≫ specOverMap (targetAlgebraEquiv k B).toAlgHom
  rw [specOverMap_comp, specOverMap_comp, projection_eq_origin]

end SHIGURE.Quantities.MissingLawInput
