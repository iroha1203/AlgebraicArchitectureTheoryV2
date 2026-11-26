import Formal.SHIGURE.Part1.StructureCategory
import Formal.SHIGURE.Part2.QuantityTransport.AgreementQuotient
import Formal.SHIGURE.Part2.QuantityTransport.WrittenLaws
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

variable (k : Type u) [CommRing k] {sig : Signature.{u}} (A : Structure sig)

/-- The empty state context has a single argument tuple. -/
private abbrev EmptyArgument :=
  {a : Assignment A.carrier [] // a ∈ (Set.univ : Set (Assignment A.carrier []))}

/-- The unique tuple in the argument and input domains. -/
private def emptyArgument : EmptyArgument A :=
  ⟨Assignment.empty, Set.mem_univ _⟩

/-- A tuple in the empty context has no values to distinguish it from the canonical tuple. -/
private theorem emptyArgument_eq (a : EmptyArgument A) : a = emptyArgument A :=
  Subtype.ext (Assignment.eq_empty a.val)

/-- The fixed equation (q()=0) on an empty state context. -/
def written : WrittenLaws k sig where
  Quantity := PUnit
  domainContext _ := []
  Law := PUnit
  inputContext _ := []
  Occurrence _ := PUnit
  application _ _ := ⟨PUnit.unit, ⟨Term.argsNil⟩⟩
  left _ := .quantity PUnit.unit
  right _ := .scalar 0

/-- The source interprets the equation at its single possible input. -/
def sourceInterpretation : (written k (sig := sig)).Interpretation A where
  domain _ := Set.univ
  input _ := Set.univ
  defined _ _ _ := fun i => nomatch i
  inDomain _ _ _ := Set.mem_univ _

/-- The target has the same state structure and quantity domain, with no required Law inputs. -/
def targetInterpretation : (written k (sig := sig)).Interpretation A where
  domain _ := Set.univ
  input _ := ∅
  defined _ e _ := False.elim e.property
  inDomain _ e _ := False.elim e.property

/-- Compile the single mandatory input in Example 5.10. -/
def source : Presentation k A := (sourceInterpretation k A).presentation

/-- Compile the same written equality with an empty target input set. -/
def target : Presentation k A := (targetInterpretation k A).presentation

/-- The identity structure map carries the sole quantity input to the sole target input. -/
def comparison : QuantityMap (source k A) (target k A) :=
  (sourceInterpretation k A).quantityMap (targetInterpretation k A) (StructureMap.id A)
    (fun _ _ => Set.mem_univ _)

/-- The actual structure map cannot carry the source's designated input to a designated input. -/
theorem structureMap_does_not_preserve_inputs :
    ¬ ∀ l (e : (sourceInterpretation k A).input l),
      e.val.map (StructureMap.id A).onSort ∈ (targetInterpretation k A).input l := by
  intro preserve
  exact preserve PUnit.unit (emptyArgument A)

/-- No Law map can act on the source's required input. -/
theorem noLawMap : ¬ Nonempty (LawMap (source k A) (target k A)) := by
  rintro ⟨h⟩
  exact (h.input PUnit.unit (emptyArgument A)).property

/-- The written zero equation requires exactly the vanishing of the quantity. -/
private theorem source_holds_iff {R : Type u} [CommRing R] [Algebra k R]
    (q : (source k A).Candidate R) :
    (source k A).Holds q ↔ ∀ j x, q j x = 0 := by
  change (sourceInterpretation k A).presentation.Holds q ↔ _
  rw [WrittenLaws.Interpretation.holds_iff_written]
  constructor
  · intro h j x
    have hq := h PUnit.unit (emptyArgument A)
    change q PUnit.unit ((sourceInterpretation k A).applicationCoordinate
      PUnit.unit (emptyArgument A) PUnit.unit).2 = algebraMap k R 0 at hq
    rw [emptyArgument_eq A ((sourceInterpretation k A).applicationCoordinate
      PUnit.unit (emptyArgument A) PUnit.unit).2, map_zero] at hq
    cases j
    rwa [emptyArgument_eq A x]
  · intro h l e
    change q PUnit.unit ((sourceInterpretation k A).applicationCoordinate l e PUnit.unit).2 = algebraMap k R 0
    rw [map_zero]
    exact h _ _

/-- The free model with quantity value one is lawful at the target. -/
def targetOne : (target k A).Model k :=
  ⟨fun _ _ => 1, fun _ e => False.elim e.property⟩

/-- Over a nonzero ring the pullback of quantity one violates the source equation. -/
theorem targetOne_pullback_fails [Nontrivial k] :
    ¬ (source k A).Holds ((comparison k A).candidate (targetOne k A).val) := by
  intro h
  exact one_ne_zero ((source_holds_iff k A _).mp h PUnit.unit (emptyArgument A))

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
  zeroModelAlgebra k (source k A) (fun _ _ _ q => source_holds_iff k A q)

/-- With no Law inputs the target residual ideal is zero. -/
theorem targetResidualIdeal_eq_bot : (target k A).residualIdeal = ⊥ := by
  apply le_antisymm _ bot_le
  exact ((target k A).residualIdeal_le_iff).mpr (fun _ e => False.elim e.property)

/-- The target Law scheme is the relative affine line. -/
def targetAlgebraEquiv : (target k A).LawAlgebra ≃ₐ[k] Polynomial k :=
  (Ideal.quotientEquivAlgOfEq k (targetResidualIdeal_eq_bot k A)).trans
    ((AlgEquiv.quotientBot k _).trans
      ((MvPolynomial.renameEquiv k
        (show (target k A).Coordinate ≃ PUnit.{u + 1} from
          { toFun := fun _ => PUnit.unit
            invFun := fun _ => ⟨PUnit.unit, emptyArgument A⟩
            left_inv := by
              rintro ⟨⟨⟩, a⟩
              rw [emptyArgument_eq A a]
            right_inv := by rintro ⟨⟩; rfl })).trans (MvPolynomial.pUnitAlgEquiv k)))

/-- The agreement equations impose exactly the original source Law. -/
private theorem correspondence_holds_iff {R : Type u} [CommRing R] [Algebra k R]
    (q : (comparison k A).correspondencePresentation.Candidate R) :
    (comparison k A).correspondencePresentation.Holds q ↔
      (source k A).Holds ((comparison k A).candidate q) := by
  constructor
  · intro h l e
    simpa only [QuantityMap.correspondencePresentation, Expression.eval_rename] using h (.inr l) e
  · intro h l e
    cases l with
    | inl _ => exact False.elim e.property
    | inr l =>
      simpa only [QuantityMap.correspondencePresentation, Expression.eval_rename] using h l e

/-- The matching equations leave one quantity forced to be zero. -/
def correspondenceAlgebraEquiv :
    (comparison k A).correspondencePresentation.LawAlgebra ≃ₐ[k] k :=
  zeroModelAlgebra k (comparison k A).correspondencePresentation (by
    intro R _ _ q
    rw [correspondence_holds_iff, source_holds_iff]
    rfl)

/-- Under the displayed identifications the second projection is the origin of the affine line. -/
theorem projection_eq_origin :
    (correspondenceAlgebraEquiv k A).toAlgHom.comp (comparison k A).targetQuotient =
      (Polynomial.aeval (0 : k)).comp (targetAlgebraEquiv k A).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨⟨⟩, a⟩
  rw [emptyArgument_eq A a]
  change (correspondenceAlgebraEquiv k A)
      (Ideal.Quotient.mk (comparison k A).correspondencePresentation.residualIdeal
        (MvPolynomial.X ⟨PUnit.unit, emptyArgument A⟩)) =
    Polynomial.aeval (0 : k) ((targetAlgebraEquiv k A)
      (Ideal.Quotient.mk (target k A).residualIdeal (MvPolynomial.X ⟨PUnit.unit, emptyArgument A⟩)))
  have origin : (correspondenceAlgebraEquiv k A)
      (Ideal.Quotient.mk (comparison k A).correspondencePresentation.residualIdeal
        (MvPolynomial.X ⟨PUnit.unit, emptyArgument A⟩)) = 0 := by
    change MvPolynomial.aeval (fun _ => (0 : k))
      (MvPolynomial.X (⟨PUnit.unit, emptyArgument A⟩ : (target k A).Coordinate)) = 0
    rw [MvPolynomial.aeval_X]
  have variable_image : (targetAlgebraEquiv k A)
      (Ideal.Quotient.mk (target k A).residualIdeal (MvPolynomial.X ⟨PUnit.unit, emptyArgument A⟩)) =
      Polynomial.X := by
    change MvPolynomial.pUnitAlgEquiv k
      (MvPolynomial.rename (fun _ => PUnit.unit)
        (MvPolynomial.X (R := k) (⟨PUnit.unit, emptyArgument A⟩ : (target k A).Coordinate))) = _
    rw [MvPolynomial.rename_X]
    exact MvPolynomial.eval₂_X _ _ _
  rw [origin, variable_image, Polynomial.aeval_X]

/-- The second projection becomes the inclusion of the origin as a relative scheme map. -/
theorem schemeProjection_eq_origin :
    (specOverAlgEquiv (correspondenceAlgebraEquiv k A)).hom ≫ (comparison k A).targetProjection =
      specOverMap (Polynomial.aeval (0 : k)) ≫ (specOverAlgEquiv (targetAlgebraEquiv k A)).hom := by
  change specOverMap (correspondenceAlgebraEquiv k A).toAlgHom ≫
      specOverMap (comparison k A).targetQuotient =
    specOverMap (Polynomial.aeval (0 : k)) ≫ specOverMap (targetAlgebraEquiv k A).toAlgHom
  rw [specOverMap_comp, specOverMap_comp, projection_eq_origin]

end SHIGURE.Quantities.MissingLawInput
