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

variable (k : Type u) [CommRing k] {sig : Signature.{u}}

/-- The singleton domain whose unary argument is the specified state. -/
private def singletonDomain {A : Structure sig} {s : sig.SortType} (a : A.carrier s) :
    Set (Assignment A.carrier [s]) :=
  {Assignment.cons a Assignment.empty}

/-- The unary assignment naming the only element of a singleton domain. -/
private def singletonArgument {A : Structure sig} {s : sig.SortType} (a : A.carrier s) :
    singletonDomain a :=
  ⟨Assignment.cons a Assignment.empty, Set.mem_singleton _⟩

/-- Every argument in the domain equals the named unary assignment. -/
private theorem singletonArgument_eq {A : Structure sig} {s : sig.SortType} (a : A.carrier s)
    (x : singletonDomain a) : x = singletonArgument a :=
  Subtype.ext (Set.mem_singleton_iff.mp x.property)

/-- The fixed unary equation (q(x)=0). -/
def written (s : sig.SortType) : WrittenLaws k sig where
  Quantity := PUnit
  domainContext _ := [s]
  Law := PUnit
  inputContext _ := [s]
  Occurrence _ := PUnit
  application _ _ := ⟨PUnit.unit, ⟨fun i => .var i⟩⟩
  left _ := .quantity PUnit.unit
  right _ := .scalar 0

variable {A B : Structure sig} {s : sig.SortType}

/-- The source interprets the equation at the input a in the domain {a}. -/
def sourceInterpretation (a : A.carrier s) : (written k s).Interpretation A where
  domain _ := singletonDomain a
  input _ := singletonDomain a
  defined _ e _ := fun i => ⟨e.val i, rfl⟩
  inDomain l e x := by
    have same : ((written k s).application l x).2.value A
        ⟨e.val, fun i => ⟨e.val i, rfl⟩⟩ = e.val := by
      apply Assignment.ext
      intro t i
      exact (((written k s).application l x).2.evaluatesAt_value A
        ⟨e.val, fun i => ⟨e.val i, rfl⟩⟩ i).symm
    rw [same]
    exact e.property

/-- The target has domain {b} and the empty set of Law inputs. -/
def targetInterpretation (b : B.carrier s) : (written k s).Interpretation B where
  domain _ := singletonDomain b
  input _ := ∅
  defined _ e _ := False.elim e.property
  inDomain _ e _ := False.elim e.property

/-- Compile the mandatory input in Example 5.10. -/
def source (a : A.carrier s) : Presentation k A := (sourceInterpretation k a).presentation

/-- Compile the same equality with the empty target input set. -/
def target (b : B.carrier s) : Presentation k B := (targetInterpretation k b).presentation

variable (f : StructureMap A B) (a : A.carrier s)

/-- A structure map taking a to b carries the domain {a} into the domain {b}. -/
def comparison : QuantityMap (source k a) (target k (f.onSort s a)) :=
  (sourceInterpretation k a).quantityMap (targetInterpretation k (f.onSort s a)) f (by
    intro j x
    change x.val.map f.onSort ∈ singletonDomain (f.onSort s a)
    rw [singletonArgument_eq a x]
    exact Set.mem_singleton_iff.mpr (by simp [singletonArgument]))

/-- The structure map cannot carry a into the empty set of designated target inputs. -/
theorem structureMap_does_not_preserve_inputs :
    ¬ ∀ l (e : (sourceInterpretation k a).input l),
      e.val.map f.onSort ∈ (targetInterpretation k (f.onSort s a)).input l := by
  intro preserve
  exact preserve PUnit.unit (singletonArgument a)

/-- No Law map can act on the source's required input. -/
theorem noLawMap (a : A.carrier s) (b : B.carrier s) :
    ¬ Nonempty (LawMap (source k a) (target k b)) := by
  rintro ⟨h⟩
  exact (h.input PUnit.unit (singletonArgument a)).property

/-- The written zero equation requires exactly the vanishing of the quantity. -/
private theorem source_holds_iff (a : A.carrier s) {R : Type u} [CommRing R] [Algebra k R]
    (q : (source k a).Candidate R) :
    (source k a).Holds q ↔ ∀ j x, q j x = 0 := by
  change (sourceInterpretation k a).presentation.Holds q ↔ _
  rw [WrittenLaws.Interpretation.holds_iff_written]
  constructor
  · intro h j x
    have hq := h PUnit.unit (singletonArgument a)
    change q PUnit.unit ((sourceInterpretation k a).applicationCoordinate
      PUnit.unit (singletonArgument a) PUnit.unit).2 = algebraMap k R 0 at hq
    rw [singletonArgument_eq a ((sourceInterpretation k a).applicationCoordinate
      PUnit.unit (singletonArgument a) PUnit.unit).2, map_zero] at hq
    cases j
    rwa [singletonArgument_eq a x]
  · intro h l e
    change q PUnit.unit ((sourceInterpretation k a).applicationCoordinate l e PUnit.unit).2 = algebraMap k R 0
    rw [map_zero]
    exact h _ _

/-- The free model with quantity value one is lawful at the target. -/
def targetOne (b : B.carrier s) : (target k b).Model k :=
  ⟨fun _ _ => 1, fun _ e => False.elim e.property⟩

/-- Over a nonzero ring the pullback of quantity one violates the source equation. -/
theorem targetOne_pullback_fails [Nontrivial k] :
    ¬ (source k a).Holds ((comparison k f a).candidate (targetOne k (f.onSort s a)).val) := by
  intro h
  exact one_ne_zero ((source_holds_iff k a _).mp h PUnit.unit (singletonArgument a))

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
def sourceAlgebraEquiv (a : A.carrier s) : (source k a).LawAlgebra ≃ₐ[k] k :=
  zeroModelAlgebra k (source k a) (fun _ _ _ q => source_holds_iff k a q)

/-- With no Law inputs the target residual ideal is zero. -/
theorem targetResidualIdeal_eq_bot (b : B.carrier s) : (target k b).residualIdeal = ⊥ := by
  apply le_antisymm _ bot_le
  exact ((target k b).residualIdeal_le_iff).mpr (fun _ e => False.elim e.property)

/-- The target Law scheme is the relative affine line. -/
def targetAlgebraEquiv (b : B.carrier s) : (target k b).LawAlgebra ≃ₐ[k] Polynomial k :=
  (Ideal.quotientEquivAlgOfEq k (targetResidualIdeal_eq_bot k b)).trans
    ((AlgEquiv.quotientBot k _).trans
      ((MvPolynomial.renameEquiv k
        (show (target k b).Coordinate ≃ PUnit.{u + 1} from
          { toFun := fun _ => PUnit.unit
            invFun := fun _ => ⟨PUnit.unit, singletonArgument b⟩
            left_inv := by
              rintro ⟨⟨⟩, x⟩
              rw [singletonArgument_eq b x]
            right_inv := by rintro ⟨⟩; rfl })).trans (MvPolynomial.pUnitAlgEquiv k)))

/-- The agreement equations impose exactly the original source Law. -/
private theorem correspondence_holds_iff {R : Type u} [CommRing R] [Algebra k R]
    (q : (comparison k f a).correspondencePresentation.Candidate R) :
    (comparison k f a).correspondencePresentation.Holds q ↔
      (source k a).Holds ((comparison k f a).candidate q) := by
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
    (comparison k f a).correspondencePresentation.LawAlgebra ≃ₐ[k] k :=
  zeroModelAlgebra k (comparison k f a).correspondencePresentation (by
    intro R _ _ q
    rw [correspondence_holds_iff, source_holds_iff]
    refine ⟨?_, fun h j x => h _ ((comparison k f a).argument j x)⟩
    intro h j x
    cases j
    rw [singletonArgument_eq (f.onSort s a) x]
    have atSource := h PUnit.unit (singletonArgument a)
    change q PUnit.unit ((comparison k f a).argument PUnit.unit (singletonArgument a)) = 0 at atSource
    rwa [singletonArgument_eq (f.onSort s a)
      ((comparison k f a).argument PUnit.unit (singletonArgument a))] at atSource)

/-- Under the displayed identifications the second projection is the origin of the affine line. -/
theorem projection_eq_origin :
    (correspondenceAlgebraEquiv k f a).toAlgHom.comp (comparison k f a).targetQuotient =
      (Polynomial.aeval (0 : k)).comp (targetAlgebraEquiv k (f.onSort s a)).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨⟨⟩, x⟩
  rw [singletonArgument_eq (f.onSort s a) x]
  change (correspondenceAlgebraEquiv k f a)
      (Ideal.Quotient.mk (comparison k f a).correspondencePresentation.residualIdeal
        (MvPolynomial.X ⟨PUnit.unit, singletonArgument (f.onSort s a)⟩)) =
    Polynomial.aeval (0 : k) ((targetAlgebraEquiv k (f.onSort s a))
      (Ideal.Quotient.mk (target k (f.onSort s a)).residualIdeal (MvPolynomial.X ⟨PUnit.unit, singletonArgument (f.onSort s a)⟩)))
  have origin : (correspondenceAlgebraEquiv k f a)
      (Ideal.Quotient.mk (comparison k f a).correspondencePresentation.residualIdeal
        (MvPolynomial.X ⟨PUnit.unit, singletonArgument (f.onSort s a)⟩)) = 0 := by
    change MvPolynomial.aeval (fun _ => (0 : k))
      (MvPolynomial.X (⟨PUnit.unit, singletonArgument (f.onSort s a)⟩ : (target k (f.onSort s a)).Coordinate)) = 0
    rw [MvPolynomial.aeval_X]
  have variable_image : (targetAlgebraEquiv k (f.onSort s a))
      (Ideal.Quotient.mk (target k (f.onSort s a)).residualIdeal (MvPolynomial.X ⟨PUnit.unit, singletonArgument (f.onSort s a)⟩)) =
      Polynomial.X := by
    change MvPolynomial.pUnitAlgEquiv k
      (MvPolynomial.rename (fun _ => PUnit.unit)
        (MvPolynomial.X (R := k) (⟨PUnit.unit, singletonArgument (f.onSort s a)⟩ : (target k (f.onSort s a)).Coordinate))) = _
    rw [MvPolynomial.rename_X]
    exact MvPolynomial.eval₂_X _ _ _
  rw [origin, variable_image, Polynomial.aeval_X]

/-- The second projection becomes the inclusion of the origin as a relative scheme map. -/
theorem schemeProjection_eq_origin :
    (specOverAlgEquiv (correspondenceAlgebraEquiv k f a)).hom ≫ (comparison k f a).targetProjection =
      specOverMap (Polynomial.aeval (0 : k)) ≫ (specOverAlgEquiv (targetAlgebraEquiv k (f.onSort s a))).hom := by
  change specOverMap (correspondenceAlgebraEquiv k f a).toAlgHom ≫
      specOverMap (comparison k f a).targetQuotient =
    specOverMap (Polynomial.aeval (0 : k)) ≫ specOverMap (targetAlgebraEquiv k (f.onSort s a)).toAlgHom
  rw [specOverMap_comp, specOverMap_comp, projection_eq_origin]

end SHIGURE.Quantities.MissingLawInput
