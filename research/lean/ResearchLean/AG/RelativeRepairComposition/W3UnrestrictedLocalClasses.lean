import ResearchLean.AG.RelativeRepairComposition.W3UnrestrictedLocalEquivalences
import ResearchLean.AG.RelativeRepairComposition.W2OrdinaryClasses

/-! # All unrestricted W3 local classes and full automorphisms

The whole original U and V categories have one class and automorphism A at
every actual repair. The original overlap has one class and automorphism A².
Each comparison uses full category equivalences rather than effect quotients.
-/
namespace AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs
open W3LocalRepairs W3LocalLabels W3LocalOperationCoordinates W3EmptyGroupoids
attribute [local instance] localAction

/-- A whole one-object group category has both inverse point coordinates on its isomorphism quotient. -/
noncomputable def singleClassEquiv (G : Type*) [Group G] :
    Quotient (isIsomorphicSetoid (SingleObj G)) ≃ Unit where
  toFun _ := ()
  invFun _ := Quotient.mk _ (SingleObj.star G)
  left_inv q := Quotient.inductionOn q (fun R =>
    congrArg (Quotient.mk (isIsomorphicSetoid (SingleObj G)))
      (Subsingleton.elim (SingleObj.star G) R))
  right_inv _ := rfl

/-- Every full automorphism of a one-object group category is its same original group arrow. -/
def singleAutEquiv (G : Type*) [Group G] (R : SingleObj G) : Aut R ≃* G where
  toFun f := f.hom
  invFun g := {
    hom := g
    inv := g⁻¹
    hom_inv_id := inv_mul_cancel g
    inv_hom_id := mul_inv_cancel g }
  left_inv f := by apply Aut.ext; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The complete original unrestricted overlap category retains all arrows of B(A²). -/
noncomputable def overlapEquivalence (sheared : Bool) :
    LocalCategory sheared overlap candidates ≌ BA2 :=
  W2SingletonCoordinates.equivalence (overlapObjectEquiv sheared candidates)
    (overlapLabelEquiv sheared candidates).toMultiplicative

/-- All unrestricted original U classes have both inverse point coordinates. -/
noncomputable def leftClassEquiv (sheared : Bool) :
    Quotient (isIsomorphicSetoid (LocalCategory sheared leftRegion candidates)) ≃ Unit :=
  (W2OrdinaryClasses.equivalenceClasses
    (W3UnrestrictedLocalEquivalences.leftEquivalence sheared).symm).trans
    (singleClassEquiv (Multiplicative A))

/-- All unrestricted original V classes have both inverse point coordinates. -/
noncomputable def rightClassEquiv (sheared : Bool) :
    Quotient (isIsomorphicSetoid (LocalCategory sheared rightRegion candidates)) ≃ Unit :=
  (W2OrdinaryClasses.equivalenceClasses
    (W3UnrestrictedLocalEquivalences.rightEquivalence sheared).symm).trans
    (singleClassEquiv (Multiplicative A))

/-- All unrestricted original overlap classes have both inverse point coordinates. -/
noncomputable def overlapClassEquiv (sheared : Bool) :
    Quotient (isIsomorphicSetoid (LocalCategory sheared overlap candidates)) ≃ Unit :=
  (W2OrdinaryClasses.equivalenceClasses (overlapEquivalence sheared)).trans
    (singleClassEquiv (Multiplicative (A × A)))

/-- Every independent actual unrestricted U object's whole automorphism group is all original A. -/
noncomputable def leftAutEquiv (sheared : Bool) (R : LocalCategory sheared leftRegion candidates) :
    Aut R ≃* Multiplicative A :=
  ((W3UnrestrictedLocalEquivalences.leftEquivalence sheared).fullyFaithfulInverse.autMulEquivOfFullyFaithful R).trans
    (singleAutEquiv (Multiplicative A)
      ((W3UnrestrictedLocalEquivalences.leftEquivalence sheared).inverse.obj R))

/-- Every independent actual unrestricted V object's whole automorphism group is all original A. -/
noncomputable def rightAutEquiv (sheared : Bool) (R : LocalCategory sheared rightRegion candidates) :
    Aut R ≃* Multiplicative A :=
  ((W3UnrestrictedLocalEquivalences.rightEquivalence sheared).fullyFaithfulInverse.autMulEquivOfFullyFaithful R).trans
    (singleAutEquiv (Multiplicative A)
      ((W3UnrestrictedLocalEquivalences.rightEquivalence sheared).inverse.obj R))

/-- Every original unrestricted overlap object's whole automorphism group is all original A². -/
noncomputable def overlapAutEquiv (sheared : Bool) (R : LocalCategory sheared overlap candidates) :
    Aut R ≃* Multiplicative (A × A) :=
  ((overlapEquivalence sheared).fullyFaithfulFunctor.autMulEquivOfFullyFaithful R).trans
    (singleAutEquiv (Multiplicative (A × A)) ((overlapEquivalence sheared).functor.obj R))

/-- Every actual unrestricted U isomorphism class is counted, with exactly one class. -/
theorem left_class_card (sheared : Bool) :
    Nat.card (Quotient (isIsomorphicSetoid (LocalCategory sheared leftRegion candidates))) = 1 := by
  rw [Nat.card_congr (leftClassEquiv sheared), Nat.card_eq_fintype_card]
  rfl

/-- Every actual unrestricted V isomorphism class is counted, with exactly one class. -/
theorem right_class_card (sheared : Bool) :
    Nat.card (Quotient (isIsomorphicSetoid (LocalCategory sheared rightRegion candidates))) = 1 := by
  rw [Nat.card_congr (rightClassEquiv sheared), Nat.card_eq_fintype_card]
  rfl

/-- Every actual unrestricted overlap isomorphism class is counted, with exactly one class. -/
theorem overlap_class_card (sheared : Bool) :
    Nat.card (Quotient (isIsomorphicSetoid (LocalCategory sheared overlap candidates))) = 1 := by
  rw [Nat.card_congr (overlapClassEquiv sheared), Nat.card_eq_fintype_card]
  rfl

end AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3UnrestrictedLocalClasses
