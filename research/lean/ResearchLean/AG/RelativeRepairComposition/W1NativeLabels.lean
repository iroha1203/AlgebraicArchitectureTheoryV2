import ResearchLean.AG.RelativeRepairComposition.W1ActualRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineGroupoid
import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Full native W1 labels, isomorphism classes and automorphisms

## Implementation notes

The fixed original vertex forces every full native gauge label to vanish.
No label quotient or chosen coordinate family is used as a groupoid. The
isomorphism quotient is Mathlib's quotient of the whole native action category,
and the existing whole affine groupoid equivalence preserves its real arrows.
-/
namespace AAT.AG.RelativeRepairComposition.W1NativeLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1ActualRepairs

/-- All original native actual repairs and all full gauge arrows, fixing the original vertex and the same physical edges. -/
abbrev NativeCategory (negative : Bool) (x y : ZMod 3) (S : Set (EdgeName (K := geometry))) :=
  RepairGroupoid (originalTower negative x y) fixedRegion.vertices (fixedEdges S)

/-- The fixed original vertex forces the complete native vertex-kernel label to be zero, for every permission set. -/
theorem label_zero (negative : Bool) (x y : ZMod 3) (S : Set (EdgeName (K := geometry)))
    (b : supportedC0 (originalTower negative x y) fixedRegion.vertices (fixedEdges S)) : b = 0 := by
  apply Subtype.ext
  funext v
  exact supportedC0_vertex_zero (originalTower negative x y) fixedRegion.vertices
    (fixedEdges S) b v (Set.mem_univ v)

/-- Every full native actual arrow keeps precisely the identity entire label; no ineffective labels are discarded. -/
theorem hom_label_zero {negative : Bool} {x y : ZMod 3} {S : Set (EdgeName (K := geometry))}
    {R Q : NativeCategory negative x y S} (f : R ⟶ Q) :
    f.1 = (1 : Multiplicative (supportedC0 (originalTower negative x y)
      fixedRegion.vertices (fixedEdges S))) := by
  apply Multiplicative.toAdd.injective
  exact label_zero negative x y S (Multiplicative.toAdd f.1)

/-- Two entire original native repairs are isomorphic precisely when they are the same actual repair. -/
theorem hom_iff {negative : Bool} {x y : ZMod 3} {S : Set (EdgeName (K := geometry))}
    (R Q : NativeCategory negative x y S) : Nonempty (R ⟶ Q) ↔ R = Q := by
  constructor
  · rintro ⟨f⟩
    have hf := f.2
    rw [hom_label_zero f] at hf
    change (1 : Multiplicative (supportedC0 (originalTower negative x y)
      fixedRegion.vertices (fixedEdges S))) • R.back = Q.back at hf
    rw [one_smul] at hf
    cases R
    cases Q
    cases hf
    rfl
  · intro he
    subst Q
    exact ⟨𝟙 R⟩

/-- Every whole native hom-set has at most one arrow on the complete original labels. -/
theorem hom_unique {negative : Bool} {x y : ZMod 3} {S : Set (EdgeName (K := geometry))}
    {R Q : NativeCategory negative x y S} (f g : R ⟶ Q) : f = g := by
  apply Subtype.ext
  rw [hom_label_zero f, hom_label_zero g]

/-- Every actual native automorphism is the identity, on the full original kernel labels. -/
theorem aut_identity {negative : Bool} {x y : ZMod 3} {S : Set (EdgeName (K := geometry))}
    (R : NativeCategory negative x y S) (f : R ≅ R) : f = Iso.refl R := by
  apply Iso.ext
  exact hom_unique _ _

/-- The complete native categorical object set is precisely the independently derived original equation solution set. -/
noncomputable def objectParametersEquiv (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    NativeCategory negative x y S ≃ {p : Parameters // Equations negative x y p ∧ Allowed S p} where
  toFun R := nativeParametersEquiv negative x y S R.back
  invFun p := ⟨(), (nativeParametersEquiv negative x y S).symm p⟩
  left_inv R := by
    rcases R with ⟨u, R⟩
    cases u
    exact congrArg (fun R : SupportedRepair (originalTower negative x y) (fixedEdges S) =>
      (⟨(), R⟩ : NativeCategory negative x y S))
        ((nativeParametersEquiv negative x y S).symm_apply_apply R)
  right_inv p := (nativeParametersEquiv negative x y S).apply_symm_apply p

/-- The actual original isomorphism classes retain every full derived parameter and have no gauge identifications. -/
noncomputable def classParametersEquiv (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    Quotient (isIsomorphicSetoid (NativeCategory negative x y S)) ≃
      {p : Parameters // Equations negative x y p ∧ Allowed S p} where
  toFun := Quotient.lift (objectParametersEquiv negative x y S) (by
    intro R Q he
    exact congrArg (objectParametersEquiv negative x y S) ((hom_iff R Q).mp ⟨he.some.hom⟩))
  invFun p := Quotient.mk _ ((objectParametersEquiv negative x y S).symm p)
  left_inv Q := Quotient.inductionOn Q (fun R => by
    change Quotient.mk _ ((objectParametersEquiv negative x y S).symm
      ((objectParametersEquiv negative x y S) R)) = Quotient.mk _ R
    rw [Equiv.symm_apply_apply])
  right_inv p := (objectParametersEquiv negative x y S).apply_symm_apply p

/-- Entire native isomorphism classes and all independent actual repairs have equal cardinality, for every x,y,S and either holonomy. -/
theorem class_card_eq_actual_card (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory negative x y S))) =
      Nat.card (RealRepairs negative x y S) := by
  rw [Nat.card_congr (classParametersEquiv negative x y S),
    Nat.card_congr (actualParametersEquiv negative x y S)]

/-- The existing full affine groupoid equivalence retains every independent actual operation and full native arrow of this W1 input. -/
noncomputable def wholeAffineEquivalence (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    NativeCategory negative x y S ≌
      NativeAffine.Groupoid geometry (reference negative x y) (reference negative x y)
        comparison (linear_faces negative x y) fixedRegion.vertices (fixedEdges S) :=
  NativeAffine.groupoidEquivalence geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) fixedRegion.vertices (fixedEdges S)

end AAT.AG.RelativeRepairComposition.W1NativeLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1NativeLabels
