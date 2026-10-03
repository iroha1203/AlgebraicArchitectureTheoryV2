import ResearchLean.AG.RelativeRepairComposition.W3LocalLabels
import ResearchLean.AG.RelativeRepairComposition.W3GaugeLabels
import ResearchLean.AG.RelativeRepairComposition.W2SingletonCoordinates
import Mathlib.CategoryTheory.Endomorphism

/-! # Full original W3 groupoids under empty permission

Singleton actual objects retain their entire label groups. U and V are BA,
the original overlap is B(A²), and the global category is B(fixed T).
-/
namespace AAT.AG.RelativeRepairComposition.W3EmptyGroupoids
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3GaugeLabels
open W3LocalRepairs W3LocalLabels
attribute [local instance] localAction

/-- BA keeps every vector in the complete original A as an arrow. -/
abbrev BA := SingleObj (Multiplicative A)
/-- B(A²) keeps the two independent original overlap vectors. -/
abbrev BA2 := SingleObj (Multiplicative (A × A))
/-- The full fixed-vector group gives the original restricted global arrows. -/
abbrev BFixed (sheared : Bool) := SingleObj (Multiplicative (FixedVectors sheared))

/-- A singleton actual object family retains its full label group as its automorphisms. -/
noncomputable def singletonAutEquiv {G X : Type*} [Group G] [MulAction G X]
    (e : X ≃ Unit) (R : ActionCategory G X) : Aut R ≃* G where
  toFun f := f.hom.1
  invFun g := {
    hom := ⟨g, e.injective (Subsingleton.elim _ _)⟩
    inv := ⟨g⁻¹, e.injective (Subsingleton.elim _ _)⟩
    hom_inv_id := Subtype.ext (inv_mul_cancel g)
    inv_hom_id := Subtype.ext (mul_inv_cancel g) }
  left_inv f := by apply Aut.ext; exact Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The full actual restricted global category keeps its entire fixed-vector group. -/
noncomputable def globalEquivalence (sheared : Bool) : ActualCategory sheared ∅ ≌ BFixed sheared := by
  letI := gaugeAddAction geometry (reference sheared) (reference sheared) comparison
    (linear_faces sheared) fixedRegion.vertices (fixedEdges ∅)
  exact W2SingletonCoordinates.equivalence (emptyObjectEquiv sheared)
    (emptyLabelEquiv sheared).toMultiplicative

/-- The full actual original U groupoid is BA on all objects and arrows. -/
noncomputable def leftEquivalence (sheared : Bool) : LocalCategory sheared leftRegion ∅ ≌ BA :=
  W2SingletonCoordinates.equivalence (localEmptyObjectEquiv sheared leftRegion)
    (leftLabelEquiv sheared).toMultiplicative

/-- The full actual original V groupoid is BA with its full T boundary label. -/
noncomputable def rightEquivalence (sheared : Bool) : LocalCategory sheared rightRegion ∅ ≌ BA :=
  W2SingletonCoordinates.equivalence (localEmptyObjectEquiv sheared rightRegion)
    (rightLabelEquiv sheared).toMultiplicative

/-- The full original restricted overlap category retains all arrows of B(A²). -/
noncomputable def overlapEquivalence (sheared : Bool) : LocalCategory sheared overlap ∅ ≌ BA2 :=
  W2SingletonCoordinates.equivalence (localEmptyObjectEquiv sheared overlap)
    (overlapLabelEquiv sheared ∅).toMultiplicative

/-- Every actual U object's full automorphism group is the entire original A. -/
noncomputable def leftAutEquiv (sheared : Bool) (R : LocalCategory sheared leftRegion ∅) :
    Aut R ≃* Multiplicative A :=
  (singletonAutEquiv (localEmptyObjectEquiv sheared leftRegion) R).trans
    (leftLabelEquiv sheared).toMultiplicative

/-- Every actual V object's full automorphism group is the entire original A. -/
noncomputable def rightAutEquiv (sheared : Bool) (R : LocalCategory sheared rightRegion ∅) :
    Aut R ≃* Multiplicative A :=
  (singletonAutEquiv (localEmptyObjectEquiv sheared rightRegion) R).trans
    (rightLabelEquiv sheared).toMultiplicative

/-- Every actual overlap object's full automorphism group is the entire original A². -/
noncomputable def overlapAutEquiv (sheared : Bool) (R : LocalCategory sheared overlap ∅) :
    Aut R ≃* Multiplicative (A × A) :=
  (singletonAutEquiv (localEmptyObjectEquiv sheared overlap) R).trans
    (overlapLabelEquiv sheared ∅).toMultiplicative

/-- Forward U automorphism coordinates keep the complete original s vector. -/
theorem leftAutEquiv_label (sheared : Bool) (R : LocalCategory sheared leftRegion ∅) (f : Aut R) :
    (leftAutEquiv sheared R f).toAdd = f.hom.1.toAdd.1 leftS := rfl

/-- Forward V automorphism coordinates keep the complete original t vector. -/
theorem rightAutEquiv_label (sheared : Bool) (R : LocalCategory sheared rightRegion ∅) (f : Aut R) :
    (rightAutEquiv sheared R f).toAdd = f.hom.1.toAdd.1 rightT := rfl

/-- Forward overlap automorphism coordinates keep both complete original vertex vectors. -/
theorem overlapAutEquiv_label (sheared : Bool) (R : LocalCategory sheared overlap ∅) (f : Aut R) :
    (overlapAutEquiv sheared R f).toAdd =
      (f.hom.1.toAdd.1 overlapS,f.hom.1.toAdd.1 overlapT) := rfl

end AAT.AG.RelativeRepairComposition.W3EmptyGroupoids
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3EmptyGroupoids
