import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.LinearInterfaceAction
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Complete section changes of the same original interface

## Implementation notes

Both sections act on the same full internal differential. Their regularity is
an explicit hypothesis of this generic lemma; the original finite application
supplies it from the accepted generator. Public values are unchanged, and the
whole kernel coordinate changes by the difference of section preimages.
-/
namespace AAT.AG.RelativeRepairComposition.LinearInterface
open CategoryTheory
universe uk ux uz uv ub
variable {k : Type uk} [Field k]
variable {X : Type ux} {Z : Type uz} {V : Type uv} {B : Type ub}
variable [AddCommGroup X] [Module k X] [AddCommGroup Z] [Module k Z]
variable [AddCommGroup V] [Module k V] [AddCommGroup B] [Module k B]
variable (D : X →ₗ[k] V) (F : Z →ₗ[k] V)
variable (σ τ υ : V →ₗ[k] X)
variable (hσ : ∀ x, D (σ (D x)) = D x)
variable (hτ : ∀ x, D (τ (D x)) = D x)
variable (hυ : ∀ x, D (υ (D x)) = D x) (r : V)

include hσ hτ in
/-- Both computed public predicates express the same intrinsic cokernel equation. -/
theorem relation_section_iff (z : Z) :
    z ∈ Relation D F σ r ↔ z ∈ Relation D F τ r :=
  (mem_relation D F σ hσ r z).trans (mem_relation D F τ hτ r z).symm

/-- The complete coordinates change through their independently defined original solution. -/
def sectionComparison : Coordinates D F σ r ≃ Coordinates D F τ r :=
  (coordinateEquiv D F σ hσ r).symm.trans (coordinateEquiv D F τ hτ r)

/-- Every public coordinate retains exactly its original value. -/
theorem section_comparison_public (y : Coordinates D F σ r) :
    (sectionComparison D F σ τ hσ hτ r y).1.1 = y.1.1 := rfl

/-- The full internal freedom changes by the stated difference of section preimages. -/
theorem section_comparison_kernel (y : Coordinates D F σ r) :
    (sectionComparison D F σ τ hσ hτ r y).2.1 =
      y.2.1 + (σ - τ) (r - F y.1.1) := by
  change (σ (r - F y.1.1) + y.2.1) - τ (r - F y.1.1) =
    y.2.1 + (σ (r - F y.1.1) - τ (r - F y.1.1))
  abel

include hσ hτ in
/-- The section difference belongs to the entire original kernel. -/
theorem section_difference_mem (z : ↥(Relation D F σ r)) :
    (σ - τ) (r - F z.1) ∈ LinearMap.ker D := by
  let z' : ↥(Relation D F τ r) := ⟨z.1,(relation_section_iff D F σ τ hσ hτ r z.1).mp z.2⟩
  change D (σ (r - F z.1) - τ (r - F z.1)) = 0
  have ht : D (τ (r - F z.1)) = r - F z.1 := section_residual D F τ r z'
  rw [map_sub,section_residual D F σ r z,ht,sub_self]

/-- Reconstruction of every original solution is unchanged by the section comparison. -/
theorem rec_section_comparison (y : Coordinates D F σ r) :
    rec D F τ r (sectionComparison D F σ τ hσ hτ r y) = rec D F σ r y :=
  rec_coord D F τ hτ r (rec D F σ r y)

/-- Reading a solution in the new section is the comparison of its old coordinates. -/
theorem coord_section_comparison (h : Solution D F r) :
    sectionComparison D F σ τ hσ hτ r (coord D F σ hσ r h) = coord D F τ hτ r h := by
  change coord D F τ hτ r (rec D F σ r (coord D F σ hσ r h)) = _
  rw [rec_coord]

/-- Reversing the two sections restores every public value and internal vector. -/
theorem section_comparison_inverse (y : Coordinates D F σ r) :
    sectionComparison D F τ σ hτ hσ r (sectionComparison D F σ τ hσ hτ r y) = y := by
  change coord D F σ hσ r (rec D F τ r (sectionComparison D F σ τ hσ hτ r y)) = _
  rw [rec_section_comparison,coord_rec]

/-- Three section changes compose on the whole coordinate object. -/
theorem section_comparison_comp (y : Coordinates D F σ r) :
    sectionComparison D F τ υ hτ hυ r (sectionComparison D F σ τ hσ hτ r y) =
      sectionComparison D F σ υ hσ hυ r y := by
  change coord D F υ hυ r (rec D F τ r (sectionComparison D F σ τ hσ hτ r y)) = _
  rw [rec_section_comparison]
  rfl

/-- Equal sections give the identity on the full coordinate space. -/
theorem section_comparison_self (y : Coordinates D F σ r) :
    sectionComparison D F σ σ hσ hσ r y = y := coord_rec D F σ hσ r y

variable (a : B →ₗ[k] X) (c : B →ₗ[k] Z)
variable (hzero : ∀ b, D (a b) + F (c b) = 0)

/-- The comparison commutes with every full original label, including stabilizers. -/
theorem section_comparison_gauge (b : B) (y : Objects D F σ hσ a c hzero r) :
    sectionComparison D F σ τ hσ hτ r (gauge D F σ hσ a c hzero r b y) =
      gauge D F τ hτ a c hzero r b (sectionComparison D F σ τ hσ hτ r y) := by
  apply (coordinateEquiv D F τ hτ r).symm.injective
  apply Subtype.ext
  change (rec D F τ r (sectionComparison D F σ τ hσ hτ r
    (gauge D F σ hσ a c hzero r b y))).1 =
      (rec D F τ r (gauge D F τ hτ a c hzero r b (sectionComparison D F σ τ hσ hτ r y))).1
  rw [rec_section_comparison,rec_gauge,rec_gauge,rec_section_comparison]

/-- Full native section comparison retains the same original label group. -/
def sectionEquivalence : Groupoid D F σ hσ a c hzero r ≌ Groupoid D F τ hτ a c hzero r :=
  changedLabelEquivalence (MulEquiv.refl (Multiplicative B))
    (show Objects D F σ hσ a c hzero r ≃ Objects D F τ hτ a c hzero r from
      sectionComparison D F σ τ hσ hτ r)
    (fun b y => section_comparison_gauge D F σ τ hσ hτ r a c hzero b.toAdd y)

/-- Every forward arrow keeps its full original label. -/
theorem section_functor_label {x y : Groupoid D F σ hσ a c hzero r} (f : x ⟶ y) :
    ((sectionEquivalence D F σ τ hσ hτ r a c hzero).functor.map f).1 = f.1 := rfl

/-- Every inverse arrow keeps its full original label. -/
theorem section_inverse_label {x y : Groupoid D F τ hτ a c hzero r} (f : x ⟶ y) :
    ((sectionEquivalence D F σ τ hσ hτ r a c hzero).inverse.map f).1 = f.1 := rfl

/-- The forward and inverse compose to the identity on all objects and arrows. -/
theorem section_functor_inverse :
    (sectionEquivalence D F σ τ hσ hτ r a c hzero).functor ⋙
      (sectionEquivalence D F σ τ hσ hτ r a c hzero).inverse =
        𝟭 (Groupoid D F σ hσ a c hzero r) :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative B))
    (show Objects D F σ hσ a c hzero r ≃ Objects D F τ hτ a c hzero r from
      sectionComparison D F σ τ hσ hτ r)
    (fun b y => section_comparison_gauge D F σ τ hσ hτ r a c hzero b.toAdd y)

/-- The inverse and forward compose to the identity on all coordinates and arrows. -/
theorem section_inverse_functor :
    (sectionEquivalence D F σ τ hσ hτ r a c hzero).inverse ⋙
      (sectionEquivalence D F σ τ hσ hτ r a c hzero).functor =
        𝟭 (Groupoid D F τ hτ a c hzero r) :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative B))
    (show Objects D F σ hσ a c hzero r ≃ Objects D F τ hτ a c hzero r from
      sectionComparison D F σ τ hσ hτ r)
    (fun b y => section_comparison_gauge D F σ τ hσ hτ r a c hzero b.toAdd y)

end AAT.AG.RelativeRepairComposition.LinearInterface
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
