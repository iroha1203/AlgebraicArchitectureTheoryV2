import ResearchLean.AG.RelativeRepairComposition.SymbolicInterface
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Evaluation preserves every full original label

## Implementation notes

The external parameter has zero gauge coboundary. Every original label acts on
the same public coordinate and the whole private kernel in its parameter fibre.
Evaluation has identity label map, so both native inverse functors retain labels
and stabilizers without passing to a quotient.
-/
namespace AAT.AG.RelativeRepairComposition.SymbolicInterface
open CategoryTheory LinearInterface
universe uk ux uz uv up ub
variable {k : Type uk} [Field k]
variable {X : Type ux} {Z : Type uz} {V : Type uv} {P : Type up} {G : Type ub}
variable [AddCommGroup X] [Module k X] [AddCommGroup Z] [Module k Z]
variable [AddCommGroup V] [Module k V] [AddCommGroup P] [Module k P]
variable [AddCommGroup G] [Module k G]
variable (D : X →ₗ[k] V) (F : Z →ₗ[k] V) (σ : V →ₗ[k] X)
variable (hσ : ∀ x, D (σ (D x)) = D x) (B : P →ₗ[k] V) (r : V)
variable (a : G →ₗ[k] X) (c : G →ₗ[k] Z) (hzero : ∀ g, D (a g) + F (c g) = 0)

/-- The entire original public coboundary keeps the external parameter coordinate fixed. -/
def publicCoboundary : G →ₗ[k] (Z × P) := c.prod 0

include hzero in
/-- Every full original label satisfies the same pre-evaluation differential identity. -/
theorem symbolic_coboundary_zero (g : G) :
    D (a g) + publicMap F B (publicCoboundary (P := P) c g) = 0 := by
  change D (a g) + (F (c g) - B 0) = 0
  simpa only [map_zero, sub_zero] using hzero g

/-- The object fibre keeps every original public value and every internal kernel vector. -/
def FiberObjects (_hσ : ∀ x, D (σ (D x)) = D x)
    (_a : G →ₗ[k] X) (_c : G →ₗ[k] Z) (_hzero : ∀ g, D (_a g) + F (_c g) = 0) (v : P) :=
  RelationFiber D F σ B r v × LinearMap.ker D

/-- Each original full label acts in its parameter fibre with the same public and kernel increments. -/
def fiberGauge (v : P) (g : G) (y : FiberObjects D F σ B r hσ a c hzero v) :
    FiberObjects D F σ B r hσ a c hzero v :=
  (⟨y.1.1 + c g,by
    apply (relation_evaluation D F σ B r v _).mpr
    exact (gauge D F σ hσ a c hzero (rhs B r v) g
      (coordinateFiberEquiv D F σ B r v y)).1.2⟩,
    y.2 + gamma D σ hσ a g)

/-- Sum and zero of full original labels give their native action in every fibre. -/
instance fiberAddAction (v : P) : AddAction G (FiberObjects D F σ B r hσ a c hzero v) where
  vadd := fiberGauge D F σ hσ B r a c hzero v
  zero_vadd y := by
    apply Prod.ext
    · apply Subtype.ext
      change y.1.1 + c 0 = y.1.1
      rw [map_zero, add_zero]
    · change y.2 + gamma D σ hσ a 0 = y.2
      rw [map_zero, add_zero]
  add_vadd g g' y := by
    apply Prod.ext
    · apply Subtype.ext
      change y.1.1 + c (g + g') = y.1.1 + c g' + c g
      rw [map_add]
      abel
    · change y.2 + gamma D σ hσ a (g + g') = y.2 + gamma D σ hσ a g' + gamma D σ hσ a g
      rw [map_add]
      abel

/-- Evaluating the full original-label action is exactly the same evaluated coordinate action. -/
theorem fiber_evaluation_equivariant (v : P) (g : Multiplicative G)
    (y : FiberObjects D F σ B r hσ a c hzero v) :
    letI : AddAction G (Coordinates D F σ (rhs B r v)) :=
      interfaceAddAction D F σ hσ a c hzero (rhs B r v)
    coordinateFiberEquiv D F σ B r v (g • y) =
      g • (coordinateFiberEquiv D F σ B r v y : Objects D F σ hσ a c hzero (rhs B r v)) := by
  letI : AddAction G (Coordinates D F σ (rhs B r v)) :=
      interfaceAddAction D F σ hσ a c hzero (rhs B r v)
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- Each parameter fibre is the full native groupoid on all original labels. -/
abbrev FiberGroupoid (v : P) := ActionCategory (Multiplicative G)
  (FiberObjects D F σ B r hσ a c hzero v)

/-- Evaluation gives a native equivalence with identity map on every original label. -/
def fiberEquivalence (v : P) :
    FiberGroupoid D F σ hσ B r a c hzero v ≌ Groupoid D F σ hσ a c hzero (rhs B r v) := by
  letI : AddAction G (Coordinates D F σ (rhs B r v)) :=
      interfaceAddAction D F σ hσ a c hzero (rhs B r v)
  letI : AddAction G (RelationFiber D F σ B r v × LinearMap.ker D) :=
    fiberAddAction D F σ hσ B r a c hzero v
  exact changedLabelEquivalence (MulEquiv.refl (Multiplicative G)) (coordinateFiberEquiv D F σ B r v)
    (fiber_evaluation_equivariant D F σ hσ B r a c hzero v)

/-- The evaluation functor followed by its inverse is exactly identity on all objects and arrows. -/
theorem fiber_functor_inverse (v : P) :
    (fiberEquivalence D F σ hσ B r a c hzero v).functor ⋙
      (fiberEquivalence D F σ hσ B r a c hzero v).inverse =
        𝟭 (FiberGroupoid D F σ hσ B r a c hzero v) :=
  changed_label_functor_inverse _ _ _

/-- The inverse evaluation functor followed by evaluation is exactly identity on all objects and arrows. -/
theorem fiber_inverse_functor (v : P) :
    (fiberEquivalence D F σ hσ B r a c hzero v).inverse ⋙
      (fiberEquivalence D F σ hσ B r a c hzero v).functor =
        𝟭 (Groupoid D F σ hσ a c hzero (rhs B r v)) :=
  changed_label_inverse_functor _ _ _

/-- Evaluation preserves the entire original gauge label, including stabilizers. -/
theorem fiber_functor_label (v : P) {x y : FiberGroupoid D F σ hσ B r a c hzero v} (f : x ⟶ y) :
    ((fiberEquivalence D F σ hσ B r a c hzero v).functor.map f).1 = f.1 := rfl

/-- Inverse evaluation preserves the entire original gauge label, including stabilizers. -/
theorem fiber_inverse_label (v : P) {x y : Groupoid D F σ hσ a c hzero (rhs B r v)} (f : x ⟶ y) :
    ((fiberEquivalence D F σ hσ B r a c hzero v).inverse.map f).1 = f.1 := rfl

end AAT.AG.RelativeRepairComposition.SymbolicInterface
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
