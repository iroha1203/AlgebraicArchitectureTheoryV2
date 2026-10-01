import ResearchLean.AG.RelativeRepairComposition.LinearInterfaceAction

/-!
# One symbolic relation and all of its parameter fibres

## Implementation notes

The public linear map includes the parameter as an external coordinate before
any value is substituted. The same internal differential and generated section
serve every fibre. Evaluation retains all public values and the entire internal
kernel. Existence may differ between fibres; no map between successful repairs
at arbitrary different parameter values is asserted.
-/
namespace AAT.AG.RelativeRepairComposition.SymbolicInterface
open CategoryTheory
open LinearInterface
universe uk ux uz uv up
variable {k : Type uk} [Field k]
variable {X : Type ux} {Z : Type uz} {V : Type uv} {P : Type up}
variable [AddCommGroup X] [Module k X] [AddCommGroup Z] [Module k Z]
variable [AddCommGroup V] [Module k V] [AddCommGroup P] [Module k P]
variable (D : X →ₗ[k] V) (F : Z →ₗ[k] V) (σ : V →ₗ[k] X)
variable (B : P →ₗ[k] V) (r : V)

/-- Before evaluation, the public relation includes the full external parameter coordinate. -/
def publicMap : (Z × P) →ₗ[k] V := F.comp (LinearMap.fst k Z P) - B.comp (LinearMap.snd k Z P)

/-- Evaluation changes only the affine right-hand side. -/
def rhs (v : P) : V := r + B v

/-- The pre-evaluation cokernel equation and every evaluated equation have exactly the same test. -/
theorem relation_evaluation (v : P) (z : Z) :
    (z,v) ∈ Relation D (publicMap F B) σ r ↔ z ∈ Relation D F σ (rhs B r v) := by
  change projection D σ (F z - B v) = projection D σ r ↔
    projection D σ (F z) = projection D σ (r + B v)
  rw [map_sub, map_add]
  exact sub_eq_iff_eq_add

/-- A fibre retains the same public coordinate, with its parameter fixed to the evaluated value. -/
abbrev RelationFiber (v : P) := {z : Z // (z,v) ∈ Relation D (publicMap F B) σ r}

/-- Both directions of public evaluation retain every original public value. -/
def relationFiberEquiv (v : P) : RelationFiber D F σ B r v ≃ ↥(Relation D F σ (rhs B r v)) where
  toFun z := ⟨z.1,(relation_evaluation D F σ B r v z.1).mp z.2⟩
  invFun z := ⟨z.1,(relation_evaluation D F σ B r v z.1).mpr z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Evaluation retains every vector in the original internal kernel. -/
def coordinateFiberEquiv (v : P) :
    (RelationFiber D F σ B r v × LinearMap.ker D) ≃ Coordinates D F σ (rhs B r v) :=
  Equiv.prodCongr (relationFiberEquiv D F σ B r v) (Equiv.refl _)

/-- Independent pre-elimination solutions are restricted only by their actual parameter coordinate. -/
abbrev SolutionFiber (v : P) := {s : Solution D (publicMap F B) r // s.1.2.2 = v}

/-- Both directions of independent solution evaluation retain every private and public value. -/
def solutionFiberEquiv (v : P) : SolutionFiber D F B r v ≃ Solution D F (rhs B r v) where
  toFun s := ⟨(s.1.1.1,s.1.1.2.1),by
    have hs := s.1.2
    change D s.1.1.1 + (F s.1.1.2.1 - B s.1.1.2.2) = r at hs
    rw [s.2] at hs
    change D s.1.1.1 + F s.1.1.2.1 = r + B v
    exact (sub_eq_iff_eq_add.mp (by simpa only [add_sub_assoc] using hs))⟩
  invFun s := ⟨⟨(s.1.1,(s.1.2,v)),by
    change D s.1.1 + (F s.1.2 - B v) = r
    rw [← add_sub_assoc,s.2]
    exact add_sub_cancel_right r (B v)⟩,rfl⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact s.2.symm
  right_inv s := Subtype.ext rfl

/-- The symbolic section residual is the same actual vector as the evaluated residual. -/
theorem section_residual_evaluation (v : P) (z : Z) :
    σ (r - publicMap F B (z,v)) = σ (rhs B r v - F z) := by
  congr 1
  change r - (F z - B v) = r + B v - F z
  abel

/-- Full reconstruction evaluates the same section plus every retained internal-kernel vector. -/
theorem reconstruction_evaluation (v : P) (z : RelationFiber D F σ B r v) (w : LinearMap.ker D) :
    (rec D (publicMap F B) σ r (⟨(z.1,v),z.2⟩,w)).1 =
      ((rec D F σ (rhs B r v) (coordinateFiberEquiv D F σ B r v (z,w))).1.1,(z.1,v)) := by
  apply Prod.ext
  · change σ (r - publicMap F B (z.1,v)) + w.1 = σ (rhs B r v - F z.1) + w.1
    rw [section_residual_evaluation]
  · rfl

/-- The full kernel coordinate extraction commutes with evaluation of each independent solution fibre. -/
theorem kernel_coordinate_evaluation (hσ : ∀ x, D (σ (D x)) = D x)
    (v : P) (s : SolutionFiber D F B r v) :
    (coord D (publicMap F B) σ hσ r s.1).2 =
      (coord D F σ hσ (rhs B r v) (solutionFiberEquiv D F B r v s)).2 := by
  apply Subtype.ext
  change s.1.1.1 - σ (r - publicMap F B s.1.1.2) =
    s.1.1.1 - σ (rhs B r v - F s.1.1.2.1)
  have hp : s.1.1.2 = (s.1.1.2.1,v) := Prod.ext rfl s.2
  rw [hp, section_residual_evaluation]

end AAT.AG.RelativeRepairComposition.SymbolicInterface
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
