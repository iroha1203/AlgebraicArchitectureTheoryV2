import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.LinearInterface

/-!
# Effective projection as the full native cokernel

## Implementation notes

The generated section gives a normal-form vector for each original cokernel
class. All quotient classes are retained: equality is tested by the computed
projection, and the native quotient is linearly identified with its full image.
-/
namespace AAT.AG.RelativeRepairComposition.LinearInterface
universe uk ux uv
variable {k : Type uk} [Field k]
variable {X : Type ux} {V : Type uv}
variable [AddCommGroup X] [Module k X] [AddCommGroup V] [Module k V]
variable (D : X →ₗ[k] V) (σ : V →ₗ[k] X) (hσ : ∀ x, D (σ (D x)) = D x)

/-- The computed normal form descends to the entire native original cokernel. -/
def quotientProjection : (V ⧸ LinearMap.range D) →ₗ[k] LinearMap.range (projection D σ) :=
  (LinearMap.range D).liftQ (projection D σ).rangeRestrict (by
    rintro v ⟨x,rfl⟩
    apply Subtype.ext
    exact projection_D D σ hσ x)

/-- Every original class has exactly its computed normal-form vector. -/
theorem quotient_projection_mk (v : V) :
    (quotientProjection D σ hσ (q D v)).1 = projection D σ v := rfl

/-- The computed normal form retains every distinction of the full original cokernel. -/
theorem quotient_projection_injective : Function.Injective (quotientProjection D σ hσ) := by
  intro y y' he
  induction y using Quotient.inductionOn' with
  | h v =>
    induction y' using Quotient.inductionOn' with
    | h v' =>
      exact (q_eq_iff_projection_eq D σ hσ v v').mpr (congrArg Subtype.val he)

/-- Every computed projection-image vector is a native original cokernel class. -/
theorem quotient_projection_surjective : Function.Surjective (quotientProjection D σ hσ) := by
  rintro ⟨v,x,hx⟩
  exact ⟨q D x,Subtype.ext hx⟩

/-- The complete native original cokernel is the generated normal-form image. -/
noncomputable def quotientEquivalence : (V ⧸ LinearMap.range D) ≃ₗ[k] LinearMap.range (projection D σ) :=
  LinearEquiv.ofBijective (quotientProjection D σ hσ)
    ⟨quotient_projection_injective D σ hσ,quotient_projection_surjective D σ hσ⟩

end AAT.AG.RelativeRepairComposition.LinearInterface

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
