import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationExactness
import ResearchLean.AG.GeometryTransport.FiniteWitnesses

/-!
# Finite boundary witness for realization-exact upper equivalence

The G-108 negative core hom has an involutive Atom map, but its full upper map
normalizes arbitrary architecture objects and is not injective.  Consequently
it cannot be the forward map of the exact upper equivalence required by the
revision-5 GOAL.  This is stronger than failure of realization-exactness: the
requested negative upper-equivalence fixture itself cannot be formed.
-/

namespace AAT.AG.DoctrineFiberProduct

open AtomFoundation GeometryTransport
open AAT.AG.ReadingFunctorialityFinite

/-- First architecture object used to expose loss of object-level data. -/
noncomputable def negativeUpperUnitObject : ArchitectureObject FiniteModel.carrier where
  configuration := exactSourceCore.object.configuration
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- A second object with the same configuration but a genuinely different
structure-map carrier. -/
noncomputable def negativeUpperBoolObject : ArchitectureObject FiniteModel.carrier where
  configuration := exactSourceCore.object.configuration
  StructureMaps := Bool
  SelectedQuantities := PUnit
  structureMaps := false
  selectedQuantities := PUnit.unit

theorem negativeUpperUnitObject_ne_boolObject :
    negativeUpperUnitObject ≠ negativeUpperBoolObject := by
  intro hobjects
  have htypes := congrArg ArchitectureObject.StructureMaps hobjects
  let e : PUnit ≃ Bool := Equiv.cast htypes
  have htruefalse : true = false := by
    calc
      true = e (e.symm true) := (e.apply_symm_apply true).symm
      _ = e (e.symm false) := by
        exact congrArg e (Subsingleton.elim _ _)
      _ = false := e.apply_symm_apply false
  exact Bool.noConfusion htruefalse

/-- The negative upper map collapses the two distinct architecture objects. -/
theorem negativeCoreUpper_objectMap_not_injective :
    ¬ Function.Injective NegativeGeometryWitness.coreHom.upper.objectMap := by
  intro hinjective
  apply negativeUpperUnitObject_ne_boolObject
  apply hinjective
  rfl

/-- No exact upper equivalence can have the G-108 negative upper map as its
forward component.  The forward/backward cancellation would make the forward
object map injective, contradicting the explicit object collapse above. -/
theorem no_negativeExactUpperEquivalence :
    ¬ ∃ e : ExactUpperEquivalence exactSourceCore exactTargetCore,
      e.forward = NegativeGeometryWitness.coreHom.upper := by
  rintro ⟨e, hforward⟩
  apply negativeCoreUpper_objectMap_not_injective
  intro A B hAB
  have hAB' : e.forward.objectMap A = e.forward.objectMap B := by
    rw [hforward]
    exact hAB
  have hmaps := congrArg SignedExactCoreReadingHom.objectMap
    e.forward_backward
  have hleft (X : ArchitectureObject FiniteModel.carrier) :
      e.backward.objectMap (e.forward.objectMap X) = X := by
    exact congrFun hmaps X
  calc
    A = e.backward.objectMap (e.forward.objectMap A) := (hleft A).symm
    _ = e.backward.objectMap (e.forward.objectMap B) := congrArg _ hAB'
    _ = B := hleft B

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
