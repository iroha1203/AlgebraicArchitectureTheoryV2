import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF13
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleDecisionFixtures

/-!
# Fixed source-presentation firing

This module instantiates the revision-2 source-presentation change with the
actual horizontal transposition of the finite decision fixture.  The selected
core and complete-geometry isomorphisms are reconstructed from `swap01Total`;
no changed input or induced-action inequality is supplied as data.

The induced source-pair action is then evaluated on the authored comparator
`compositeSwap12`.  Conjugation by `swap01` fixes the concrete local axis value
`1`, whereas the original comparator sends it to `2`, so the generated action
is genuinely nontrivial on the required local `Fin 4` carrier.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open UpperGeometryCompatibleProblemInputData

set_option maxHeartbeats 4000000

namespace UpperDecisionWitness

/-- The horizontal core map as an actual endomorphism in the selected target
fiber. -/
noncomputable def swap01CoreFiberHom : coreObject ⟶ coreObject := by
  letI : (packageProjection FiniteModel.carrier).IsHomLift
      (𝟙 activeReverseTargetPoint) swap01Total.base :=
    CategoryTheory.IsHomLift.of_commsq
      (packageProjection FiniteModel.carrier)
      (𝟙 activeReverseTargetPoint) swap01Total.base
      coreObject.2 coreObject.2 (by rfl)
  exact ⟨swap01Total.base, inferInstance⟩

/-- The involutive horizontal core map as a core-fiber automorphism. -/
noncomputable def swap01CoreFiberIso : coreObject ≅ coreObject where
  hom := swap01CoreFiberHom
  inv := swap01CoreFiberHom
  hom_inv_id := by
    apply Subtype.ext
    exact congrArg (fun hom => hom.base) swap01Total_square
  inv_hom_id := by
    apply Subtype.ext
    exact congrArg (fun hom => hom.base) swap01Total_square

/-- The fixed source-presentation change induced by the actual horizontal
complete-geometry automorphism. -/
noncomputable def swap01SourcePresentationChange :
    UpperGeometryCompatibleSourcePresentationChange problemData where
  sourceFiber _ := coreObject
  sourceGeometry _ := sourceGeometry PUnit.unit
  coreIso _ := swap01CoreFiberIso
  geometryIso _ := swap01Iso
  geometryIso_hom_base _ := rfl
  geometryIso_inv_base _ := rfl
  geometryIso_hom_coefficient_id _ := rfl
  geometryIso_inv_coefficient_id _ := rfl

/-- Core permutations keep the distinguished context object definitionally
fixed while acting on its local carriers. -/
@[simp] theorem contextForward_corePermutation_base
    (permutation : Equiv.Perm (Fin 4)) :
    contextForward (corePermutationTotal permutation)
        (⟨baseContext⟩ : package.site.category) =
      (⟨baseContext⟩ : package.site.category) := by
  rfl

/-- A composite of core permutations likewise keeps the distinguished
context object fixed. -/
@[simp] theorem contextForward_corePermutation_comp_base
    (first second : Equiv.Perm (Fin 4)) :
    contextForward ((corePermutationTotal first).comp
        (corePermutationTotal second))
        (⟨baseContext⟩ : package.site.category) =
      (⟨baseContext⟩ : package.site.category) := by
  rfl

/-- Conjugating the authored comparator by the horizontal complete-geometry
automorphism fixes the distinguished local axis value `1`. -/
theorem swap01_conjugated_comparator_local_axis_fixes_one :
    HEq ((CompositeFiberAut.hom
      (CompositeFiberAut.conjugationMulEquiv swap01Iso
        compositeSwap12)).geometry.axisComp
          (⟨baseContext⟩ : package.site.category) (1 : Fin 4)) (1 : Fin 4) := by
  change HEq
    (localAxisPermutation swap01
      (contextForward
        ((corePermutationTotal swap01).comp (corePermutationTotal swap12))
        (⟨baseContext⟩ : package.site.category))
      (localAxisPermutation swap12
        (contextForward (corePermutationTotal swap01)
          (⟨baseContext⟩ : package.site.category))
        (localAxisPermutation swap01
          (⟨baseContext⟩ : package.site.category) (1 : Fin 4))))
    (1 : Fin 4)
  have hSingle :=
    congrArg (fun W : package.site.category => W.ctx)
      (contextForward_corePermutation_base swap01)
  have hComposite :=
    congrArg (fun W : package.site.category => W.ctx)
      (contextForward_corePermutation_comp_base swap01 swap12)
  simp [localAxisPermutation, swap01, swap12]
  rfl

/-- The first component of the actual generated source-pair action has the
same concrete local-axis evaluation. -/
theorem swap01_induced_source_pair_local_axis_fixes_one :
    HEq ((CompositeFiberAut.hom
      ((swap01SourcePresentationChange.generatedSourcePairMulEquivAt
        PUnit.unit (compositeSwap12, 1)).1)).geometry.axisComp
          (⟨baseContext⟩ : package.site.category) (1 : Fin 4)) (1 : Fin 4) := by
  change HEq ((CompositeFiberAut.hom
    (CompositeFiberAut.conjugationMulEquiv swap01Iso
      compositeSwap12)).geometry.axisComp
        (⟨baseContext⟩ : package.site.category) (1 : Fin 4)) (1 : Fin 4)
  exact swap01_conjugated_comparator_local_axis_fixes_one

/-- The authored comparator itself sends the same local axis value from `1`
to `2`. -/
theorem compositeSwap12_local_axis_fires :
    (CompositeFiberAut.hom compositeSwap12).geometry.axisComp
        (⟨baseContext⟩ : package.site.category) (1 : Fin 4) = (2 : Fin 4) := by
  simpa [sourceTransport] using authored_comparator_local_axis_fires

/-- The fixed horizontal presentation change acts nontrivially on the concrete
source pair consisting of the authored comparator and the identity. -/
theorem swap01_induced_source_pair_action_ne :
    swap01SourcePresentationChange.generatedSourcePairMulEquivAt PUnit.unit
        (compositeSwap12, 1) ≠
      (compositeSwap12, 1) := by
  intro equality
  have firstEquality := congrArg Prod.fst equality
  have fixed := swap01_induced_source_pair_local_axis_fixes_one
  rw [firstEquality] at fixed
  rw [compositeSwap12_local_axis_fires] at fixed
  exact (by decide : (2 : Fin 4) ≠ 1) (eq_of_heq fixed)

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
