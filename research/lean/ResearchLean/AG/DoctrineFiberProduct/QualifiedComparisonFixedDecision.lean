import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonInputCharacterization
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryQualifications

/-!
# Fixed comparison decisions for G-118(B2)

The generated complete geometry mate is invertible.  The proof does not infer
this from its three carrier injections: it first cancels the pulled Cartesian
route leg from the actual mate triangle, uses the independently constructed
core mate isomorphism, and then reflects the refinement inverse through the
faithful exactification bridge.

For the fixed decision datum this selects the positive B2 branch.  The general
comparison-isomorphism API then decides both stabilizers and both projections;
the named comparator pair supplies the required nonempty singleton fiber,
while the base/identity pair remains outside the comparison subgroup.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCleavage

/-- An exact complete geometry hom is invertible whenever its exact core map
and its image in refinement geometry are invertible.  The actual refinement
inverse is exactified and identified with the original hom through the
faithful exact embedding. -/
theorem geometryTotalHom_isIso_of_refinement_isIso
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : GeometryTotalHom G H)
    [IsIso (show G.core ⟶ H.core from hom.base)]
    [IsIso (show RefinementGeometryObject.mk G ⟶
      RefinementGeometryObject.mk H from
        (exactGeometryToRefinementGeometry U).map hom)] :
    IsIso (show G ⟶ H from hom) := by
  let exactified : GeometryTotalHom G H :=
    exactGeometryHomOfRefinement hom.base
      ((exactGeometryToRefinementGeometry U).map hom) rfl
  letI : IsIso (show G ⟶ H from exactified) :=
    exactGeometryHomOfRefinement_isIso hom.base
      ((exactGeometryToRefinementGeometry U).map hom) rfl
  have equality : exactified = hom := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    exact exactGeometryHomOfRefinement_toRefinement hom.base
      ((exactGeometryToRefinementGeometry U).map hom) rfl
  rw [← equality]
  infer_instance

/-- The actual generated complete mate is invertible for every compatible
input geometry.  Cartesian cancellation is performed before exactification,
so no carrierwise injectivity premise is used. -/
theorem upperGeometryMate_isIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    IsIso (show baseRouteGeometry ctx target ⟶ pulledRouteGeometry ctx target
      from upperGeometryMate ctx target) := by
  let mate : (⟨baseRouteGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
      ⟨pulledRouteGeometry ctx target⟩ :=
    (exactGeometryToRefinementGeometry U).map (upperGeometryMate ctx target)
  let pulledLeg : (⟨pulledRouteGeometry ctx target⟩ :
      RefinementGeometryCategory U) ⟶ ⟨target.geometry⟩ :=
    pulledRouteGeometryHom ctx target
  let composite : (⟨baseRouteGeometry ctx target⟩ :
      RefinementGeometryCategory U) ⟶ ⟨target.geometry⟩ := mate ≫ pulledLeg
  have compositeStrong : (refinementGeometryProjection U).IsStronglyCartesian
      (show RefinementPackageHom
        ⟨(baseRouteGeometry ctx target).core⟩ ⟨target.geometry.core⟩ from
          composite.base)
      (show (⟨baseRouteGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
        ⟨target.geometry⟩ from composite) := by
    rw [show composite =
        baseRouteGeometryHom ctx target from upperGeometryMate_fac ctx target]
    exact baseRouteGeometryHom_isStronglyCartesian ctx target
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (show RefinementPackageHom
        ⟨(baseRouteGeometry ctx target).core⟩ ⟨target.geometry.core⟩ from
          composite.base)
      (show (⟨baseRouteGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
        ⟨target.geometry⟩ from composite) := compositeStrong
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (mate.base ≫ pulledLeg.base) (mate ≫ pulledLeg) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      composite.base composite
    exact compositeStrong
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (show RefinementPackageHom
        ⟨(pulledRouteGeometry ctx target).core⟩ ⟨target.geometry.core⟩ from
          pulledLeg.base)
      (show (⟨pulledRouteGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
        ⟨target.geometry⟩ from pulledLeg) := by
    dsimp [pulledLeg]
    exact pulledRouteGeometryHom_isStronglyCartesian ctx target
  letI : (refinementGeometryProjection U).IsHomLift mate.base mate :=
    refinementGeometryHom_isHomLift mate
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      mate.base mate :=
    CategoryTheory.Functor.IsStronglyCartesian.of_comp
      (p := refinementGeometryProjection U)
      (f := mate.base) (g := pulledLeg.base) (φ := mate) (ψ := pulledLeg)
  let coreIso := generatedRouteCoreMateIso ctx target
  letI : IsIso (generatedRouteCoreMate ctx target) := by
    change IsIso coreIso.hom
    infer_instance
  letI : IsIso (show (baseRouteGeometry ctx target).core ⟶
      (pulledRouteGeometry ctx target).core from
        (upperGeometryMate ctx target).base) := by
    change IsIso ((CategoryTheory.Functor.Fiber.fiberInclusion).map
      (generatedRouteCoreMate ctx target))
    infer_instance
  letI : IsIso mate.base := by
    change IsIso ((exactPackageToRefinement U).map
      (upperGeometryMate ctx target).base)
    infer_instance
  letI : IsIso mate :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := refinementGeometryProjection U) (f := mate.base) mate
  exact geometryTotalHom_isIso_of_refinement_isIso (upperGeometryMate ctx target)

end UpperGeometryCleavage

namespace UpperGeometryCompatibleProblemInputData

/-- Every generated compatible comparison component is an isomorphism in the
complete geometry category. -/
theorem generatedCompatibleUpperGeometryMateAt_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    IsIso (show input.generatedBaseRouteGeometryAt i ⟶
      input.generatedPulledRouteGeometryAt i from
        input.generatedCompatibleUpperGeometryMateAt i) := by
  exact UpperGeometryCleavage.upperGeometryMate_isIso
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- G-118(B2) positive branch: the fixed complete comparison is an
isomorphism. -/
theorem solution_component_isIso :
    IsIso (show problem.data.generatedBaseRouteGeometryAt PUnit.unit ⟶
      problem.data.generatedPulledRouteGeometryAt PUnit.unit from
        solution.component PUnit.unit) := by
  change IsIso (show problem.data.generatedBaseRouteGeometryAt PUnit.unit ⟶
    problem.data.generatedPulledRouteGeometryAt PUnit.unit from
      problem.data.generatedCompatibleUpperGeometryMateAt PUnit.unit)
  exact problem.data.generatedCompatibleUpperGeometryMateAt_isIso PUnit.unit

/-- The fixed comparison, packaged as the actual complete geometry iso. -/
noncomputable def solutionComponentIso :
    problem.data.generatedBaseRouteGeometryAt PUnit.unit ≅
      problem.data.generatedPulledRouteGeometryAt PUnit.unit := by
  letI := solution_component_isIso
  exact asIso (solution.component PUnit.unit)

/-- G-118(B2): the fixed target comparison stabilizer is trivial. -/
theorem solution_targetStabilizer_eq_bot :
    qualifiedComparisonTargetStabilizer (solution.component PUnit.unit) = ⊥ := by
  simpa [solutionComponentIso] using
    qualifiedComparisonTargetStabilizer_eq_bot_of_iso solutionComponentIso

/-- G-118(B2): the fixed source comparison stabilizer is trivial. -/
theorem solution_sourceStabilizer_eq_bot :
    qualifiedComparisonSourceStabilizer (solution.component PUnit.unit) = ⊥ := by
  simpa [solutionComponentIso] using
    qualifiedComparisonSourceStabilizer_eq_bot_of_iso solutionComponentIso

/-- The fixed comparison subgroup is the conjugation graph of its complete
geometry isomorphism. -/
noncomputable def solutionQualifiedComparisonGraphMulEquiv :
    CompositeFiberAut
        (problem.data.generatedBaseRouteGeometryAt PUnit.unit) ≃*
      qualifiedComparisonSubgroup (solution.component PUnit.unit) := by
  simpa [solutionComponentIso] using
    qualifiedComparisonIsoGraphMulEquiv solutionComponentIso

/-- G-118(B2): every qualified source change has a target partner. -/
theorem solution_sourceProjection_surjective :
    Function.Surjective
      (qualifiedComparisonSourceProjection (solution.component PUnit.unit)) := by
  simpa [solutionComponentIso] using
    qualifiedComparisonIsoSourceProjection_surjective solutionComponentIso

/-- G-118(B2): every qualified target change has a source partner. -/
theorem solution_targetProjection_surjective :
    Function.Surjective
      (qualifiedComparisonTargetProjection (solution.component PUnit.unit)) := by
  simpa [solutionComponentIso] using
    qualifiedComparisonIsoTargetProjection_surjective solutionComponentIso

/-- The mandatory fixed generated pair belongs to the actual comparison
subgroup. -/
theorem solution_comparator_pair_mem :
    (problem.data.generatedBaseRouteComparator DecisionCell.comparison,
        problem.data.generatedPulledRouteComparator DecisionCell.comparison) ∈
      qualifiedComparisonSubgroup (solution.component PUnit.unit) := by
  exact upperDecisionSolution_comparatorDescentAt

/-- The mandatory base-comparator/identity pair does not belong to the actual
comparison subgroup. -/
theorem solution_base_identity_pair_not_mem :
    ¬ (problem.data.generatedBaseRouteComparator DecisionCell.comparison, 1) ∈
      qualifiedComparisonSubgroup (solution.component PUnit.unit) := by
  simpa [UpperGeometryCompatibleProblemInputData.GeneratedQualifiedComparisonRelation]
    using generatedQualifiedComparisonRelation_base_identity_not

/-- The fixed pulled comparator is nonidentity; otherwise the positive named
pair would be the fixed negative base/identity pair. -/
theorem generated_pulled_comparator_ne_one :
    problem.data.generatedPulledRouteComparator DecisionCell.comparison ≠ 1 := by
  intro equality
  apply solution_base_identity_pair_not_mem
  rw [← equality]
  exact solution_comparator_pair_mem

/-- The nonempty target-partner fiber over `b_*` is a singleton.  Existence is
the actual `p_*`; uniqueness follows by cancelling the now-proved isomorphic
comparison. -/
theorem solution_baseComparator_targetPartner_existsUnique :
    ∃! pulled : CompositeFiberAut
        (problem.data.generatedPulledRouteGeometryAt PUnit.unit),
      (problem.data.generatedBaseRouteComparator DecisionCell.comparison,
          pulled) ∈
        qualifiedComparisonSubgroup (solution.component PUnit.unit) := by
  refine ⟨problem.data.generatedPulledRouteComparator DecisionCell.comparison,
    solution_comparator_pair_mem, ?_⟩
  intro pulled relation
  let named : QualifiedComparisonTargetLift (solution.component PUnit.unit)
      (problem.data.generatedBaseRouteComparator DecisionCell.comparison) :=
    ⟨problem.data.generatedPulledRouteComparator DecisionCell.comparison,
      solution_comparator_pair_mem⟩
  let candidate : QualifiedComparisonTargetLift (solution.component PUnit.unit)
      (problem.data.generatedBaseRouteComparator DecisionCell.comparison) :=
    ⟨pulled, relation⟩
  obtain ⟨stabilizer, action⟩ :=
    qualifiedComparisonTargetLiftAction_transitive named candidate
  have stabilizerValue : stabilizer.1 = 1 := by
    have memBottom : stabilizer.1 ∈ (⊥ : Subgroup
        (CompositeFiberAut
          (problem.data.generatedPulledRouteGeometryAt PUnit.unit))) := by
      rw [← solution_targetStabilizer_eq_bot]
      exact stabilizer.2
    simpa using memBottom
  have stabilizerIdentity : stabilizer = 1 := Subtype.ext stabilizerValue
  rw [stabilizerIdentity, one_smul] at action
  exact (congrArg Subtype.val action).symm

/-- Symmetrically, the nonempty source-partner fiber over `p_*` is a
singleton with named point `b_*`. -/
theorem solution_pulledComparator_sourcePartner_existsUnique :
    ∃! base : CompositeFiberAut
        (problem.data.generatedBaseRouteGeometryAt PUnit.unit),
      (base, problem.data.generatedPulledRouteComparator
          DecisionCell.comparison) ∈
        qualifiedComparisonSubgroup (solution.component PUnit.unit) := by
  refine ⟨problem.data.generatedBaseRouteComparator DecisionCell.comparison,
    solution_comparator_pair_mem, ?_⟩
  intro base relation
  let named : QualifiedComparisonSourceLift (solution.component PUnit.unit)
      (problem.data.generatedPulledRouteComparator DecisionCell.comparison) :=
    ⟨problem.data.generatedBaseRouteComparator DecisionCell.comparison,
      solution_comparator_pair_mem⟩
  let candidate : QualifiedComparisonSourceLift (solution.component PUnit.unit)
      (problem.data.generatedPulledRouteComparator DecisionCell.comparison) :=
    ⟨base, relation⟩
  obtain ⟨stabilizer, action⟩ :=
    qualifiedComparisonSourceLiftAction_transitive named candidate
  have stabilizerValue : stabilizer.1 = 1 := by
    have memBottom : stabilizer.1 ∈ (⊥ : Subgroup
        (CompositeFiberAut
          (problem.data.generatedBaseRouteGeometryAt PUnit.unit))) := by
      rw [← solution_sourceStabilizer_eq_bot]
      exact stabilizer.2
    simpa using memBottom
  have stabilizerIdentity : stabilizer = 1 := Subtype.ext stabilizerValue
  rw [stabilizerIdentity, one_smul] at action
  exact (congrArg Subtype.val action).symm

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
