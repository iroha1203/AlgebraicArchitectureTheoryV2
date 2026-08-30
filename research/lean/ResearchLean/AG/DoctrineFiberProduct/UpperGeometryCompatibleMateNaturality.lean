import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryEdges

/-!
# Canonical mate naturality on generated compatible routes

The G-114 core mate is conjugated onto the two generated route diagrams and
identified with the pointwise G-115 geometry mate.  Combining that core
naturality with the complete edge factor laws yields route-between edge
naturality without a caller-supplied route transport or naturality equation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The canonical G-115 complete geometry mate at one compatible vertex. -/
noncomputable def generatedCompatibleUpperGeometryMateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.upperGeometryMate
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The compatible pointwise mate projects to the generated exact core mate. -/
@[simp] theorem generatedCompatibleUpperGeometryMateAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedCompatibleUpperGeometryMateAt i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1 := rfl

/-- The compatible pointwise mate satisfies the full geometry route triangle. -/
theorem generatedCompatibleUpperGeometryMateAt_triangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedCompatibleUpperGeometryMateAt i))
        (input.generatedPulledRouteLegAt i) =
      input.generatedBaseRouteLegAt i := by
  exact UpperGeometryCleavage.upperGeometryMate_fac
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The actual G-114 core mate conjugated onto the generated route diagrams. -/
noncomputable def generatedCompatibleConjugateCoreMateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedBaseRouteCoreDiagram.obj ⟨i⟩) ⟶
      (input.generatedPulledRouteCoreDiagram.obj ⟨i⟩) :=
  (input.generatedBaseRouteCoreIsoAt i).hom ≫
    ctx.mate.app (input.sourceFiberDiagram.obj ⟨i⟩) ≫
      (input.generatedPulledRouteCoreIsoAt i).inv

/-- Refinement embedding identifies the conjugated G-114 component with the
mate transported by the route comparisons. -/
theorem generatedCompatibleConjugateCoreMateAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (input.generatedCompatibleConjugateCoreMateAt i).1 =
      UpperGeometryCleavage.transportedG114RefinementMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i) := by
  unfold generatedCompatibleConjugateCoreMateAt
    generatedBaseRouteCoreIsoAt generatedPulledRouteCoreIsoAt
  change (exactPackageToRefinement U).map
      (UpperGeometryCleavage.baseRouteComparisonCoreHom
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1 ≫
    (exactPackageToRefinement U).map
      (ctx.mate.app (input.sourceFiberDiagram.obj ⟨i⟩)).1 ≫
    (exactPackageToRefinement U).map
      (UpperGeometryCleavage.pulledRouteComparisonCoreInv
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1 = _
  rw [UpperGeometryCleavage.baseRouteComparisonCoreHom_toRefinement,
    UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
  rfl

/-- The conjugated actual G-114 component is the pointwise generated exact
core mate. -/
theorem generatedCompatibleConjugateCoreMateAt_eq_generated
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedCompatibleConjugateCoreMateAt i =
      UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  apply exactPackageToRefinement_map_injective
  change (exactPackageToRefinement U).map
      (input.generatedCompatibleConjugateCoreMateAt i).1 =
    (exactPackageToRefinement U).map
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1
  rw [input.generatedCompatibleConjugateCoreMateAt_toRefinement,
    UpperGeometryCleavage.generatedRouteCoreMate_toRefinement,
    UpperGeometryCleavage.transportedG114RefinementMate_eq_generated]

/-- The conjugated G-114 core mate is natural along every presented path. -/
theorem generatedCompatibleConjugateCoreMateAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    input.generatedBaseRouteCoreDiagram.map path ≫
        input.generatedCompatibleConjugateCoreMateAt j =
      input.generatedCompatibleConjugateCoreMateAt i ≫
        input.generatedPulledRouteCoreDiagram.map path := by
  dsimp [generatedBaseRouteCoreDiagram, generatedPulledRouteCoreDiagram,
    generatedCompatibleConjugateCoreMateAt]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [ActiveRefinementBCContext.baseCoreDiagram,
    ActiveRefinementBCContext.pulledCoreDiagram, Functor.comp_map]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg
      (fun hom => (input.generatedBaseRouteCoreIsoAt i).hom ≫ hom ≫
        (input.generatedPulledRouteCoreIsoAt j).inv)
      (ctx.mate.naturality (input.sourceFiberDiagram.map path))

/-- The pointwise generated exact core mate is natural on the two generated
route diagrams. -/
theorem generatedCompatibleRouteCoreMateAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    input.generatedBaseRouteCoreDiagram.map path ≫
        UpperGeometryCleavage.generatedRouteCoreMate
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨j⟩))
          (input.sourceTargetGeometryAt j) =
      UpperGeometryCleavage.generatedRouteCoreMate
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i) ≫
        input.generatedPulledRouteCoreDiagram.map path := by
  rw [← input.generatedCompatibleConjugateCoreMateAt_eq_generated i,
    ← input.generatedCompatibleConjugateCoreMateAt_eq_generated j]
  exact input.generatedCompatibleConjugateCoreMateAt_naturality path

/-- The complete generated geometry mate is natural on every authored source
edge, with no caller-supplied route naturality certificate. -/
theorem generatedCompatibleUpperGeometryMateAt_edge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.generatedBaseRouteGeometryEdge edge).comp
        (input.generatedCompatibleUpperGeometryMateAt j) =
      (input.generatedCompatibleUpperGeometryMateAt i).comp
        (input.generatedPulledRouteGeometryEdge edge) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  let left := (exactGeometryToRefinementGeometry U).map
    ((input.generatedBaseRouteGeometryEdge edge).comp
      (input.generatedCompatibleUpperGeometryMateAt j))
  let right := (exactGeometryToRefinementGeometry U).map
    ((input.generatedCompatibleUpperGeometryMateAt i).comp
      (input.generatedPulledRouteGeometryEdge edge))
  have hcore := input.generatedCompatibleRouteCoreMateAt_naturality
    (presentedEdgePath edge)
  have hleftBase : left.base =
      (exactPackageToRefinement U).map
        ((input.generatedBaseRouteGeometryEdge edge).comp
          (input.generatedCompatibleUpperGeometryMateAt j)).base := rfl
  have hrightBase : right.base =
      (exactPackageToRefinement U).map
        ((input.generatedBaseRouteGeometryEdge edge).comp
          (input.generatedCompatibleUpperGeometryMateAt j)).base := by
    change (exactPackageToRefinement U).map
        ((input.generatedCompatibleUpperGeometryMateAt i).base ≫
          (input.generatedPulledRouteGeometryEdge edge).base) =
      (exactPackageToRefinement U).map
        ((input.generatedBaseRouteGeometryEdge edge).base ≫
          (input.generatedCompatibleUpperGeometryMateAt j).base)
    apply congrArg (exactPackageToRefinement U).map
    simpa only [generatedBaseRouteGeometryEdge_base,
      generatedPulledRouteGeometryEdge_base,
      generatedCompatibleUpperGeometryMateAt_base] using
        congrArg (fun f => f.1) hcore.symm
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      ((exactPackageToRefinement U).map
        ((input.generatedBaseRouteGeometryEdge edge).comp
          (input.generatedCompatibleUpperGeometryMateAt j)).base)
      left hleftBase
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      ((exactPackageToRefinement U).map
        ((input.generatedBaseRouteGeometryEdge edge).comp
          (input.generatedCompatibleUpperGeometryMateAt j)).base)
      right hrightBase
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian j
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt j).base
    (input.generatedPulledRouteLegAt j)
    ((exactPackageToRefinement U).map
      ((input.generatedBaseRouteGeometryEdge edge).comp
        (input.generatedCompatibleUpperGeometryMateAt j)).base)
  change RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteGeometryEdge edge))
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedCompatibleUpperGeometryMateAt j)))
      (input.generatedPulledRouteLegAt j) =
    RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedCompatibleUpperGeometryMateAt i))
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge)))
      (input.generatedPulledRouteLegAt j)
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
  rw [input.generatedCompatibleUpperGeometryMateAt_triangle j]
  rw [input.generatedBaseRouteGeometryEdge_fac edge]
  rw [input.generatedPulledRouteGeometryEdge_fac edge]
  rw [← UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    input.generatedCompatibleUpperGeometryMateAt_triangle i]

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
