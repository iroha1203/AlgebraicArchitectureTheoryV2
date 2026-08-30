import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteCoreNaturality

/-!
# Exactification of G-115 refinement-geometry maps

The cartesian universal property used to generate finite route edges lives in
the refinement-geometry category.  When its lower package map is the exact
embedding of a `PackageTotalHom`, this module recovers the corresponding exact
`GeometryTotalHom` without changing the completed predecessor APIs.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence

namespace UpperGeometryCleavage

set_option maxHeartbeats 3000000

/-- Composition of complete refinement-geometry maps is associative as a
structure-level equality. -/
theorem refinementGeometryHom_comp_assoc
    {U : AtomCarrier.{u}} {G H K L : GeometryPackage.{u, v} U}
    (F : RefinementGeometryHom G H) (T : RefinementGeometryHom H K)
    (S : RefinementGeometryHom K L) :
    (F.comp T).comp S = F.comp (T.comp S) := by
  apply RefinementGeometryHom.ext
  · apply RefinementPackageHom.ext
    · rfl
    · exact PackageTotalHom.upper_comp_assoc
        F.base.upper T.base.upper S.base.upper
  · apply heq_of_eq
    apply RefinementGeomReadHom.ext <;> rfl

/-- Recover an exact geometry reading from a refinement-geometry reading whose
lower map is the exact embedding of the supplied package map. -/
noncomputable def exactGeomReadHomOfRefinement
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (hom : RefinementGeometryHom G H)
    (hbase : hom.base = (exactPackageToRefinement U).map f) :
    GeomReadHom G H f := by
  let geometry : RefinementGeomReadHom G H
      ((exactPackageToRefinement U).map f) := hbase ▸ hom.geometry
  exact {
    coverage := {
      requiredSupport := geometry.coverage.requiredSupport
      requiredEquationCoordinate := geometry.coverage.requiredEquationCoordinate
      selectedViolationWitness := geometry.coverage.selectedViolationWitness
      requiredAxis := geometry.coverage.requiredAxis
      supportVisibleOn := geometry.coverage.supportVisibleOn
      equationCoordinateVisibleOn := geometry.coverage.equationCoordinateVisibleOn
      violationWitnessVisibleOn := geometry.coverage.violationWitnessVisibleOn
      axisReadableOn := geometry.coverage.axisReadableOn
      boundaryVisibleOn := geometry.coverage.boundaryVisibleOn
    }
    overlap := { overlapIso := geometry.overlap.overlapIso }
    coefficientHom := geometry.coefficientHom
    raw_eq := by simpa [refinementRawTransport] using geometry.raw_eq
    supportComp := geometry.supportComp
    axisComp := geometry.axisComp
    observableComp := geometry.observableComp
    supportReads := geometry.supportReads
    axisReads := geometry.axisReads
    observableReads := geometry.observableReads
    support_naturality := geometry.support_naturality
    axis_naturality := geometry.axis_naturality
    observable_naturality := geometry.observable_naturality
  }

/-- Exactify a complete refinement-geometry map over a specified exact lower
package map. -/
noncomputable def exactGeometryHomOfRefinement
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (hom : RefinementGeometryHom G H)
    (hbase : hom.base = (exactPackageToRefinement U).map f) :
    GeometryTotalHom G H where
  base := f
  geometry := exactGeomReadHomOfRefinement f hom hbase

@[simp] theorem exactGeometryHomOfRefinement_base
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (hom : RefinementGeometryHom G H)
    (hbase : hom.base = (exactPackageToRefinement U).map f) :
    (exactGeometryHomOfRefinement f hom hbase).base = f := rfl

/-- Re-embedding the exactification recovers the complete original
refinement-geometry map, including coefficient and local reading data. -/
theorem exactGeometryHomOfRefinement_toRefinement
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (hom : RefinementGeometryHom G H)
    (hbase : hom.base = (exactPackageToRefinement U).map f) :
    (exactGeometryToRefinementGeometry U).map
        (exactGeometryHomOfRefinement f hom hbase) = hom := by
  cases hom with
  | mk base geometry =>
    dsimp at hbase ⊢
    subst base
    apply RefinementGeometryHom.ext
    · rfl
    · apply heq_of_eq
      apply RefinementGeomReadHom.ext <;> rfl

/-- Every refinement-geometry morphism is tautologically a lift of its own
projection. -/
theorem refinementGeometryHom_isHomLift
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : RefinementGeometryHom G H) :
    (refinementGeometryProjection U).IsHomLift hom.base hom := by
  apply CategoryTheory.IsHomLift.of_fac'
    (refinementGeometryProjection U) hom.base hom rfl rfl
  rfl

/-- A refinement-geometry morphism is a lift over any propositionally equal
description of its projection. -/
theorem refinementGeometryHom_isHomLift_of_base_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨G.core⟩ ⟨H.core⟩)
    (hom : RefinementGeometryHom G H) (hbase : hom.base = g) :
    (refinementGeometryProjection U).IsHomLift g hom := by
  apply CategoryTheory.IsHomLift.of_fac'
    (refinementGeometryProjection U) g hom rfl rfl
  simpa using hbase

end UpperGeometryCleavage

namespace UpperRefinementBCProblemData

set_option maxHeartbeats 3000000

/-- The exact base-route edge transported to generated endpoints factors the
generated route leg through the actual common-source edge. -/
theorem generatedBaseCoreEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (exactPackageToRefinement U).map
        (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge)).1 ≫
        (UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)).base =
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base ≫
        (exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base := by
  change ((exactPackageToRefinement U).map
      ((problem.generatedBaseCoreIsoAt i).hom.1 ≫
        ((ctx.baseCoreDiagram problem.sourceFiberDiagram).map
          (presentedEdgePath edge)).1 ≫
        (problem.generatedBaseCoreIsoAt j).inv.1) ≫ _) = _
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [generatedBaseCoreIsoAt,
    UpperGeometryCleavage.baseRouteComparisonCoreIso]
  rw [show ((ctx.baseCoreDiagram problem.sourceFiberDiagram).map
      (presentedEdgePath edge)).1 =
      (problem.baseTransport.edgeLift edge).base by
        exact (problem.baseTransport.edge_base edge).symm]
  have hInv : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.baseRouteComparisonCoreInv
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)).1 ≫
        (UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)).base =
      ctx.baseCompositeLegAt (problem.sourceFiberDiagram.obj ⟨j⟩) := by
    rw [UpperGeometryCleavage.baseRouteComparisonCoreInv_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, generatedTargetGeometryAt,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonInv_fac
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)
  have hNat := problem.base_naturality_projection edge
  change (exactPackageToRefinement U).map
      (problem.baseTransport.edgeLift edge).base ≫
      ctx.baseCompositeLegAt (problem.sourceFiberDiagram.obj ⟨j⟩) =
    ctx.baseCompositeLegAt (problem.sourceFiberDiagram.obj ⟨i⟩) ≫
      (exactPackageToRefinement U).map
        (problem.sourceTransport.edgeLift edge).base at hNat
  have hHom : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.baseRouteComparisonCoreHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)).1 ≫
        ctx.baseCompositeLegAt (problem.sourceFiberDiagram.obj ⟨i⟩) =
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base := by
    rw [UpperGeometryCleavage.baseRouteComparisonCoreHom_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, generatedTargetGeometryAt,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonHom_fac
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)
  simp only [Category.assoc]
  rw [hInv, hNat]
  rw [← Category.assoc, hHom]

/-- The exact pulled-route edge transported to generated endpoints factors the
generated route leg through the actual common-source edge. -/
theorem generatedPulledCoreEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (exactPackageToRefinement U).map
        (problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)).1 ≫
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)).base =
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base ≫
        (exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base := by
  change ((exactPackageToRefinement U).map
      ((problem.generatedPulledCoreIsoAt i).hom.1 ≫
        ((ctx.pulledCoreDiagram problem.sourceFiberDiagram).map
          (presentedEdgePath edge)).1 ≫
        (problem.generatedPulledCoreIsoAt j).inv.1) ≫ _) = _
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [generatedPulledCoreIsoAt,
    UpperGeometryCleavage.pulledRouteComparisonCoreIso]
  rw [show ((ctx.pulledCoreDiagram problem.sourceFiberDiagram).map
      (presentedEdgePath edge)).1 =
      (problem.pulledTransport.edgeLift edge).base by
        exact (problem.pulledTransport.edge_base edge).symm]
  have hInv : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.pulledRouteComparisonCoreInv
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)).1 ≫
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)).base =
      ctx.pulledCompositeLegAt (problem.sourceFiberDiagram.obj ⟨j⟩) := by
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, generatedTargetGeometryAt,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonInv_fac
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)
  have hNat := problem.pulled_naturality_projection edge
  change (exactPackageToRefinement U).map
      (problem.pulledTransport.edgeLift edge).base ≫
      ctx.pulledCompositeLegAt (problem.sourceFiberDiagram.obj ⟨j⟩) =
    ctx.pulledCompositeLegAt (problem.sourceFiberDiagram.obj ⟨i⟩) ≫
      (exactPackageToRefinement U).map
        (problem.sourceTransport.edgeLift edge).base at hNat
  have hHom : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.pulledRouteComparisonCoreHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)).1 ≫
        ctx.pulledCompositeLegAt (problem.sourceFiberDiagram.obj ⟨i⟩) =
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base := by
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreHom_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, generatedTargetGeometryAt,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonHom_fac
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)
  simp only [Category.assoc]
  rw [hInv, hNat]
  rw [← Category.assoc, hHom]

/-- Cartesian factorization of the common-source edge through the generated
base route, before exactification. The qualification will be generated from
the G-115 cleavage rather than retained as problem data. -/
noncomputable def generatedBaseRefinementGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    RefinementGeometryHom (problem.generatedBaseRouteGeometryAt i)
      (problem.generatedBaseRouteGeometryAt j) := by
  letI := hcart
  let candidate := RefinementGeometryHom.comp
    (UpperGeometryCleavage.baseRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
      (problem.generatedTargetGeometryAt i))
    ((exactGeometryToRefinementGeometry U).map
      (problem.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (UpperGeometryCleavage.baseRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j)).base
    (UpperGeometryCleavage.baseRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))
    (g := (exactPackageToRefinement U).map
      (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge)).1)
    (f' := (RefinementGeometryHom.comp
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i))
      ((exactGeometryToRefinementGeometry U).map
        (problem.sourceTransport.edgeLift edge))).base)
    (problem.generatedBaseCoreEdge_fac edge).symm candidate

/-- The cartesian factor has the exact generated base-core edge as its lower
projection. -/
theorem generatedBaseRefinementGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    (problem.generatedBaseRefinementGeometryEdge edge hcart).base =
      (exactPackageToRefinement U).map
        (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge)).1 := by
  letI := hcart
  let candidate := RefinementGeometryHom.comp
    (UpperGeometryCleavage.baseRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
      (problem.generatedTargetGeometryAt i))
    ((exactGeometryToRefinementGeometry U).map
      (problem.sourceTransport.edgeLift edge))
  letI : (refinementGeometryProjection U).IsHomLift
      ((UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base ≫
        (exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base) candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementGeometryProjection U) _ candidate rfl rfl
    rfl
  unfold generatedBaseRefinementGeometryEdge
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge)).1)
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))
      (problem.generatedBaseCoreEdge_fac edge).symm candidate)).symm

/-- Exact generated base-route geometry edge obtained from the cartesian
factor and the G-115 geometry exactification. -/
noncomputable def generatedBaseGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    GeometryTotalHom (problem.generatedBaseRouteGeometryAt i)
      (problem.generatedBaseRouteGeometryAt j) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge)).1
    (problem.generatedBaseRefinementGeometryEdge edge hcart)
    (problem.generatedBaseRefinementGeometryEdge_base edge hcart)

@[simp] theorem generatedBaseGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    (problem.generatedBaseGeometryEdge edge hcart).base =
      (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge)).1 := rfl

/-- Refinement embedding recovers the universal base-route geometry factor. -/
theorem generatedBaseGeometryEdge_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    (exactGeometryToRefinementGeometry U).map
        (problem.generatedBaseGeometryEdge edge hcart) =
      problem.generatedBaseRefinementGeometryEdge edge hcart := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement
    (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge)).1
    (problem.generatedBaseRefinementGeometryEdge edge hcart)
    (problem.generatedBaseRefinementGeometryEdge_base edge hcart)

/-- The generated exact base edge satisfies full geometry naturality with the
generated route leg and the actual common-source edge. -/
theorem generatedBaseGeometryEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedBaseGeometryEdge edge hcart))
        (UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)) =
      RefinementGeometryHom.comp
        (UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i))
        ((exactGeometryToRefinementGeometry U).map
          (problem.sourceTransport.edgeLift edge)) := by
  rw [problem.generatedBaseGeometryEdge_toRefinement edge hcart]
  letI := hcart
  let candidate := RefinementGeometryHom.comp
    (UpperGeometryCleavage.baseRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
      (problem.generatedTargetGeometryAt i))
    ((exactGeometryToRefinementGeometry U).map
      (problem.sourceTransport.edgeLift edge))
  letI : (refinementGeometryProjection U).IsHomLift
      ((UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base ≫
        (exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base) candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementGeometryProjection U) _ candidate rfl rfl
    rfl
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (UpperGeometryCleavage.baseRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j)).base
    (UpperGeometryCleavage.baseRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))
    (problem.generatedBaseCoreEdge_fac edge).symm candidate

/-- Cartesian factorization of the common-source edge through the generated
pulled route, before exactification. -/
noncomputable def generatedPulledRefinementGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    RefinementGeometryHom (problem.generatedPulledRouteGeometryAt i)
      (problem.generatedPulledRouteGeometryAt j) := by
  letI := hcart
  let candidate := RefinementGeometryHom.comp
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
      (problem.generatedTargetGeometryAt i))
    ((exactGeometryToRefinementGeometry U).map
      (problem.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j)).base
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))
    (g := (exactPackageToRefinement U).map
      (problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)).1)
    (f' := (RefinementGeometryHom.comp
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i))
      ((exactGeometryToRefinementGeometry U).map
        (problem.sourceTransport.edgeLift edge))).base)
    (problem.generatedPulledCoreEdge_fac edge).symm candidate

/-- The cartesian factor has the exact generated pulled-core edge as its lower
projection. -/
theorem generatedPulledRefinementGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    (problem.generatedPulledRefinementGeometryEdge edge hcart).base =
      (exactPackageToRefinement U).map
        (problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)).1 := by
  letI := hcart
  let candidate := RefinementGeometryHom.comp
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
      (problem.generatedTargetGeometryAt i))
    ((exactGeometryToRefinementGeometry U).map
      (problem.sourceTransport.edgeLift edge))
  letI : (refinementGeometryProjection U).IsHomLift
      ((UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base ≫
        (exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base) candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementGeometryProjection U) _ candidate rfl rfl
    rfl
  unfold generatedPulledRefinementGeometryEdge
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)).1)
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))
      (problem.generatedPulledCoreEdge_fac edge).symm candidate)).symm

/-- Exact generated pulled-route geometry edge obtained from the cartesian
factor and the G-115 geometry exactification. -/
noncomputable def generatedPulledGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    GeometryTotalHom (problem.generatedPulledRouteGeometryAt i)
      (problem.generatedPulledRouteGeometryAt j) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)).1
    (problem.generatedPulledRefinementGeometryEdge edge hcart)
    (problem.generatedPulledRefinementGeometryEdge_base edge hcart)

@[simp] theorem generatedPulledGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    (problem.generatedPulledGeometryEdge edge hcart).base =
      (problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)).1 := rfl

/-- Refinement embedding recovers the universal pulled-route geometry factor. -/
theorem generatedPulledGeometryEdge_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    (exactGeometryToRefinementGeometry U).map
        (problem.generatedPulledGeometryEdge edge hcart) =
      problem.generatedPulledRefinementGeometryEdge edge hcart := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement
    (problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)).1
    (problem.generatedPulledRefinementGeometryEdge edge hcart)
    (problem.generatedPulledRefinementGeometryEdge_base edge hcart)

/-- The generated exact pulled edge satisfies full geometry naturality with
the generated route leg and the actual common-source edge. -/
theorem generatedPulledGeometryEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hcart : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedPulledGeometryEdge edge hcart))
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)) =
      RefinementGeometryHom.comp
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i))
        ((exactGeometryToRefinementGeometry U).map
          (problem.sourceTransport.edgeLift edge)) := by
  rw [problem.generatedPulledGeometryEdge_toRefinement edge hcart]
  letI := hcart
  let candidate := RefinementGeometryHom.comp
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
      (problem.generatedTargetGeometryAt i))
    ((exactGeometryToRefinementGeometry U).map
      (problem.sourceTransport.edgeLift edge))
  letI : (refinementGeometryProjection U).IsHomLift
      ((UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).base ≫
        (exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base) candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementGeometryProjection U) _ candidate rfl rfl
    rfl
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j)).base
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))
    (problem.generatedPulledCoreEdge_fac edge).symm candidate

/-- Conditional finite-edge naturality of the generated exact geometry mate.
The two cartesian hypotheses are precisely the route-leg qualifications that
the G-115 cleavage construction must supply. -/
theorem generatedUpperGeometryMateAt_edge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j)
    (hbase : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)))
    (hpulled : (refinementGeometryProjection U).IsStronglyCartesian
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)).base
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))) :
    (problem.generatedBaseGeometryEdge edge hbase).comp
        (problem.generatedUpperGeometryMateAt j) =
      (problem.generatedUpperGeometryMateAt i).comp
        (problem.generatedPulledGeometryEdge edge hpulled) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  let left := (exactGeometryToRefinementGeometry U).map
    ((problem.generatedBaseGeometryEdge edge hbase).comp
      (problem.generatedUpperGeometryMateAt j))
  let right := (exactGeometryToRefinementGeometry U).map
    ((problem.generatedUpperGeometryMateAt i).comp
      (problem.generatedPulledGeometryEdge edge hpulled))
  have hcore := problem.generatedRouteCoreMateAt_naturality
    (presentedEdgePath edge)
  change (problem.generatedBaseCoreDiagram.map (presentedEdgePath edge) ≫
      UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)) =
    (UpperGeometryCleavage.generatedRouteCoreMate
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
      (problem.generatedTargetGeometryAt i) ≫
      problem.generatedPulledCoreDiagram.map (presentedEdgePath edge)) at hcore
  have hleftBase : left.base =
      (exactPackageToRefinement U).map
        ((problem.generatedBaseGeometryEdge edge hbase).comp
          (problem.generatedUpperGeometryMateAt j)).base := rfl
  have hrightBase : right.base =
      (exactPackageToRefinement U).map
        ((problem.generatedBaseGeometryEdge edge hbase).comp
          (problem.generatedUpperGeometryMateAt j)).base := by
    change (exactPackageToRefinement U).map
        ((problem.generatedUpperGeometryMateAt i).base ≫
          (problem.generatedPulledGeometryEdge edge hpulled).base) =
      (exactPackageToRefinement U).map
        ((problem.generatedBaseGeometryEdge edge hbase).base ≫
          (problem.generatedUpperGeometryMateAt j).base)
    apply congrArg (exactPackageToRefinement U).map
    simpa only [generatedBaseGeometryEdge_base,
      generatedPulledGeometryEdge_base, generatedUpperGeometryMateAt_base]
      using congrArg (fun f => f.1) hcore.symm
  letI hleftLift := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    ((exactPackageToRefinement U).map
      ((problem.generatedBaseGeometryEdge edge hbase).comp
        (problem.generatedUpperGeometryMateAt j)).base) left hleftBase
  letI hrightLift := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    ((exactPackageToRefinement U).map
      ((problem.generatedBaseGeometryEdge edge hbase).comp
        (problem.generatedUpperGeometryMateAt j)).base) right hrightBase
  letI := hpulled
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j)).base
    (UpperGeometryCleavage.pulledRouteGeometryHom
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))
    ((exactPackageToRefinement U).map
      ((problem.generatedBaseGeometryEdge edge hbase).comp
        (problem.generatedUpperGeometryMateAt j)).base)
  change RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedBaseGeometryEdge edge hbase))
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedUpperGeometryMateAt j)))
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j)) =
    RefinementGeometryHom.comp
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedUpperGeometryMateAt i))
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedPulledGeometryEdge edge hpulled)))
      (UpperGeometryCleavage.pulledRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
        (problem.generatedTargetGeometryAt j))
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
  rw [problem.generatedUpperGeometryMateAt_triangle j]
  rw [problem.generatedBaseGeometryEdge_fac edge hbase]
  rw [problem.generatedPulledGeometryEdge_fac edge hpulled]
  rw [← UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    problem.generatedUpperGeometryMateAt_triangle i]

end UpperRefinementBCProblemData
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
