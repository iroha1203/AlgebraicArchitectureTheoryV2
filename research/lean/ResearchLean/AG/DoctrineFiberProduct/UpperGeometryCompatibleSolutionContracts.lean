import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleGlobalMate
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointComparatorConjugation

/-!
# Canonical and generated compatible upper solution contracts

The old `UpperRefinementBCSolution` remains the one-way G-114 selected-route
contract.  This module introduces the two G-115-local solution types that will
be related by endpoint conjugation.  Both contracts retain nil, append, and
authored two-cell pasting as explicit equations rather than exposing them only
as downstream corollaries.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-! ## Independently generated canonical-authored path evaluations -/

/-- Evaluate a path using the directly generated canonical-authored base
edges. -/
noncomputable def canonicalAuthoredBaseRoutePathLift
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    {i j : P.Vertex} → P.Path i j →
      GeometryTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i)
        (input.canonicalAuthoredBaseRouteGeometryAt j)
  | _, _, .nil vertex =>
      GeometryTotalHom.id (input.canonicalAuthoredBaseRouteGeometryAt vertex)
  | _, _, .cons edge tail =>
      (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        (input.canonicalAuthoredBaseRoutePathLift tail)

/-- Evaluate a path using the directly generated canonical-authored pulled
edges. -/
noncomputable def canonicalAuthoredPulledRoutePathLift
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    {i j : P.Vertex} → P.Path i j →
      GeometryTotalHom (input.canonicalAuthoredPulledRouteGeometryAt i)
        (input.canonicalAuthoredPulledRouteGeometryAt j)
  | _, _, .nil vertex =>
      GeometryTotalHom.id (input.canonicalAuthoredPulledRouteGeometryAt vertex)
  | _, _, .cons edge tail =>
      (input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
        (input.canonicalAuthoredPulledRoutePathLift tail)

/-! ## The two fixed G-115 solution contracts -/

/-- A solution on the canonical-authored endpoint geometries.  Its comparator
fields use the independently pulled-back literal source comparator. -/
structure CanonicalUpperRefinementBCSolution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) where
  /-- Vertical complete-geometry component at every vertex. -/
  component : (i : P.Vertex) →
    GeometryTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt i)
  /-- The lower projection is the G-115-local generated core mate. -/
  component_base : ∀ i,
    (component i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1
  /-- The vertical component fixes the authored coefficient ring. -/
  component_coefficient_id : ∀ i,
    (component i).geometry.coefficientHom = RingHom.id k
  /-- Complete geometry factorization through the canonical-authored legs. -/
  triangle : ∀ i,
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (component i))
        (input.canonicalAuthoredPulledRouteGeometryHomAt i) =
      input.canonicalAuthoredBaseRouteGeometryHomAt i
  /-- Naturality on every independently generated authored edge. -/
  edge_naturality : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp (component j) =
      (component i).comp
        (input.canonicalAuthoredPulledRouteGeometryEdge edge)
  /-- Intertwining of the two independently pulled-back literal comparators. -/
  comparator_intertwining : ∀ cell : P.TwoCell,
    (input.canonicalAuthoredBaseRouteComparator cell).comp
        (component (P.twoTarget cell)) =
      (component (P.twoTarget cell)).comp
        (input.canonicalAuthoredPulledRouteComparator cell)
  /-- Naturality on the empty path is retained as an independent equation. -/
  nil_naturality : ∀ i,
    (input.canonicalAuthoredBaseRoutePathLift (.nil i)).comp (component i) =
      (component i).comp
        (input.canonicalAuthoredPulledRoutePathLift (.nil i))
  /-- Naturality on every appended pair is retained as an independent
  equation. -/
  append_naturality : ∀ {i j l : P.Vertex}
      (first : P.Path i j) (second : P.Path j l),
    (input.canonicalAuthoredBaseRoutePathLift (first.append second)).comp
        (component l) =
      (component i).comp
        (input.canonicalAuthoredPulledRoutePathLift (first.append second))
  /-- Pasting the authored left two-cell path with the independently generated
  comparator is an explicit contract equation. -/
  authored_twoCell_pasting : ∀ cell : P.TwoCell,
    ((input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
      (input.canonicalAuthoredBaseRouteComparator cell)).comp
        (component (P.twoTarget cell)) =
      (component (P.twoSource cell)).comp
        ((input.canonicalAuthoredPulledRoutePathLift (P.twoLeft cell)).comp
          (input.canonicalAuthoredPulledRouteComparator cell))

/-- A solution on the theorem-generated compatible endpoint geometries. -/
structure GeometryCompatibleUpperRefinementBCSolution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) where
  /-- Vertical complete-geometry component at every vertex. -/
  component : (i : P.Vertex) →
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i)
  /-- The lower projection is the G-115-local generated core mate. -/
  component_base : ∀ i,
    (component i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1
  /-- The vertical component fixes the authored coefficient ring. -/
  component_coefficient_id : ∀ i,
    (component i).geometry.coefficientHom = RingHom.id k
  /-- Complete geometry factorization through the generated route legs. -/
  triangle : ∀ i,
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (component i))
        (input.generatedPulledRouteLegAt i) =
      input.generatedBaseRouteLegAt i
  /-- Naturality on every theorem-generated edge. -/
  edge_naturality : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (input.generatedBaseRouteGeometryEdge edge).comp (component j) =
      (component i).comp (input.generatedPulledRouteGeometryEdge edge)
  /-- Intertwining of the two theorem-generated route comparators. -/
  comparator_intertwining : ∀ cell : P.TwoCell,
    (CompositeFiberAut.hom
      (input.generatedBaseRouteComparator cell)).comp
        (component (P.twoTarget cell)) =
      (component (P.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell))
  /-- Naturality on the empty path is retained as an independent equation. -/
  nil_naturality : ∀ i,
    (input.generatedBaseRouteLiftData.pathLift (.nil i)).comp (component i) =
      (component i).comp
        (input.generatedPulledRouteLiftData.pathLift (.nil i))
  /-- Naturality on every appended pair is retained as an independent
  equation. -/
  append_naturality : ∀ {i j l : P.Vertex}
      (first : P.Path i j) (second : P.Path j l),
    (input.generatedBaseRouteLiftData.pathLift (first.append second)).comp
        (component l) =
      (component i).comp
        (input.generatedPulledRouteLiftData.pathLift (first.append second))
  /-- Pasting the authored left two-cell path with the generated comparator is
  an explicit contract equation. -/
  authored_twoCell_pasting : ∀ cell : P.TwoCell,
    ((input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell)).comp
      (CompositeFiberAut.hom
        (input.generatedBaseRouteComparator cell))).comp
        (component (P.twoTarget cell)) =
      (component (P.twoSource cell)).comp
        ((input.generatedPulledRouteLiftData.pathLift (P.twoLeft cell)).comp
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell)))

/-! ## The theorem-generated solution -/

/-- The generated compatible mate fixes the authored coefficient ring.  This
is forced by its actual factorization triangle and the two independently
proved route-leg normalizations. -/
theorem generatedCompatibleUpperGeometryMateAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedCompatibleUpperGeometryMateAt i).geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedCompatibleUpperGeometryMateAt_triangle i)
  change
    (input.generatedPulledRouteLegAt i).geometry.coefficientHom.comp
        (input.generatedCompatibleUpperGeometryMateAt i).geometry.coefficientHom =
      (input.generatedBaseRouteLegAt i).geometry.coefficientHom at h
  rw [input.generatedPulledRouteLegAt_coefficient_id,
    input.generatedBaseRouteLegAt_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

/-- Edge naturality extends to every generated compatible path. -/
theorem generatedCompatibleUpperGeometryMateAt_path_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.generatedBaseRouteLiftData.pathLift path).comp
        (input.generatedCompatibleUpperGeometryMateAt j) =
      (input.generatedCompatibleUpperGeometryMateAt i).comp
        (input.generatedPulledRouteLiftData.pathLift path) := by
  induction path with
  | nil vertex =>
      change (GeometryTotalHom.id _).comp
          (input.generatedCompatibleUpperGeometryMateAt vertex) =
        (input.generatedCompatibleUpperGeometryMateAt vertex).comp
          (GeometryTotalHom.id _)
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (input.generatedCompatibleUpperGeometryMateAt vertex)).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ (input.generatedCompatibleUpperGeometryMateAt vertex)).symm
  | cons edge tail inductionHypothesis =>
      change ((input.generatedBaseRouteGeometryEdge edge).comp
          (input.generatedBaseRouteLiftData.pathLift tail)).comp
          (input.generatedCompatibleUpperGeometryMateAt _) =
        (input.generatedCompatibleUpperGeometryMateAt _).comp
          ((input.generatedPulledRouteGeometryEdge edge).comp
            (input.generatedPulledRouteLiftData.pathLift tail))
      calc
        _ = (input.generatedBaseRouteGeometryEdge edge).comp
            ((input.generatedBaseRouteLiftData.pathLift tail).comp
              (input.generatedCompatibleUpperGeometryMateAt _)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.generatedBaseRouteGeometryEdge edge)
            (input.generatedBaseRouteLiftData.pathLift tail)
            (input.generatedCompatibleUpperGeometryMateAt _)
        _ = (input.generatedBaseRouteGeometryEdge edge).comp
            ((input.generatedCompatibleUpperGeometryMateAt _).comp
              (input.generatedPulledRouteLiftData.pathLift tail)) :=
          congrArg _ inductionHypothesis
        _ = ((input.generatedBaseRouteGeometryEdge edge).comp
              (input.generatedCompatibleUpperGeometryMateAt _)).comp
            (input.generatedPulledRouteLiftData.pathLift tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.generatedBaseRouteGeometryEdge edge)
            (input.generatedCompatibleUpperGeometryMateAt _)
            (input.generatedPulledRouteLiftData.pathLift tail)).symm
        _ = ((input.generatedCompatibleUpperGeometryMateAt _).comp
              (input.generatedPulledRouteGeometryEdge edge)).comp
            (input.generatedPulledRouteLiftData.pathLift tail) :=
          congrArg (fun hom => hom.comp
            (input.generatedPulledRouteLiftData.pathLift tail))
            (input.generatedCompatibleUpperGeometryMateAt_edge_naturality edge)
        _ = _ := @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ (input.generatedCompatibleUpperGeometryMateAt _)
          (input.generatedPulledRouteGeometryEdge edge)
          (input.generatedPulledRouteLiftData.pathLift tail)

/-- The generated mate satisfies the independent append equation. -/
theorem generatedCompatibleUpperGeometryMateAt_append_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j l : P.Vertex} (first : P.Path i j) (second : P.Path j l) :
    (input.generatedBaseRouteLiftData.pathLift (first.append second)).comp
        (input.generatedCompatibleUpperGeometryMateAt l) =
      (input.generatedCompatibleUpperGeometryMateAt i).comp
        (input.generatedPulledRouteLiftData.pathLift
          (first.append second)) :=
  input.generatedCompatibleUpperGeometryMateAt_path_naturality
    (first.append second)

/-- The generated mate satisfies the authored two-cell pasting equation. -/
theorem generatedCompatibleUpperGeometryMateAt_authored_twoCell_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell)).comp
      (CompositeFiberAut.hom
        (input.generatedBaseRouteComparator cell))).comp
        (input.generatedCompatibleUpperGeometryMateAt (P.twoTarget cell)) =
      (input.generatedCompatibleUpperGeometryMateAt (P.twoSource cell)).comp
        ((input.generatedPulledRouteLiftData.pathLift (P.twoLeft cell)).comp
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell))) := by
  calc
    _ = (input.generatedBaseRouteLiftData.pathLift
          (P.twoLeft cell)).comp
        ((CompositeFiberAut.hom
          (input.generatedBaseRouteComparator cell)).comp
          (input.generatedCompatibleUpperGeometryMateAt
            (P.twoTarget cell))) := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _
      (input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell))
      (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
      (input.generatedCompatibleUpperGeometryMateAt (P.twoTarget cell))
    _ = (input.generatedBaseRouteLiftData.pathLift
          (P.twoLeft cell)).comp
        ((input.generatedCompatibleUpperGeometryMateAt
          (P.twoTarget cell)).comp
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell))) :=
      congrArg _
        (input.generatedCompatibleUpperGeometryMateAt_comparator_intertwining cell)
    _ = ((input.generatedBaseRouteLiftData.pathLift
          (P.twoLeft cell)).comp
          (input.generatedCompatibleUpperGeometryMateAt
            (P.twoTarget cell))).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _
        (input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell))
        (input.generatedCompatibleUpperGeometryMateAt (P.twoTarget cell))
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell))).symm
    _ = ((input.generatedCompatibleUpperGeometryMateAt
          (P.twoSource cell)).comp
          (input.generatedPulledRouteLiftData.pathLift
            (P.twoLeft cell))).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)))
        (input.generatedCompatibleUpperGeometryMateAt_path_naturality
          (P.twoLeft cell))
    _ = _ := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _
      (input.generatedCompatibleUpperGeometryMateAt (P.twoSource cell))
      (input.generatedPulledRouteLiftData.pathLift (P.twoLeft cell))
      (CompositeFiberAut.hom
        (input.generatedPulledRouteComparator cell))

/-- Canonical generated solution constructed from the G-115 mate, its route
naturality, and the global comparator equation.  No solution is supplied by a
caller. -/
noncomputable def generatedGeometryCompatibleUpperRefinementBCSolution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    GeometryCompatibleUpperRefinementBCSolution input where
  component := input.generatedCompatibleUpperGeometryMateAt
  component_base := input.generatedCompatibleUpperGeometryMateAt_base
  component_coefficient_id :=
    input.generatedCompatibleUpperGeometryMateAt_coefficient_id
  triangle := input.generatedCompatibleUpperGeometryMateAt_triangle
  edge_naturality := input.generatedCompatibleUpperGeometryMateAt_edge_naturality
  comparator_intertwining :=
    input.generatedCompatibleUpperGeometryMateAt_comparator_intertwining
  nil_naturality i :=
    input.generatedCompatibleUpperGeometryMateAt_path_naturality (.nil i)
  append_naturality first second :=
    input.generatedCompatibleUpperGeometryMateAt_append_naturality first second
  authored_twoCell_pasting :=
    input.generatedCompatibleUpperGeometryMateAt_authored_twoCell_pasting

/-! ## The canonical-authored solution component -/

/-- Exact lower map of the endpoint-conjugated canonical-authored mate. -/
noncomputable def canonicalAuthoredUpperGeometryMateCoreAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    PackageTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i).core
      (input.canonicalAuthoredPulledRouteGeometryAt i).core := by
  simpa only [input.canonicalAuthoredBaseRouteGeometryAt_core,
    input.canonicalAuthoredPulledRouteGeometryAt_core] using
      (input.generatedCompatibleUpperGeometryMateAt i).base

/-- Refinement presentation of the canonical-authored mate, obtained by
componentwise endpoint conjugation. -/
noncomputable def canonicalAuthoredUpperGeometryMateRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt i) :=
  (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
    (exactGeometryToRefinementGeometry U).map
      (input.generatedCompatibleUpperGeometryMateAt i) ≫
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv

/-- The conjugated refinement mate lies over its literal exact lower map. -/
theorem canonicalAuthoredUpperGeometryMateRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredUpperGeometryMateRefinementAt i).base =
      (exactPackageToRefinement U).map
        (input.canonicalAuthoredUpperGeometryMateCoreAt i) := by
  unfold canonicalAuthoredUpperGeometryMateRefinementAt
  change
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.base ≫
      (exactPackageToRefinement U).map
        (input.generatedCompatibleUpperGeometryMateAt i).base ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.base = _
  rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_base,
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_base]
  simp only [Category.id_comp]
  rfl

/-- Exact canonical-authored complete geometry mate. -/
noncomputable def canonicalAuthoredUpperGeometryMateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredUpperGeometryMateCoreAt i)
    (input.canonicalAuthoredUpperGeometryMateRefinementAt i)
    (input.canonicalAuthoredUpperGeometryMateRefinementAt_base i)

/-- Exact embedding recovers the componentwise conjugation formula. -/
theorem canonicalAuthoredUpperGeometryMateAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredUpperGeometryMateAt i) =
      input.canonicalAuthoredUpperGeometryMateRefinementAt i :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The canonical-authored component has the fixed G-115-local lower mate. -/
@[simp] theorem canonicalAuthoredUpperGeometryMateAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredUpperGeometryMateAt i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1 := by
  rfl

/-- The endpoint-conjugated component satisfies the independently authored
geometry triangle. -/
theorem canonicalAuthoredUpperGeometryMateAt_triangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredUpperGeometryMateAt i))
        (input.canonicalAuthoredPulledRouteGeometryHomAt i) =
      input.canonicalAuthoredBaseRouteGeometryHomAt i := by
  rw [input.canonicalAuthoredUpperGeometryMateAt_toRefinement]
  unfold canonicalAuthoredUpperGeometryMateRefinementAt
  change
    (((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
      (exactGeometryToRefinementGeometry U).map
        (input.generatedCompatibleUpperGeometryMateAt i) ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv) ≫
        input.canonicalAuthoredPulledRouteGeometryHomAt i) = _
  calc
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (exactGeometryToRefinementGeometry U).map
          (input.generatedCompatibleUpperGeometryMateAt i) ≫
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv ≫
          input.canonicalAuthoredPulledRouteGeometryHomAt i) := by
      simp only [Category.assoc]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (exactGeometryToRefinementGeometry U).map
          (input.generatedCompatibleUpperGeometryMateAt i) ≫
        input.generatedPulledRouteLegAt i := by
      rw [input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_fac]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        input.generatedBaseRouteLegAt i := by
      exact congrArg
        (fun hom =>
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫ hom)
        (input.generatedCompatibleUpperGeometryMateAt_triangle i)
    _ = _ := input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac i

/-- The canonical-authored component fixes the authored coefficient ring. -/
theorem canonicalAuthoredUpperGeometryMateAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredUpperGeometryMateAt i).geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredUpperGeometryMateAt_triangle i)
  change
    (input.canonicalAuthoredPulledRouteGeometryHomAt i).geometry.coefficientHom.comp
        (input.canonicalAuthoredUpperGeometryMateAt i).geometry.coefficientHom =
      (input.canonicalAuthoredBaseRouteGeometryHomAt i).geometry.coefficientHom at h
  rw [input.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom,
    input.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom] at h
  simpa only [RingHom.id_comp] using h

/-- Inverse form of pulled endpoint naturality. -/
theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    ((exactGeometryToRefinementGeometry U).map
      (input.generatedPulledRouteGeometryEdge edge)) ≫
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).inv =
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteGeometryEdge edge)) := by
  let sourceComparison :=
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i
  let targetComparison :=
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j
  let generatedEdge := (exactGeometryToRefinementGeometry U).map
    (input.generatedPulledRouteGeometryEdge edge)
  let canonicalEdge := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteGeometryEdge edge)
  have hnaturality : canonicalEdge ≫ targetComparison.hom =
      sourceComparison.hom ≫ generatedEdge := by
    exact input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality edge
  calc
    generatedEdge ≫ targetComparison.inv =
        sourceComparison.inv ≫ (sourceComparison.hom ≫ generatedEdge) ≫
          targetComparison.inv := by simp
    _ = sourceComparison.inv ≫ (canonicalEdge ≫ targetComparison.hom) ≫
          targetComparison.inv := by rw [hnaturality]
    _ = sourceComparison.inv ≫ canonicalEdge := by simp

/-- Endpoint conjugation preserves edge naturality for the canonical-authored
mate. -/
theorem canonicalAuthoredUpperGeometryMateAt_edge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        (input.canonicalAuthoredUpperGeometryMateAt j) =
      (input.canonicalAuthoredUpperGeometryMateAt i).comp
        (input.canonicalAuthoredPulledRouteGeometryEdge edge) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteGeometryEdge edge)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredUpperGeometryMateAt j)) =
      ((exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredUpperGeometryMateAt i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteGeometryEdge edge))
  rw [input.canonicalAuthoredUpperGeometryMateAt_toRefinement,
    input.canonicalAuthoredUpperGeometryMateAt_toRefinement]
  unfold canonicalAuthoredUpperGeometryMateRefinementAt
  let cb := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteGeometryEdge edge)
  let bi := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom
  let bj := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom
  let gb := (exactGeometryToRefinementGeometry U).map
    (input.generatedBaseRouteGeometryEdge edge)
  let mi := (exactGeometryToRefinementGeometry U).map
    (input.generatedCompatibleUpperGeometryMateAt i)
  let mj := (exactGeometryToRefinementGeometry U).map
    (input.generatedCompatibleUpperGeometryMateAt j)
  let gp := (exactGeometryToRefinementGeometry U).map
    (input.generatedPulledRouteGeometryEdge edge)
  let pi := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv
  let pj := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).inv
  let cp := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteGeometryEdge edge)
  have hbase :=
    input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality edge
  change cb ≫ bj = bi ≫ gb at hbase
  have hmate := congrArg
    (exactGeometryToRefinementGeometry U).map
    (input.generatedCompatibleUpperGeometryMateAt_edge_naturality edge)
  change gb ≫ mj = mi ≫ gp at hmate
  have hinv :=
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality_inv edge
  change gp ≫ pj = pi ≫ cp at hinv
  change cb ≫ (bj ≫ mj ≫ pj) =
    (bi ≫ mi ≫ pi) ≫ cp
  calc
    cb ≫ (bj ≫ mj ≫ pj) = ((cb ≫ bj) ≫ mj) ≫ pj := by
      simp only [Category.assoc]
    _ = ((bi ≫ gb) ≫ mj) ≫ pj := by rw [hbase]
    _ = (bi ≫ (gb ≫ mj)) ≫ pj := by
      exact congrArg (fun hom => hom ≫ pj) (Category.assoc bi gb mj)
    _ = (bi ≫ (mi ≫ gp)) ≫ pj := by rw [hmate]
    _ = bi ≫ mi ≫ (gp ≫ pj) := by simp only [Category.assoc]
    _ = bi ≫ mi ≫ (pi ≫ cp) := by rw [hinv]
    _ = (bi ≫ mi ≫ pi) ≫ cp := by simp only [Category.assoc]

/-- The literal canonical-authored comparators intertwine the endpoint-
conjugated mate. -/
theorem canonicalAuthoredUpperGeometryMateAt_comparator_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredBaseRouteComparator cell).comp
        (input.canonicalAuthoredUpperGeometryMateAt (P.twoTarget cell)) =
      (input.canonicalAuthoredUpperGeometryMateAt (P.twoTarget cell)).comp
        (input.canonicalAuthoredPulledRouteComparator cell) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteComparator cell)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredUpperGeometryMateAt (P.twoTarget cell))) =
      ((exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredUpperGeometryMateAt (P.twoTarget cell))) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteComparator cell))
  rw [input.canonicalAuthoredUpperGeometryMateAt_toRefinement]
  unfold canonicalAuthoredUpperGeometryMateRefinementAt
  let cb := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteComparator cell)
  let b := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)).hom
  let gb := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
  let m := (exactGeometryToRefinementGeometry U).map
    (input.generatedCompatibleUpperGeometryMateAt (P.twoTarget cell))
  let gp := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))
  let p := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)).inv
  let cp := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteComparator cell)
  have hmate := congrArg
    (exactGeometryToRefinementGeometry U).map
    (input.generatedCompatibleUpperGeometryMateAt_comparator_intertwining cell)
  change gb ≫ m = m ≫ gp at hmate
  have hbase := input.canonicalAuthoredBaseRouteComparator_conjugation cell
  change cb ≫ b = b ≫ gb at hbase
  have hpulled := input.canonicalAuthoredPulledRouteComparator_conjugation_inv cell
  change gp ≫ p = p ≫ cp at hpulled
  change cb ≫ (b ≫ m ≫ p) = (b ≫ m ≫ p) ≫ cp
  calc
    cb ≫ (b ≫ m ≫ p) = ((cb ≫ b) ≫ m) ≫ p := by
      simp only [Category.assoc]
    _ = ((b ≫ gb) ≫ m) ≫ p := by rw [hbase]
    _ = (b ≫ (gb ≫ m)) ≫ p := by
      exact congrArg (fun hom => hom ≫ p) (Category.assoc b gb m)
    _ = (b ≫ (m ≫ gp)) ≫ p := by rw [hmate]
    _ = b ≫ m ≫ (gp ≫ p) := by simp only [Category.assoc]
    _ = b ≫ m ≫ (p ≫ cp) := by rw [hpulled]
    _ = (b ≫ m ≫ p) ≫ cp := by simp only [Category.assoc]

/-- Edge naturality extends to every independently generated canonical-
authored path. -/
theorem canonicalAuthoredUpperGeometryMateAt_path_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.canonicalAuthoredBaseRoutePathLift path).comp
        (input.canonicalAuthoredUpperGeometryMateAt j) =
      (input.canonicalAuthoredUpperGeometryMateAt i).comp
        (input.canonicalAuthoredPulledRoutePathLift path) := by
  induction path with
  | nil vertex =>
      change (GeometryTotalHom.id _).comp
          (input.canonicalAuthoredUpperGeometryMateAt vertex) =
        (input.canonicalAuthoredUpperGeometryMateAt vertex).comp
          (GeometryTotalHom.id _)
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (input.canonicalAuthoredUpperGeometryMateAt vertex)).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ (input.canonicalAuthoredUpperGeometryMateAt vertex)).symm
  | cons edge tail inductionHypothesis =>
      change ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
          (input.canonicalAuthoredBaseRoutePathLift tail)).comp
          (input.canonicalAuthoredUpperGeometryMateAt _) =
        (input.canonicalAuthoredUpperGeometryMateAt _).comp
          ((input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
            (input.canonicalAuthoredPulledRoutePathLift tail))
      calc
        _ = (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
            ((input.canonicalAuthoredBaseRoutePathLift tail).comp
              (input.canonicalAuthoredUpperGeometryMateAt _)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.canonicalAuthoredBaseRouteGeometryEdge edge)
            (input.canonicalAuthoredBaseRoutePathLift tail)
            (input.canonicalAuthoredUpperGeometryMateAt _)
        _ = (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
            ((input.canonicalAuthoredUpperGeometryMateAt _).comp
              (input.canonicalAuthoredPulledRoutePathLift tail)) :=
          congrArg _ inductionHypothesis
        _ = ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
              (input.canonicalAuthoredUpperGeometryMateAt _)).comp
            (input.canonicalAuthoredPulledRoutePathLift tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.canonicalAuthoredBaseRouteGeometryEdge edge)
            (input.canonicalAuthoredUpperGeometryMateAt _)
            (input.canonicalAuthoredPulledRoutePathLift tail)).symm
        _ = ((input.canonicalAuthoredUpperGeometryMateAt _).comp
              (input.canonicalAuthoredPulledRouteGeometryEdge edge)).comp
            (input.canonicalAuthoredPulledRoutePathLift tail) :=
          congrArg (fun hom => hom.comp
            (input.canonicalAuthoredPulledRoutePathLift tail))
            (input.canonicalAuthoredUpperGeometryMateAt_edge_naturality edge)
        _ = _ := @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ (input.canonicalAuthoredUpperGeometryMateAt _)
          (input.canonicalAuthoredPulledRouteGeometryEdge edge)
          (input.canonicalAuthoredPulledRoutePathLift tail)

/-- The canonical-authored mate satisfies the independent append equation. -/
theorem canonicalAuthoredUpperGeometryMateAt_append_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j l : P.Vertex} (first : P.Path i j) (second : P.Path j l) :
    (input.canonicalAuthoredBaseRoutePathLift (first.append second)).comp
        (input.canonicalAuthoredUpperGeometryMateAt l) =
      (input.canonicalAuthoredUpperGeometryMateAt i).comp
        (input.canonicalAuthoredPulledRoutePathLift (first.append second)) :=
  input.canonicalAuthoredUpperGeometryMateAt_path_naturality
    (first.append second)

/-- The canonical-authored mate satisfies literal authored two-cell pasting. -/
theorem canonicalAuthoredUpperGeometryMateAt_authored_twoCell_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
      (input.canonicalAuthoredBaseRouteComparator cell)).comp
        (input.canonicalAuthoredUpperGeometryMateAt (P.twoTarget cell)) =
      (input.canonicalAuthoredUpperGeometryMateAt (P.twoSource cell)).comp
        ((input.canonicalAuthoredPulledRoutePathLift (P.twoLeft cell)).comp
          (input.canonicalAuthoredPulledRouteComparator cell)) := by
  calc
    _ = (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
        ((input.canonicalAuthoredBaseRouteComparator cell).comp
          (input.canonicalAuthoredUpperGeometryMateAt
            (P.twoTarget cell))) := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell))
      (input.canonicalAuthoredBaseRouteComparator cell)
      (input.canonicalAuthoredUpperGeometryMateAt (P.twoTarget cell))
    _ = (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
        ((input.canonicalAuthoredUpperGeometryMateAt
          (P.twoTarget cell)).comp
          (input.canonicalAuthoredPulledRouteComparator cell)) :=
      congrArg _
        (input.canonicalAuthoredUpperGeometryMateAt_comparator_intertwining cell)
    _ = ((input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
          (input.canonicalAuthoredUpperGeometryMateAt
            (P.twoTarget cell))).comp
        (input.canonicalAuthoredPulledRouteComparator cell) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell))
        (input.canonicalAuthoredUpperGeometryMateAt (P.twoTarget cell))
        (input.canonicalAuthoredPulledRouteComparator cell)).symm
    _ = ((input.canonicalAuthoredUpperGeometryMateAt
          (P.twoSource cell)).comp
          (input.canonicalAuthoredPulledRoutePathLift
            (P.twoLeft cell))).comp
        (input.canonicalAuthoredPulledRouteComparator cell) :=
      congrArg (fun hom => hom.comp
        (input.canonicalAuthoredPulledRouteComparator cell))
        (input.canonicalAuthoredUpperGeometryMateAt_path_naturality
          (P.twoLeft cell))
    _ = _ := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (input.canonicalAuthoredUpperGeometryMateAt (P.twoSource cell))
      (input.canonicalAuthoredPulledRoutePathLift (P.twoLeft cell))
      (input.canonicalAuthoredPulledRouteComparator cell)

/-- Canonical-authored solution generated by endpoint conjugation from the
theorem-produced G-115 mate. -/
noncomputable def canonicalUpperRefinementBCSolution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    CanonicalUpperRefinementBCSolution input where
  component := input.canonicalAuthoredUpperGeometryMateAt
  component_base := input.canonicalAuthoredUpperGeometryMateAt_base
  component_coefficient_id :=
    input.canonicalAuthoredUpperGeometryMateAt_coefficient_id
  triangle := input.canonicalAuthoredUpperGeometryMateAt_triangle
  edge_naturality := input.canonicalAuthoredUpperGeometryMateAt_edge_naturality
  comparator_intertwining :=
    input.canonicalAuthoredUpperGeometryMateAt_comparator_intertwining
  nil_naturality i :=
    input.canonicalAuthoredUpperGeometryMateAt_path_naturality (.nil i)
  append_naturality first second :=
    input.canonicalAuthoredUpperGeometryMateAt_append_naturality first second
  authored_twoCell_pasting :=
    input.canonicalAuthoredUpperGeometryMateAt_authored_twoCell_pasting

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
