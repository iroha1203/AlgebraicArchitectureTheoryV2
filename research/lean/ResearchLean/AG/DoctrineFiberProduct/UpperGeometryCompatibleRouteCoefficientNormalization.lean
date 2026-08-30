import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryQualifications

/-!
# Fixed-coefficient normalization for generated compatible routes

The realized-refinement cleavage now retains the authored coefficient carrier
and ring structure definitionally.  This module packages that normalization at
each endpoint, derives edge and comparator coefficient identities from their
actual factor graphs, proves finite path and two-cell projection laws, and
assembles the two generated fixed-coefficient route transports.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The generated base-route endpoint with its coefficient ring normalized to
the authored fixed ring. -/
noncomputable def generatedBaseRouteFixedGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    FixedCoefficientGeometryAt
      (input.generatedBaseRouteCoreDiagram.obj ⟨i⟩).1 k := by
  exact {
    geometry := (input.generatedBaseRouteGeometryAt i).geometry
    raw := (input.generatedBaseRouteGeometryAt i).raw
  }

/-- The generated pulled-route endpoint with its coefficient ring normalized
to the authored fixed ring. -/
noncomputable def generatedPulledRouteFixedGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    FixedCoefficientGeometryAt
      (input.generatedPulledRouteCoreDiagram.obj ⟨i⟩).1 k := by
  exact {
    geometry := (input.generatedPulledRouteGeometryAt i).geometry
    raw := (input.generatedPulledRouteGeometryAt i).raw
  }

/-- Forgetting the base-route coefficient normalization recovers the literal
generated route geometry. -/
@[simp] theorem generatedBaseRouteFixedGeometryAt_package
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedBaseRouteFixedGeometryAt i).package =
      input.generatedBaseRouteGeometryAt i := rfl

/-- Forgetting the pulled-route coefficient normalization recovers the literal
generated route geometry. -/
@[simp] theorem generatedPulledRouteFixedGeometryAt_package
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedPulledRouteFixedGeometryAt i).package =
      input.generatedPulledRouteGeometryAt i := rfl

/-- The generated base-route leg fixes the authored coefficient ring. -/
@[simp] theorem generatedBaseRouteLegAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedBaseRouteLegAt i).geometry.coefficientHom =
      RingHom.id k := by
  ext x
  rfl

/-- The generated pulled-route leg fixes the authored coefficient ring. -/
@[simp] theorem generatedPulledRouteLegAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedPulledRouteLegAt i).geometry.coefficientHom =
      RingHom.id k := by
  ext x
  rfl

/-- Base-route edge at the definitionally fixed coefficient endpoints. -/
noncomputable def generatedBaseRouteFixedGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (input.generatedBaseRouteFixedGeometryAt i).package
      (input.generatedBaseRouteFixedGeometryAt j).package :=
  input.generatedBaseRouteGeometryEdge edge

/-- Pulled-route edge at the definitionally fixed coefficient endpoints. -/
noncomputable def generatedPulledRouteFixedGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (input.generatedPulledRouteFixedGeometryAt i).package
      (input.generatedPulledRouteFixedGeometryAt j).package :=
  input.generatedPulledRouteGeometryEdge edge

/-- The normalized base-route edge has the generated core-diagram map as its
literal lower projection. -/
@[simp] theorem generatedBaseRouteFixedGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.generatedBaseRouteFixedGeometryEdge edge).base =
      (input.generatedBaseRouteCoreDiagram.map
        (presentedEdgePath edge)).1 := rfl

/-- The normalized pulled-route edge has the generated core-diagram map as its
literal lower projection. -/
@[simp] theorem generatedPulledRouteFixedGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.generatedPulledRouteFixedGeometryEdge edge).base =
      (input.generatedPulledRouteCoreDiagram.map
        (presentedEdgePath edge)).1 := rfl

/-- The actual base-route factor graph forces the normalized edge coefficient
map to be the identity. -/
theorem generatedBaseRouteFixedGeometryEdge_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.generatedBaseRouteFixedGeometryEdge edge).geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedBaseRouteGeometryEdge_fac edge)
  change
    (input.generatedBaseRouteLegAt j).geometry.coefficientHom.comp
        (input.generatedBaseRouteGeometryEdge edge).geometry.coefficientHom =
      (input.sourceTransport.edgeLift edge).geometry.coefficientHom.comp
        (input.generatedBaseRouteLegAt i).geometry.coefficientHom at h
  rw [input.generatedBaseRouteLegAt_coefficient_id,
    input.generatedBaseRouteLegAt_coefficient_id,
    input.sourceTransport.edge_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- The actual pulled-route factor graph forces the normalized edge coefficient
map to be the identity. -/
theorem generatedPulledRouteFixedGeometryEdge_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.generatedPulledRouteFixedGeometryEdge edge).geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedPulledRouteGeometryEdge_fac edge)
  change
    (input.generatedPulledRouteLegAt j).geometry.coefficientHom.comp
        (input.generatedPulledRouteGeometryEdge edge).geometry.coefficientHom =
      (input.sourceTransport.edgeLift edge).geometry.coefficientHom.comp
        (input.generatedPulledRouteLegAt i).geometry.coefficientHom at h
  rw [input.generatedPulledRouteLegAt_coefficient_id,
    input.generatedPulledRouteLegAt_coefficient_id,
    input.sourceTransport.edge_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- Base-route comparator at the definitionally fixed coefficient endpoint. -/
noncomputable def generatedBaseRouteFixedComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut
      (input.generatedBaseRouteFixedGeometryAt (P.twoTarget cell)).package :=
  input.generatedBaseRouteComparator cell

/-- Pulled-route comparator at the definitionally fixed coefficient endpoint. -/
noncomputable def generatedPulledRouteFixedComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut
      (input.generatedPulledRouteFixedGeometryAt (P.twoTarget cell)).package :=
  input.generatedPulledRouteComparator cell

/-- The authored comparator factor graph forces the generated base-route
comparator coefficient map to be the identity. -/
theorem generatedBaseRouteFixedComparator_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.generatedBaseRouteFixedComparator cell)).geometry.coefficientHom =
        RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedBaseRouteComparator_fac cell)
  change
    (input.generatedBaseRouteLegAt (P.twoTarget cell)).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (input.generatedBaseRouteComparator cell)).geometry.coefficientHom =
      (CompositeFiberAut.hom
          (input.sourceTransport.comparator cell)).geometry.coefficientHom.comp
        (input.generatedBaseRouteLegAt
          (P.twoTarget cell)).geometry.coefficientHom at h
  rw [input.generatedBaseRouteLegAt_coefficient_id,
    input.sourceTransport.comparator_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- The authored comparator factor graph forces the generated pulled-route
comparator coefficient map to be the identity. -/
theorem generatedPulledRouteFixedComparator_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.generatedPulledRouteFixedComparator cell)).geometry.coefficientHom =
        RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedPulledRouteComparator_fac cell)
  change
    (input.generatedPulledRouteLegAt (P.twoTarget cell)).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)).geometry.coefficientHom =
      (CompositeFiberAut.hom
          (input.sourceTransport.comparator cell)).geometry.coefficientHom.comp
        (input.generatedPulledRouteLegAt
          (P.twoTarget cell)).geometry.coefficientHom at h
  rw [input.generatedPulledRouteLegAt_coefficient_id,
    input.sourceTransport.comparator_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- Qualified lift data of the fixed-coefficient generated base route. -/
noncomputable def generatedBaseRouteLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerLiftData.{u, v} P U where
  geometry i := (input.generatedBaseRouteFixedGeometryAt i).package
  edgeLift edge := input.generatedBaseRouteFixedGeometryEdge edge
  edgeGeometryStrong edge := by
    exact input.generatedBaseRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge := by
    exact input.generatedBaseRouteCoreEdge_isStronglyCocartesian edge

/-- Qualified lift data of the fixed-coefficient generated pulled route. -/
noncomputable def generatedPulledRouteLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerLiftData.{u, v} P U where
  geometry i := (input.generatedPulledRouteFixedGeometryAt i).package
  edgeLift edge := input.generatedPulledRouteFixedGeometryEdge edge
  edgeGeometryStrong edge := by
    exact input.generatedPulledRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge := by
    exact input.generatedPulledRouteCoreEdge_isStronglyCocartesian edge

/-- Projecting a base-route path lift recovers the actual generated core
diagram map on that path. -/
theorem generatedBaseRoutePathLift_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.generatedBaseRouteLiftData.pathLift path).base =
      (input.generatedBaseRouteCoreDiagram.map path).1 := by
  induction path with
  | nil vertex =>
      have h := congrArg (fun f => f.1)
        (input.generatedBaseRouteCoreDiagram.map_id ⟨vertex⟩)
      exact h.symm
  | cons edge tail ih =>
      change (input.generatedBaseRouteFixedGeometryEdge edge).base.comp
          (input.generatedBaseRouteLiftData.pathLift tail).base = _
      rw [input.generatedBaseRouteFixedGeometryEdge_base edge, ih]
      have h := congrArg (fun f => f.1)
        (input.generatedBaseRouteCoreDiagram.map_comp
          (presentedEdgePath edge) tail)
      exact h.symm

/-- Projecting a pulled-route path lift recovers the actual generated core
diagram map on that path. -/
theorem generatedPulledRoutePathLift_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.generatedPulledRouteLiftData.pathLift path).base =
      (input.generatedPulledRouteCoreDiagram.map path).1 := by
  induction path with
  | nil vertex =>
      have h := congrArg (fun f => f.1)
        (input.generatedPulledRouteCoreDiagram.map_id ⟨vertex⟩)
      exact h.symm
  | cons edge tail ih =>
      change (input.generatedPulledRouteFixedGeometryEdge edge).base.comp
          (input.generatedPulledRouteLiftData.pathLift tail).base = _
      rw [input.generatedPulledRouteFixedGeometryEdge_base edge, ih]
      have h := congrArg (fun f => f.1)
        (input.generatedPulledRouteCoreDiagram.map_comp
          (presentedEdgePath edge) tail)
      exact h.symm

/-- Parallel base-route path lifts have equal extraction-level projections
because the generated core diagram is valued in one actual core fiber. -/
theorem generatedBaseRouteTwoCellBase
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.generatedBaseRouteLiftData.pathLift
        (P.twoLeft cell)).base.base =
      (input.generatedBaseRouteLiftData.pathLift
        (P.twoRight cell)).base.base := by
  rw [input.generatedBaseRoutePathLift_base,
    input.generatedBaseRoutePathLift_base]
  let left := input.generatedBaseRouteCoreDiagram.map (P.twoLeft cell)
  let right := input.generatedBaseRouteCoreDiagram.map (P.twoRight cell)
  letI : (packageProjection U).IsHomLift
      (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) left.1 := left.2
  letI : (packageProjection U).IsHomLift
      (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) right.1 := right.2
  have leftFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U)
    (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) left.1
  have rightFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U)
    (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) right.1
  simpa only using leftFac.trans rightFac.symm

/-- Parallel pulled-route path lifts have equal extraction-level projections
because the generated core diagram is valued in the same actual core fiber. -/
theorem generatedPulledRouteTwoCellBase
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.generatedPulledRouteLiftData.pathLift
        (P.twoLeft cell)).base.base =
      (input.generatedPulledRouteLiftData.pathLift
        (P.twoRight cell)).base.base := by
  rw [input.generatedPulledRoutePathLift_base,
    input.generatedPulledRoutePathLift_base]
  let left := input.generatedPulledRouteCoreDiagram.map (P.twoLeft cell)
  let right := input.generatedPulledRouteCoreDiagram.map (P.twoRight cell)
  letI : (packageProjection U).IsHomLift
      (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) left.1 := left.2
  letI : (packageProjection U).IsHomLift
      (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) right.1 := right.2
  have leftFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U)
    (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) left.1
  have rightFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U)
    (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) right.1
  simpa only using leftFac.trans rightFac.symm

/-- The actual fixed-coefficient G-109 transport generated on the base-first
route.  Every field beyond the one authored source transport is constructed by
the preceding route theorems. -/
noncomputable def generatedBaseRouteTransport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    FixedCoefficientTwoLayerTransportOver P
      input.generatedBaseRouteCoreDiagram k
      input.generatedBaseRouteFixedGeometryAt where
  edgeLift edge := input.generatedBaseRouteFixedGeometryEdge edge
  edge_base edge := input.generatedBaseRouteFixedGeometryEdge_base edge
  edgeGeometryStrong edge :=
    input.generatedBaseRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge :=
    input.generatedBaseRouteCoreEdge_isStronglyCocartesian edge
  twoCellBase cell := input.generatedBaseRouteTwoCellBase cell
  comparator cell := input.generatedBaseRouteFixedComparator cell
  edge_coefficient_id edge :=
    input.generatedBaseRouteFixedGeometryEdge_coefficient_id edge
  comparator_coefficient_id cell :=
    input.generatedBaseRouteFixedComparator_coefficient_id cell

/-- The actual fixed-coefficient G-109 transport generated independently on
the pulled-first route. -/
noncomputable def generatedPulledRouteTransport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    FixedCoefficientTwoLayerTransportOver P
      input.generatedPulledRouteCoreDiagram k
      input.generatedPulledRouteFixedGeometryAt where
  edgeLift edge := input.generatedPulledRouteFixedGeometryEdge edge
  edge_base edge := input.generatedPulledRouteFixedGeometryEdge_base edge
  edgeGeometryStrong edge :=
    input.generatedPulledRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge :=
    input.generatedPulledRouteCoreEdge_isStronglyCocartesian edge
  twoCellBase cell := input.generatedPulledRouteTwoCellBase cell
  comparator cell := input.generatedPulledRouteFixedComparator cell
  edge_coefficient_id edge :=
    input.generatedPulledRouteFixedGeometryEdge_coefficient_id edge
  comparator_coefficient_id cell :=
    input.generatedPulledRouteFixedComparator_coefficient_id cell

/-- Forgetting the fixed-coefficient evidence from the base-route transport
recovers its generated lift data. -/
@[simp] theorem generatedBaseRouteTransport_toTwoLayerLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.generatedBaseRouteTransport.toTwoLayerLiftData =
      input.generatedBaseRouteLiftData := rfl

/-- Forgetting the fixed-coefficient evidence from the pulled-route transport
recovers its independently generated lift data. -/
@[simp] theorem generatedPulledRouteTransport_toTwoLayerLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.generatedPulledRouteTransport.toTwoLayerLiftData =
      input.generatedPulledRouteLiftData := rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
