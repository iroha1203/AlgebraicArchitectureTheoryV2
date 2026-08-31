import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointExactIsos
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCoefficientNormalization

/-!
# Fixed-coefficient transports on the canonical-authored routes

The canonical-authored endpoint geometries have the same exact cores as the
two generated route diagrams, definitionally.  This module retains those
existing diagrams, qualifies the independently pulled-back authored edges,
packages the independently pulled-back comparators as composite-fiber
automorphisms, and assembles the two fixed-coefficient transports.

The geometry edges and comparators are not replaced by conjugated definitions.
Endpoint naturality and comparator conjugation are used only to recover their
isomorphism qualifications; the stored morphisms remain the direct Cartesian
pullbacks of the authored source data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- The canonical-authored base endpoint over the existing generated base
core diagram, with its authored coefficient ring retained definitionally. -/
noncomputable def canonicalAuthoredBaseRouteFixedGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    FixedCoefficientGeometryAt
      (input.generatedBaseRouteCoreDiagram.obj ⟨i⟩).1 k := by
  exact {
    geometry := (input.canonicalAuthoredBaseRouteGeometryAt i).geometry
    raw := (input.canonicalAuthoredBaseRouteGeometryAt i).raw
  }

/-- The canonical-authored pulled endpoint over the existing generated pulled
core diagram, with its authored coefficient ring retained definitionally. -/
noncomputable def canonicalAuthoredPulledRouteFixedGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    FixedCoefficientGeometryAt
      (input.generatedPulledRouteCoreDiagram.obj ⟨i⟩).1 k := by
  exact {
    geometry := (input.canonicalAuthoredPulledRouteGeometryAt i).geometry
    raw := (input.canonicalAuthoredPulledRouteGeometryAt i).raw
  }

/-- Forgetting the fixed-coefficient wrapper recovers the literal
canonical-authored base endpoint. -/
@[simp] theorem canonicalAuthoredBaseRouteFixedGeometryAt_package
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseRouteFixedGeometryAt i).package =
      input.canonicalAuthoredBaseRouteGeometryAt i := rfl

/-- Forgetting the fixed-coefficient wrapper recovers the literal
canonical-authored pulled endpoint. -/
@[simp] theorem canonicalAuthoredPulledRouteFixedGeometryAt_package
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledRouteFixedGeometryAt i).package =
      input.canonicalAuthoredPulledRouteGeometryAt i := rfl

/-- Canonical-authored base edge at the definitionally fixed endpoint types. -/
noncomputable def canonicalAuthoredBaseRouteFixedGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (input.canonicalAuthoredBaseRouteFixedGeometryAt i).package
      (input.canonicalAuthoredBaseRouteFixedGeometryAt j).package :=
  input.canonicalAuthoredBaseRouteGeometryEdge edge

/-- Canonical-authored pulled edge at the definitionally fixed endpoint
types. -/
noncomputable def canonicalAuthoredPulledRouteFixedGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (input.canonicalAuthoredPulledRouteFixedGeometryAt i).package
      (input.canonicalAuthoredPulledRouteFixedGeometryAt j).package :=
  input.canonicalAuthoredPulledRouteGeometryEdge edge

/-- The canonical-authored base edge projects to the existing generated core
diagram map. -/
@[simp] theorem canonicalAuthoredBaseRouteFixedGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredBaseRouteFixedGeometryEdge edge).base =
      (input.generatedBaseRouteCoreDiagram.map
        (presentedEdgePath edge)).1 := by
  change (input.canonicalAuthoredBaseRouteGeometryEdge edge).base = _
  rw [input.canonicalAuthoredBaseRouteGeometryEdge_base edge]
  rfl

/-- The canonical-authored pulled edge projects to the existing generated
pulled core diagram map. -/
@[simp] theorem canonicalAuthoredPulledRouteFixedGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredPulledRouteFixedGeometryEdge edge).base =
      (input.generatedPulledRouteCoreDiagram.map
        (presentedEdgePath edge)).1 := by
  change (input.canonicalAuthoredPulledRouteGeometryEdge edge).base = _
  rw [input.canonicalAuthoredPulledRouteGeometryEdge_base edge]
  rfl

/-- The actual authored base-edge factorization forces its coefficient map to
be the identity. -/
theorem canonicalAuthoredBaseRouteFixedGeometryEdge_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredBaseRouteFixedGeometryEdge edge).geometry.coefficientHom =
      RingHom.id k := by
  change (input.canonicalAuthoredBaseRouteGeometryEdge edge).geometry.coefficientHom = _
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredBaseRouteGeometryEdge_fac edge)
  change
    (input.canonicalAuthoredBaseRouteGeometryHomAt j).geometry.coefficientHom.comp
        (input.canonicalAuthoredBaseRouteGeometryEdge edge).geometry.coefficientHom =
      (input.sourceTransport.edgeLift edge).geometry.coefficientHom.comp
        (input.canonicalAuthoredBaseRouteGeometryHomAt i).geometry.coefficientHom at h
  rw [input.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom,
    input.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom,
    input.sourceTransport.edge_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- The actual authored pulled-edge factorization forces its coefficient map
to be the identity. -/
theorem canonicalAuthoredPulledRouteFixedGeometryEdge_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredPulledRouteFixedGeometryEdge edge).geometry.coefficientHom =
      RingHom.id k := by
  change (input.canonicalAuthoredPulledRouteGeometryEdge edge).geometry.coefficientHom = _
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredPulledRouteGeometryEdge_fac edge)
  change
    (input.canonicalAuthoredPulledRouteGeometryHomAt j).geometry.coefficientHom.comp
        (input.canonicalAuthoredPulledRouteGeometryEdge edge).geometry.coefficientHom =
      (input.sourceTransport.edgeLift edge).geometry.coefficientHom.comp
        (input.canonicalAuthoredPulledRouteGeometryHomAt i).geometry.coefficientHom at h
  rw [input.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom,
    input.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom,
    input.sourceTransport.edge_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- Exact endpoint naturality makes the independently pulled-back
canonical-authored base edge an isomorphism, without redefining the edge by
conjugation. -/
theorem canonicalAuthoredBaseRouteGeometryEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show input.canonicalAuthoredBaseRouteGeometryAt i ⟶
      input.canonicalAuthoredBaseRouteGeometryAt j from
      input.canonicalAuthoredBaseRouteGeometryEdge edge) := by
  let comparison :=
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt j
  letI : IsIso (show input.canonicalAuthoredBaseRouteGeometryAt i ⟶
      input.generatedBaseRouteGeometryAt i from
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i) := by
    change IsIso
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i).hom
    infer_instance
  letI : IsIso (show input.generatedBaseRouteGeometryAt i ⟶
      input.generatedBaseRouteGeometryAt j from
      input.generatedBaseRouteGeometryEdge edge) :=
    input.generatedBaseRouteGeometryEdge_isIso edge
  haveI : IsIso
      (input.canonicalAuthoredBaseRouteGeometryEdge edge ≫ comparison.hom) := by
    dsimp only [comparison]
    change IsIso (show input.canonicalAuthoredBaseRouteGeometryAt i ⟶
      input.generatedBaseRouteGeometryAt j from
        (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt j))
    rw [input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_naturality edge]
    change IsIso
      ((show input.canonicalAuthoredBaseRouteGeometryAt i ⟶
          input.generatedBaseRouteGeometryAt i from
          input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i) ≫
        (show input.generatedBaseRouteGeometryAt i ⟶
          input.generatedBaseRouteGeometryAt j from
          input.generatedBaseRouteGeometryEdge edge))
    infer_instance
  exact IsIso.of_isIso_comp_right
    (input.canonicalAuthoredBaseRouteGeometryEdge edge) comparison.hom

/-- Exact endpoint naturality makes the independently pulled-back
canonical-authored pulled edge an isomorphism, without redefining the edge by
conjugation. -/
theorem canonicalAuthoredPulledRouteGeometryEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show input.canonicalAuthoredPulledRouteGeometryAt i ⟶
      input.canonicalAuthoredPulledRouteGeometryAt j from
      input.canonicalAuthoredPulledRouteGeometryEdge edge) := by
  let comparison :=
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt j
  letI : IsIso (show input.canonicalAuthoredPulledRouteGeometryAt i ⟶
      input.generatedPulledRouteGeometryAt i from
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i) := by
    change IsIso
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i).hom
    infer_instance
  letI : IsIso (show input.generatedPulledRouteGeometryAt i ⟶
      input.generatedPulledRouteGeometryAt j from
      input.generatedPulledRouteGeometryEdge edge) :=
    input.generatedPulledRouteGeometryEdge_isIso edge
  haveI : IsIso
      (input.canonicalAuthoredPulledRouteGeometryEdge edge ≫ comparison.hom) := by
    dsimp only [comparison]
    change IsIso (show input.canonicalAuthoredPulledRouteGeometryAt i ⟶
      input.generatedPulledRouteGeometryAt j from
        (input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt j))
    rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_naturality edge]
    change IsIso
      ((show input.canonicalAuthoredPulledRouteGeometryAt i ⟶
          input.generatedPulledRouteGeometryAt i from
          input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i) ≫
        (show input.generatedPulledRouteGeometryAt i ⟶
          input.generatedPulledRouteGeometryAt j from
          input.generatedPulledRouteGeometryEdge edge))
    infer_instance
  exact IsIso.of_isIso_comp_right
    (input.canonicalAuthoredPulledRouteGeometryEdge edge) comparison.hom

/-- The canonical-authored base edge has the geometry-stage strong
cocartesian qualification. -/
theorem canonicalAuthoredBaseRouteGeometryEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (geometryProjection U).IsStronglyCocartesian
      (input.canonicalAuthoredBaseRouteGeometryEdge edge).base
      (input.canonicalAuthoredBaseRouteGeometryEdge edge) := by
  letI : IsIso (show input.canonicalAuthoredBaseRouteGeometryAt i ⟶
      input.canonicalAuthoredBaseRouteGeometryAt j from
      input.canonicalAuthoredBaseRouteGeometryEdge edge) :=
    input.canonicalAuthoredBaseRouteGeometryEdge_isIso edge
  letI : (geometryProjection U).IsHomLift
      (input.canonicalAuthoredBaseRouteGeometryEdge edge).base
      (input.canonicalAuthoredBaseRouteGeometryEdge edge) := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map
        (input.canonicalAuthoredBaseRouteGeometryEdge edge))
      (input.canonicalAuthoredBaseRouteGeometryEdge edge)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := geometryProjection U)
    (f := (input.canonicalAuthoredBaseRouteGeometryEdge edge).base)
    (input.canonicalAuthoredBaseRouteGeometryEdge edge)

/-- The canonical-authored pulled edge has the geometry-stage strong
cocartesian qualification. -/
theorem canonicalAuthoredPulledRouteGeometryEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (geometryProjection U).IsStronglyCocartesian
      (input.canonicalAuthoredPulledRouteGeometryEdge edge).base
      (input.canonicalAuthoredPulledRouteGeometryEdge edge) := by
  letI : IsIso (show input.canonicalAuthoredPulledRouteGeometryAt i ⟶
      input.canonicalAuthoredPulledRouteGeometryAt j from
      input.canonicalAuthoredPulledRouteGeometryEdge edge) :=
    input.canonicalAuthoredPulledRouteGeometryEdge_isIso edge
  letI : (geometryProjection U).IsHomLift
      (input.canonicalAuthoredPulledRouteGeometryEdge edge).base
      (input.canonicalAuthoredPulledRouteGeometryEdge edge) := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map
        (input.canonicalAuthoredPulledRouteGeometryEdge edge))
      (input.canonicalAuthoredPulledRouteGeometryEdge edge)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := geometryProjection U)
    (f := (input.canonicalAuthoredPulledRouteGeometryEdge edge).base)
    (input.canonicalAuthoredPulledRouteGeometryEdge edge)

/-- The canonical-authored base edge has the core-stage strong cocartesian
qualification over the existing generated core diagram. -/
theorem canonicalAuthoredBaseRouteCoreEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (input.canonicalAuthoredBaseRouteGeometryEdge edge).base.base
      (input.canonicalAuthoredBaseRouteGeometryEdge edge).base := by
  rw [input.canonicalAuthoredBaseRouteGeometryEdge_base edge]
  letI : IsIso (show
      (input.canonicalAuthoredBaseRouteGeometryAt i).core ⟶
        (input.canonicalAuthoredBaseRouteGeometryAt j).core from
      input.canonicalAuthoredBaseRouteCoreEdge edge) := by
    unfold canonicalAuthoredBaseRouteCoreEdge
    exact input.generatedBaseRouteCoreEdge_isIso edge
  letI : (packageProjection U).IsHomLift
      (input.canonicalAuthoredBaseRouteCoreEdge edge).base
      (input.canonicalAuthoredBaseRouteCoreEdge edge) := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map
        (input.canonicalAuthoredBaseRouteCoreEdge edge))
      (input.canonicalAuthoredBaseRouteCoreEdge edge)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := packageProjection U)
    (f := (input.canonicalAuthoredBaseRouteCoreEdge edge).base)
    (input.canonicalAuthoredBaseRouteCoreEdge edge)

/-- The canonical-authored pulled edge has the core-stage strong cocartesian
qualification over the existing generated pulled core diagram. -/
theorem canonicalAuthoredPulledRouteCoreEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (input.canonicalAuthoredPulledRouteGeometryEdge edge).base.base
      (input.canonicalAuthoredPulledRouteGeometryEdge edge).base := by
  rw [input.canonicalAuthoredPulledRouteGeometryEdge_base edge]
  letI : IsIso (show
      (input.canonicalAuthoredPulledRouteGeometryAt i).core ⟶
        (input.canonicalAuthoredPulledRouteGeometryAt j).core from
      input.canonicalAuthoredPulledRouteCoreEdge edge) := by
    unfold canonicalAuthoredPulledRouteCoreEdge
    exact input.generatedPulledRouteCoreEdge_isIso edge
  letI : (packageProjection U).IsHomLift
      (input.canonicalAuthoredPulledRouteCoreEdge edge).base
      (input.canonicalAuthoredPulledRouteCoreEdge edge) := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map
        (input.canonicalAuthoredPulledRouteCoreEdge edge))
      (input.canonicalAuthoredPulledRouteCoreEdge edge)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := packageProjection U)
    (f := (input.canonicalAuthoredPulledRouteCoreEdge edge).base)
    (input.canonicalAuthoredPulledRouteCoreEdge edge)

/-- Exact comparator conjugation makes the direct canonical-authored base
comparator an isomorphism in the complete geometry category. -/
theorem canonicalAuthoredBaseRouteComparator_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    IsIso (show
      input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell) ⟶
        input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell) from
      input.canonicalAuthoredBaseRouteComparator cell) := by
  let comparison := input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
    (P.twoTarget cell)
  letI : IsIso (show
      input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell) ⟶
        input.generatedBaseRouteGeometryAt (P.twoTarget cell) from
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
        (P.twoTarget cell)) := by
    change IsIso
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
        (P.twoTarget cell)).hom
    infer_instance
  letI : IsIso (show
      input.generatedBaseRouteGeometryAt (P.twoTarget cell) ⟶
        input.generatedBaseRouteGeometryAt (P.twoTarget cell) from
      CompositeFiberAut.hom (input.generatedBaseRouteComparator cell)) := by
    change IsIso (input.generatedBaseRouteComparator cell).1.hom
    infer_instance
  haveI : IsIso
      (input.canonicalAuthoredBaseRouteComparator cell ≫ comparison.hom) := by
    dsimp only [comparison]
    change IsIso (show
      input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell) ⟶
        input.generatedBaseRouteGeometryAt (P.twoTarget cell) from
      (input.canonicalAuthoredBaseRouteComparator cell).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)))
    rw [input.canonicalAuthoredBaseRouteComparator_exact_conjugation cell]
    change IsIso
      ((show input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell) ⟶
          input.generatedBaseRouteGeometryAt (P.twoTarget cell) from
          input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
            (P.twoTarget cell)) ≫
        (show input.generatedBaseRouteGeometryAt (P.twoTarget cell) ⟶
          input.generatedBaseRouteGeometryAt (P.twoTarget cell) from
          CompositeFiberAut.hom (input.generatedBaseRouteComparator cell)))
    infer_instance
  exact IsIso.of_isIso_comp_right
    (input.canonicalAuthoredBaseRouteComparator cell) comparison.hom

/-- Exact comparator conjugation makes the direct canonical-authored pulled
comparator an isomorphism in the complete geometry category. -/
theorem canonicalAuthoredPulledRouteComparator_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    IsIso (show
      input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell) ⟶
        input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell) from
      input.canonicalAuthoredPulledRouteComparator cell) := by
  let comparison := input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
    (P.twoTarget cell)
  letI : IsIso (show
      input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell) ⟶
        input.generatedPulledRouteGeometryAt (P.twoTarget cell) from
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
        (P.twoTarget cell)) := by
    change IsIso
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
        (P.twoTarget cell)).hom
    infer_instance
  letI : IsIso (show
      input.generatedPulledRouteGeometryAt (P.twoTarget cell) ⟶
        input.generatedPulledRouteGeometryAt (P.twoTarget cell) from
      CompositeFiberAut.hom (input.generatedPulledRouteComparator cell)) := by
    change IsIso (input.generatedPulledRouteComparator cell).1.hom
    infer_instance
  haveI : IsIso
      (input.canonicalAuthoredPulledRouteComparator cell ≫ comparison.hom) := by
    dsimp only [comparison]
    change IsIso (show
      input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell) ⟶
        input.generatedPulledRouteGeometryAt (P.twoTarget cell) from
      (input.canonicalAuthoredPulledRouteComparator cell).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)))
    rw [input.canonicalAuthoredPulledRouteComparator_exact_conjugation cell]
    change IsIso
      ((show input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell) ⟶
          input.generatedPulledRouteGeometryAt (P.twoTarget cell) from
          input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
            (P.twoTarget cell)) ≫
        (show input.generatedPulledRouteGeometryAt (P.twoTarget cell) ⟶
          input.generatedPulledRouteGeometryAt (P.twoTarget cell) from
          CompositeFiberAut.hom (input.generatedPulledRouteComparator cell)))
    infer_instance
  exact IsIso.of_isIso_comp_right
    (input.canonicalAuthoredPulledRouteComparator cell) comparison.hom

/-- The direct base comparator, packaged with the isomorphism recovered from
endpoint conjugation, is a composite-fiber automorphism. -/
noncomputable def canonicalAuthoredBaseRouteFixedComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut
      (input.canonicalAuthoredBaseRouteFixedGeometryAt
        (P.twoTarget cell)).package := by
  letI : IsIso (show
      input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell) ⟶
        input.canonicalAuthoredBaseRouteGeometryAt (P.twoTarget cell) from
      input.canonicalAuthoredBaseRouteComparator cell) :=
    input.canonicalAuthoredBaseRouteComparator_isIso cell
  refine ⟨asIso (input.canonicalAuthoredBaseRouteComparator cell), ?_⟩
  change (input.canonicalAuthoredBaseRouteComparatorCore cell).base = _
  unfold canonicalAuthoredBaseRouteComparatorCore
  exact CompositeFiberAut.hom_base_base_eq
    (input.generatedBaseRouteComparator cell)

/-- The direct pulled comparator, packaged with the isomorphism recovered
from endpoint conjugation, is a composite-fiber automorphism. -/
noncomputable def canonicalAuthoredPulledRouteFixedComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut
      (input.canonicalAuthoredPulledRouteFixedGeometryAt
        (P.twoTarget cell)).package := by
  letI : IsIso (show
      input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell) ⟶
        input.canonicalAuthoredPulledRouteGeometryAt (P.twoTarget cell) from
      input.canonicalAuthoredPulledRouteComparator cell) :=
    input.canonicalAuthoredPulledRouteComparator_isIso cell
  refine ⟨asIso (input.canonicalAuthoredPulledRouteComparator cell), ?_⟩
  change (input.canonicalAuthoredPulledRouteComparatorCore cell).base = _
  unfold canonicalAuthoredPulledRouteComparatorCore
  exact CompositeFiberAut.hom_base_base_eq
    (input.generatedPulledRouteComparator cell)

/-- The composite-fiber wrapper retains the literal canonical-authored base
comparator as its forward geometry morphism. -/
@[simp] theorem canonicalAuthoredBaseRouteFixedComparator_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut.hom
        (input.canonicalAuthoredBaseRouteFixedComparator cell) =
      input.canonicalAuthoredBaseRouteComparator cell := rfl

/-- The composite-fiber wrapper retains the literal canonical-authored
pulled comparator as its forward geometry morphism. -/
@[simp] theorem canonicalAuthoredPulledRouteFixedComparator_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut.hom
        (input.canonicalAuthoredPulledRouteFixedComparator cell) =
      input.canonicalAuthoredPulledRouteComparator cell := rfl

/-- The actual base comparator factorization forces the canonical-authored
comparator coefficient map to be the identity. -/
theorem canonicalAuthoredBaseRouteFixedComparator_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.canonicalAuthoredBaseRouteFixedComparator cell)).geometry.coefficientHom =
        RingHom.id k := by
  rw [input.canonicalAuthoredBaseRouteFixedComparator_hom cell]
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredBaseRouteComparator_fac cell)
  change
    (input.canonicalAuthoredBaseRouteGeometryHomAt
        (P.twoTarget cell)).geometry.coefficientHom.comp
      (input.canonicalAuthoredBaseRouteComparator cell).geometry.coefficientHom =
    (CompositeFiberAut.hom
        (input.sourceTransport.comparator cell)).geometry.coefficientHom.comp
      (input.canonicalAuthoredBaseRouteGeometryHomAt
        (P.twoTarget cell)).geometry.coefficientHom at h
  rw [input.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom,
    input.sourceTransport.comparator_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- The actual pulled comparator factorization forces the canonical-authored
comparator coefficient map to be the identity. -/
theorem canonicalAuthoredPulledRouteFixedComparator_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.canonicalAuthoredPulledRouteFixedComparator cell)).geometry.coefficientHom =
        RingHom.id k := by
  rw [input.canonicalAuthoredPulledRouteFixedComparator_hom cell]
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredPulledRouteComparator_fac cell)
  change
    (input.canonicalAuthoredPulledRouteGeometryHomAt
        (P.twoTarget cell)).geometry.coefficientHom.comp
      (input.canonicalAuthoredPulledRouteComparator cell).geometry.coefficientHom =
    (CompositeFiberAut.hom
        (input.sourceTransport.comparator cell)).geometry.coefficientHom.comp
      (input.canonicalAuthoredPulledRouteGeometryHomAt
        (P.twoTarget cell)).geometry.coefficientHom at h
  rw [input.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom,
    input.sourceTransport.comparator_coefficient_id] at h
  simpa only [RingHom.id_comp, RingHom.comp_id] using h

/-- Qualified lift data of the canonical-authored base route. -/
noncomputable def canonicalAuthoredBaseRouteLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerLiftData.{u, v} P U where
  geometry i := (input.canonicalAuthoredBaseRouteFixedGeometryAt i).package
  edgeLift edge := input.canonicalAuthoredBaseRouteFixedGeometryEdge edge
  edgeGeometryStrong edge :=
    input.canonicalAuthoredBaseRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge :=
    input.canonicalAuthoredBaseRouteCoreEdge_isStronglyCocartesian edge

/-- Qualified lift data of the canonical-authored pulled route. -/
noncomputable def canonicalAuthoredPulledRouteLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerLiftData.{u, v} P U where
  geometry i := (input.canonicalAuthoredPulledRouteFixedGeometryAt i).package
  edgeLift edge := input.canonicalAuthoredPulledRouteFixedGeometryEdge edge
  edgeGeometryStrong edge :=
    input.canonicalAuthoredPulledRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge :=
    input.canonicalAuthoredPulledRouteCoreEdge_isStronglyCocartesian edge

/-- Projecting a canonical-authored base path lift recovers the existing
generated base core-diagram map. -/
theorem canonicalAuthoredBaseRoutePathLift_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.canonicalAuthoredBaseRouteLiftData.pathLift path).base =
      (input.generatedBaseRouteCoreDiagram.map path).1 := by
  induction path with
  | nil vertex =>
      have h := congrArg (fun f => f.1)
        (input.generatedBaseRouteCoreDiagram.map_id ⟨vertex⟩)
      exact h.symm
  | cons edge tail ih =>
      change (input.canonicalAuthoredBaseRouteFixedGeometryEdge edge).base.comp
          (input.canonicalAuthoredBaseRouteLiftData.pathLift tail).base = _
      rw [input.canonicalAuthoredBaseRouteFixedGeometryEdge_base edge, ih]
      have h := congrArg (fun f => f.1)
        (input.generatedBaseRouteCoreDiagram.map_comp
          (presentedEdgePath edge) tail)
      exact h.symm

/-- Projecting a canonical-authored pulled path lift recovers the existing
generated pulled core-diagram map. -/
theorem canonicalAuthoredPulledRoutePathLift_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.canonicalAuthoredPulledRouteLiftData.pathLift path).base =
      (input.generatedPulledRouteCoreDiagram.map path).1 := by
  induction path with
  | nil vertex =>
      have h := congrArg (fun f => f.1)
        (input.generatedPulledRouteCoreDiagram.map_id ⟨vertex⟩)
      exact h.symm
  | cons edge tail ih =>
      change (input.canonicalAuthoredPulledRouteFixedGeometryEdge edge).base.comp
          (input.canonicalAuthoredPulledRouteLiftData.pathLift tail).base = _
      rw [input.canonicalAuthoredPulledRouteFixedGeometryEdge_base edge, ih]
      have h := congrArg (fun f => f.1)
        (input.generatedPulledRouteCoreDiagram.map_comp
          (presentedEdgePath edge) tail)
      exact h.symm

/-- Parallel canonical-authored base path lifts agree after the composite
projection because they use the existing generated base core diagram. -/
theorem canonicalAuthoredBaseRouteTwoCellBase
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredBaseRouteLiftData.pathLift
        (P.twoLeft cell)).base.base =
      (input.canonicalAuthoredBaseRouteLiftData.pathLift
        (P.twoRight cell)).base.base := by
  rw [input.canonicalAuthoredBaseRoutePathLift_base,
    input.canonicalAuthoredBaseRoutePathLift_base]
  simpa only [input.generatedBaseRoutePathLift_base] using
    input.generatedBaseRouteTwoCellBase cell

/-- Parallel canonical-authored pulled path lifts agree after the composite
projection because they use the existing generated pulled core diagram. -/
theorem canonicalAuthoredPulledRouteTwoCellBase
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredPulledRouteLiftData.pathLift
        (P.twoLeft cell)).base.base =
      (input.canonicalAuthoredPulledRouteLiftData.pathLift
        (P.twoRight cell)).base.base := by
  rw [input.canonicalAuthoredPulledRoutePathLift_base,
    input.canonicalAuthoredPulledRoutePathLift_base]
  simpa only [input.generatedPulledRoutePathLift_base] using
    input.generatedPulledRouteTwoCellBase cell

/-- Ordinary two-layer transport data underlying the canonical-authored base
route. -/
noncomputable def canonicalAuthoredBaseRouteData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerTransportData.{u, v} P U where
  lift := input.canonicalAuthoredBaseRouteLiftData
  twoCellBase cell := input.canonicalAuthoredBaseRouteTwoCellBase cell
  comparator cell := input.canonicalAuthoredBaseRouteFixedComparator cell

/-- Ordinary two-layer transport data underlying the canonical-authored
pulled route. -/
noncomputable def canonicalAuthoredPulledRouteData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    TwoLayerTransportData.{u, v} P U where
  lift := input.canonicalAuthoredPulledRouteLiftData
  twoCellBase cell := input.canonicalAuthoredPulledRouteTwoCellBase cell
  comparator cell := input.canonicalAuthoredPulledRouteFixedComparator cell

/-- Complete G-109 transport on the canonical-authored base route, retaining
the existing generated base core diagram. -/
noncomputable def canonicalAuthoredBaseRouteTransport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    FixedCoefficientTwoLayerTransportOver P
      input.generatedBaseRouteCoreDiagram k
      input.canonicalAuthoredBaseRouteFixedGeometryAt where
  edgeLift edge := input.canonicalAuthoredBaseRouteFixedGeometryEdge edge
  edge_base edge := input.canonicalAuthoredBaseRouteFixedGeometryEdge_base edge
  edgeGeometryStrong edge :=
    input.canonicalAuthoredBaseRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge :=
    input.canonicalAuthoredBaseRouteCoreEdge_isStronglyCocartesian edge
  twoCellBase cell := input.canonicalAuthoredBaseRouteTwoCellBase cell
  comparator cell := input.canonicalAuthoredBaseRouteFixedComparator cell
  edge_coefficient_id edge :=
    input.canonicalAuthoredBaseRouteFixedGeometryEdge_coefficient_id edge
  comparator_coefficient_id cell :=
    input.canonicalAuthoredBaseRouteFixedComparator_coefficient_id cell

/-- Complete G-109 transport on the canonical-authored pulled route,
retaining the existing generated pulled core diagram. -/
noncomputable def canonicalAuthoredPulledRouteTransport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    FixedCoefficientTwoLayerTransportOver P
      input.generatedPulledRouteCoreDiagram k
      input.canonicalAuthoredPulledRouteFixedGeometryAt where
  edgeLift edge := input.canonicalAuthoredPulledRouteFixedGeometryEdge edge
  edge_base edge := input.canonicalAuthoredPulledRouteFixedGeometryEdge_base edge
  edgeGeometryStrong edge :=
    input.canonicalAuthoredPulledRouteGeometryEdge_isStronglyCocartesian edge
  edgeCoreStrong edge :=
    input.canonicalAuthoredPulledRouteCoreEdge_isStronglyCocartesian edge
  twoCellBase cell := input.canonicalAuthoredPulledRouteTwoCellBase cell
  comparator cell := input.canonicalAuthoredPulledRouteFixedComparator cell
  edge_coefficient_id edge :=
    input.canonicalAuthoredPulledRouteFixedGeometryEdge_coefficient_id edge
  comparator_coefficient_id cell :=
    input.canonicalAuthoredPulledRouteFixedComparator_coefficient_id cell

/-- Forgetting the fixed-coefficient evidence from the canonical-authored base
transport recovers its qualified lift data. -/
@[simp] theorem canonicalAuthoredBaseRouteTransport_toTwoLayerLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.canonicalAuthoredBaseRouteTransport.toTwoLayerLiftData =
      input.canonicalAuthoredBaseRouteLiftData := rfl

/-- Forgetting the fixed-coefficient evidence from the canonical-authored
pulled transport recovers its qualified lift data. -/
@[simp] theorem canonicalAuthoredPulledRouteTransport_toTwoLayerLiftData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.canonicalAuthoredPulledRouteTransport.toTwoLayerLiftData =
      input.canonicalAuthoredPulledRouteLiftData := rfl

/-- Forgetting only fixed-coefficient evidence from the canonical-authored
base transport recovers its ordinary two-layer transport data. -/
@[simp] theorem canonicalAuthoredBaseRouteTransport_toTwoLayerTransportData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.canonicalAuthoredBaseRouteTransport.toTwoLayerTransportData =
      input.canonicalAuthoredBaseRouteData := rfl

/-- Forgetting only fixed-coefficient evidence from the canonical-authored
pulled transport recovers its ordinary two-layer transport data. -/
@[simp] theorem canonicalAuthoredPulledRouteTransport_toTwoLayerTransportData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.canonicalAuthoredPulledRouteTransport.toTwoLayerTransportData =
      input.canonicalAuthoredPulledRouteData := rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
