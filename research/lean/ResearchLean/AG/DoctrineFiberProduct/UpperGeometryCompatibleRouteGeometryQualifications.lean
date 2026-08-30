import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteEdgeQualifications

/-!
# Geometry-stage qualifications for compatible route edges

The generated route refinement edges are Cartesian by cancellation against
their literal Cartesian route legs.  Their exact core projections are
isomorphisms, so the refinement edges are isomorphisms as well.  A reusable
exactification lemma then reflects an explicit refinement inverse back to the
complete geometry category.  This yields the geometry-stage cocartesian
qualifications required by the fixed-coefficient transport contract without
adding route certificates to the compatible input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCleavage

/-- Exactification preserves an isomorphism when both the complete lower map
and the refinement geometry map are isomorphisms.  The inverse is obtained by
exactifying the actual refinement inverse, and both inverse laws are reflected
through the faithful exact embedding. -/
theorem exactGeometryHomOfRefinement_isIso
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (hom : RefinementGeometryHom G H)
    (hbase : hom.base = (exactPackageToRefinement U).map f)
    [IsIso (show G.core ⟶ H.core from f)]
    [IsIso (show RefinementGeometryObject.mk G ⟶
      RefinementGeometryObject.mk H from hom)] :
    IsIso (show G ⟶ H from
      exactGeometryHomOfRefinement f hom hbase) := by
  let hom' : RefinementGeometryObject.mk G ⟶
      RefinementGeometryObject.mk H := hom
  let f' : G.core ⟶ H.core := f
  have hinvbase : (show RefinementGeometryHom H G from inv hom').base =
      (exactPackageToRefinement U).map (inv f') := by
    change (refinementGeometryProjection U).map (inv hom') =
      (exactPackageToRefinement U).map (inv f')
    calc
      (refinementGeometryProjection U).map (inv hom') =
          inv ((refinementGeometryProjection U).map hom') :=
        Functor.map_inv _ _
      _ = inv ((exactPackageToRefinement U).map f') :=
        IsIso.inv_eq_inv.mpr hbase
      _ = (exactPackageToRefinement U).map (inv f') :=
        (Functor.map_inv _ _).symm
  let inverse : GeometryTotalHom H G :=
    exactGeometryHomOfRefinement (inv f')
      (show RefinementGeometryHom H G from inv hom') hinvbase
  refine ⟨⟨inverse, ?_, ?_⟩⟩
  · apply (exactGeometryToRefinementGeometry U).map_injective
    rw [Functor.map_comp,
      exactGeometryHomOfRefinement_toRefinement,
      exactGeometryHomOfRefinement_toRefinement]
    change hom' ≫ inv hom' = 𝟙 _
    simp
  · apply (exactGeometryToRefinementGeometry U).map_injective
    rw [Functor.map_comp,
      exactGeometryHomOfRefinement_toRefinement,
      exactGeometryHomOfRefinement_toRefinement]
    change inv hom' ≫ hom' = 𝟙 _
    simp

end UpperGeometryCleavage

namespace UpperGeometryCompatibleProblemInputData

/-- The generated base-route refinement geometry edge is strongly Cartesian.
Its composite with the target route leg is the composite of two independently
qualified morphisms: the source route leg and the authored source edge. -/
theorem generatedBaseRouteRefinementGeometryEdge_isStronglyCartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteRefinementGeometryEdge edge).base
      (input.generatedBaseRouteRefinementGeometryEdge edge) := by
  rw [← input.generatedBaseRouteGeometryEdge_toRefinement edge]
  let sourceEdge := (exactGeometryToRefinementGeometry U).map
    (input.sourceTransport.edgeLift edge)
  let targetLeg := input.generatedBaseRouteLegAt j
  letI : IsIso (show (input.sourceGeometry i).package ⟶
      (input.sourceGeometry j).package from
        input.sourceTransport.edgeLift edge) :=
    input.sourceTransportGeometryEdge_isIso edge
  letI : IsIso sourceEdge := by dsimp [sourceEdge]; infer_instance
  letI : (refinementGeometryProjection U).IsHomLift
      sourceEdge.base sourceEdge :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceEdge
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceEdge.base sourceEdge :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceEdge.base) sourceEdge
  letI := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI := input.generatedBaseRouteLegAt_isStronglyCartesian j
  have hright : (refinementGeometryProjection U).IsStronglyCartesian
      (RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
        sourceEdge).base
      (RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
        sourceEdge) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      ((input.generatedBaseRouteLegAt i).base ≫ sourceEdge.base)
      (RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i) sourceEdge)
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  haveI : (refinementGeometryProjection U).IsStronglyCartesian
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteGeometryEdge edge)) targetLeg).base
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteGeometryEdge edge)) targetLeg) := by
    rw [input.generatedBaseRouteGeometryEdge_fac edge]
    exact hright
  haveI : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (input.generatedBaseRouteGeometryEdge edge)).base ≫ targetLeg.base)
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteGeometryEdge edge)) targetLeg) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteGeometryEdge edge)) targetLeg).base
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteGeometryEdge edge)) targetLeg)
    infer_instance
  letI : (refinementGeometryProjection U).IsHomLift
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedBaseRouteGeometryEdge edge)).base
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedBaseRouteGeometryEdge edge)) :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift _
  exact CategoryTheory.Functor.IsStronglyCartesian.of_comp
    (p := refinementGeometryProjection U)
    (f := ((exactGeometryToRefinementGeometry U).map
      (input.generatedBaseRouteGeometryEdge edge)).base)
    (g := targetLeg.base)
    (φ := (exactGeometryToRefinementGeometry U).map
      (input.generatedBaseRouteGeometryEdge edge)) (ψ := targetLeg)

/-- The generated pulled-route refinement geometry edge is strongly Cartesian
by the same cancellation argument on the distinct pulled route. -/
theorem generatedPulledRouteRefinementGeometryEdge_isStronglyCartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteRefinementGeometryEdge edge).base
      (input.generatedPulledRouteRefinementGeometryEdge edge) := by
  rw [← input.generatedPulledRouteGeometryEdge_toRefinement edge]
  let sourceEdge := (exactGeometryToRefinementGeometry U).map
    (input.sourceTransport.edgeLift edge)
  let targetLeg := input.generatedPulledRouteLegAt j
  letI : IsIso (show (input.sourceGeometry i).package ⟶
      (input.sourceGeometry j).package from
        input.sourceTransport.edgeLift edge) :=
    input.sourceTransportGeometryEdge_isIso edge
  letI : IsIso sourceEdge := by dsimp [sourceEdge]; infer_instance
  letI : (refinementGeometryProjection U).IsHomLift
      sourceEdge.base sourceEdge :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceEdge
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceEdge.base sourceEdge :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceEdge.base) sourceEdge
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian j
  have hright : (refinementGeometryProjection U).IsStronglyCartesian
      (RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
        sourceEdge).base
      (RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
        sourceEdge) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      ((input.generatedPulledRouteLegAt i).base ≫ sourceEdge.base)
      (RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i) sourceEdge)
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  haveI : (refinementGeometryProjection U).IsStronglyCartesian
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge)) targetLeg).base
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge)) targetLeg) := by
    rw [input.generatedPulledRouteGeometryEdge_fac edge]
    exact hright
  haveI : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (input.generatedPulledRouteGeometryEdge edge)).base ≫ targetLeg.base)
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge)) targetLeg) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge)) targetLeg).base
      (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge)) targetLeg)
    infer_instance
  letI : (refinementGeometryProjection U).IsHomLift
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedPulledRouteGeometryEdge edge)).base
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedPulledRouteGeometryEdge edge)) :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift _
  exact CategoryTheory.Functor.IsStronglyCartesian.of_comp
    (p := refinementGeometryProjection U)
    (f := ((exactGeometryToRefinementGeometry U).map
      (input.generatedPulledRouteGeometryEdge edge)).base)
    (g := targetLeg.base)
    (φ := (exactGeometryToRefinementGeometry U).map
      (input.generatedPulledRouteGeometryEdge edge)) (ψ := targetLeg)

/-- The base-route refinement edge is an isomorphism: its Cartesian
qualification above lies over the Cycle 37 generated core-edge isomorphism. -/
theorem generatedBaseRouteRefinementGeometryEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show RefinementGeometryObject.mk
        (input.generatedBaseRouteGeometryAt i) ⟶
      RefinementGeometryObject.mk (input.generatedBaseRouteGeometryAt j) from
      input.generatedBaseRouteRefinementGeometryEdge edge) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteRefinementGeometryEdge edge).base
      (input.generatedBaseRouteRefinementGeometryEdge edge) :=
    input.generatedBaseRouteRefinementGeometryEdge_isStronglyCartesian edge
  letI : IsIso (input.generatedBaseRouteCoreDiagram.map
      (presentedEdgePath edge)).1 := input.generatedBaseRouteCoreEdge_isIso edge
  letI : IsIso ((refinementGeometryProjection U).map
      (input.generatedBaseRouteRefinementGeometryEdge edge)) := by
    rw [refinementGeometryProjection_map,
      input.generatedBaseRouteRefinementGeometryEdge_base edge]
    infer_instance
  letI : IsIso (show RefinementPackageObject.mk
      (input.generatedBaseRouteGeometryAt i).core ⟶
      RefinementPackageObject.mk
        (input.generatedBaseRouteGeometryAt j).core from
      (input.generatedBaseRouteRefinementGeometryEdge edge).base) := by
    change IsIso ((refinementGeometryProjection U).map
      (input.generatedBaseRouteRefinementGeometryEdge edge))
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
    (p := refinementGeometryProjection U)
    (f := (input.generatedBaseRouteRefinementGeometryEdge edge).base)
    (input.generatedBaseRouteRefinementGeometryEdge edge)

/-- The pulled-route refinement edge is an isomorphism: its independent
Cartesian cancellation lies over the pulled Cycle 37 core-edge isomorphism. -/
theorem generatedPulledRouteRefinementGeometryEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show RefinementGeometryObject.mk
        (input.generatedPulledRouteGeometryAt i) ⟶
      RefinementGeometryObject.mk (input.generatedPulledRouteGeometryAt j) from
      input.generatedPulledRouteRefinementGeometryEdge edge) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteRefinementGeometryEdge edge).base
      (input.generatedPulledRouteRefinementGeometryEdge edge) :=
    input.generatedPulledRouteRefinementGeometryEdge_isStronglyCartesian edge
  letI : IsIso (input.generatedPulledRouteCoreDiagram.map
      (presentedEdgePath edge)).1 := input.generatedPulledRouteCoreEdge_isIso edge
  letI : IsIso ((refinementGeometryProjection U).map
      (input.generatedPulledRouteRefinementGeometryEdge edge)) := by
    rw [refinementGeometryProjection_map,
      input.generatedPulledRouteRefinementGeometryEdge_base edge]
    infer_instance
  letI : IsIso (show RefinementPackageObject.mk
      (input.generatedPulledRouteGeometryAt i).core ⟶
      RefinementPackageObject.mk
        (input.generatedPulledRouteGeometryAt j).core from
      (input.generatedPulledRouteRefinementGeometryEdge edge).base) := by
    change IsIso ((refinementGeometryProjection U).map
      (input.generatedPulledRouteRefinementGeometryEdge edge))
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
    (p := refinementGeometryProjection U)
    (f := (input.generatedPulledRouteRefinementGeometryEdge edge).base)
    (input.generatedPulledRouteRefinementGeometryEdge edge)

/-- Exactifying the actual base-route refinement inverse gives the inverse of
the complete generated base-route geometry edge. -/
theorem generatedBaseRouteGeometryEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show input.generatedBaseRouteGeometryAt i ⟶
      input.generatedBaseRouteGeometryAt j from
        input.generatedBaseRouteGeometryEdge edge) := by
  letI : IsIso (input.generatedBaseRouteCoreDiagram.map
      (presentedEdgePath edge)).1 := input.generatedBaseRouteCoreEdge_isIso edge
  letI : IsIso (show RefinementGeometryObject.mk
        (input.generatedBaseRouteGeometryAt i) ⟶
      RefinementGeometryObject.mk (input.generatedBaseRouteGeometryAt j) from
      input.generatedBaseRouteRefinementGeometryEdge edge) :=
    input.generatedBaseRouteRefinementGeometryEdge_isIso edge
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_isIso
    (input.generatedBaseRouteCoreDiagram.map (presentedEdgePath edge)).1
    (input.generatedBaseRouteRefinementGeometryEdge edge)
    (input.generatedBaseRouteRefinementGeometryEdge_base edge)

/-- Exactifying the actual pulled-route refinement inverse gives the inverse
of the complete generated pulled-route geometry edge. -/
theorem generatedPulledRouteGeometryEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show input.generatedPulledRouteGeometryAt i ⟶
      input.generatedPulledRouteGeometryAt j from
        input.generatedPulledRouteGeometryEdge edge) := by
  letI : IsIso (input.generatedPulledRouteCoreDiagram.map
      (presentedEdgePath edge)).1 := input.generatedPulledRouteCoreEdge_isIso edge
  letI : IsIso (show RefinementGeometryObject.mk
        (input.generatedPulledRouteGeometryAt i) ⟶
      RefinementGeometryObject.mk (input.generatedPulledRouteGeometryAt j) from
      input.generatedPulledRouteRefinementGeometryEdge edge) :=
    input.generatedPulledRouteRefinementGeometryEdge_isIso edge
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_isIso
    (input.generatedPulledRouteCoreDiagram.map (presentedEdgePath edge)).1
    (input.generatedPulledRouteRefinementGeometryEdge edge)
    (input.generatedPulledRouteRefinementGeometryEdge_base edge)

/-- The complete base-route geometry edge has the G-109 geometry-stage strong
cocartesian qualification, generated from its isomorphism. -/
theorem generatedBaseRouteGeometryEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (geometryProjection U).IsStronglyCocartesian
      (input.generatedBaseRouteGeometryEdge edge).base
      (input.generatedBaseRouteGeometryEdge edge) := by
  letI : IsIso (show input.generatedBaseRouteGeometryAt i ⟶
      input.generatedBaseRouteGeometryAt j from
        input.generatedBaseRouteGeometryEdge edge) :=
    input.generatedBaseRouteGeometryEdge_isIso edge
  letI : (geometryProjection U).IsHomLift
      (input.generatedBaseRouteGeometryEdge edge).base
      (input.generatedBaseRouteGeometryEdge edge) := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map (input.generatedBaseRouteGeometryEdge edge))
      (input.generatedBaseRouteGeometryEdge edge)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := geometryProjection U)
    (f := (input.generatedBaseRouteGeometryEdge edge).base)
    (input.generatedBaseRouteGeometryEdge edge)

/-- The complete pulled-route geometry edge has the G-109 geometry-stage
strong cocartesian qualification, generated from its isomorphism. -/
theorem generatedPulledRouteGeometryEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (geometryProjection U).IsStronglyCocartesian
      (input.generatedPulledRouteGeometryEdge edge).base
      (input.generatedPulledRouteGeometryEdge edge) := by
  letI : IsIso (show input.generatedPulledRouteGeometryAt i ⟶
      input.generatedPulledRouteGeometryAt j from
        input.generatedPulledRouteGeometryEdge edge) :=
    input.generatedPulledRouteGeometryEdge_isIso edge
  letI : (geometryProjection U).IsHomLift
      (input.generatedPulledRouteGeometryEdge edge).base
      (input.generatedPulledRouteGeometryEdge edge) := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map (input.generatedPulledRouteGeometryEdge edge))
      (input.generatedPulledRouteGeometryEdge edge)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := geometryProjection U)
    (f := (input.generatedPulledRouteGeometryEdge edge).base)
    (input.generatedPulledRouteGeometryEdge edge)

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
