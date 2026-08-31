import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointGeometryLaws
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryEdges

/-!
# Presentation naturality of the complete endpoint comparisons

The canonical-authored presentation edges are constructed independently by
pulling each authored source edge back through the direct strongly Cartesian
normalization legs.  Strong-Cartesian uniqueness then identifies their
transport across the complete endpoint comparison isomorphisms with the
previously generated presentation edges.

Implementation notes: the canonical-authored edges are not defined by
conjugating the generated edges with the endpoint isomorphisms.  They use the
literal source transport and the direct route legs, so the naturality squares
are consequences of the two universal properties rather than definitionally
stored coherence.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The generated exact base core edge, transported to the independently
normalized canonical-authored endpoint types. -/
noncomputable def canonicalAuthoredBaseRouteCoreEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    PackageTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i).core
      (input.canonicalAuthoredBaseRouteGeometryAt j).core := by
  simpa only [input.canonicalAuthoredBaseRouteGeometryAt_core] using
    (input.generatedBaseRouteCoreDiagram.map (presentedEdgePath edge)).1

/-- Cartesian pullback of an authored source edge through the direct
canonical-authored base normalization leg. -/
noncomputable def canonicalAuthoredBaseRouteRefinementGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.canonicalAuthoredBaseRouteGeometryAt j) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredBaseRouteGeometryHomAt j).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt j) :=
    input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian j
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredBaseRouteGeometryHomAt i)
    ((exactGeometryToRefinementGeometry U).map
      (input.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (input.canonicalAuthoredBaseRouteGeometryHomAt j).base
    (input.canonicalAuthoredBaseRouteGeometryHomAt j)
    (g := (exactPackageToRefinement U).map
      (input.canonicalAuthoredBaseRouteCoreEdge edge))
    (f' := candidate.base)
    (by simpa [canonicalAuthoredBaseRouteCoreEdge] using
      (input.generatedBaseRouteCoreEdge_fac edge).symm)
    candidate

/-- The direct base presentation edge lies over the generated exact core
presentation edge. -/
theorem canonicalAuthoredBaseRouteRefinementGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredBaseRouteRefinementGeometryEdge edge).base =
      (exactPackageToRefinement U).map
        (input.canonicalAuthoredBaseRouteCoreEdge edge) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredBaseRouteGeometryHomAt j).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt j) :=
    input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian j
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredBaseRouteGeometryHomAt i)
    ((exactGeometryToRefinementGeometry U).map
      (input.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  unfold canonicalAuthoredBaseRouteRefinementGeometryEdge
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (input.canonicalAuthoredBaseRouteCoreEdge edge))
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (input.canonicalAuthoredBaseRouteGeometryHomAt j).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt j)
      (by simpa [canonicalAuthoredBaseRouteCoreEdge] using
        (input.generatedBaseRouteCoreEdge_fac edge).symm)
      candidate)).symm

/-- Exact complete canonical-authored base presentation edge. -/
noncomputable def canonicalAuthoredBaseRouteGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.canonicalAuthoredBaseRouteGeometryAt j) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredBaseRouteCoreEdge edge)
    (input.canonicalAuthoredBaseRouteRefinementGeometryEdge edge)
    (input.canonicalAuthoredBaseRouteRefinementGeometryEdge_base edge)

@[simp] theorem canonicalAuthoredBaseRouteGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredBaseRouteGeometryEdge edge).base =
      input.canonicalAuthoredBaseRouteCoreEdge edge := rfl

/-- Refinement embedding recovers the independently constructed base edge. -/
theorem canonicalAuthoredBaseRouteGeometryEdge_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseRouteGeometryEdge edge) =
      input.canonicalAuthoredBaseRouteRefinementGeometryEdge edge :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The direct base presentation edge factors against the literal authored
source edge. -/
theorem canonicalAuthoredBaseRouteGeometryEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteGeometryEdge edge))
        (input.canonicalAuthoredBaseRouteGeometryHomAt j) =
      RefinementGeometryHom.comp
        (input.canonicalAuthoredBaseRouteGeometryHomAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.sourceTransport.edgeLift edge)) := by
  rw [input.canonicalAuthoredBaseRouteGeometryEdge_toRefinement edge]
  unfold canonicalAuthoredBaseRouteRefinementGeometryEdge
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredBaseRouteGeometryHomAt j).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt j) :=
    input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian j
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredBaseRouteGeometryHomAt i)
    ((exactGeometryToRefinementGeometry U).map
      (input.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (input.canonicalAuthoredBaseRouteGeometryHomAt j).base
    (input.canonicalAuthoredBaseRouteGeometryHomAt j)
    (by simpa [canonicalAuthoredBaseRouteCoreEdge] using
      (input.generatedBaseRouteCoreEdge_fac edge).symm)
    candidate

/-- The generated exact pulled core edge, transported to the independently
normalized canonical-authored endpoint types. -/
noncomputable def canonicalAuthoredPulledRouteCoreEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    PackageTotalHom (input.canonicalAuthoredPulledRouteGeometryAt i).core
      (input.canonicalAuthoredPulledRouteGeometryAt j).core := by
  simpa only [input.canonicalAuthoredPulledRouteGeometryAt_core] using
    (input.generatedPulledRouteCoreDiagram.map (presentedEdgePath edge)).1

/-- Cartesian pullback of an authored source edge through the direct
canonical-authored pulled normalization leg. -/
noncomputable def canonicalAuthoredPulledRouteRefinementGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom (input.canonicalAuthoredPulledRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt j) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredPulledRouteGeometryHomAt j).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt j) :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian j
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredPulledRouteGeometryHomAt i)
    ((exactGeometryToRefinementGeometry U).map
      (input.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (input.canonicalAuthoredPulledRouteGeometryHomAt j).base
    (input.canonicalAuthoredPulledRouteGeometryHomAt j)
    (g := (exactPackageToRefinement U).map
      (input.canonicalAuthoredPulledRouteCoreEdge edge))
    (f' := candidate.base)
    (by simpa [canonicalAuthoredPulledRouteCoreEdge] using
      (input.generatedPulledRouteCoreEdge_fac edge).symm)
    candidate

/-- The direct pulled presentation edge lies over the generated exact core
presentation edge. -/
theorem canonicalAuthoredPulledRouteRefinementGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredPulledRouteRefinementGeometryEdge edge).base =
      (exactPackageToRefinement U).map
        (input.canonicalAuthoredPulledRouteCoreEdge edge) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredPulledRouteGeometryHomAt j).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt j) :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian j
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredPulledRouteGeometryHomAt i)
    ((exactGeometryToRefinementGeometry U).map
      (input.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  unfold canonicalAuthoredPulledRouteRefinementGeometryEdge
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (input.canonicalAuthoredPulledRouteCoreEdge edge))
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (input.canonicalAuthoredPulledRouteGeometryHomAt j).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt j)
      (by simpa [canonicalAuthoredPulledRouteCoreEdge] using
        (input.generatedPulledRouteCoreEdge_fac edge).symm)
      candidate)).symm

/-- Exact complete canonical-authored pulled presentation edge. -/
noncomputable def canonicalAuthoredPulledRouteGeometryEdge
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (input.canonicalAuthoredPulledRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt j) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalAuthoredPulledRouteCoreEdge edge)
    (input.canonicalAuthoredPulledRouteRefinementGeometryEdge edge)
    (input.canonicalAuthoredPulledRouteRefinementGeometryEdge_base edge)

@[simp] theorem canonicalAuthoredPulledRouteGeometryEdge_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredPulledRouteGeometryEdge edge).base =
      input.canonicalAuthoredPulledRouteCoreEdge edge := rfl

/-- Refinement embedding recovers the independently constructed pulled edge. -/
theorem canonicalAuthoredPulledRouteGeometryEdge_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledRouteGeometryEdge edge) =
      input.canonicalAuthoredPulledRouteRefinementGeometryEdge edge :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The direct pulled presentation edge factors against the literal authored
source edge. -/
theorem canonicalAuthoredPulledRouteGeometryEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteGeometryEdge edge))
        (input.canonicalAuthoredPulledRouteGeometryHomAt j) =
      RefinementGeometryHom.comp
        (input.canonicalAuthoredPulledRouteGeometryHomAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.sourceTransport.edgeLift edge)) := by
  rw [input.canonicalAuthoredPulledRouteGeometryEdge_toRefinement edge]
  unfold canonicalAuthoredPulledRouteRefinementGeometryEdge
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.canonicalAuthoredPulledRouteGeometryHomAt j).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt j) :=
    input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian j
  let candidate := RefinementGeometryHom.comp
    (input.canonicalAuthoredPulledRouteGeometryHomAt i)
    ((exactGeometryToRefinementGeometry U).map
      (input.sourceTransport.edgeLift edge))
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (input.canonicalAuthoredPulledRouteGeometryHomAt j).base
    (input.canonicalAuthoredPulledRouteGeometryHomAt j)
    (by simpa [canonicalAuthoredPulledRouteCoreEdge] using
      (input.generatedPulledRouteCoreEdge_fac edge).symm)
    candidate

/-- The complete base endpoint comparisons form a natural family on the
independently generated presentation edges. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteGeometryEdge edge))
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom =
      RefinementGeometryHom.comp
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedBaseRouteGeometryEdge edge)) := by
  let left := RefinementGeometryHom.comp
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteGeometryEdge edge))
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom
  let right := RefinementGeometryHom.comp
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom
    ((exactGeometryToRefinementGeometry U).map
      (input.generatedBaseRouteGeometryEdge edge))
  have hrightBase : right.base = left.base := by
    dsimp [left, right]
    change
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.base ≫
          (exactPackageToRefinement U).map
            (input.generatedBaseRouteGeometryEdge edge).base =
        (exactPackageToRefinement U).map
            (input.canonicalAuthoredBaseRouteGeometryEdge edge).base ≫
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom.base
    rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_base i,
      input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_base j]
    exact (Category.comp_id ((exactPackageToRefinement U).map
      (input.generatedBaseRouteCoreDiagram.map
        (presentedEdgePath edge)).1)).symm
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift left
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      left.base right hrightBase
  letI := input.generatedBaseRouteLegAt_isStronglyCartesian j
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedBaseRouteLegAt j).base
    (input.generatedBaseRouteLegAt j)
    left.base
  change RefinementGeometryHom.comp left
      (input.generatedBaseRouteLegAt j) =
    RefinementGeometryHom.comp right
      (input.generatedBaseRouteLegAt j)
  dsimp only [left, right]
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
  calc
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteGeometryEdge edge))
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom
          (input.generatedBaseRouteLegAt j)) =
      RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteGeometryEdge edge))
        (input.canonicalAuthoredBaseRouteGeometryHomAt j) := by
          exact congrArg _
            (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac j)
    _ = RefinementGeometryHom.comp
        (input.canonicalAuthoredBaseRouteGeometryHomAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.sourceTransport.edgeLift edge)) :=
      input.canonicalAuthoredBaseRouteGeometryEdge_fac edge
    _ = RefinementGeometryHom.comp
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom
          ((exactGeometryToRefinementGeometry U).map
            (input.generatedBaseRouteGeometryEdge edge)))
        (input.generatedBaseRouteLegAt j) := by
      rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
        input.generatedBaseRouteGeometryEdge_fac edge,
        ← UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
      exact congrArg
        (fun hom => RefinementGeometryHom.comp hom
          ((exactGeometryToRefinementGeometry U).map
            (input.sourceTransport.edgeLift edge)))
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac i).symm

/-- The complete pulled endpoint comparisons form a natural family on the
independently generated presentation edges. -/
theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteGeometryEdge edge))
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).hom =
      RefinementGeometryHom.comp
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge)) := by
  let left := RefinementGeometryHom.comp
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredPulledRouteGeometryEdge edge))
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).hom
  let right := RefinementGeometryHom.comp
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom
    ((exactGeometryToRefinementGeometry U).map
      (input.generatedPulledRouteGeometryEdge edge))
  have hrightBase : right.base = left.base := by
    dsimp [left, right]
    change
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.base ≫
          (exactPackageToRefinement U).map
            (input.generatedPulledRouteGeometryEdge edge).base =
        (exactPackageToRefinement U).map
            (input.canonicalAuthoredPulledRouteGeometryEdge edge).base ≫
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).hom.base
    rw [input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_base i,
      input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_base j]
    exact (Category.comp_id ((exactPackageToRefinement U).map
      (input.generatedPulledRouteCoreDiagram.map
        (presentedEdgePath edge)).1)).symm
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift left
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      left.base right hrightBase
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian j
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt j).base
    (input.generatedPulledRouteLegAt j)
    left.base
  change RefinementGeometryHom.comp left
      (input.generatedPulledRouteLegAt j) =
    RefinementGeometryHom.comp right
      (input.generatedPulledRouteLegAt j)
  dsimp only [left, right]
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
  calc
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteGeometryEdge edge))
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).hom
          (input.generatedPulledRouteLegAt j)) =
      RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteGeometryEdge edge))
        (input.canonicalAuthoredPulledRouteGeometryHomAt j) := by
          exact congrArg _
            (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac j)
    _ = RefinementGeometryHom.comp
        (input.canonicalAuthoredPulledRouteGeometryHomAt i)
        ((exactGeometryToRefinementGeometry U).map
          (input.sourceTransport.edgeLift edge)) :=
      input.canonicalAuthoredPulledRouteGeometryEdge_fac edge
    _ = RefinementGeometryHom.comp
        (RefinementGeometryHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom
          ((exactGeometryToRefinementGeometry U).map
            (input.generatedPulledRouteGeometryEdge edge)))
        (input.generatedPulledRouteLegAt j) := by
      rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
        input.generatedPulledRouteGeometryEdge_fac edge,
        ← UpperGeometryCleavage.refinementGeometryHom_comp_assoc]
      exact congrArg
        (fun hom => RefinementGeometryHom.comp hom
          ((exactGeometryToRefinementGeometry U).map
            (input.sourceTransport.edgeLift edge)))
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac i).symm

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
