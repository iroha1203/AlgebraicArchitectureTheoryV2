import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredReselectionEquivalence
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryPairedCoefficientTrivialReselection

/-!
# Canonical-authored reselected path transport

This module transports actual canonical-authored reselected edges and paths to
their generated-route counterparts.  The comparison is stated in the exact
complete-geometry category and is derived from endpoint naturality and the
Cycle 74 pointwise conjugation, rather than stored as an additional
certificate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

/-- Whiskering a naturality square by a target endomorphism commutes with
transporting that endomorphism by conjugation.  This category-level lemma
keeps later route-specific proofs independent of large definitional unfolds. -/
theorem conjugatedPostcomposition_naturality
    {C : Type u} [Category.{v} C]
    {source target source' target' : C}
    (sourceIso : source ≅ source') (targetIso : target ≅ target')
    (edge : source ⟶ target) (edge' : source' ⟶ target')
    (automorphism : target ⟶ target)
    (naturality : edge ≫ targetIso.hom = sourceIso.hom ≫ edge') :
    (edge ≫ automorphism) ≫ targetIso.hom =
      sourceIso.hom ≫
        (edge' ≫ ((targetIso.inv ≫ automorphism) ≫ targetIso.hom)) := by
  calc
    (edge ≫ automorphism) ≫ targetIso.hom =
        edge ≫ (automorphism ≫ targetIso.hom) :=
      Category.assoc _ _ _
    _ = edge ≫
        (targetIso.hom ≫
          (targetIso.inv ≫ (automorphism ≫ targetIso.hom))) :=
      congrArg (fun hom => edge ≫ hom)
        (targetIso.hom_inv_id_assoc
          (automorphism ≫ targetIso.hom)).symm
    _ = (edge ≫ targetIso.hom) ≫
        (targetIso.inv ≫ (automorphism ≫ targetIso.hom)) :=
      (Category.assoc _ _ _).symm
    _ = (sourceIso.hom ≫ edge') ≫
        (targetIso.inv ≫ (automorphism ≫ targetIso.hom)) :=
      congrArg
        (fun hom => hom ≫
          (targetIso.inv ≫ (automorphism ≫ targetIso.hom)))
        naturality
    _ = sourceIso.hom ≫
        (edge' ≫ (targetIso.inv ≫ (automorphism ≫ targetIso.hom))) :=
      Category.assoc _ _ _
    _ = sourceIso.hom ≫
        (edge' ≫ ((targetIso.inv ≫ automorphism) ≫ targetIso.hom)) :=
      congrArg (fun hom => sourceIso.hom ≫ (edge' ≫ hom))
        (Category.assoc _ _ _).symm

/-- A naturality square for the homs of two isomorphisms gives the inverse
naturality square without an additional premise. -/
theorem inverseNaturality_of_naturality
    {C : Type u} [Category.{v} C]
    {source target source' target' : C}
    (sourceIso : source ≅ source') (targetIso : target ≅ target')
    (edge : source ⟶ target) (edge' : source' ⟶ target')
    (naturality : edge ≫ targetIso.hom = sourceIso.hom ≫ edge') :
    edge' ≫ targetIso.inv = sourceIso.inv ≫ edge := by
  calc
    edge' ≫ targetIso.inv =
        sourceIso.inv ≫
          (sourceIso.hom ≫ (edge' ≫ targetIso.inv)) :=
      (sourceIso.inv_hom_id_assoc
        (edge' ≫ targetIso.inv)).symm
    _ = sourceIso.inv ≫
        ((sourceIso.hom ≫ edge') ≫ targetIso.inv) :=
      congrArg (fun hom => sourceIso.inv ≫ hom)
        (Category.assoc _ _ _).symm
    _ = sourceIso.inv ≫
        ((edge ≫ targetIso.hom) ≫ targetIso.inv) :=
      congrArg (fun hom => sourceIso.inv ≫ (hom ≫ targetIso.inv))
        naturality.symm
    _ = sourceIso.inv ≫ edge := by
      simp

/-- The inverse direction of conjugated postcomposition transport follows
from the same hom naturality square. -/
theorem conjugatedPostcomposition_inverse_naturality
    {C : Type u} [Category.{v} C]
    {source target source' target' : C}
    (sourceIso : source ≅ source') (targetIso : target ≅ target')
    (edge : source ⟶ target) (edge' : source' ⟶ target')
    (automorphism : target' ⟶ target')
    (naturality : edge ≫ targetIso.hom = sourceIso.hom ≫ edge') :
    (edge' ≫ automorphism) ≫ targetIso.inv =
      sourceIso.inv ≫
        (edge ≫ ((targetIso.hom ≫ automorphism) ≫ targetIso.inv)) := by
  exact conjugatedPostcomposition_naturality sourceIso.symm targetIso.symm
    edge' edge automorphism
    (inverseNaturality_of_naturality sourceIso targetIso edge edge' naturality)

namespace UpperGeometryCompatibleProblemInputData

/-- A canonical-authored base reselected edge is carried to its generated
counterpart by the exact endpoint comparison. -/
theorem canonicalAuthoredBaseReselectedEdge_forward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift input.canonicalAuthoredBaseRouteLiftData
      reselection.toUpperEdgeReselection edge).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).comp
        (upperReselectedEdgeLift input.generatedBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
            reselection).toUpperEdgeReselection edge) := by
  rw [upperReselectedEdgeLift_eq_for_g115,
    upperReselectedEdgeLift_eq_for_g115]
  change
    ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        (CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge))).comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).comp
        ((input.generatedBaseRouteGeometryEdge edge).comp
          (CompositeFiberAut.hom
            (input.canonicalAuthoredBaseCompositeFiberAutForwardAt j
              (reselection.toUpperEdgeReselection i j edge))))
  rw [input.canonicalAuthoredBaseCompositeFiberAutForwardAt_hom]
  exact conjugatedPostcomposition_naturality
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt j)
    (input.canonicalAuthoredBaseRouteGeometryEdge edge)
    (input.generatedBaseRouteGeometryEdge edge)
    (CompositeFiberAut.hom
      (reselection.toUpperEdgeReselection i j edge))
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_naturality edge)

/-- A canonical-authored pulled reselected edge is carried to its generated
counterpart by the exact endpoint comparison. -/
theorem canonicalAuthoredPulledReselectedEdge_forward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift input.canonicalAuthoredPulledRouteLiftData
      reselection.toUpperEdgeReselection edge).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i).comp
        (upperReselectedEdgeLift input.generatedPulledRouteLiftData
          (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
            reselection).toUpperEdgeReselection edge) := by
  rw [upperReselectedEdgeLift_eq_for_g115,
    upperReselectedEdgeLift_eq_for_g115]
  change
    ((input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
        (CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge))).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i).comp
        ((input.generatedPulledRouteGeometryEdge edge).comp
          (CompositeFiberAut.hom
            (input.canonicalAuthoredPulledCompositeFiberAutForwardAt j
              (reselection.toUpperEdgeReselection i j edge))))
  rw [input.canonicalAuthoredPulledCompositeFiberAutForwardAt_hom]
  exact conjugatedPostcomposition_naturality
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt j)
    (input.canonicalAuthoredPulledRouteGeometryEdge edge)
    (input.generatedPulledRouteGeometryEdge edge)
    (CompositeFiberAut.hom
      (reselection.toUpperEdgeReselection i j edge))
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_naturality edge)

/-- A generated base reselected edge is returned to its canonical-authored
counterpart by the inverse exact endpoint comparison. -/
theorem canonicalAuthoredBaseReselectedEdge_backward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift input.generatedBaseRouteLiftData
      reselection.toUpperEdgeReselection edge).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt j) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i).comp
        (upperReselectedEdgeLift input.canonicalAuthoredBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
            reselection).toUpperEdgeReselection edge) := by
  rw [upperReselectedEdgeLift_eq_for_g115,
    upperReselectedEdgeLift_eq_for_g115]
  change
    ((input.generatedBaseRouteGeometryEdge edge).comp
        (CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge))).comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt j) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i).comp
        ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
          (CompositeFiberAut.hom
            (input.canonicalAuthoredBaseCompositeFiberAutBackwardAt j
              (reselection.toUpperEdgeReselection i j edge))))
  rw [input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_hom]
  exact conjugatedPostcomposition_inverse_naturality
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt j)
    (input.canonicalAuthoredBaseRouteGeometryEdge edge)
    (input.generatedBaseRouteGeometryEdge edge)
    (CompositeFiberAut.hom
      (reselection.toUpperEdgeReselection i j edge))
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_naturality edge)

/-- A generated pulled reselected edge is returned to its canonical-authored
counterpart by the inverse exact endpoint comparison. -/
theorem canonicalAuthoredPulledReselectedEdge_backward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedPulledCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift input.generatedPulledRouteLiftData
      reselection.toUpperEdgeReselection edge).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt j) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i).comp
        (upperReselectedEdgeLift input.canonicalAuthoredPulledRouteLiftData
          (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
            reselection).toUpperEdgeReselection edge) := by
  rw [upperReselectedEdgeLift_eq_for_g115,
    upperReselectedEdgeLift_eq_for_g115]
  change
    ((input.generatedPulledRouteGeometryEdge edge).comp
        (CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge))).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt j) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i).comp
        ((input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
          (CompositeFiberAut.hom
            (input.canonicalAuthoredPulledCompositeFiberAutBackwardAt j
              (reselection.toUpperEdgeReselection i j edge))))
  rw [input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_hom]
  exact conjugatedPostcomposition_inverse_naturality
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt j)
    (input.canonicalAuthoredPulledRouteGeometryEdge edge)
    (input.generatedPulledRouteGeometryEdge edge)
    (CompositeFiberAut.hom
      (reselection.toUpperEdgeReselection i j edge))
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_naturality edge)

/-- Exact base endpoint transport extends from generators to every reselected
path. -/
theorem canonicalAuthoredBaseReselectedPath_forward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
      reselection.toUpperEdgeReselection path).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).comp
        (upperReselectedPathLift input.generatedBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
            reselection).toUpperEdgeReselection path) := by
  induction path with
  | nil vertex =>
      rw [upperReselectedPathLift_nil_for_g115,
        upperReselectedPathLift_nil_for_g115]
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _).symm
  | @cons source middle target edge tail inductionHypothesis =>
      rw [upperReselectedPathLift_cons_for_g115,
        upperReselectedPathLift_cons_for_g115]
      calc
        _ = (upperReselectedEdgeLift
              input.canonicalAuthoredBaseRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((upperReselectedPathLift
              input.canonicalAuthoredBaseRouteLiftData
              reselection.toUpperEdgeReselection tail).comp
                (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
                  target)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _
        _ = (upperReselectedEdgeLift
              input.canonicalAuthoredBaseRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
              middle).comp
                (upperReselectedPathLift input.generatedBaseRouteLiftData
                  (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
                    reselection).toUpperEdgeReselection tail)) :=
          congrArg _ inductionHypothesis
        _ = ((upperReselectedEdgeLift
                input.canonicalAuthoredBaseRouteLiftData
                reselection.toUpperEdgeReselection edge).comp
              (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
                middle)).comp
            (upperReselectedPathLift input.generatedBaseRouteLiftData
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
                reselection).toUpperEdgeReselection tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _).symm
        _ = ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
                source).comp
              (upperReselectedEdgeLift input.generatedBaseRouteLiftData
                (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
                  reselection).toUpperEdgeReselection edge)).comp
            (upperReselectedPathLift input.generatedBaseRouteLiftData
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
                reselection).toUpperEdgeReselection tail) :=
          congrArg (fun hom => hom.comp
            (upperReselectedPathLift input.generatedBaseRouteLiftData
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
                reselection).toUpperEdgeReselection tail))
            (input.canonicalAuthoredBaseReselectedEdge_forward_naturality
              reselection edge)
        _ = _ :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _

/-- Exact pulled endpoint transport extends from generators to every
reselected path. -/
theorem canonicalAuthoredPulledReselectedPath_forward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
      reselection.toUpperEdgeReselection path).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt j) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i).comp
        (upperReselectedPathLift input.generatedPulledRouteLiftData
          (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
            reselection).toUpperEdgeReselection path) := by
  induction path with
  | nil vertex =>
      rw [upperReselectedPathLift_nil_for_g115,
        upperReselectedPathLift_nil_for_g115]
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _).symm
  | @cons source middle target edge tail inductionHypothesis =>
      rw [upperReselectedPathLift_cons_for_g115,
        upperReselectedPathLift_cons_for_g115]
      calc
        _ = (upperReselectedEdgeLift
              input.canonicalAuthoredPulledRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              reselection.toUpperEdgeReselection tail).comp
                (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
                  target)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _
        _ = (upperReselectedEdgeLift
              input.canonicalAuthoredPulledRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
              middle).comp
                (upperReselectedPathLift input.generatedPulledRouteLiftData
                  (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
                    reselection).toUpperEdgeReselection tail)) :=
          congrArg _ inductionHypothesis
        _ = ((upperReselectedEdgeLift
                input.canonicalAuthoredPulledRouteLiftData
                reselection.toUpperEdgeReselection edge).comp
              (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
                middle)).comp
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
                reselection).toUpperEdgeReselection tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _).symm
        _ = ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
                source).comp
              (upperReselectedEdgeLift input.generatedPulledRouteLiftData
                (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
                  reselection).toUpperEdgeReselection edge)).comp
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
                reselection).toUpperEdgeReselection tail) :=
          congrArg (fun hom => hom.comp
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
                reselection).toUpperEdgeReselection tail))
            (input.canonicalAuthoredPulledReselectedEdge_forward_naturality
              reselection edge)
        _ = _ :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _

/-- Inverse exact base endpoint transport extends from generators to every
generated reselected path. -/
theorem canonicalAuthoredBaseReselectedPath_backward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      reselection.toUpperEdgeReselection path).comp
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt j) =
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i).comp
        (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
            reselection).toUpperEdgeReselection path) := by
  induction path with
  | nil vertex =>
      rw [upperReselectedPathLift_nil_for_g115,
        upperReselectedPathLift_nil_for_g115]
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _).symm
  | @cons source middle target edge tail inductionHypothesis =>
      rw [upperReselectedPathLift_cons_for_g115,
        upperReselectedPathLift_cons_for_g115]
      calc
        _ = (upperReselectedEdgeLift input.generatedBaseRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((upperReselectedPathLift input.generatedBaseRouteLiftData
              reselection.toUpperEdgeReselection tail).comp
                (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
                  target)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _
        _ = (upperReselectedEdgeLift input.generatedBaseRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
              middle).comp
                (upperReselectedPathLift
                  input.canonicalAuthoredBaseRouteLiftData
                  (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
                    reselection).toUpperEdgeReselection tail)) :=
          congrArg _ inductionHypothesis
        _ = ((upperReselectedEdgeLift input.generatedBaseRouteLiftData
                reselection.toUpperEdgeReselection edge).comp
              (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
                middle)).comp
            (upperReselectedPathLift
              input.canonicalAuthoredBaseRouteLiftData
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
                reselection).toUpperEdgeReselection tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _).symm
        _ = ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
                source).comp
              (upperReselectedEdgeLift
                input.canonicalAuthoredBaseRouteLiftData
                (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
                  reselection).toUpperEdgeReselection edge)).comp
            (upperReselectedPathLift
              input.canonicalAuthoredBaseRouteLiftData
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
                reselection).toUpperEdgeReselection tail) :=
          congrArg (fun hom => hom.comp
            (upperReselectedPathLift
              input.canonicalAuthoredBaseRouteLiftData
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
                reselection).toUpperEdgeReselection tail))
            (input.canonicalAuthoredBaseReselectedEdge_backward_naturality
              reselection edge)
        _ = _ :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _

/-- Inverse exact pulled endpoint transport extends from generators to every
generated reselected path. -/
theorem canonicalAuthoredPulledReselectedPath_backward_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedPulledCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift input.generatedPulledRouteLiftData
      reselection.toUpperEdgeReselection path).comp
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt j) =
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i).comp
        (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
          (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
            reselection).toUpperEdgeReselection path) := by
  induction path with
  | nil vertex =>
      rw [upperReselectedPathLift_nil_for_g115,
        upperReselectedPathLift_nil_for_g115]
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _).symm
  | @cons source middle target edge tail inductionHypothesis =>
      rw [upperReselectedPathLift_cons_for_g115,
        upperReselectedPathLift_cons_for_g115]
      calc
        _ = (upperReselectedEdgeLift input.generatedPulledRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((upperReselectedPathLift input.generatedPulledRouteLiftData
              reselection.toUpperEdgeReselection tail).comp
                (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
                  target)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _
        _ = (upperReselectedEdgeLift input.generatedPulledRouteLiftData
              reselection.toUpperEdgeReselection edge).comp
            ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
              middle).comp
                (upperReselectedPathLift
                  input.canonicalAuthoredPulledRouteLiftData
                  (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
                    reselection).toUpperEdgeReselection tail)) :=
          congrArg _ inductionHypothesis
        _ = ((upperReselectedEdgeLift input.generatedPulledRouteLiftData
                reselection.toUpperEdgeReselection edge).comp
              (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
                middle)).comp
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
                reselection).toUpperEdgeReselection tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _).symm
        _ = ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
                source).comp
              (upperReselectedEdgeLift
                input.canonicalAuthoredPulledRouteLiftData
                (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
                  reselection).toUpperEdgeReselection edge)).comp
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
                reselection).toUpperEdgeReselection tail) :=
          congrArg (fun hom => hom.comp
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
                reselection).toUpperEdgeReselection tail))
            (input.canonicalAuthoredPulledReselectedEdge_backward_naturality
              reselection edge)
        _ = _ :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
