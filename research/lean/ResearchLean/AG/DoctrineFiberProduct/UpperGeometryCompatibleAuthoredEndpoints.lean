import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCoefficientNormalization

/-!
# Authored-compatible endpoint normalization

The compatible construction and the G-114 route diagrams have isomorphic, not
definitionally equal, endpoint core packages.  This module uses the two exact
upper maps of the theorem-generated core-fiber isomorphisms to rebuild the
complete geometry and raw data on the literal G-114 endpoints.  These are the
authored-compatible endpoints that will form the raw problem; the canonical
generated endpoints remain separate comparison targets.

No endpoint comparison, inverse, Cartesian certificate, route edge, comparator,
or solution is accepted from the compatible input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The upper maps used to normalize the base endpoint cancel on the literal
G-114 endpoint. -/
theorem generatedBaseRouteEndpointUpper_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedBaseRouteCoreIsoAt i).inv.1.upper.comp
        (input.generatedBaseRouteCoreIsoAt i).hom.1.upper =
      SignedExactCoreReadingHom.refl
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).baseMatePackage.1 := by
  have h := congrArg (fun hom => hom.1.upper)
    (input.generatedBaseRouteCoreIsoAt i).inv_hom_id
  change (input.generatedBaseRouteCoreIsoAt i).inv.1.upper.comp
      (input.generatedBaseRouteCoreIsoAt i).hom.1.upper =
    SignedExactCoreReadingHom.refl
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).baseMatePackage.1 at h
  exact h

/-- The same base upper maps cancel on the canonical generated endpoint. -/
theorem generatedBaseRouteEndpointUpper_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedBaseRouteCoreIsoAt i).hom.1.upper.comp
        (input.generatedBaseRouteCoreIsoAt i).inv.1.upper =
      SignedExactCoreReadingHom.refl
        (input.generatedBaseRouteFixedGeometryAt i).package.core := by
  have h := congrArg (fun hom => hom.1.upper)
    (input.generatedBaseRouteCoreIsoAt i).hom_inv_id
  change (input.generatedBaseRouteCoreIsoAt i).hom.1.upper.comp
      (input.generatedBaseRouteCoreIsoAt i).inv.1.upper =
    SignedExactCoreReadingHom.refl
      (input.generatedBaseRouteFixedGeometryAt i).package.core at h
  exact h

/-- The independently generated pulled endpoint upper maps cancel on the
literal G-114 endpoint. -/
theorem generatedPulledRouteEndpointUpper_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedPulledRouteCoreIsoAt i).inv.1.upper.comp
        (input.generatedPulledRouteCoreIsoAt i).hom.1.upper =
      SignedExactCoreReadingHom.refl
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).pulledMatePackage.1 := by
  have h := congrArg (fun hom => hom.1.upper)
    (input.generatedPulledRouteCoreIsoAt i).inv_hom_id
  change (input.generatedPulledRouteCoreIsoAt i).inv.1.upper.comp
      (input.generatedPulledRouteCoreIsoAt i).hom.1.upper =
    SignedExactCoreReadingHom.refl
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).pulledMatePackage.1 at h
  exact h

/-- The pulled upper maps also cancel on the canonical generated endpoint. -/
theorem generatedPulledRouteEndpointUpper_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedPulledRouteCoreIsoAt i).hom.1.upper.comp
        (input.generatedPulledRouteCoreIsoAt i).inv.1.upper =
      SignedExactCoreReadingHom.refl
        (input.generatedPulledRouteFixedGeometryAt i).package.core := by
  have h := congrArg (fun hom => hom.1.upper)
    (input.generatedPulledRouteCoreIsoAt i).hom_inv_id
  change (input.generatedPulledRouteCoreIsoAt i).hom.1.upper.comp
      (input.generatedPulledRouteCoreIsoAt i).inv.1.upper =
    SignedExactCoreReadingHom.refl
      (input.generatedPulledRouteFixedGeometryAt i).package.core at h
  exact h

/-- Complete base-route geometry normalized onto the literal G-114 base
endpoint by the exact inverse/hom pair of the generated core comparison. -/
noncomputable def generatedAuthoredBaseRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
    (input.generatedBaseRouteFixedGeometryAt i).package
    (input.generatedBaseRouteCoreIsoAt i).inv.1.upper
    (input.generatedBaseRouteCoreIsoAt i).hom.1.upper

/-- Complete pulled-route geometry normalized independently onto the literal
G-114 pulled endpoint. -/
noncomputable def generatedAuthoredPulledRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
    (input.generatedPulledRouteFixedGeometryAt i).package
    (input.generatedPulledRouteCoreIsoAt i).inv.1.upper
    (input.generatedPulledRouteCoreIsoAt i).hom.1.upper

/-- The authored-compatible base geometry is carried by the actual G-114 base
mate package, not by the canonical generated endpoint. -/
@[simp] theorem generatedAuthoredBaseRouteGeometryAt_core
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedAuthoredBaseRouteGeometryAt i).core =
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).baseMatePackage.1 :=
  rfl

/-- The authored-compatible pulled geometry is carried by the actual G-114
pulled mate package. -/
@[simp] theorem generatedAuthoredPulledRouteGeometryAt_core
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedAuthoredPulledRouteGeometryAt i).core =
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).pulledMatePackage.1 :=
  rfl

/-- Base endpoint normalization retains the one authored coefficient ring. -/
@[simp] theorem generatedAuthoredBaseRouteGeometryAt_coefficient
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedAuthoredBaseRouteGeometryAt i).Coefficient = k :=
  rfl

/-- Pulled endpoint normalization retains the same authored coefficient ring. -/
@[simp] theorem generatedAuthoredPulledRouteGeometryAt_coefficient
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedAuthoredPulledRouteGeometryAt i).Coefficient = k :=
  rfl

/-- Fixed-core/fixed-coefficient form of the authored-compatible base
endpoint, suitable for the raw upper problem contract. -/
noncomputable def generatedAuthoredBaseRouteFixedGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    FixedCoefficientGeometryAt
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).baseMatePackage.1 k where
  geometry := (input.generatedAuthoredBaseRouteGeometryAt i).geometry
  raw := (input.generatedAuthoredBaseRouteGeometryAt i).raw

/-- Fixed-core/fixed-coefficient form of the independently normalized pulled
endpoint. -/
noncomputable def generatedAuthoredPulledRouteFixedGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    FixedCoefficientGeometryAt
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)).pulledMatePackage.1 k where
  geometry := (input.generatedAuthoredPulledRouteGeometryAt i).geometry
  raw := (input.generatedAuthoredPulledRouteGeometryAt i).raw

/-- Forgetting the fixed endpoint wrapper recovers the complete normalized
base geometry. -/
@[simp] theorem generatedAuthoredBaseRouteFixedGeometryAt_package
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedAuthoredBaseRouteFixedGeometryAt i).package =
      input.generatedAuthoredBaseRouteGeometryAt i :=
  rfl

/-- Forgetting the fixed endpoint wrapper recovers the complete normalized
pulled geometry. -/
@[simp] theorem generatedAuthoredPulledRouteFixedGeometryAt_package
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedAuthoredPulledRouteFixedGeometryAt i).package =
      input.generatedAuthoredPulledRouteGeometryAt i :=
  rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
