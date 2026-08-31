import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointComparisons

/-!
# Realization-exact direct route normalization

This module turns a theorem-generated realization-exact upper equivalence into
the direct geometry normalization that it actually supports.  It does not
upgrade the unrelated G-114 selected-endpoint core isomorphisms to realization
data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCleavage

/-- Object-level direct normalization of a target geometry by an exact upper
equivalence.  Realization supplies are connected separately at the concrete
route specializations below. -/
noncomputable def realizationNormalizedGeometry
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (e : ExactUpperEquivalence P G.core) : GeometryPackage.{u, v} U :=
  pullGeometryPackageAlongUpperPair G e.forward e.backward

@[simp] theorem realizationNormalizedGeometry_core
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (e : ExactUpperEquivalence P G.core) :
    (realizationNormalizedGeometry G e).core = P := rfl

@[simp] theorem realizationNormalizedGeometry_coefficient
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (e : ExactUpperEquivalence P G.core) :
    (realizationNormalizedGeometry G e).Coefficient = G.Coefficient := rfl

end UpperGeometryCleavage

namespace UpperGeometryCompatibleProblemInputData

/-- The base-first route normalized directly from the authored source by the
two explicit inverse-package transports.  This is not the G-114 selected
endpoint normalization. -/
noncomputable def canonicalAuthoredBaseRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.realizationNormalizedGeometry
    (input.sourceGeometry i).package
    (input.generatedBaseRouteUpperEquivalenceAt i)

/-- The pulled-first direct normalization, independently generated in the
opposite explicit route order. -/
noncomputable def canonicalAuthoredPulledRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.realizationNormalizedGeometry
    (input.sourceGeometry i).package
    (input.generatedPulledRouteUpperEquivalenceAt i)

@[simp] theorem canonicalAuthoredBaseRouteGeometryAt_core
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseRouteGeometryAt i).core =
      (input.generatedBaseRouteGeometryAt i).core :=
  rfl

@[simp] theorem canonicalAuthoredPulledRouteGeometryAt_core
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledRouteGeometryAt i).core =
      (input.generatedPulledRouteGeometryAt i).core :=
  rfl

@[simp] theorem canonicalAuthoredBaseRouteGeometryAt_coefficient
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseRouteGeometryAt i).Coefficient = k :=
  rfl

@[simp] theorem canonicalAuthoredPulledRouteGeometryAt_coefficient
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledRouteGeometryAt i).Coefficient = k :=
  rfl

/-- The direct base normalization retains the literal backward-upper raw
reindexing. -/
@[simp] theorem canonicalAuthoredBaseRouteGeometryAt_raw
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseRouteGeometryAt i).raw =
      UpperGeometryCleavage.rawReindexUpper
        (input.sourceGeometry i).geometry
        (input.canonicalAuthoredBaseRouteGeometryAt i).geometry
        (input.generatedBaseRouteUpperEquivalenceAt i).backward
        (input.sourceGeometry i).raw :=
  rfl

/-- The direct pulled normalization retains its independently ordered literal
backward-upper raw reindexing. -/
@[simp] theorem canonicalAuthoredPulledRouteGeometryAt_raw
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledRouteGeometryAt i).raw =
      UpperGeometryCleavage.rawReindexUpper
        (input.sourceGeometry i).geometry
        (input.canonicalAuthoredPulledRouteGeometryAt i).geometry
        (input.generatedPulledRouteUpperEquivalenceAt i).backward
        (input.sourceGeometry i).raw :=
  rfl

/-- The theorem-generated forward realization supply, now typed on the direct
base normalization. -/
noncomputable def canonicalAuthoredBaseRouteForwardSupplyAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperRealizationTransportSupply
      (input.canonicalAuthoredBaseRouteGeometryAt i).core
      (input.sourceGeometry i).package.core
      (input.generatedBaseRouteUpperEquivalenceAt i).forward :=
  (input.generatedBaseRouteRealizationExactAt i).homSupply

/-- The genuine inverse realization supply for the direct base normalization. -/
noncomputable def canonicalAuthoredBaseRouteBackwardSupplyAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperRealizationTransportSupply
      (input.sourceGeometry i).package.core
      (input.canonicalAuthoredBaseRouteGeometryAt i).core
      (input.generatedBaseRouteUpperEquivalenceAt i).backward :=
  (input.generatedBaseRouteRealizationExactAt i).invSupply

/-- The independently generated pulled-route forward realization supply. -/
noncomputable def canonicalAuthoredPulledRouteForwardSupplyAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperRealizationTransportSupply
      (input.canonicalAuthoredPulledRouteGeometryAt i).core
      (input.sourceGeometry i).package.core
      (input.generatedPulledRouteUpperEquivalenceAt i).forward :=
  (input.generatedPulledRouteRealizationExactAt i).homSupply

/-- The genuine inverse realization supply for the direct pulled
normalization. -/
noncomputable def canonicalAuthoredPulledRouteBackwardSupplyAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperRealizationTransportSupply
      (input.sourceGeometry i).package.core
      (input.canonicalAuthoredPulledRouteGeometryAt i).core
      (input.generatedPulledRouteUpperEquivalenceAt i).backward :=
  (input.generatedPulledRouteRealizationExactAt i).invSupply

/-- Forward raw transport along the direct base normalization cancels its
literal backward normalization. -/
theorem canonicalAuthoredBaseRouteRaw_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.rawReindexUpper
        (input.canonicalAuthoredBaseRouteGeometryAt i).geometry
        (input.sourceGeometry i).geometry
        (input.generatedBaseRouteUpperEquivalenceAt i).forward
        (input.canonicalAuthoredBaseRouteGeometryAt i).raw =
      (input.sourceGeometry i).raw := by
  rw [input.canonicalAuthoredBaseRouteGeometryAt_raw i]
  exact UpperGeometryCleavage.rawReindexUpper_cancel
    (input.canonicalAuthoredBaseRouteGeometryAt i).geometry
    (input.sourceGeometry i).geometry
    (input.generatedBaseRouteUpperEquivalenceAt i).forward
    (input.generatedBaseRouteUpperEquivalenceAt i).backward
    (input.generatedBaseRouteUpperEquivalenceAt i).backward_forward
    (input.sourceGeometry i).raw

/-- Forward raw transport along the independently normalized pulled route also
cancels its backward normalization. -/
theorem canonicalAuthoredPulledRouteRaw_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.rawReindexUpper
        (input.canonicalAuthoredPulledRouteGeometryAt i).geometry
        (input.sourceGeometry i).geometry
        (input.generatedPulledRouteUpperEquivalenceAt i).forward
        (input.canonicalAuthoredPulledRouteGeometryAt i).raw =
      (input.sourceGeometry i).raw := by
  rw [input.canonicalAuthoredPulledRouteGeometryAt_raw i]
  exact UpperGeometryCleavage.rawReindexUpper_cancel
    (input.canonicalAuthoredPulledRouteGeometryAt i).geometry
    (input.sourceGeometry i).geometry
    (input.generatedPulledRouteUpperEquivalenceAt i).forward
    (input.generatedPulledRouteUpperEquivalenceAt i).backward
    (input.generatedPulledRouteUpperEquivalenceAt i).backward_forward
    (input.sourceGeometry i).raw

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
