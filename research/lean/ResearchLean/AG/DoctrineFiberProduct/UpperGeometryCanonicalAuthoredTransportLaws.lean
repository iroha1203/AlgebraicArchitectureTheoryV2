import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredReselectionEquivalence
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSolutionEquivalence

/-!
# Algebraic laws for canonical-authored transport

This module upgrades the Cycle 74 composite-fiber conjugation equivalence to
a multiplicative equivalence and exposes exact complete-geometry
normalizations for the two solution-transport components.

Implementation notes: the multiplicative equivalence reuses the existing
forward map, inverse map, and inverse laws of `conjugationEquiv`.  The solution
normalizations are proved through the faithful exact embedding; they do not
replace the independently exactified solution components by new definitions.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace CompositeFiberAut

/-- Conjugation by a total-geometry isomorphism is a multiplicative
equivalence of the two composite-fiber automorphism groups. -/
noncomputable def conjugationMulEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) : CompositeFiberAut G ≃* CompositeFiberAut H where
  toEquiv := conjugationEquiv iso
  map_mul' left right := by
    apply Subtype.ext
    exact (Aut.autMulEquivOfIso iso).map_mul left.1 right.1

/-- The multiplicative conjugation equivalence has the same forward map as
the underlying Cycle 74 equivalence. -/
@[simp] theorem conjugationMulEquiv_apply
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (automorphism : CompositeFiberAut G) :
    conjugationMulEquiv iso automorphism =
      conjugationEquiv iso automorphism :=
  rfl

/-- The forward multiplicative conjugation has the expected complete
geometry hom. -/
@[simp] theorem conjugationMulEquiv_hom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (automorphism : CompositeFiberAut G) :
    CompositeFiberAut.hom (conjugationMulEquiv iso automorphism) =
      (iso.inv.comp (CompositeFiberAut.hom automorphism)).comp iso.hom :=
  conjugationEquiv_hom iso automorphism

/-- Multiplicative conjugation sends the identity automorphism to the
identity automorphism. -/
@[simp] theorem conjugationMulEquiv_map_one
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) :
    conjugationMulEquiv iso (1 : CompositeFiberAut G) = 1 :=
  map_one (conjugationMulEquiv iso)

/-- Multiplicative conjugation preserves products of composite-fiber
automorphisms. -/
@[simp] theorem conjugationMulEquiv_map_mul
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (left right : CompositeFiberAut G) :
    conjugationMulEquiv iso (left * right) =
      conjugationMulEquiv iso left * conjugationMulEquiv iso right :=
  map_mul (conjugationMulEquiv iso) left right

/-- Multiplicative conjugation preserves inverse composite-fiber
automorphisms. -/
@[simp] theorem conjugationMulEquiv_map_inv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (automorphism : CompositeFiberAut G) :
    conjugationMulEquiv iso automorphism⁻¹ =
      (conjugationMulEquiv iso automorphism)⁻¹ :=
  map_inv (conjugationMulEquiv iso) automorphism

end CompositeFiberAut

namespace UpperGeometryCompatibleProblemInputData

/-- The independently exactified forward solution component is exactly the
composition of the base endpoint inverse, the canonical component, and the
pulled endpoint hom. -/
theorem canonicalSolutionForwardAt_exact_normalization
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    input.canonicalSolutionForwardAt solution i =
      ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i).comp
        (solution.component i)).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [input.canonicalSolutionForwardAt_toRefinement]
  unfold canonicalSolutionForwardRefinementAt
  change
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom =
      (exactGeometryToRefinementGeometry U).map
        ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i ≫
          solution.component i) ≫
            input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i)
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement]
  rfl

/-- The independently exactified backward solution component is exactly the
composition of the base endpoint hom, the generated component, and the pulled
endpoint inverse. -/
theorem generatedSolutionBackwardAt_exact_normalization
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    input.generatedSolutionBackwardAt solution i =
      ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).comp
        (solution.component i)).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [input.generatedSolutionBackwardAt_toRefinement]
  unfold generatedSolutionBackwardRefinementAt
  change
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv =
      (exactGeometryToRefinementGeometry U).map
        ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i ≫
          solution.component i) ≫
            input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i)
  rw [Functor.map_comp, Functor.map_comp,
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement,
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement]
  rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
