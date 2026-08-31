import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCochains

/-!
# Coefficient-trivial upper reselections for G-115

This module cuts out the coefficient-trivial part of the existing G-109
upper edge-reselection space.  The definition retains the actual
`UpperEdgeReselection`; it adds only the theorem that every chosen target
automorphism fixes the already selected common coefficient ring.

This is a typing predecessor for the paired solution-intertwining relation.
It does not claim that every upper reselection is coefficient-trivial or that
the restricted orbit already supplies a paired solution transport.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

/-- An actual upper edge reselection whose every target-fiber automorphism
fixes the fixed coefficient ring pointwise. -/
structure CoefficientTrivialUpperEdgeReselection
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry) where
  /-- The underlying existing G-109 upper edge reselection. -/
  toUpperEdgeReselection : UpperEdgeReselection data.toTwoLayerLiftData
  /-- Every selected target-fiber automorphism fixes the common coefficient. -/
  coefficient_id : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (CompositeFiberAut.hom
      (toUpperEdgeReselection i j edge)).geometry.coefficientHom =
        RingHom.id k

namespace CoefficientTrivialUpperEdgeReselection

/-- Coefficient-trivial reselections are equal when their actual upper
reselection families are equal; the coefficient law is proof data. -/
@[ext]
theorem ext
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    {left right : CoefficientTrivialUpperEdgeReselection data}
    (h : left.toUpperEdgeReselection = right.toUpperEdgeReselection) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

/-- The identity upper edge reselection is coefficient-trivial. -/
noncomputable def one
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry) :
    CoefficientTrivialUpperEdgeReselection data where
  toUpperEdgeReselection := 1
  coefficient_id := by
    intro i j edge
    rfl

@[simp] theorem one_toUpperEdgeReselection
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry) :
    (one data).toUpperEdgeReselection = 1 := rfl

/-- Coefficient-trivial upper edge reselections are closed under the existing
pointwise upper-reselection multiplication. -/
noncomputable def mul
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    (left right : CoefficientTrivialUpperEdgeReselection data) :
    CoefficientTrivialUpperEdgeReselection data where
  toUpperEdgeReselection := left.toUpperEdgeReselection *
    right.toUpperEdgeReselection
  coefficient_id := by
    intro i j edge
    simp only [Pi.mul_apply]
    change (((right.toUpperEdgeReselection i j edge).1.hom.comp
      (left.toUpperEdgeReselection i j edge).1.hom).geometry.coefficientHom) =
        RingHom.id k
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change ((left.toUpperEdgeReselection i j edge).1.hom.geometry.coefficientHom.comp
      (right.toUpperEdgeReselection i j edge).1.hom.geometry.coefficientHom) =
        RingHom.id k
    have leftCoefficient := left.coefficient_id edge
    have rightCoefficient := right.coefficient_id edge
    change (left.toUpperEdgeReselection i j edge).1.hom.geometry.coefficientHom =
      RingHom.id k at leftCoefficient
    change (right.toUpperEdgeReselection i j edge).1.hom.geometry.coefficientHom =
      RingHom.id k at rightCoefficient
    rw [leftCoefficient, rightCoefficient]
    rfl

@[simp] theorem mul_toUpperEdgeReselection
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    (left right : CoefficientTrivialUpperEdgeReselection data) :
    (mul left right).toUpperEdgeReselection =
      left.toUpperEdgeReselection * right.toUpperEdgeReselection := rfl

end CoefficientTrivialUpperEdgeReselection

/-- Membership in the orbit generated by coefficient-trivial upper edge
reselections.  The cochain is the existing actual `upperRawDefectCochain`. -/
def InCoefficientTrivialUpperReselectionOrbit
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry)
    (cochain : UpperDefectCochain data.toTwoLayerTransportData) : Prop :=
  ∃ reselection : CoefficientTrivialUpperEdgeReselection data,
    upperRawDefectCochain data.toTwoLayerTransportData
      reselection.toUpperEdgeReselection = cochain

/-- The coefficient-trivial orbit is an actual suborbit of the existing upper
reselection orbit; no new orbit action or supplied class is introduced. -/
theorem InCoefficientTrivialUpperReselectionOrbit.toInUpperReselectionOrbit
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    {cochain : UpperDefectCochain data.toTwoLayerTransportData}
    (h : InCoefficientTrivialUpperReselectionOrbit data cochain) :
    InUpperReselectionOrbit data.toTwoLayerTransportData cochain := by
  rcases h with ⟨reselection, equality⟩
  exact ⟨reselection.toUpperEdgeReselection, equality⟩

/-- The raw cochain of the identity upper reselection lies in the restricted
orbit by an explicit coefficient-trivial witness. -/
theorem identityRawDefectCochain_mem_coefficientTrivialOrbit
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry) :
    InCoefficientTrivialUpperReselectionOrbit data
      (upperRawDefectCochain data.toTwoLayerTransportData 1) := by
  exact ⟨CoefficientTrivialUpperEdgeReselection.one data, rfl⟩

namespace UpperGeometryCompatibleProblemInputData

/-- Coefficient-trivial reselections on the actually generated base route. -/
abbrev GeneratedBaseCoefficientTrivialUpperEdgeReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :=
  CoefficientTrivialUpperEdgeReselection input.generatedBaseRouteTransport

/-- Coefficient-trivial reselections on the independently generated pulled
route. -/
abbrev GeneratedPulledCoefficientTrivialUpperEdgeReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :=
  CoefficientTrivialUpperEdgeReselection input.generatedPulledRouteTransport

/-- The identity cochain on the generated base route belongs to the actual
coefficient-trivial restricted orbit. -/
theorem generatedBaseIdentityRawDefectCochain_mem_coefficientTrivialOrbit
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    InCoefficientTrivialUpperReselectionOrbit
      input.generatedBaseRouteTransport
      (upperRawDefectCochain input.generatedBaseRouteData 1) := by
  exact identityRawDefectCochain_mem_coefficientTrivialOrbit
    input.generatedBaseRouteTransport

/-- The identity cochain on the independently generated pulled route belongs
to the actual coefficient-trivial restricted orbit. -/
theorem generatedPulledIdentityRawDefectCochain_mem_coefficientTrivialOrbit
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    InCoefficientTrivialUpperReselectionOrbit
      input.generatedPulledRouteTransport
      (upperRawDefectCochain input.generatedPulledRouteData 1) := by
  exact identityRawDefectCochain_mem_coefficientTrivialOrbit
    input.generatedPulledRouteTransport

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
