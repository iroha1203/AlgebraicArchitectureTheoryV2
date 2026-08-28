import ResearchLean.AG.DiagnosticConservativity.WholeRouteCompatibility

/-!
# G-113 revision 2 whole-unit cross-system compatibility

The whole G-111 source- and target-unit routes mate to the corresponding
whole G-112 routes.  Each proof factors through the generated equality-cast
conjugacy: the reviewed triangle on each side identifies its actual route with
the appropriate cast, and contravariance reverses that cast.

## Implementation notes

The proofs use whole-route equations rather than expanding adjunction units
and counits again.  A direct componentwise mate calculation was rejected
because Cycle 17 already supplies a stronger typed cast bridge and because
repeating the generatorwise calculation would not consume both predecessor
whole-route triangle theorems.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- The conjugate of the whole G-111 source-unit route is the whole G-112
source-unit route.  This is the G-113(h) source-unit compatibility theorem;
both triangle laws and the generated equality-cast mate are proof inputs from
reviewed predecessor declarations, not caller-supplied premises. -/
theorem semanticGlobalTransportEquivalence_leftUnitRouteIso_conjugate
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    conjugateIsoEquiv
        (semanticGlobalTransportReindexAdjunction hom)
        (semanticGlobalTransportReindexAdjunction (𝟙 source ≫ hom))
        (coreFiberLeftUnitRouteIso hom) =
      semanticGlobalLeftUnitRouteIso hom := by
  rw [coreFiberLeftUnitRouteIso_eq_cast]
  rw [semanticGlobalTransportEquivalence_eqCast_conjugate]
  exact (semanticGlobalLeftUnitRouteIso_eq_cast hom).symm

/-- The conjugate of the whole G-111 target-unit route is the whole G-112
target-unit route.  This is the G-113(h) target-unit compatibility theorem;
both triangle laws and the generated equality-cast mate are proof inputs from
reviewed predecessor declarations, not caller-supplied premises. -/
theorem semanticGlobalTransportEquivalence_rightUnitRouteIso_conjugate
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    conjugateIsoEquiv
        (semanticGlobalTransportReindexAdjunction hom)
        (semanticGlobalTransportReindexAdjunction (hom ≫ 𝟙 target))
        (coreFiberRightUnitRouteIso hom) =
      semanticGlobalRightUnitRouteIso hom := by
  rw [coreFiberRightUnitRouteIso_eq_cast]
  rw [semanticGlobalTransportEquivalence_eqCast_conjugate]
  exact (semanticGlobalRightUnitRouteIso_eq_cast hom).symm

/-- Whole source-unit compatibility at every vertex of an indexed hom.
This G-113(h) indexed API theorem specializes the generated semantic result
without adding a unit or coherence premise. -/
theorem indexedDiagnosticTransportEquivalence_leftUnitRouteIso_conjugate
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    conjugateIsoEquiv
        (indexedDiagnosticTransportAdjunction hom vertex)
        (semanticGlobalTransportReindexAdjunction
          (𝟙 (D.vertex vertex) ≫ hom.app vertex))
        (coreFiberLeftUnitRouteIso (hom.app vertex)) =
      semanticGlobalLeftUnitRouteIso (hom.app vertex) := by
  simpa only [indexedDiagnosticTransportAdjunction] using
    semanticGlobalTransportEquivalence_leftUnitRouteIso_conjugate
      (hom.app vertex)

/-- Whole target-unit compatibility at every vertex of an indexed hom.
This G-113(h) indexed API theorem specializes the generated semantic result
without adding a unit or coherence premise. -/
theorem indexedDiagnosticTransportEquivalence_rightUnitRouteIso_conjugate
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    conjugateIsoEquiv
        (indexedDiagnosticTransportAdjunction hom vertex)
        (semanticGlobalTransportReindexAdjunction
          (hom.app vertex ≫ 𝟙 (E.vertex vertex)))
        (coreFiberRightUnitRouteIso (hom.app vertex)) =
      semanticGlobalRightUnitRouteIso (hom.app vertex) := by
  simpa only [indexedDiagnosticTransportAdjunction] using
    semanticGlobalTransportEquivalence_rightUnitRouteIso_conjugate
      (hom.app vertex)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
