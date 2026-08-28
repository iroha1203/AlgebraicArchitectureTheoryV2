import ResearchLean.AG.DiagnosticConservativity.WholeRouteCompatibility

/-!
# G-113 revision 2 whole-pentagon cross-system compatibility

The conjugate mate of the whole left G-111 pentagon route is the whole left
G-112 route.  The proof uses mate compatibility with vertical composition and
right whiskering, then the two generated binary compositor conjugacies.  The
right-route equation follows from the reviewed whole pentagon equations on
both sides.

## Implementation notes

The left route is chosen as the generating calculation because it contains no
associativity cast: its two compositor factors match `conjugateEquiv_comp` and
`conjugateEquiv_whiskerRight` directly.  A separate unit/counit expansion was
rejected.  The right equation is transported through the whole-route pentagon
equalities, so the Cycle 17 covariant/contravariant associativity casts remain
part of the proved route rather than being erased by normalization.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- The conjugate of the whole left G-111 pentagon route is the whole left
G-112 pentagon route.  This G-113(h) theorem is generated from mate composition,
mate whiskering, and the reviewed binary compositor conjugacies; it accepts no
pentagon comparison as a premise. -/
theorem semanticGlobalTransportEquivalence_pentagonLeftRouteIso_conjugate
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    conjugateIsoEquiv
        (((semanticGlobalTransportReindexAdjunction first).comp
          (semanticGlobalTransportReindexAdjunction second)).comp
            (semanticGlobalTransportReindexAdjunction third))
        (semanticGlobalTransportReindexAdjunction
          ((first ≫ second) ≫ third))
        (coreFiberPentagonLeftRouteIso first second third) =
      semanticGlobalPentagonLeftRouteIso first second third := by
  apply Iso.ext
  change conjugateEquiv
      (((semanticGlobalTransportReindexAdjunction first).comp
        (semanticGlobalTransportReindexAdjunction second)).comp
          (semanticGlobalTransportReindexAdjunction third))
      (semanticGlobalTransportReindexAdjunction
        ((first ≫ second) ≫ third))
      ((coreFiberPentagonLeftRouteIso first second third).hom) =
    (semanticGlobalPentagonLeftRouteIso first second third).hom
  unfold coreFiberPentagonLeftRouteIso
  unfold semanticGlobalPentagonLeftRouteIso
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  rw [← conjugateEquiv_comp
    (((semanticGlobalTransportReindexAdjunction first).comp
      (semanticGlobalTransportReindexAdjunction second)).comp
        (semanticGlobalTransportReindexAdjunction third))
    ((semanticGlobalTransportReindexAdjunction (first ≫ second)).comp
      (semanticGlobalTransportReindexAdjunction third))]
  rw [conjugateEquiv_whiskerRight]
  rw [show conjugateEquiv
      ((semanticGlobalTransportReindexAdjunction first).comp
        (semanticGlobalTransportReindexAdjunction second))
      (semanticGlobalTransportReindexAdjunction (first ≫ second))
      (coreFiberCompositor first second).hom =
        (exact_bottom_semantic_global_compositor first second).hom by
    exact congrArg Iso.hom
      (semanticGlobalTransportEquivalence_compositor_conjugate first second)]
  rw [show conjugateEquiv
      ((semanticGlobalTransportReindexAdjunction (first ≫ second)).comp
        (semanticGlobalTransportReindexAdjunction third))
      (semanticGlobalTransportReindexAdjunction
        ((first ≫ second) ≫ third))
      (coreFiberCompositor (first ≫ second) third).hom =
        (exact_bottom_semantic_global_compositor
          (first ≫ second) third).hom by
    exact congrArg Iso.hom
      (semanticGlobalTransportEquivalence_compositor_conjugate
        (first ≫ second) third)]

/-- The conjugate of the whole right G-111 pentagon route is the whole right
G-112 pentagon route.  This G-113(h) theorem uses the reviewed whole pentagon
equalities on both sides after the generated left-route conjugacy; the
associativity casts therefore remain part of the statement and proof route. -/
theorem semanticGlobalTransportEquivalence_pentagonRightRouteIso_conjugate
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    conjugateIsoEquiv
        (((semanticGlobalTransportReindexAdjunction first).comp
          (semanticGlobalTransportReindexAdjunction second)).comp
            (semanticGlobalTransportReindexAdjunction third))
        (semanticGlobalTransportReindexAdjunction
          ((first ≫ second) ≫ third))
        (coreFiberPentagonRightRouteIso first second third) =
      semanticGlobalPentagonRightRouteIso first second third := by
  rw [← coreFiberPentagonRouteIso_eq first second third]
  rw [semanticGlobalTransportEquivalence_pentagonLeftRouteIso_conjugate]
  exact semanticGlobalPentagonRouteIso_eq first second third

/-- Whole left-pentagon compatibility at every vertex of three composable
indexed homs.  This G-113(h) indexed API theorem adds no compositor or
pentagon premise. -/
theorem indexedDiagnosticTransportEquivalence_pentagonLeftRouteIso_conjugate
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (vertex : G.Vertex) :
    conjugateIsoEquiv
        (((indexedDiagnosticTransportAdjunction first vertex).comp
          (indexedDiagnosticTransportAdjunction second vertex)).comp
            (indexedDiagnosticTransportAdjunction third vertex))
        (indexedDiagnosticTransportAdjunction
          ((first.comp second).comp third) vertex)
        (coreFiberPentagonLeftRouteIso
          (first.app vertex) (second.app vertex) (third.app vertex)) =
      semanticGlobalPentagonLeftRouteIso
        (first.app vertex) (second.app vertex) (third.app vertex) := by
  simpa only [indexedDiagnosticTransportAdjunction,
    IndexedBaseDiagramHom.comp_app] using
    semanticGlobalTransportEquivalence_pentagonLeftRouteIso_conjugate
      (first.app vertex) (second.app vertex) (third.app vertex)

/-- Whole right-pentagon compatibility at every vertex of three composable
indexed homs.  This G-113(h) indexed API theorem retains the reviewed
associativity casts and adds no coherence premise. -/
theorem indexedDiagnosticTransportEquivalence_pentagonRightRouteIso_conjugate
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (vertex : G.Vertex) :
    conjugateIsoEquiv
        (((indexedDiagnosticTransportAdjunction first vertex).comp
          (indexedDiagnosticTransportAdjunction second vertex)).comp
            (indexedDiagnosticTransportAdjunction third vertex))
        (indexedDiagnosticTransportAdjunction
          ((first.comp second).comp third) vertex)
        (coreFiberPentagonRightRouteIso
          (first.app vertex) (second.app vertex) (third.app vertex)) =
      semanticGlobalPentagonRightRouteIso
        (first.app vertex) (second.app vertex) (third.app vertex) := by
  simpa only [indexedDiagnosticTransportAdjunction,
    IndexedBaseDiagramHom.comp_app] using
    semanticGlobalTransportEquivalence_pentagonRightRouteIso_conjugate
      (first.app vertex) (second.app vertex) (third.app vertex)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
