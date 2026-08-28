import ResearchLean.AG.DiagnosticConservativity.PentagonDownstreamCompatibility

/-!
# G-113 revision 2 whole-pentagon cochain compatibility

The Cycle 20 whole-pentagon endpoint actions are applied at every two-cell
target to obtain four raw-defect cochain equivalences: the left and right
G-111 routes and the independently generated inverse mates of the left and
right G-112 routes.  Both cross-system pairs agree, and the two mate routes
satisfy the pentagon on the complete cochain space.

This is a value-level equivalence on every cochain coordinate.  Orbit and
coherence propositions require their own witness-transport theorems and are
not inferred here merely from equality of these maps.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-- Apply the left whole G-111 pentagon endpoint action at every raw-defect
cochain coordinate. -/
noncomputable def indexedDiagnosticPentagonG111LeftDefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        (((first.comp second).comp third).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticPentagonG111LeftEndpointEquivalence
      first second third source (G.twoTarget cell)

/-- Apply the cast-bearing right whole G-111 pentagon endpoint action at every
raw-defect cochain coordinate. -/
noncomputable def indexedDiagnosticPentagonG111RightDefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        (((first.comp second).comp third).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticPentagonG111RightEndpointEquivalence
      first second third source (G.twoTarget cell)

/-- Apply the inverse-mate left whole G-112 pentagon endpoint action at every
raw-defect cochain coordinate. -/
noncomputable def indexedDiagnosticPentagonMateLeftDefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        (((first.comp second).comp third).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticPentagonMateLeftEndpointEquivalence
      first second third source (G.twoTarget cell)

/-- Apply the inverse-mate right whole G-112 pentagon endpoint action at every
raw-defect cochain coordinate. -/
noncomputable def indexedDiagnosticPentagonMateRightDefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        (((first.comp second).comp third).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (third.transportedInterpretation
          (second.transportedInterpretation
            (first.transportedInterpretation source))).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticPentagonMateRightEndpointEquivalence
      first second third source (G.twoTarget cell)

/-- The left whole G-112-mate and G-111 cochain actions agree at every
two-cell coordinate. -/
theorem indexedDiagnosticPentagonMateLeftDefectCochainEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticPentagonMateLeftDefectCochainEquivalence
        first second third source =
      indexedDiagnosticPentagonG111LeftDefectCochainEquivalence
        first second third source := by
  apply MulEquiv.ext
  intro cochain
  funext cell
  change indexedDiagnosticPentagonMateLeftEndpointEquivalence
      first second third source (G.twoTarget cell) (cochain cell) =
    indexedDiagnosticPentagonG111LeftEndpointEquivalence
      first second third source (G.twoTarget cell) (cochain cell)
  rw [indexedDiagnosticPentagonMateLeftEndpointEquivalence_eq_g111]

/-- The right whole G-112-mate and G-111 cochain actions agree at every
two-cell coordinate. -/
theorem indexedDiagnosticPentagonMateRightDefectCochainEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticPentagonMateRightDefectCochainEquivalence
        first second third source =
      indexedDiagnosticPentagonG111RightDefectCochainEquivalence
        first second third source := by
  apply MulEquiv.ext
  intro cochain
  funext cell
  change indexedDiagnosticPentagonMateRightEndpointEquivalence
      first second third source (G.twoTarget cell) (cochain cell) =
    indexedDiagnosticPentagonG111RightEndpointEquivalence
      first second third source (G.twoTarget cell) (cochain cell)
  rw [indexedDiagnosticPentagonMateRightEndpointEquivalence_eq_g111]

/-- The two whole G-112-mate cochain actions satisfy the pentagon equation on
the complete raw-defect cochain space. -/
theorem indexedDiagnosticPentagonMateDefectCochainEquivalence_eq
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F H : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (third : IndexedBaseDiagramHom F H)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticPentagonMateLeftDefectCochainEquivalence
        first second third source =
      indexedDiagnosticPentagonMateRightDefectCochainEquivalence
        first second third source := by
  apply MulEquiv.ext
  intro cochain
  funext cell
  change indexedDiagnosticPentagonMateLeftEndpointEquivalence
      first second third source (G.twoTarget cell) (cochain cell) =
    indexedDiagnosticPentagonMateRightEndpointEquivalence
      first second third source (G.twoTarget cell) (cochain cell)
  rw [indexedDiagnosticPentagonMateEndpointEquivalence_eq]

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
