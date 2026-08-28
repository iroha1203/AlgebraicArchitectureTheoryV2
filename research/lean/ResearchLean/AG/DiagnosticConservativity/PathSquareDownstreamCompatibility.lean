import ResearchLean.AG.DiagnosticConservativity.PathSquareCompatibility

/-!
# G-113 revision 2 downstream path-square compatibility

The G-111 horizontal operation is a paste of consecutive path squares, not an
operation on indexed diagram homs.  Cycle 25 fixed the corresponding forward
and inverse commuting equations at the total-lift and reselection layers.

This module assembles the whole G-113 exactness surface over that actual pasted
square.  The package is generated from the fixed indexed hom and source
interpretation: it contains no caller-supplied equivalence, inverse,
commutativity, coherence, vanishing, or orbit certificate.  Its path fields
consume the component-to-paste-to-append chain, and its remaining fields expose
the exact fiber, endpoint, reselection, raw-defect cochain, orbit, coherence,
and obstruction maps governed by those same path values.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/--
The generated G-113 `(a)`--`(g)` exactness package over one authored G-111
horizontal path-square paste.

The two paths only select the square whose compatibility is being recorded.
All downstream fields remain quantified over arbitrary source and target
values, because cochains and the proposition layers are global over the fixed
indexed shape rather than carrying a separate horizontal operation.
-/
structure IndexedDiagnosticHorizontalPastingExactness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) : Prop where
  /-- The pasted base square and the direct appended-path square have the same sides. -/
  baseSides :
    (hom.horizontalPathSquare first second).top =
        (hom.pathSquare (first.append second)).top ∧
      (hom.horizontalPathSquare first second).bottom =
        (hom.pathSquare (first.append second)).bottom ∧
      (hom.horizontalPathSquare first second).left =
        (hom.pathSquare (first.append second)).left ∧
      (hom.horizontalPathSquare first second).right =
        (hom.pathSquare (first.append second)).right
  /-- The square keeps its authored horizontal-paste provenance. -/
  route :
    (hom.horizontalPathSquare first second).route =
      .pasteHorizontal first.squareRoute second.squareRoute
  /-- `(a)`: the forward functor of the explicit equivalence is the G-111 push. -/
  fiberFunctor : ∀ vertex,
    (indexedDiagnosticTransportEquivalence hom vertex).functor =
      indexedDiagnosticTransportPush hom vertex
  /-- `(a)`: the inverse functor of the explicit equivalence is the G-112 reindexing. -/
  fiberInverse : ∀ vertex,
    (indexedDiagnosticTransportEquivalence hom vertex).inverse =
      indexedDiagnosticTransportReindex hom vertex
  /-- `(a)`: the generated push is an equivalence at every vertex. -/
  fiberIsEquivalence : ∀ vertex,
    (indexedDiagnosticTransportPush hom vertex).IsEquivalence
  /-- `(b)`: the endpoint equivalence forward map is the generated endpoint action. -/
  endpointForward : ∀ vertex
      (automorphism : PackageFiberAut (source.package vertex)),
    indexedDiagnosticEndpointEquivalence hom source vertex automorphism =
      hom.endpointAction source vertex automorphism
  /-- `(b)`: every source endpoint value is recovered after a forward round trip. -/
  endpointSourceRoundTrip : ∀ vertex
      (automorphism : PackageFiberAut (source.package vertex)),
    (indexedDiagnosticEndpointEquivalence hom source vertex).symm
        (indexedDiagnosticEndpointEquivalence hom source vertex automorphism) =
      automorphism
  /-- `(b)`: every target endpoint value is recovered from the generated inverse. -/
  endpointInverse : ∀ vertex
      (targetAutomorphism : PackageFiberAut
        ((hom.transportedInterpretation source).package vertex)),
    indexedDiagnosticEndpointEquivalence hom source vertex
        ((indexedDiagnosticEndpointEquivalence hom source vertex).symm
          targetAutomorphism) = targetAutomorphism
  /-- `(c)`: the reselection equivalence forward map is the G-111 transport. -/
  reselectionForward : ∀ reselection : IndexedEdgeReselection source,
    indexedDiagnosticReselectionEquivalence hom source reselection =
      hom.transportedReselection source reselection
  /-- `(c)`: forward then inverse reselection transport is the identity. -/
  reselectionSourceRoundTrip : ∀ reselection : IndexedEdgeReselection source,
    hom.inverseTransportedReselection source
        (hom.transportedReselection source reselection) = reselection
  /-- `(c)`: inverse then forward reselection transport is the identity. -/
  reselectionTargetRoundTrip : ∀ targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source),
    hom.transportedReselection source
        (hom.inverseTransportedReselection source targetReselection) =
      targetReselection
  /-- The forward appended-path square is obtained through horizontal pasting. -/
  pathForward : ∀ reselection : IndexedEdgeReselection source,
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection)
          (first.append second)) =
      (source.reselectedPathLift reselection (first.append second)).comp
        (hom.diagnosticVertexLift source k)
  /-- The arbitrary-target appended-path square is obtained through inverse pasting. -/
  pathInverse : ∀ targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source),
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection (first.append second)) =
      (source.reselectedPathLift
        (hom.inverseTransportedReselection source targetReselection)
        (first.append second)).comp (hom.diagnosticVertexLift source k)
  /-- `(f)`: raw-defect cochains commute with forward transport. -/
  cochainForward : ∀ reselection : IndexedEdgeReselection source,
    indexedDiagnosticDefectCochainEquivalence hom source
        (rawDefectCochain source.toAdmissibleTransportData reselection) =
      rawDefectCochain
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (hom.transportedReselection source reselection)
  /-- `(f)`: raw-defect cochains commute with generated inverse transport. -/
  cochainInverse : ∀ targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source),
    (indexedDiagnosticDefectCochainEquivalence hom source).symm
        (rawDefectCochain
          (hom.transportedInterpretation source).toAdmissibleTransportData
          targetReselection) =
      rawDefectCochain source.toAdmissibleTransportData
        (hom.inverseTransportedReselection source targetReselection)
  /-- `(f)`: every source cochain is recovered after a forward round trip. -/
  cochainSourceRoundTrip : ∀ cochain : DefectCochain
      source.toAdmissibleTransportData,
    (indexedDiagnosticDefectCochainEquivalence hom source).symm
        (indexedDiagnosticDefectCochainEquivalence hom source cochain) = cochain
  /-- `(f)`: every target cochain is recovered after an inverse round trip. -/
  cochainTargetRoundTrip : ∀ targetCochain : DefectCochain
      (hom.transportedInterpretation source).toAdmissibleTransportData,
    indexedDiagnosticDefectCochainEquivalence hom source
        ((indexedDiagnosticDefectCochainEquivalence hom source).symm
          targetCochain) = targetCochain
  /-- `(g)`: forward cochain transport preserves and reflects orbit membership. -/
  orbitForward : ∀ cochain : DefectCochain source.toAdmissibleTransportData,
    InReselectionOrbit source.toAdmissibleTransportData cochain ↔
      InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (indexedDiagnosticDefectCochainEquivalence hom source cochain)
  /-- `(g)`: arbitrary target orbit membership is reflected by the inverse. -/
  orbitInverse : ∀ targetCochain : DefectCochain
      (hom.transportedInterpretation source).toAdmissibleTransportData,
    InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        targetCochain ↔
      InReselectionOrbit source.toAdmissibleTransportData
        ((indexedDiagnosticDefectCochainEquivalence hom source).symm
          targetCochain)
  /-- `(d)`: forward reselection transport preserves and reflects coherence. -/
  coherenceForward : ∀ reselection : IndexedEdgeReselection source,
    source.IndexedCoherentAt reselection ↔
      (hom.transportedInterpretation source).IndexedCoherentAt
        (hom.transportedReselection source reselection)
  /-- `(d)`: arbitrary target coherence is reflected by generated inverse transport. -/
  coherenceInverse : ∀ targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source),
    (hom.transportedInterpretation source).IndexedCoherentAt targetReselection ↔
      source.IndexedCoherentAt
        (hom.inverseTransportedReselection source targetReselection)
  /-- `(e)`: obstruction vanishing is preserved and reflected. -/
  obstruction :
    TransportObstructionVanishes source.toAdmissibleTransportData ↔
      TransportObstructionVanishes
        (hom.transportedInterpretation source).toAdmissibleTransportData

/--
Generate the whole horizontal-pasting exactness package from the G-111 square,
the G-112-backed inverse transport, and the already proved G-113 equivalences.
-/
noncomputable def indexedDiagnosticHorizontalPastingExactness
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    IndexedDiagnosticHorizontalPastingExactness hom source first second where
  baseSides := hom.indexedDiagnosticHorizontalPathPasting_base_eq_pathSquare
    first second
  route := hom.indexedDiagnosticHorizontalPathPasting_route first second
  fiberFunctor := indexedDiagnosticTransportEquivalence_functor hom
  fiberInverse := indexedDiagnosticTransportEquivalence_inverse hom
  fiberIsEquivalence := indexedDiagnosticTransportPush_isEquivalence hom
  endpointForward := indexedDiagnosticEndpointEquivalence_apply hom source
  endpointSourceRoundTrip := fun vertex automorphism =>
    (indexedDiagnosticEndpointEquivalence hom source vertex).symm_apply_apply
      automorphism
  endpointInverse := fun vertex targetAutomorphism =>
    (indexedDiagnosticEndpointEquivalence hom source vertex).apply_symm_apply
      targetAutomorphism
  reselectionForward := hom.indexedDiagnosticReselectionEquivalence_apply source
  reselectionSourceRoundTrip :=
    hom.inverseTransportedReselection_transportedReselection source
  reselectionTargetRoundTrip :=
    hom.transportedReselection_inverseTransportedReselection source
  pathForward := fun reselection =>
    hom.indexedDiagnosticHorizontalPathPasting_eq_pathSquare source reselection
      first second
  pathInverse := fun targetReselection =>
    hom.indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare source
      targetReselection first second
  cochainForward :=
    hom.indexedDiagnosticDefectCochainEquivalence_rawDefectCochain source
  cochainInverse :=
    hom.indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain source
  cochainSourceRoundTrip := fun cochain =>
    (indexedDiagnosticDefectCochainEquivalence hom source).symm_apply_apply cochain
  cochainTargetRoundTrip := fun targetCochain =>
    (indexedDiagnosticDefectCochainEquivalence hom source).apply_symm_apply
      targetCochain
  orbitForward := hom.indexedDiagnosticInReselectionOrbit_iff source
  orbitInverse := hom.indexedDiagnosticInReselectionOrbit_symm_iff source
  coherenceForward := hom.indexedCoherentAt_transport_iff source
  coherenceInverse := hom.indexedCoherentAt_inverseTransport_iff source
  obstruction := hom.indexedTransportObstructionVanishes_iff source

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
