import ResearchLean.AG.DiagnosticConservativity.ObstructionExactness

/-!
# G-113 revision 2 raw-defect cochain exactness

The endpoint equivalences assemble pointwise into an explicit equivalence of
raw-defect cochains.  Its forward and inverse maps commute with the generated
reselection transports, so equality and inequality of arbitrary cochains are
reflected in both directions.

## Implementation notes

The cochain equivalence is the dependent product of the endpoint equivalences,
because the automorphism group varies with the target vertex of each two-cell.
The auxiliary canonicalized interpretation changes only the authored
comparators and is used to derive canonical-comparator naturality from
generated coherence and strongly cocartesian uniqueness.  We reject taking
that naturality or source coherence as an input, since either would move the
commuting conclusion into a caller-supplied premise.  We also reject the older
pointwise cochain homomorphism as the principal definition because it does not
provide the inverse required by conjunct `(f)`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-- Replace the authored comparators by the canonical comparators at one reselection. -/
noncomputable def canonicalizedDiagnosticInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    IndexedDiagnosticInterpretation D :=
  { source with
    comparator := fun cell =>
      canonicalTwoCellComparator source.toAdmissibleTransportData
        reselection cell }

/-- Canonicalization installs precisely the canonical comparator. -/
@[simp]
theorem canonicalizedDiagnosticInterpretation_comparator
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) (cell : G.TwoCell) :
    (canonicalizedDiagnosticInterpretation source reselection).comparator cell =
      canonicalTwoCellComparator source.toAdmissibleTransportData
        reselection cell := rfl

/-- Canonicalizing the comparators leaves every reselected path lift unchanged. -/
@[simp]
theorem canonicalizedDiagnosticInterpretation_reselectedPathLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (canonicalizedDiagnosticInterpretation source reselection).reselectedPathLift
        reselection path =
      source.reselectedPathLift reselection path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.reselectedPathLift,
        IndexedDiagnosticInterpretation.reselectedEdgeLift]
      rw [inductionHypothesis]
      rfl

/-- The canonicalized interpretation is coherent at its defining reselection. -/
theorem canonicalizedDiagnosticInterpretation_coherent
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    (canonicalizedDiagnosticInterpretation source reselection).IndexedCoherentAt
      reselection := by
  intro cell
  rw [canonicalizedDiagnosticInterpretation_reselectedPathLift,
    canonicalizedDiagnosticInterpretation_reselectedPathLift]
  change (source.reselectedPathLift reselection (G.twoLeft cell)).comp
      (PackageFiberAut.hom (canonicalTwoCellComparator
        source.toAdmissibleTransportData reselection cell)) =
    source.reselectedPathLift reselection (G.twoRight cell)
  rw [← source.toAdmissibleTransportData_reselectedPathLift reselection,
    ← source.toAdmissibleTransportData_reselectedPathLift reselection]
  exact canonicalTwoCellComparator_fac source.toAdmissibleTransportData
    reselection cell

/-- Transporting after canonicalization leaves every reselected target path unchanged. -/
@[simp]
theorem transportedCanonicalized_reselectedPathLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (hom.transportedInterpretation
        (canonicalizedDiagnosticInterpretation source reselection)).reselectedPathLift
        (hom.transportedReselection
          (canonicalizedDiagnosticInterpretation source reselection) reselection) path =
      (hom.transportedInterpretation source).reselectedPathLift
        (hom.transportedReselection source reselection) path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.reselectedPathLift,
        IndexedDiagnosticInterpretation.reselectedEdgeLift]
      rw [inductionHypothesis]
      rfl

/-- Canonicalizing comparators leaves every generated endpoint action unchanged. -/
@[simp]
theorem endpointAction_canonicalizedDiagnosticInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) (vertex : G.Vertex) :
    hom.endpointAction (canonicalizedDiagnosticInterpretation source reselection)
        vertex =
      hom.endpointAction source vertex := rfl

/-- Endpoint transport sends each canonical comparator to the target canonical comparator. -/
theorem endpointAction_canonicalTwoCellComparator
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) (cell : G.TwoCell) :
    hom.endpointAction source (G.twoTarget cell)
        (canonicalTwoCellComparator source.toAdmissibleTransportData
          reselection cell) =
      canonicalTwoCellComparator
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (hom.transportedReselection source reselection) cell := by
  let canonicalized := canonicalizedDiagnosticInterpretation source reselection
  let targetLeft :=
    TransportCoherence.reselectedPathLift
      (hom.transportedInterpretation source).toAdmissibleTransportData.lift
      (hom.transportedReselection source reselection)
      (G.twoLeft cell).toPresentedPath
  letI : (packageProjection U).IsStronglyCocartesian
      targetLeft.base targetLeft :=
    TransportCoherence.reselectedPathLift_isStronglyCocartesian
      (hom.transportedInterpretation source).toAdmissibleTransportData.lift
      (hom.transportedReselection source reselection)
      (G.twoLeft cell).toPresentedPath
  apply PackageFiberAut.ext_of_strong_fac targetLeft
  have transportedCoherent := hom.indexedCoherentAt_transport canonicalized
    reselection (canonicalizedDiagnosticInterpretation_coherent source reselection)
  calc
    targetLeft.comp
        (PackageFiberAut.hom
          (hom.endpointAction source (G.twoTarget cell)
            (canonicalTwoCellComparator source.toAdmissibleTransportData
              reselection cell))) =
      (hom.transportedInterpretation source).reselectedPathLift
        (hom.transportedReselection source reselection)
        (G.twoRight cell) := by
          have mapped := transportedCoherent cell
          dsimp only [canonicalized] at mapped
          rw [transportedCanonicalized_reselectedPathLift,
            transportedCanonicalized_reselectedPathLift] at mapped
          dsimp only [targetLeft]
          rw [(hom.transportedInterpretation source).toAdmissibleTransportData_reselectedPathLift
            (hom.transportedReselection source reselection)]
          simpa only [
            transportedInterpretation_comparator,
            endpointAction_canonicalizedDiagnosticInterpretation,
            canonicalizedDiagnosticInterpretation_comparator] using mapped
    _ = targetLeft.comp
        (PackageFiberAut.hom
          (canonicalTwoCellComparator
            (hom.transportedInterpretation source).toAdmissibleTransportData
            (hom.transportedReselection source reselection) cell)) :=
      (by
        dsimp only [targetLeft]
        have fac := (canonicalTwoCellComparator_fac
          (hom.transportedInterpretation source).toAdmissibleTransportData
          (hom.transportedReselection source reselection) cell).symm
        rw [(hom.transportedInterpretation source).toAdmissibleTransportData_reselectedPathLift
          (hom.transportedReselection source reselection)] at fac
        exact fac)

/--
The explicit conjunct `(f)` cochain equivalence, generated pointwise from the
Cycle 5 endpoint equivalences and requiring no additional exactness premise.
-/
noncomputable def indexedDiagnosticDefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain source.toAdmissibleTransportData ≃*
      DefectCochain
        (hom.transportedInterpretation source).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticEndpointEquivalence hom source (G.twoTarget cell)

/-- The cochain equivalence acts pointwise by the endpoint equivalence. -/
theorem indexedDiagnosticDefectCochainEquivalence_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (cochain : DefectCochain source.toAdmissibleTransportData)
    (cell : G.TwoCell) :
    indexedDiagnosticDefectCochainEquivalence hom source cochain cell =
      indexedDiagnosticEndpointEquivalence hom source (G.twoTarget cell)
        (cochain cell) := rfl

/-- Endpoint equivalence transports the fixed ordered raw defect on one two-cell. -/
theorem indexedDiagnosticEndpointEquivalence_rawTwoCellDefect
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) (cell : G.TwoCell) :
    indexedDiagnosticEndpointEquivalence hom source (G.twoTarget cell)
        (rawTwoCellDefect source.toAdmissibleTransportData reselection cell) =
      rawTwoCellDefect
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (hom.transportedReselection source reselection) cell := by
  rw [indexedDiagnosticEndpointEquivalence_apply]
  unfold rawTwoCellDefect
  rw [map_mul, map_inv]
  rw [hom.endpointAction_canonicalTwoCellComparator source reselection cell]
  rfl

/--
The forward conjunct `(f)` equivalence commutes with `rawDefectCochain`; its
premises are exactly the fixed indexed hom, generated interpretation, and the
cochain coordinate supplied by a source reselection.
-/
theorem indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    indexedDiagnosticDefectCochainEquivalence hom source
        (rawDefectCochain source.toAdmissibleTransportData reselection) =
      rawDefectCochain
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (hom.transportedReselection source reselection) := by
  funext cell
  exact hom.indexedDiagnosticEndpointEquivalence_rawTwoCellDefect
    source reselection cell

/-- The inverse cochain equivalence commutes with inverse reselection transport. -/
theorem indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) :
    (indexedDiagnosticDefectCochainEquivalence hom source).symm
        (rawDefectCochain
          (hom.transportedInterpretation source).toAdmissibleTransportData
          targetReselection) =
      rawDefectCochain source.toAdmissibleTransportData
        (hom.inverseTransportedReselection source targetReselection) := by
  apply (indexedDiagnosticDefectCochainEquivalence hom source).injective
  rw [(indexedDiagnosticDefectCochainEquivalence hom source).apply_symm_apply]
  rw [indexedDiagnosticDefectCochainEquivalence_rawDefectCochain]
  rw [hom.transportedReselection_inverseTransportedReselection]

/-- Forward cochain transport reflects and preserves arbitrary equality. -/
theorem indexedDiagnosticDefectCochainEquivalence_apply_eq_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (left right : DefectCochain source.toAdmissibleTransportData) :
    indexedDiagnosticDefectCochainEquivalence hom source left =
        indexedDiagnosticDefectCochainEquivalence hom source right ↔
      left = right := by
  constructor
  · intro transportedEq
    exact (indexedDiagnosticDefectCochainEquivalence hom source).injective
      transportedEq
  · intro equality
    exact congrArg (indexedDiagnosticDefectCochainEquivalence hom source) equality

/-- Forward cochain transport reflects and preserves arbitrary inequality. -/
theorem indexedDiagnosticDefectCochainEquivalence_apply_ne_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (left right : DefectCochain source.toAdmissibleTransportData) :
    indexedDiagnosticDefectCochainEquivalence hom source left ≠
        indexedDiagnosticDefectCochainEquivalence hom source right ↔
      left ≠ right := by
  constructor
  · intro transportedNe sourceEq
    exact transportedNe
      (congrArg (indexedDiagnosticDefectCochainEquivalence hom source) sourceEq)
  · intro sourceNe transportedEq
    exact sourceNe
      ((indexedDiagnosticDefectCochainEquivalence hom source).injective transportedEq)

/-- Inverse cochain transport reflects and preserves arbitrary equality. -/
theorem indexedDiagnosticDefectCochainEquivalence_symm_apply_eq_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (left right : DefectCochain
      (hom.transportedInterpretation source).toAdmissibleTransportData) :
    (indexedDiagnosticDefectCochainEquivalence hom source).symm left =
        (indexedDiagnosticDefectCochainEquivalence hom source).symm right ↔
      left = right := by
  constructor
  · intro transportedEq
    exact (indexedDiagnosticDefectCochainEquivalence hom source).symm.injective
      transportedEq
  · intro equality
    exact congrArg (indexedDiagnosticDefectCochainEquivalence hom source).symm equality

/-- Inverse cochain transport reflects and preserves arbitrary inequality. -/
theorem indexedDiagnosticDefectCochainEquivalence_symm_apply_ne_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (left right : DefectCochain
      (hom.transportedInterpretation source).toAdmissibleTransportData) :
    (indexedDiagnosticDefectCochainEquivalence hom source).symm left ≠
        (indexedDiagnosticDefectCochainEquivalence hom source).symm right ↔
      left ≠ right := by
  constructor
  · intro transportedNe sourceEq
    exact transportedNe
      (congrArg (indexedDiagnosticDefectCochainEquivalence hom source).symm sourceEq)
  · intro sourceNe transportedEq
    exact sourceNe
      ((indexedDiagnosticDefectCochainEquivalence hom source).symm.injective transportedEq)

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
