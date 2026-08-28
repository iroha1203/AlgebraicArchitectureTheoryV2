import ResearchLean.AG.DiagnosticConservativity.TransportCoherence
import ResearchLean.AG.DiagnosticConservativity.OrbitExactness
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastingCoherence

/-!
# G-113 revision 2 downstream vertical-composition compatibility

The G-111 compositor and the inverse mate of the G-112 semantic-global
compositor independently compare direct and successive diagnostic transport.
This module identifies those comparisons by the Cycle 11 mate theorem and
lifts the resulting endpoint equation to reselections, raw-defect cochains,
and arbitrary-target orbit membership.

## Implementation notes

The G-112 compositor points from successive reindexing to direct reindexing.
The inverse of `conjugateIsoEquiv` therefore pulls it back to the required
direct-to-successive comparison of the left adjoints.  The construction does
not identify direct and successive transported interpretations by definitional
equality: their explicit compositor acts on endpoint automorphisms.  The
reselection and cochain comparisons are dependent products of that endpoint
action over every coordinate; a comparison at a selected coordinate would not
provide the full indexed compatibility required here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-! ## Endpoint automorphisms -/

/-- The G-111 compositor acts on endpoint automorphisms from direct composite
transport to successive transport. -/
noncomputable def indexedDiagnosticCompositionEndpointCompositorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut
        (((first.comp second).transportedInterpretation source).package vertex) ≃*
      PackageFiberAut
        ((second.transportedInterpretation
          (first.transportedInterpretation source)).package vertex) :=
  packageFiberAutMulEquivOfCoreFiberIso
    ((coreFiberCompositor (first.app vertex) (second.app vertex)).app
      (source.fiberPackage vertex))

/-- Pull the G-112 semantic-global compositor back through the generated
G-113 mate equivalence and let the resulting fiber isomorphism act on endpoint
automorphisms. -/
noncomputable def indexedDiagnosticCompositionMateEndpointCompositorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut
        (((first.comp second).transportedInterpretation source).package vertex) ≃*
      PackageFiberAut
        ((second.transportedInterpretation
          (first.transportedInterpretation source)).package vertex) :=
  packageFiberAutMulEquivOfCoreFiberIso
    (((conjugateIsoEquiv
      ((indexedDiagnosticTransportAdjunction first vertex).comp
        (indexedDiagnosticTransportAdjunction second vertex))
      (indexedDiagnosticTransportAdjunction (first.comp second) vertex)).symm
        (exact_bottom_semantic_global_compositor
          (first.app vertex) (second.app vertex))).app
            (source.fiberPackage vertex))

/-- The G-112-mate endpoint compositor comparison is exactly the independently
generated G-111 compositor comparison. -/
theorem indexedDiagnosticCompositionMateEndpointCompositorEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    indexedDiagnosticCompositionMateEndpointCompositorEquivalence
        first second source vertex =
      indexedDiagnosticCompositionEndpointCompositorEquivalence
        first second source vertex := by
  unfold indexedDiagnosticCompositionMateEndpointCompositorEquivalence
  rw [← indexedDiagnosticTransportEquivalence_comp_conjugate
    first second vertex]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Direct endpoint transport followed by the G-112-mate compositor comparison
equals successive endpoint transport for every automorphism. -/
theorem indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    indexedDiagnosticCompositionMateEndpointCompositorEquivalence
        first second source vertex
        (indexedDiagnosticEndpointEquivalence (first.comp second) source vertex
          automorphism) =
      indexedDiagnosticEndpointEquivalence second
        (first.transportedInterpretation source) vertex
        (indexedDiagnosticEndpointEquivalence first source vertex
          automorphism) := by
  rw [indexedDiagnosticCompositionMateEndpointCompositorEquivalence_eq_g111]
  rw [indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply]
  change packageFiberAutMulEquivOfCoreFiberIso
      ((coreFiberCompositor (first.app vertex) (second.app vertex)).app
        (source.fiberPackage vertex))
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (first.app vertex ≫ second.app vertex))
        (source.fiberPackage vertex) automorphism) =
    coreFiberFunctorPackageAutHom
      (coreFiberTransportFunctor (second.app vertex))
      ((coreFiberTransportFunctor (first.app vertex)).obj
        (source.fiberPackage vertex))
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (first.app vertex))
        (source.fiberPackage vertex) automorphism)
  rw [coreFiberFunctorPackageAutHom_iso_naturality]
  rw [coreFiberFunctorPackageAutHom_comp]
  rfl

/-! ## Reselections and cochains -/

/-- Apply the independently generated G-111 endpoint compositor at every
reselection coordinate. -/
noncomputable def indexedDiagnosticCompositionReselectionCompositorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) :
    IndexedEdgeReselection
        ((first.comp second).transportedInterpretation source) ≃*
      IndexedEdgeReselection
        (second.transportedInterpretation
          (first.transportedInterpretation source)) :=
  MulEquiv.piCongrRight fun _i =>
    MulEquiv.piCongrRight fun j =>
      MulEquiv.piCongrRight fun _edge =>
        indexedDiagnosticCompositionEndpointCompositorEquivalence
          first second source j

/-- Apply the G-112-mate endpoint compositor at every reselection coordinate. -/
noncomputable def indexedDiagnosticCompositionMateReselectionCompositorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) :
    IndexedEdgeReselection
        ((first.comp second).transportedInterpretation source) ≃*
      IndexedEdgeReselection
        (second.transportedInterpretation
          (first.transportedInterpretation source)) :=
  MulEquiv.piCongrRight fun _i =>
    MulEquiv.piCongrRight fun j =>
      MulEquiv.piCongrRight fun _edge =>
        indexedDiagnosticCompositionMateEndpointCompositorEquivalence
          first second source j

/-- The G-112-mate and G-111 reselection compositor comparisons agree on every
indexed edge coordinate. -/
theorem indexedDiagnosticCompositionMateReselectionCompositorEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticCompositionMateReselectionCompositorEquivalence
        first second source =
      indexedDiagnosticCompositionReselectionCompositorEquivalence
        first second source := by
  apply MulEquiv.ext
  intro directReselection
  funext i j edge
  change indexedDiagnosticCompositionMateEndpointCompositorEquivalence
      first second source j (directReselection i j edge) =
    indexedDiagnosticCompositionEndpointCompositorEquivalence
      first second source j (directReselection i j edge)
  rw [indexedDiagnosticCompositionMateEndpointCompositorEquivalence_eq_g111]

/-- Direct reselection transport followed by the mate compositor comparison
equals successive reselection transport. -/
theorem indexedDiagnosticCompositionMateReselectionCompositorEquivalence_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    indexedDiagnosticCompositionMateReselectionCompositorEquivalence
        first second source
        (indexedDiagnosticReselectionEquivalence (first.comp second) source
          reselection) =
      indexedDiagnosticReselectionEquivalence second
        (first.transportedInterpretation source)
        (indexedDiagnosticReselectionEquivalence first source reselection) := by
  funext i j edge
  change indexedDiagnosticCompositionMateEndpointCompositorEquivalence
      first second source j
      (indexedDiagnosticEndpointEquivalence (first.comp second) source j
        (reselection i j edge)) =
    indexedDiagnosticEndpointEquivalence second
      (first.transportedInterpretation source) j
      (indexedDiagnosticEndpointEquivalence first source j
        (reselection i j edge))
  exact indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
    first second source j (reselection i j edge)

/-- Apply the independently generated G-111 endpoint compositor at every
raw-defect cochain coordinate. -/
noncomputable def indexedDiagnosticCompositionDefectCochainCompositorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        ((first.comp second).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (second.transportedInterpretation
          (first.transportedInterpretation source)).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticCompositionEndpointCompositorEquivalence
      first second source (G.twoTarget cell)

/-- Apply the G-112-mate endpoint compositor at every raw-defect cochain
coordinate. -/
noncomputable def indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        ((first.comp second).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (second.transportedInterpretation
          (first.transportedInterpretation source)).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticCompositionMateEndpointCompositorEquivalence
      first second source (G.twoTarget cell)

/-- The G-112-mate and G-111 cochain compositor comparisons agree on every
two-cell coordinate. -/
theorem indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence
        first second source =
      indexedDiagnosticCompositionDefectCochainCompositorEquivalence
        first second source := by
  apply MulEquiv.ext
  intro directCochain
  funext cell
  change indexedDiagnosticCompositionMateEndpointCompositorEquivalence
      first second source (G.twoTarget cell) (directCochain cell) =
    indexedDiagnosticCompositionEndpointCompositorEquivalence
      first second source (G.twoTarget cell) (directCochain cell)
  rw [indexedDiagnosticCompositionMateEndpointCompositorEquivalence_eq_g111]

/-- Direct cochain transport followed by the mate compositor comparison equals
successive cochain transport for every source cochain. -/
theorem indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D)
    (cochain : DefectCochain source.toAdmissibleTransportData) :
    indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence
        first second source
        (indexedDiagnosticDefectCochainEquivalence (first.comp second) source
          cochain) =
      indexedDiagnosticDefectCochainEquivalence second
        (first.transportedInterpretation source)
        (indexedDiagnosticDefectCochainEquivalence first source cochain) := by
  funext cell
  change indexedDiagnosticCompositionMateEndpointCompositorEquivalence
      first second source (G.twoTarget cell)
      (indexedDiagnosticEndpointEquivalence (first.comp second) source
        (G.twoTarget cell) (cochain cell)) =
    indexedDiagnosticEndpointEquivalence second
      (first.transportedInterpretation source) (G.twoTarget cell)
      (indexedDiagnosticEndpointEquivalence first source
        (G.twoTarget cell) (cochain cell))
  exact indexedDiagnosticCompositionMateEndpointCompositorEquivalence_apply
    first second source (G.twoTarget cell) (cochain cell)

/-! ## Orbit membership -/

/-- Arbitrary direct-target orbit membership is invariant under the generated
G-112-mate compositor comparison to successive transport. -/
theorem indexedDiagnosticCompositionInReselectionOrbit_mate_compositor_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D)
    (directCochain : DefectCochain
      ((first.comp second).transportedInterpretation source).toAdmissibleTransportData) :
    InReselectionOrbit
        ((first.comp second).transportedInterpretation source).toAdmissibleTransportData
        directCochain ↔
      InReselectionOrbit
        (second.transportedInterpretation
          (first.transportedInterpretation source)).toAdmissibleTransportData
        (indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence
          first second source directCochain) := by
  let sourceCochain :=
    (indexedDiagnosticDefectCochainEquivalence (first.comp second) source).symm
      directCochain
  have directRoundTrip :
      indexedDiagnosticDefectCochainEquivalence (first.comp second) source
          sourceCochain = directCochain := by
    exact (indexedDiagnosticDefectCochainEquivalence
      (first.comp second) source).apply_symm_apply directCochain
  have compositorEquation :=
    indexedDiagnosticCompositionMateDefectCochainCompositorEquivalence_apply
      first second source sourceCochain
  rw [directRoundTrip] at compositorEquation
  calc
    _ ↔ InReselectionOrbit source.toAdmissibleTransportData sourceCochain :=
      indexedDiagnosticInReselectionOrbit_symm_iff
        (first.comp second) source directCochain
    _ ↔ InReselectionOrbit
        (first.transportedInterpretation source).toAdmissibleTransportData
        (indexedDiagnosticDefectCochainEquivalence first source
          sourceCochain) :=
      indexedDiagnosticInReselectionOrbit_iff first source sourceCochain
    _ ↔ InReselectionOrbit
        (second.transportedInterpretation
          (first.transportedInterpretation source)).toAdmissibleTransportData
        (indexedDiagnosticDefectCochainEquivalence second
          (first.transportedInterpretation source)
          (indexedDiagnosticDefectCochainEquivalence first source
            sourceCochain)) :=
      indexedDiagnosticInReselectionOrbit_iff second
        (first.transportedInterpretation source)
        (indexedDiagnosticDefectCochainEquivalence first source sourceCochain)
    _ ↔ _ := by rw [← compositorEquation]

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
