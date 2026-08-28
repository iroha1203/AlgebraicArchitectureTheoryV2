import ResearchLean.AG.DiagnosticConservativity.WholeUnitCompatibility
import ResearchLean.AG.DiagnosticConservativity.ObstructionExactness
import ResearchLean.AG.DiagnosticConservativity.OrbitExactness

/-!
# G-113 revision 2 whole-unit downstream compatibility

For an arbitrary indexed base-diagram hom, the whole source- and target-unit
routes compare transport along the corresponding identity composite with
transport along the hom itself.  This module lets both G-111 whole routes and
the independently generated inverse mates of the G-112 whole routes act on
endpoint automorphisms.  Their cross-system equalities are then lifted to all
reselection and raw-defect cochain coordinates.

The route application equations identify direct identity-composite transport
with transport along the original hom.  They are used to move arbitrary orbit,
coherence, and coherentizability witnesses in both directions.  Thus this is
not the identity-hom compatibility theorem: `hom` remains arbitrary throughout,
and both source- and target-unit triangles occur as proof inputs.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-! ## Endpoint automorphisms -/

/-- The whole G-111 source-unit route acting on endpoint automorphisms. -/
noncomputable def indexedDiagnosticLeftUnitG111EndpointEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut
        ((((id D).comp hom).transportedInterpretation source).package vertex) ≃*
      PackageFiberAut ((hom.transportedInterpretation source).package vertex) :=
  packageFiberAutMulEquivOfCoreFiberIso
    ((coreFiberLeftUnitRouteIso (hom.app vertex)).app
      (source.fiberPackage vertex))

/-- The whole G-111 target-unit route acting on endpoint automorphisms. -/
noncomputable def indexedDiagnosticRightUnitG111EndpointEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut
        (((hom.comp (id E)).transportedInterpretation source).package vertex) ≃*
      PackageFiberAut ((hom.transportedInterpretation source).package vertex) :=
  packageFiberAutMulEquivOfCoreFiberIso
    ((coreFiberRightUnitRouteIso (hom.app vertex)).app
      (source.fiberPackage vertex))

/-- Pull the whole G-112 source-unit route back through its generated
adjunction mate and let it act on endpoint automorphisms. -/
noncomputable def indexedDiagnosticLeftUnitMateEndpointEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut
        ((((id D).comp hom).transportedInterpretation source).package vertex) ≃*
      PackageFiberAut ((hom.transportedInterpretation source).package vertex) :=
  packageFiberAutMulEquivOfCoreFiberIso
    (((conjugateIsoEquiv
      (indexedDiagnosticTransportAdjunction hom vertex)
      (semanticGlobalTransportReindexAdjunction
        (𝟙 (D.vertex vertex) ≫ hom.app vertex))).symm
      (semanticGlobalLeftUnitRouteIso (hom.app vertex))).app
        (source.fiberPackage vertex))

/-- Pull the whole G-112 target-unit route back through its generated
adjunction mate and let it act on endpoint automorphisms. -/
noncomputable def indexedDiagnosticRightUnitMateEndpointEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut
        (((hom.comp (id E)).transportedInterpretation source).package vertex) ≃*
      PackageFiberAut ((hom.transportedInterpretation source).package vertex) :=
  packageFiberAutMulEquivOfCoreFiberIso
    (((conjugateIsoEquiv
      (indexedDiagnosticTransportAdjunction hom vertex)
      (semanticGlobalTransportReindexAdjunction
        (hom.app vertex ≫ 𝟙 (E.vertex vertex)))).symm
      (semanticGlobalRightUnitRouteIso (hom.app vertex))).app
        (source.fiberPackage vertex))

/-- The G-112-mate source-unit endpoint action is the independently generated
G-111 whole source-unit action. -/
theorem indexedDiagnosticLeftUnitMateEndpointEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    indexedDiagnosticLeftUnitMateEndpointEquivalence hom source vertex =
      indexedDiagnosticLeftUnitG111EndpointEquivalence hom source vertex := by
  unfold indexedDiagnosticLeftUnitMateEndpointEquivalence
  rw [← indexedDiagnosticTransportEquivalence_leftUnitRouteIso_conjugate
    hom vertex]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- The G-112-mate target-unit endpoint action is the independently generated
G-111 whole target-unit action. -/
theorem indexedDiagnosticRightUnitMateEndpointEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    indexedDiagnosticRightUnitMateEndpointEquivalence hom source vertex =
      indexedDiagnosticRightUnitG111EndpointEquivalence hom source vertex := by
  unfold indexedDiagnosticRightUnitMateEndpointEquivalence
  rw [← indexedDiagnosticTransportEquivalence_rightUnitRouteIso_conjugate
    hom vertex]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Direct source-unit-composite endpoint transport followed by the G-112-mate
whole-unit comparison equals transport along the original hom. -/
theorem indexedDiagnosticLeftUnitMateEndpointEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    indexedDiagnosticLeftUnitMateEndpointEquivalence hom source vertex
        (indexedDiagnosticEndpointEquivalence ((id D).comp hom) source vertex
          automorphism) =
      indexedDiagnosticEndpointEquivalence hom source vertex automorphism := by
  rw [indexedDiagnosticLeftUnitMateEndpointEquivalence_eq_g111]
  rw [indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply]
  change packageFiberAutMulEquivOfCoreFiberIso
      ((coreFiberLeftUnitRouteIso (hom.app vertex)).app
        (source.fiberPackage vertex))
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (𝟙 (D.vertex vertex) ≫ hom.app vertex))
        (source.fiberPackage vertex) automorphism) =
    coreFiberFunctorPackageAutHom
      (coreFiberTransportFunctor (hom.app vertex))
      (source.fiberPackage vertex) automorphism
  rw [coreFiberFunctorPackageAutHom_iso_naturality]

/-- Direct target-unit-composite endpoint transport followed by the G-112-mate
whole-unit comparison equals transport along the original hom. -/
theorem indexedDiagnosticRightUnitMateEndpointEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    indexedDiagnosticRightUnitMateEndpointEquivalence hom source vertex
        (indexedDiagnosticEndpointEquivalence (hom.comp (id E)) source vertex
          automorphism) =
      indexedDiagnosticEndpointEquivalence hom source vertex automorphism := by
  rw [indexedDiagnosticRightUnitMateEndpointEquivalence_eq_g111]
  rw [indexedDiagnosticEndpointEquivalence_apply,
    indexedDiagnosticEndpointEquivalence_apply]
  change packageFiberAutMulEquivOfCoreFiberIso
      ((coreFiberRightUnitRouteIso (hom.app vertex)).app
        (source.fiberPackage vertex))
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (hom.app vertex ≫ 𝟙 (E.vertex vertex)))
        (source.fiberPackage vertex) automorphism) =
    coreFiberFunctorPackageAutHom
      (coreFiberTransportFunctor (hom.app vertex))
      (source.fiberPackage vertex) automorphism
  rw [coreFiberFunctorPackageAutHom_iso_naturality]

/-! ## Reselections -/

/-- Apply the G-111 source-unit endpoint action at every reselection coordinate. -/
noncomputable def indexedDiagnosticLeftUnitG111ReselectionEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    IndexedEdgeReselection
        (((id D).comp hom).transportedInterpretation source) ≃*
      IndexedEdgeReselection (hom.transportedInterpretation source) :=
  MulEquiv.piCongrRight fun _i =>
    MulEquiv.piCongrRight fun j =>
      MulEquiv.piCongrRight fun _edge =>
        indexedDiagnosticLeftUnitG111EndpointEquivalence hom source j

/-- Apply the G-111 target-unit endpoint action at every reselection coordinate. -/
noncomputable def indexedDiagnosticRightUnitG111ReselectionEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    IndexedEdgeReselection
        ((hom.comp (id E)).transportedInterpretation source) ≃*
      IndexedEdgeReselection (hom.transportedInterpretation source) :=
  MulEquiv.piCongrRight fun _i =>
    MulEquiv.piCongrRight fun j =>
      MulEquiv.piCongrRight fun _edge =>
        indexedDiagnosticRightUnitG111EndpointEquivalence hom source j

/-- Apply the G-112-mate source-unit endpoint action at every reselection coordinate. -/
noncomputable def indexedDiagnosticLeftUnitMateReselectionEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    IndexedEdgeReselection
        (((id D).comp hom).transportedInterpretation source) ≃*
      IndexedEdgeReselection (hom.transportedInterpretation source) :=
  MulEquiv.piCongrRight fun _i =>
    MulEquiv.piCongrRight fun j =>
      MulEquiv.piCongrRight fun _edge =>
        indexedDiagnosticLeftUnitMateEndpointEquivalence hom source j

/-- Apply the G-112-mate target-unit endpoint action at every reselection coordinate. -/
noncomputable def indexedDiagnosticRightUnitMateReselectionEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    IndexedEdgeReselection
        ((hom.comp (id E)).transportedInterpretation source) ≃*
      IndexedEdgeReselection (hom.transportedInterpretation source) :=
  MulEquiv.piCongrRight fun _i =>
    MulEquiv.piCongrRight fun j =>
      MulEquiv.piCongrRight fun _edge =>
        indexedDiagnosticRightUnitMateEndpointEquivalence hom source j

/-- The G-112-mate and G-111 source-unit reselection actions agree. -/
theorem indexedDiagnosticLeftUnitMateReselectionEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticLeftUnitMateReselectionEquivalence hom source =
      indexedDiagnosticLeftUnitG111ReselectionEquivalence hom source := by
  apply MulEquiv.ext
  intro reselection
  funext i j edge
  change indexedDiagnosticLeftUnitMateEndpointEquivalence hom source j
      (reselection i j edge) =
    indexedDiagnosticLeftUnitG111EndpointEquivalence hom source j
      (reselection i j edge)
  rw [indexedDiagnosticLeftUnitMateEndpointEquivalence_eq_g111]

/-- The G-112-mate and G-111 target-unit reselection actions agree. -/
theorem indexedDiagnosticRightUnitMateReselectionEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticRightUnitMateReselectionEquivalence hom source =
      indexedDiagnosticRightUnitG111ReselectionEquivalence hom source := by
  apply MulEquiv.ext
  intro reselection
  funext i j edge
  change indexedDiagnosticRightUnitMateEndpointEquivalence hom source j
      (reselection i j edge) =
    indexedDiagnosticRightUnitG111EndpointEquivalence hom source j
      (reselection i j edge)
  rw [indexedDiagnosticRightUnitMateEndpointEquivalence_eq_g111]

/-- Source-unit-composite reselection transport followed by the mate whole-unit
comparison equals transport along the original hom. -/
theorem indexedDiagnosticLeftUnitMateReselectionEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
        (((id D).comp hom).transportedReselection source reselection) =
      hom.transportedReselection source reselection := by
  funext i j edge
  change indexedDiagnosticLeftUnitMateEndpointEquivalence hom source j
      (indexedDiagnosticEndpointEquivalence ((id D).comp hom) source j
        (reselection i j edge)) =
    indexedDiagnosticEndpointEquivalence hom source j (reselection i j edge)
  exact indexedDiagnosticLeftUnitMateEndpointEquivalence_transport_apply
    hom source j (reselection i j edge)

/-- Target-unit-composite reselection transport followed by the mate whole-unit
comparison equals transport along the original hom. -/
theorem indexedDiagnosticRightUnitMateReselectionEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    indexedDiagnosticRightUnitMateReselectionEquivalence hom source
        ((hom.comp (id E)).transportedReselection source reselection) =
      hom.transportedReselection source reselection := by
  funext i j edge
  change indexedDiagnosticRightUnitMateEndpointEquivalence hom source j
      (indexedDiagnosticEndpointEquivalence (hom.comp (id E)) source j
        (reselection i j edge)) =
    indexedDiagnosticEndpointEquivalence hom source j (reselection i j edge)
  exact indexedDiagnosticRightUnitMateEndpointEquivalence_transport_apply
    hom source j (reselection i j edge)

/-! ## Raw-defect cochains and orbit membership -/

/-- Apply the G-111 source-unit endpoint action at every cochain coordinate. -/
noncomputable def indexedDiagnosticLeftUnitG111DefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        (((id D).comp hom).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (hom.transportedInterpretation source).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticLeftUnitG111EndpointEquivalence hom source
      (G.twoTarget cell)

/-- Apply the G-111 target-unit endpoint action at every cochain coordinate. -/
noncomputable def indexedDiagnosticRightUnitG111DefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        ((hom.comp (id E)).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (hom.transportedInterpretation source).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticRightUnitG111EndpointEquivalence hom source
      (G.twoTarget cell)

/-- Apply the G-112-mate source-unit endpoint action at every cochain coordinate. -/
noncomputable def indexedDiagnosticLeftUnitMateDefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        (((id D).comp hom).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (hom.transportedInterpretation source).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticLeftUnitMateEndpointEquivalence hom source
      (G.twoTarget cell)

/-- Apply the G-112-mate target-unit endpoint action at every cochain coordinate. -/
noncomputable def indexedDiagnosticRightUnitMateDefectCochainEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        ((hom.comp (id E)).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain
        (hom.transportedInterpretation source).toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticRightUnitMateEndpointEquivalence hom source
      (G.twoTarget cell)

/-- The G-112-mate and G-111 source-unit cochain actions agree at every
two-cell coordinate. -/
theorem indexedDiagnosticLeftUnitMateDefectCochainEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticLeftUnitMateDefectCochainEquivalence hom source =
      indexedDiagnosticLeftUnitG111DefectCochainEquivalence hom source := by
  apply MulEquiv.ext
  intro cochain
  funext cell
  change indexedDiagnosticLeftUnitMateEndpointEquivalence hom source
      (G.twoTarget cell) (cochain cell) =
    indexedDiagnosticLeftUnitG111EndpointEquivalence hom source
      (G.twoTarget cell) (cochain cell)
  rw [indexedDiagnosticLeftUnitMateEndpointEquivalence_eq_g111]

/-- The G-112-mate and G-111 target-unit cochain actions agree at every
two-cell coordinate. -/
theorem indexedDiagnosticRightUnitMateDefectCochainEquivalence_eq_g111
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticRightUnitMateDefectCochainEquivalence hom source =
      indexedDiagnosticRightUnitG111DefectCochainEquivalence hom source := by
  apply MulEquiv.ext
  intro cochain
  funext cell
  change indexedDiagnosticRightUnitMateEndpointEquivalence hom source
      (G.twoTarget cell) (cochain cell) =
    indexedDiagnosticRightUnitG111EndpointEquivalence hom source
      (G.twoTarget cell) (cochain cell)
  rw [indexedDiagnosticRightUnitMateEndpointEquivalence_eq_g111]

/-- Source-unit-composite cochain transport followed by the mate whole-unit
comparison equals transport along the original hom. -/
theorem indexedDiagnosticLeftUnitMateDefectCochainEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (cochain : DefectCochain source.toAdmissibleTransportData) :
    indexedDiagnosticLeftUnitMateDefectCochainEquivalence hom source
        (indexedDiagnosticDefectCochainEquivalence ((id D).comp hom) source
          cochain) =
      indexedDiagnosticDefectCochainEquivalence hom source cochain := by
  funext cell
  change indexedDiagnosticLeftUnitMateEndpointEquivalence hom source
      (G.twoTarget cell)
      (indexedDiagnosticEndpointEquivalence ((id D).comp hom) source
        (G.twoTarget cell) (cochain cell)) =
    indexedDiagnosticEndpointEquivalence hom source
      (G.twoTarget cell) (cochain cell)
  exact indexedDiagnosticLeftUnitMateEndpointEquivalence_transport_apply
    hom source (G.twoTarget cell) (cochain cell)

/-- Target-unit-composite cochain transport followed by the mate whole-unit
comparison equals transport along the original hom. -/
theorem indexedDiagnosticRightUnitMateDefectCochainEquivalence_transport_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (cochain : DefectCochain source.toAdmissibleTransportData) :
    indexedDiagnosticRightUnitMateDefectCochainEquivalence hom source
        (indexedDiagnosticDefectCochainEquivalence (hom.comp (id E)) source
          cochain) =
      indexedDiagnosticDefectCochainEquivalence hom source cochain := by
  funext cell
  change indexedDiagnosticRightUnitMateEndpointEquivalence hom source
      (G.twoTarget cell)
      (indexedDiagnosticEndpointEquivalence (hom.comp (id E)) source
        (G.twoTarget cell) (cochain cell)) =
    indexedDiagnosticEndpointEquivalence hom source
      (G.twoTarget cell) (cochain cell)
  exact indexedDiagnosticRightUnitMateEndpointEquivalence_transport_apply
    hom source (G.twoTarget cell) (cochain cell)

/-- Arbitrary source-unit-composite target orbit membership is invariant under
the generated mate comparison to transport along the original hom. -/
theorem indexedDiagnosticLeftUnitInReselectionOrbit_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (directCochain : DefectCochain
      (((id D).comp hom).transportedInterpretation source).toAdmissibleTransportData) :
    InReselectionOrbit
        (((id D).comp hom).transportedInterpretation source).toAdmissibleTransportData
        directCochain ↔
      InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (indexedDiagnosticLeftUnitMateDefectCochainEquivalence hom source
          directCochain) := by
  let sourceCochain :=
    (indexedDiagnosticDefectCochainEquivalence ((id D).comp hom) source).symm
      directCochain
  have directRoundTrip :
      indexedDiagnosticDefectCochainEquivalence ((id D).comp hom) source
          sourceCochain = directCochain :=
    (indexedDiagnosticDefectCochainEquivalence
      ((id D).comp hom) source).apply_symm_apply directCochain
  have unitEquation :=
    indexedDiagnosticLeftUnitMateDefectCochainEquivalence_transport_apply
      hom source sourceCochain
  rw [directRoundTrip] at unitEquation
  calc
    _ ↔ InReselectionOrbit source.toAdmissibleTransportData sourceCochain :=
      indexedDiagnosticInReselectionOrbit_symm_iff
        ((id D).comp hom) source directCochain
    _ ↔ InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (indexedDiagnosticDefectCochainEquivalence hom source sourceCochain) :=
      indexedDiagnosticInReselectionOrbit_iff hom source sourceCochain
    _ ↔ _ := by rw [← unitEquation]

/-- Arbitrary target-unit-composite target orbit membership is invariant under
the generated mate comparison to transport along the original hom. -/
theorem indexedDiagnosticRightUnitInReselectionOrbit_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (directCochain : DefectCochain
      ((hom.comp (id E)).transportedInterpretation source).toAdmissibleTransportData) :
    InReselectionOrbit
        ((hom.comp (id E)).transportedInterpretation source).toAdmissibleTransportData
        directCochain ↔
      InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (indexedDiagnosticRightUnitMateDefectCochainEquivalence hom source
          directCochain) := by
  let sourceCochain :=
    (indexedDiagnosticDefectCochainEquivalence (hom.comp (id E)) source).symm
      directCochain
  have directRoundTrip :
      indexedDiagnosticDefectCochainEquivalence (hom.comp (id E)) source
          sourceCochain = directCochain :=
    (indexedDiagnosticDefectCochainEquivalence
      (hom.comp (id E)) source).apply_symm_apply directCochain
  have unitEquation :=
    indexedDiagnosticRightUnitMateDefectCochainEquivalence_transport_apply
      hom source sourceCochain
  rw [directRoundTrip] at unitEquation
  calc
    _ ↔ InReselectionOrbit source.toAdmissibleTransportData sourceCochain :=
      indexedDiagnosticInReselectionOrbit_symm_iff
        (hom.comp (id E)) source directCochain
    _ ↔ InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (indexedDiagnosticDefectCochainEquivalence hom source sourceCochain) :=
      indexedDiagnosticInReselectionOrbit_iff hom source sourceCochain
    _ ↔ _ := by rw [← unitEquation]

/-! ## Coherence and obstruction propositions -/

/-- Inverse transport through the original hom after the source-unit mate
comparison equals inverse transport through the direct identity composite. -/
theorem indexedDiagnosticLeftUnitMateReselectionEquivalence_inverse
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      (((id D).comp hom).transportedInterpretation source)) :
    hom.inverseTransportedReselection source
        (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
          directReselection) =
      ((id D).comp hom).inverseTransportedReselection source
        directReselection := by
  let sourceReselection :=
    (indexedDiagnosticReselectionEquivalence ((id D).comp hom) source).symm
      directReselection
  have directRoundTrip :
      indexedDiagnosticReselectionEquivalence ((id D).comp hom) source
          sourceReselection = directReselection :=
    (indexedDiagnosticReselectionEquivalence
      ((id D).comp hom) source).apply_symm_apply directReselection
  have unitEquation :=
    indexedDiagnosticLeftUnitMateReselectionEquivalence_transport_apply
      hom source sourceReselection
  rw [← indexedDiagnosticReselectionEquivalence_apply,
    ← indexedDiagnosticReselectionEquivalence_apply] at unitEquation
  rw [directRoundTrip] at unitEquation
  change (indexedDiagnosticReselectionEquivalence hom source).symm
      (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
        directReselection) = sourceReselection
  rw [unitEquation]
  exact (indexedDiagnosticReselectionEquivalence hom source).symm_apply_apply
    sourceReselection

/-- Inverse transport through the original hom after the target-unit mate
comparison equals inverse transport through the direct identity composite. -/
theorem indexedDiagnosticRightUnitMateReselectionEquivalence_inverse
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      ((hom.comp (id E)).transportedInterpretation source)) :
    hom.inverseTransportedReselection source
        (indexedDiagnosticRightUnitMateReselectionEquivalence hom source
          directReselection) =
      (hom.comp (id E)).inverseTransportedReselection source
        directReselection := by
  let sourceReselection :=
    (indexedDiagnosticReselectionEquivalence (hom.comp (id E)) source).symm
      directReselection
  have directRoundTrip :
      indexedDiagnosticReselectionEquivalence (hom.comp (id E)) source
          sourceReselection = directReselection :=
    (indexedDiagnosticReselectionEquivalence
      (hom.comp (id E)) source).apply_symm_apply directReselection
  have unitEquation :=
    indexedDiagnosticRightUnitMateReselectionEquivalence_transport_apply
      hom source sourceReselection
  rw [← indexedDiagnosticReselectionEquivalence_apply,
    ← indexedDiagnosticReselectionEquivalence_apply] at unitEquation
  rw [directRoundTrip] at unitEquation
  change (indexedDiagnosticReselectionEquivalence hom source).symm
      (indexedDiagnosticRightUnitMateReselectionEquivalence hom source
        directReselection) = sourceReselection
  rw [unitEquation]
  exact (indexedDiagnosticReselectionEquivalence hom source).symm_apply_apply
    sourceReselection

/-- A source-unit-composite target reselection is coherent exactly when its
G-112-mate whole-unit image is coherent after transport by the original hom. -/
theorem indexedDiagnosticLeftUnitCoherentAt_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      (((id D).comp hom).transportedInterpretation source)) :
    (((id D).comp hom).transportedInterpretation source).IndexedCoherentAt
        directReselection ↔
      (hom.transportedInterpretation source).IndexedCoherentAt
        (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
          directReselection) := by
  calc
    _ ↔ source.IndexedCoherentAt
        (((id D).comp hom).inverseTransportedReselection source
          directReselection) :=
      indexedCoherentAt_inverseTransport_iff
        ((id D).comp hom) source directReselection
    _ ↔ source.IndexedCoherentAt
        (hom.inverseTransportedReselection source
          (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
            directReselection)) := by
      rw [indexedDiagnosticLeftUnitMateReselectionEquivalence_inverse]
    _ ↔ _ :=
      (indexedCoherentAt_inverseTransport_iff hom source _).symm

/-- A target-unit-composite target reselection is coherent exactly when its
G-112-mate whole-unit image is coherent after transport by the original hom. -/
theorem indexedDiagnosticRightUnitCoherentAt_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      ((hom.comp (id E)).transportedInterpretation source)) :
    ((hom.comp (id E)).transportedInterpretation source).IndexedCoherentAt
        directReselection ↔
      (hom.transportedInterpretation source).IndexedCoherentAt
        (indexedDiagnosticRightUnitMateReselectionEquivalence hom source
          directReselection) := by
  calc
    _ ↔ source.IndexedCoherentAt
        ((hom.comp (id E)).inverseTransportedReselection source
          directReselection) :=
      indexedCoherentAt_inverseTransport_iff
        (hom.comp (id E)) source directReselection
    _ ↔ source.IndexedCoherentAt
        (hom.inverseTransportedReselection source
          (indexedDiagnosticRightUnitMateReselectionEquivalence hom source
            directReselection)) := by
      rw [indexedDiagnosticRightUnitMateReselectionEquivalence_inverse]
    _ ↔ _ :=
      (indexedCoherentAt_inverseTransport_iff hom source _).symm

/-- Obstruction vanishing after direct source-unit-composite transport is
equivalent to obstruction vanishing after transport by the original hom. -/
theorem indexedDiagnosticLeftUnitTransportObstructionVanishes_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    TransportObstructionVanishes
        (((id D).comp hom).transportedInterpretation source).toAdmissibleTransportData ↔
      TransportObstructionVanishes
        (hom.transportedInterpretation source).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨directReselection, directCoherent⟩
    have directIndexed :
        (((id D).comp hom).transportedInterpretation source).IndexedCoherentAt
          directReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (((id D).comp hom).transportedInterpretation source)
        directReselection).2 directCoherent
    have homIndexed :=
      (indexedDiagnosticLeftUnitCoherentAt_mate_iff
        hom source directReselection).1 directIndexed
    exact
      ⟨indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
          directReselection,
        (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
          (hom.transportedInterpretation source)
          (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
            directReselection)).1 homIndexed⟩
  · rintro ⟨homReselection, homCoherent⟩
    have homIndexed :
        (hom.transportedInterpretation source).IndexedCoherentAt
          homReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (hom.transportedInterpretation source) homReselection).2 homCoherent
    let directReselection :=
      (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source).symm
        homReselection
    have directIndexed :
        (((id D).comp hom).transportedInterpretation source).IndexedCoherentAt
          directReselection := by
      apply (indexedDiagnosticLeftUnitCoherentAt_mate_iff
        hom source directReselection).2
      simpa only [directReselection,
        (indexedDiagnosticLeftUnitMateReselectionEquivalence
          hom source).apply_symm_apply] using homIndexed
    exact ⟨directReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (((id D).comp hom).transportedInterpretation source)
        directReselection).1 directIndexed⟩

/-- Obstruction vanishing after direct target-unit-composite transport is
equivalent to obstruction vanishing after transport by the original hom. -/
theorem indexedDiagnosticRightUnitTransportObstructionVanishes_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    TransportObstructionVanishes
        ((hom.comp (id E)).transportedInterpretation source).toAdmissibleTransportData ↔
      TransportObstructionVanishes
        (hom.transportedInterpretation source).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨directReselection, directCoherent⟩
    have directIndexed :
        ((hom.comp (id E)).transportedInterpretation source).IndexedCoherentAt
          directReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((hom.comp (id E)).transportedInterpretation source)
        directReselection).2 directCoherent
    have homIndexed :=
      (indexedDiagnosticRightUnitCoherentAt_mate_iff
        hom source directReselection).1 directIndexed
    exact
      ⟨indexedDiagnosticRightUnitMateReselectionEquivalence hom source
          directReselection,
        (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
          (hom.transportedInterpretation source)
          (indexedDiagnosticRightUnitMateReselectionEquivalence hom source
            directReselection)).1 homIndexed⟩
  · rintro ⟨homReselection, homCoherent⟩
    have homIndexed :
        (hom.transportedInterpretation source).IndexedCoherentAt
          homReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (hom.transportedInterpretation source) homReselection).2 homCoherent
    let directReselection :=
      (indexedDiagnosticRightUnitMateReselectionEquivalence hom source).symm
        homReselection
    have directIndexed :
        ((hom.comp (id E)).transportedInterpretation source).IndexedCoherentAt
          directReselection := by
      apply (indexedDiagnosticRightUnitCoherentAt_mate_iff
        hom source directReselection).2
      simpa only [directReselection,
        (indexedDiagnosticRightUnitMateReselectionEquivalence
          hom source).apply_symm_apply] using homIndexed
    exact ⟨directReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((hom.comp (id E)).transportedInterpretation source)
        directReselection).1 directIndexed⟩

/-- Obstruction vanishing is compatible with both whole-unit triangles.  The
forward witness uses the source-unit mate route; the reverse witness uses the
inverse target-unit mate route, so neither direction is restricted to a
preselected image. -/
theorem indexedDiagnosticUnitTransportObstructionVanishes_mate_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    TransportObstructionVanishes
        (((id D).comp hom).transportedInterpretation source).toAdmissibleTransportData ↔
      TransportObstructionVanishes
        ((hom.comp (id E)).transportedInterpretation source).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨leftReselection, leftCoherent⟩
    have leftIndexed :
        (((id D).comp hom).transportedInterpretation source).IndexedCoherentAt
          leftReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (((id D).comp hom).transportedInterpretation source)
        leftReselection).2 leftCoherent
    have homIndexed :=
      (indexedDiagnosticLeftUnitCoherentAt_mate_iff
        hom source leftReselection).1 leftIndexed
    let rightReselection :=
      (indexedDiagnosticRightUnitMateReselectionEquivalence hom source).symm
        (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source
          leftReselection)
    have rightIndexed :
        ((hom.comp (id E)).transportedInterpretation source).IndexedCoherentAt
          rightReselection := by
      apply (indexedDiagnosticRightUnitCoherentAt_mate_iff
        hom source rightReselection).2
      simpa only [rightReselection,
        (indexedDiagnosticRightUnitMateReselectionEquivalence
          hom source).apply_symm_apply] using homIndexed
    exact ⟨rightReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((hom.comp (id E)).transportedInterpretation source)
        rightReselection).1 rightIndexed⟩
  · rintro ⟨rightReselection, rightCoherent⟩
    have rightIndexed :
        ((hom.comp (id E)).transportedInterpretation source).IndexedCoherentAt
          rightReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((hom.comp (id E)).transportedInterpretation source)
        rightReselection).2 rightCoherent
    have homIndexed :=
      (indexedDiagnosticRightUnitCoherentAt_mate_iff
        hom source rightReselection).1 rightIndexed
    let leftReselection :=
      (indexedDiagnosticLeftUnitMateReselectionEquivalence hom source).symm
        (indexedDiagnosticRightUnitMateReselectionEquivalence hom source
          rightReselection)
    have leftIndexed :
        (((id D).comp hom).transportedInterpretation source).IndexedCoherentAt
          leftReselection := by
      apply (indexedDiagnosticLeftUnitCoherentAt_mate_iff
        hom source leftReselection).2
      simpa only [leftReselection,
        (indexedDiagnosticLeftUnitMateReselectionEquivalence
          hom source).apply_symm_apply] using homIndexed
    exact ⟨leftReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (((id D).comp hom).transportedInterpretation source)
        leftReselection).1 leftIndexed⟩

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
