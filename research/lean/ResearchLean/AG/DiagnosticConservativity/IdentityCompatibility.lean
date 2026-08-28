import ResearchLean.AG.DiagnosticConservativity.TransportCoherence
import ResearchLean.AG.DiagnosticConservativity.OrbitExactness
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticBaseChangeAutomorphism

/-!
# G-113 revision 2 downstream identity compatibility

The canonical G-111 unitor identifies transport along an indexed identity
with the original fiber object.  This module applies that same unitor to the
endpoint, reselection, and raw-defect cochain equivalences constructed in
G-113.  Each unitor comparison is proved to be the inverse of the corresponding
forward identity transport, and the orbit-membership iff is then expressed
through that generated comparison.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

private theorem coreFiberFunctorPackageAutHom_id
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : CoreFiber X) (automorphism : PackageFiberAut P.1) :
    coreFiberFunctorPackageAutHom (𝟭 (CoreFiber X)) P automorphism =
      automorphism := by
  change (packageFiberAutCoreFiberEquiv P).symm
      ((Functor.id (CoreFiber X)).mapAut P
        (packageFiberAutCoreFiberEquiv P automorphism)) = automorphism
  apply (packageFiberAutCoreFiberEquiv P).injective
  rw [MulEquiv.apply_symm_apply]
  apply Iso.ext
  rfl

/-! ## Endpoint automorphisms -/

/-- The canonical unitor carries an endpoint automorphism transported along
the indexed identity back to the original endpoint group. -/
noncomputable def indexedDiagnosticIdentityEndpointUnitorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (vertex : G.Vertex) :
    PackageFiberAut
        (((id D).transportedInterpretation source).package vertex) ≃*
      PackageFiberAut (source.package vertex) :=
  packageFiberAutMulEquivOfCoreFiberIso
    ((coreFiberUnitor (D.vertex vertex)).app (source.fiberPackage vertex))

/-- Endpoint identity transport followed by the canonical unitor comparison
is literally the original endpoint automorphism. -/
theorem indexedDiagnosticIdentityEndpointUnitorEquivalence_apply_transport
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    indexedDiagnosticIdentityEndpointUnitorEquivalence D source vertex
        (indexedDiagnosticEndpointEquivalence (id D) source vertex
          automorphism) =
      automorphism := by
  rw [indexedDiagnosticEndpointEquivalence_apply]
  change packageFiberAutMulEquivOfCoreFiberIso
      ((coreFiberUnitor (D.vertex vertex)).app (source.fiberPackage vertex))
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor (𝟙 (D.vertex vertex)))
        (source.fiberPackage vertex) automorphism) = automorphism
  rw [coreFiberFunctorPackageAutHom_iso_naturality]
  exact coreFiberFunctorPackageAutHom_id _ _

/-- The endpoint unitor comparison is exactly the inverse of the generated
identity-transport equivalence. -/
theorem indexedDiagnosticIdentityEndpointUnitorEquivalence_eq_symm
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (vertex : G.Vertex) :
    indexedDiagnosticIdentityEndpointUnitorEquivalence D source vertex =
      (indexedDiagnosticEndpointEquivalence (id D) source vertex).symm := by
  apply MulEquiv.ext
  intro targetAutomorphism
  simpa only [
    (indexedDiagnosticEndpointEquivalence (id D) source vertex).apply_symm_apply]
    using
      (indexedDiagnosticIdentityEndpointUnitorEquivalence_apply_transport
        D source vertex
        ((indexedDiagnosticEndpointEquivalence (id D) source vertex).symm
          targetAutomorphism))

/-! ## Edge reselections -/

/-- Apply the identity unitor comparison independently at every reselection
coordinate. -/
noncomputable def indexedDiagnosticIdentityReselectionUnitorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D) :
    IndexedEdgeReselection ((id D).transportedInterpretation source) ≃*
      IndexedEdgeReselection source :=
  MulEquiv.piCongrRight fun _i =>
    MulEquiv.piCongrRight fun j =>
      MulEquiv.piCongrRight fun _edge =>
        indexedDiagnosticIdentityEndpointUnitorEquivalence D source j

/-- The reselection unitor comparison is the inverse of the generated
identity-transport reselection equivalence. -/
theorem indexedDiagnosticIdentityReselectionUnitorEquivalence_eq_symm
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticIdentityReselectionUnitorEquivalence D source =
      (indexedDiagnosticReselectionEquivalence (id D) source).symm := by
  apply MulEquiv.ext
  intro targetReselection
  funext i j edge
  change indexedDiagnosticIdentityEndpointUnitorEquivalence D source j
      (targetReselection i j edge) =
    (indexedDiagnosticEndpointEquivalence (id D) source j).symm
      (targetReselection i j edge)
  rw [indexedDiagnosticIdentityEndpointUnitorEquivalence_eq_symm]

/-- Identity transport followed by the reselection unitor comparison recovers
every source reselection. -/
theorem indexedDiagnosticIdentityReselectionUnitorEquivalence_apply_transport
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    indexedDiagnosticIdentityReselectionUnitorEquivalence D source
        ((id D).transportedReselection source reselection) =
      reselection := by
  rw [indexedDiagnosticIdentityReselectionUnitorEquivalence_eq_symm,
    ← indexedDiagnosticReselectionEquivalence_apply]
  exact (indexedDiagnosticReselectionEquivalence (id D) source).symm_apply_apply
    reselection

/-! ## Raw-defect cochains and orbit membership -/

/-- Apply the endpoint unitor comparison at every two-cell coordinate. -/
noncomputable def indexedDiagnosticIdentityDefectCochainUnitorEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D) :
    DefectCochain
        ((id D).transportedInterpretation source).toAdmissibleTransportData ≃*
      DefectCochain source.toAdmissibleTransportData :=
  MulEquiv.piCongrRight fun cell =>
    indexedDiagnosticIdentityEndpointUnitorEquivalence D source
      (G.twoTarget cell)

/-- The cochain unitor comparison is the inverse of the generated identity
transport equivalence on all defect cochains. -/
theorem indexedDiagnosticIdentityDefectCochainUnitorEquivalence_eq_symm
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D) :
    indexedDiagnosticIdentityDefectCochainUnitorEquivalence D source =
      (indexedDiagnosticDefectCochainEquivalence (id D) source).symm := by
  apply MulEquiv.ext
  intro targetCochain
  funext cell
  change indexedDiagnosticIdentityEndpointUnitorEquivalence D source
      (G.twoTarget cell) (targetCochain cell) =
    (indexedDiagnosticEndpointEquivalence (id D) source
      (G.twoTarget cell)).symm (targetCochain cell)
  rw [indexedDiagnosticIdentityEndpointUnitorEquivalence_eq_symm]

/-- Identity transport followed by the cochain unitor comparison recovers
every source cochain. -/
theorem indexedDiagnosticIdentityDefectCochainUnitorEquivalence_apply_transport
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (cochain : DefectCochain source.toAdmissibleTransportData) :
    indexedDiagnosticIdentityDefectCochainUnitorEquivalence D source
        (indexedDiagnosticDefectCochainEquivalence (id D) source cochain) =
      cochain := by
  rw [indexedDiagnosticIdentityDefectCochainUnitorEquivalence_eq_symm]
  exact (indexedDiagnosticDefectCochainEquivalence (id D) source).symm_apply_apply
    cochain

/-- Orbit membership is invariant under the generated identity-unitor cochain
comparison for every target cochain. -/
theorem indexedDiagnosticIdentityInReselectionOrbit_unitor_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (targetCochain : DefectCochain
      ((id D).transportedInterpretation source).toAdmissibleTransportData) :
    InReselectionOrbit
        ((id D).transportedInterpretation source).toAdmissibleTransportData
        targetCochain ↔
      InReselectionOrbit source.toAdmissibleTransportData
        (indexedDiagnosticIdentityDefectCochainUnitorEquivalence D source
          targetCochain) := by
  rw [indexedDiagnosticIdentityDefectCochainUnitorEquivalence_eq_symm]
  exact indexedDiagnosticInReselectionOrbit_symm_iff
    (id D) source targetCochain

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
