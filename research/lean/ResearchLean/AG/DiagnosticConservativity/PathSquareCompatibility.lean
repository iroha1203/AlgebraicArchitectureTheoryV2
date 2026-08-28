import ResearchLean.AG.DiagnosticConservativity.ObstructionExactness
import ResearchLean.AG.DiagnosticConservativity.OrbitExactness

/-!
# G-113 revision 2 path-square and horizontal-pasting compatibility

The horizontal operation in the G-111 indexed API is horizontal pasting of
base squares along consecutive paths; it is not a second composition law on
indexed diagram homs.  This module therefore keeps one arbitrary diagram hom
fixed and proves that its vertexwise G-113 transport squares commute for every
reselected path.  The same theorem is proved in the inverse direction for an
arbitrary target reselection.

Path concatenation identifies the direct square on an appended path with the
actual horizontal paste of the two component squares.  The total-lift
commuting equations below follow that decomposition, while the final route
theorem retains the G-111 square-level provenance.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

/-- Package-total composition in the ambient category is associative. -/
private theorem packageTotalHom_comp_assoc
    {U : AtomCarrier.{u}} {P Q R S : AATCorePackage U}
    (first : PackageTotalHom P Q) (second : PackageTotalHom Q R)
    (third : PackageTotalHom R S) :
    first.comp (second.comp third) = (first.comp second).comp third := by
  let packageCategory : Category (AATCorePackage U) := inferInstance
  exact (@Category.assoc (AATCorePackage U) packageCategory
    P Q R S first second third).symm

namespace IndexedDiagnosticInterpretation

/-- Reselected indexed path evaluation sends concatenation to composition. -/
theorem reselectedPathLift_append
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    source.reselectedPathLift reselection (first.append second) =
      (source.reselectedPathLift reselection first).comp
        (source.reselectedPathLift reselection second) := by
  induction first with
  | nil vertex =>
      change source.reselectedPathLift reselection second =
        (PackageTotalHom.id (source.package vertex)).comp
          (source.reselectedPathLift reselection second)
      exact
        (@Category.id_comp
          (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
          (source.package vertex) (source.package k)
          (source.reselectedPathLift reselection second)).symm
  | cons edge tail inductionHypothesis =>
      simp only [IndexedBasePath.append, reselectedPathLift]
      rw [inductionHypothesis]
      exact
        (@Category.assoc
          (AATCorePackage U) (PackageTotalHom.packageTotalCategory U)
          _ _ _ _ (source.reselectedEdgeLift reselection edge)
          (source.reselectedPathLift reselection tail)
          (source.reselectedPathLift reselection second)).symm

end IndexedDiagnosticInterpretation

namespace IndexedBaseDiagramHom

/--
The G-113 total-lift square over the G-111 path square commutes for every
source reselection.  The endpoint action is the one assembled by the explicit
G-113 reselection equivalence.
-/
theorem indexedDiagnosticPathSquare_commutes
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection) path) =
      (source.reselectedPathLift reselection path).comp
        (hom.diagnosticVertexLift source j) := by
  rw [indexedDiagnosticReselectionEquivalence_apply]
  exact hom.diagnosticVertexLift_reselectedPath_naturality source reselection path

/-- The inverse G-113 reselection equivalence gives the converse path square
for an arbitrary target reselection. -/
theorem indexedDiagnosticPathSquare_inverse_commutes
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection path) =
      (source.reselectedPathLift
        (hom.inverseTransportedReselection source targetReselection) path).comp
          (hom.diagnosticVertexLift source j) := by
  have naturality := hom.diagnosticVertexLift_reselectedPath_naturality source
    (hom.inverseTransportedReselection source targetReselection) path
  rw [hom.transportedReselection_inverseTransportedReselection source
    targetReselection] at naturality
  exact naturality

/-- The base equation underneath the total-lift theorem is precisely the
commuting equation stored by the G-111 path square. -/
theorem indexedDiagnosticPathSquare_base_commutes
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (hom.pathSquare path).left ≫ (hom.pathSquare path).bottom =
      (hom.pathSquare path).top ≫ (hom.pathSquare path).right :=
  (hom.pathSquare path).commutes

/-- Horizontal pasting of two total-lift path squares commutes by the two
component path-square equations, without introducing a horizontal hom law. -/
theorem indexedDiagnosticHorizontalPathPasting_commutes
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    ((hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection)
          first)).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection)
          second) =
      (source.reselectedPathLift reselection first).comp
        ((source.reselectedPathLift reselection second).comp
          (hom.diagnosticVertexLift source k)) := by
  rw [hom.indexedDiagnosticPathSquare_commutes source reselection first]
  rw [← packageTotalHom_comp_assoc]
  rw [hom.indexedDiagnosticPathSquare_commutes source reselection second]

/-- Horizontal pasting also commutes in the inverse direction for every
authored target reselection. -/
theorem indexedDiagnosticHorizontalPathPasting_inverse_commutes
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    ((hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection first)).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection second) =
      (source.reselectedPathLift
        (hom.inverseTransportedReselection source targetReselection) first).comp
        ((source.reselectedPathLift
          (hom.inverseTransportedReselection source targetReselection)
          second).comp (hom.diagnosticVertexLift source k)) := by
  rw [hom.indexedDiagnosticPathSquare_inverse_commutes source
    targetReselection first]
  rw [← packageTotalHom_comp_assoc]
  rw [hom.indexedDiagnosticPathSquare_inverse_commutes source
    targetReselection second]

/-- The horizontally pasted target side is the target side of the direct
square on the appended path. -/
theorem indexedDiagnosticHorizontalPathPasting_target_eq_append
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    ((hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection)
          first)).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection)
          second) =
      (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection)
          (first.append second)) := by
  rw [(hom.transportedInterpretation source).reselectedPathLift_append]
  exact (packageTotalHom_comp_assoc _ _ _).symm

/-- The horizontally pasted source side is the source side of the direct
square on the appended path. -/
theorem indexedDiagnosticHorizontalPathPasting_source_eq_append
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    (source.reselectedPathLift reselection first).comp
        ((source.reselectedPathLift reselection second).comp
          (hom.diagnosticVertexLift source k)) =
      (source.reselectedPathLift reselection (first.append second)).comp
        (hom.diagnosticVertexLift source k) := by
  rw [source.reselectedPathLift_append]
  exact packageTotalHom_comp_assoc _ _ _

/-- The horizontally pasted target side for an arbitrary target reselection is
the target side of the direct square on the appended path. -/
theorem indexedDiagnosticHorizontalPathPasting_inverse_target_eq_append
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    ((hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection first)).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection second) =
      (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection (first.append second)) := by
  rw [(hom.transportedInterpretation source).reselectedPathLift_append]
  exact (packageTotalHom_comp_assoc _ _ _).symm

/-- The horizontally pasted inverse-source side is the source side of the
direct square on the appended path. -/
theorem indexedDiagnosticHorizontalPathPasting_inverse_source_eq_append
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    (source.reselectedPathLift
        (hom.inverseTransportedReselection source targetReselection) first).comp
        ((source.reselectedPathLift
          (hom.inverseTransportedReselection source targetReselection)
          second).comp (hom.diagnosticVertexLift source k)) =
      (source.reselectedPathLift
        (hom.inverseTransportedReselection source targetReselection)
        (first.append second)).comp (hom.diagnosticVertexLift source k) := by
  rw [source.reselectedPathLift_append]
  exact packageTotalHom_comp_assoc _ _ _

/-- The direct appended-path square is obtained from the two component
commuting squares through the forward horizontal-pasting route. -/
theorem indexedDiagnosticHorizontalPathPasting_eq_pathSquare
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (indexedDiagnosticReselectionEquivalence hom source reselection)
          (first.append second)) =
      (source.reselectedPathLift reselection (first.append second)).comp
        (hom.diagnosticVertexLift source k) := by
  rw [← hom.indexedDiagnosticHorizontalPathPasting_target_eq_append
    source reselection first second]
  rw [← hom.indexedDiagnosticHorizontalPathPasting_source_eq_append
    source reselection first second]
  exact hom.indexedDiagnosticHorizontalPathPasting_commutes source reselection
    first second

/-- The direct arbitrary-target appended-path square is obtained from the two
component inverse commuting squares through horizontal pasting. -/
theorem indexedDiagnosticHorizontalPathPasting_inverse_eq_pathSquare
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          targetReselection (first.append second)) =
      (source.reselectedPathLift
        (hom.inverseTransportedReselection source targetReselection)
        (first.append second)).comp (hom.diagnosticVertexLift source k) := by
  rw [← hom.indexedDiagnosticHorizontalPathPasting_inverse_target_eq_append
    source targetReselection first second]
  rw [← hom.indexedDiagnosticHorizontalPathPasting_inverse_source_eq_append
    source targetReselection first second]
  exact hom.indexedDiagnosticHorizontalPathPasting_inverse_commutes source
    targetReselection first second

/-- All four sides of the G-111 horizontal paste agree with the direct square
on the appended path.  Its route remains separately visible below. -/
theorem indexedDiagnosticHorizontalPathPasting_base_eq_pathSquare
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    (hom.horizontalPathSquare first second).top =
        (hom.pathSquare (first.append second)).top ∧
      (hom.horizontalPathSquare first second).bottom =
        (hom.pathSquare (first.append second)).bottom ∧
      (hom.horizontalPathSquare first second).left =
        (hom.pathSquare (first.append second)).left ∧
      (hom.horizontalPathSquare first second).right =
        (hom.pathSquare (first.append second)).right := by
  exact ⟨hom.horizontalPathSquare_top first second,
    hom.horizontalPathSquare_bottom first second,
    hom.horizontalPathSquare_left first second,
    hom.horizontalPathSquare_right first second⟩

/-- The horizontal compatibility theorem uses the authored G-111 horizontal
paste route rather than a fabricated horizontal composition of diagram homs. -/
theorem indexedDiagnosticHorizontalPathPasting_route
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    {i j k : G.Vertex}
    (first : IndexedBasePath G.toIndexedBaseShape i j)
    (second : IndexedBasePath G.toIndexedBaseShape j k) :
    (hom.horizontalPathSquare first second).route =
      .pasteHorizontal first.squareRoute second.squareRoute :=
  hom.horizontalPathSquare_route first second

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
