import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticCovariance

/-!
# Indexed diagnostic reselection covariance

This module proves G-111 `(d4)`.  An authored source edge reselection is sent
pointwise through the same endpoint group homomorphisms used by `(d2)` and the
target comparator.  The target reselection is generated, not accepted as a
field.  Edge/path coherence and vanishing preservation remain the next layer.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Edgewise package-fiber reselection for one indexed diagnostic interpretation. -/
abbrev IndexedEdgeReselection {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D : IndexedBaseDiagram G U}
    (source : IndexedDiagnosticInterpretation D) :=
  (i j : G.Vertex) → (edge : G.Edge i j) →
    PackageFiberAut (source.package j)

namespace IndexedBaseDiagramHom

/-- `(d4)`: map a source edge reselection through the generated endpoint actions. -/
noncomputable def transportedReselection
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    IndexedEdgeReselection (hom.transportedInterpretation source) :=
  fun i j edge => hom.endpointAction source j (reselection i j edge)

/-- `(d4)` sends the identity source reselection to the identity target reselection. -/
@[simp]
theorem transportedReselection_one
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    hom.transportedReselection source (1 : IndexedEdgeReselection source) = 1 := by
  funext i j edge
  exact hom.endpointAction_one source j

/-- `(d4)` preserves pointwise multiplication of source reselections. -/
@[simp]
theorem transportedReselection_mul
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (first second : IndexedEdgeReselection source) :
    hom.transportedReselection source (first * second) =
      hom.transportedReselection source first *
        hom.transportedReselection source second := by
  funext i j edge
  exact hom.endpointAction_mul source j (first i j edge) (second i j edge)

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
