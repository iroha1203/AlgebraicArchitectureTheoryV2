import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticTotalTransport
import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Nonidentity-edge witness for total diagnostic transport

The finite transport triangle contains genuine nonidentity package transports.
Applying the identity structural action constructs target G-106 data from that
arbitrary source datum, preserves each nonidentity edge, and regenerates every
authored comparator without supplying a target field.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- The full finite transport triangle mapped through the inhabited total
action contract. -/
noncomputable def finiteTransportTriangleIdentityTransportedData :
    AdmissibleTransportData
      (transportTrianglePresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier :=
  (DiagnosticPackageTotalAction.identity FiniteModel.carrier).transportedData
    finiteTransportTriangleData

/-- The generated target package at every triangle vertex is the source
package selected at that vertex. -/
theorem finiteTransportTriangleIdentityTransported_package
    (vertex : (transportTrianglePresentation
      FiniteModel.carrier.Atom).Vertex) :
    finiteTransportTriangleIdentityTransportedData.lift.package vertex =
      finiteTransportTriangleData.lift.package vertex := rfl

/-- Every generated target edge is exactly the corresponding nonidentity
source transport. -/
theorem finiteTransportTriangleIdentityTransported_edgeLift
    {i j : (transportTrianglePresentation
      FiniteModel.carrier.Atom).Vertex}
    (edge : (transportTrianglePresentation
      FiniteModel.carrier.Atom).Edge i j) :
    finiteTransportTriangleIdentityTransportedData.lift.edgeLift edge =
      finiteTransportTriangleData.lift.edgeLift edge := rfl

/-- The generated target edge still carries the concrete nonidentity Atom
transport. -/
theorem finiteTransportTriangleIdentityTransported_edge_atomEquiv_ne_refl
    {i j : SingleDiskVertex FiniteModel.carrier.Atom}
    (edge : @TransportTriangleEdge FiniteModel.carrier.Atom i j) :
    (finiteTransportTriangleIdentityTransportedData.lift.edgeLift edge).upper.atomEquiv ≠
      Equiv.refl FiniteModel.carrier.Atom := by
  rw [finiteTransportTriangleIdentityTransported_edgeLift]
  exact finiteTransportTriangle_edge_atomEquiv_ne_refl edge

/-- Every target comparator is regenerated as the identity action's image of
the source authored comparator. -/
theorem finiteTransportTriangleIdentityTransported_comparator
    (cell : (transportTrianglePresentation
      FiniteModel.carrier.Atom).TwoCell) :
    finiteTransportTriangleIdentityTransportedData.comparator cell =
      finiteTransportTriangleData.comparator cell := by
  apply Subtype.ext
  apply Iso.ext
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
