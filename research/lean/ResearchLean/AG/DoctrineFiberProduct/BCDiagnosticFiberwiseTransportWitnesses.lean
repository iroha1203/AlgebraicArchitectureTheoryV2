import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticFiberwiseTransport
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses

/-!
# Finite fiberwise transport witness

The double-diamond axis-fold fixture is packaged directly in the core fiber of
the finite southwest point.  Its edges are identity isomorphisms and its two
authored comparator values remain the identity and the concrete adjacent swap.
This gives a nonempty input for the generated d1/d3 engine without supplying
any post-transport field.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteAxisFoldFiberwiseAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The finite axis-fold support as an object of the selected southwest core
fiber. -/
noncomputable def finiteAxisFoldFiberPackage :
    CoreFiber finiteAuthoredSupportInstance.toSemantic :=
  ⟨finiteAxisFoldSupportPackage, finiteAxisFoldSupportPackage_point⟩

/-- Fiberwise form of the finite double-diamond source datum. -/
noncomputable def finiteAxisFoldFiberwiseTransportData :
    FiberwiseAdmissibleTransportData (doubleDiamondPresentation PUnit)
      FiniteModel.carrier finiteAuthoredSupportInstance.toSemantic where
  package := fun _ => finiteAxisFoldFiberPackage
  edgeIso := fun _ => Iso.refl finiteAxisFoldFiberPackage
  comparator
    | .first => 1
    | .second => finiteAxisFoldSwap

/-- Forgetting the fiberwise representation recovers the existing source
package at every vertex. -/
theorem finiteAxisFoldFiberwise_package
    (vertex : (doubleDiamondPresentation PUnit).Vertex) :
    finiteAxisFoldFiberwiseTransportData.toTransportData.lift.package vertex =
      finiteAxisFoldSupportPackage := rfl

/-- The generated source edge lift is the package identity. -/
theorem finiteAxisFoldFiberwise_edgeLift
    {i j : (doubleDiamondPresentation PUnit).Vertex}
    (edge : (doubleDiamondPresentation PUnit).Edge i j) :
    finiteAxisFoldFiberwiseTransportData.toTransportData.lift.edgeLift edge =
      PackageTotalHom.id finiteAxisFoldSupportPackage := rfl

/-- The first generated source comparator is identity. -/
theorem finiteAxisFoldFiberwise_comparator_first :
    finiteAxisFoldFiberwiseTransportData.toTransportData.comparator
        DoubleDiamondTwoCell.first = 1 := rfl

/-- The second generated source comparator is the concrete adjacent swap. -/
theorem finiteAxisFoldFiberwise_comparator_second :
    finiteAxisFoldFiberwiseTransportData.toTransportData.comparator
        DoubleDiamondTwoCell.second = finiteAxisFoldSwap := rfl

/-- The two source comparator values remain genuinely distinct in the
fiberwise representation. -/
theorem finiteAxisFoldFiberwise_comparators_ne :
    finiteAxisFoldFiberwiseTransportData.toTransportData.comparator
        DoubleDiamondTwoCell.first ≠
      finiteAxisFoldFiberwiseTransportData.toTransportData.comparator
        DoubleDiamondTwoCell.second := by
  simpa only [finiteAxisFoldFiberwise_comparator_first,
    finiteAxisFoldFiberwise_comparator_second] using
      finiteAxisFold_comparators_ne

/-- The finite source datum transported along the actual direct BC route. -/
noncomputable def finiteAxisFoldDirectTransportedData :
    AdmissibleTransportData (doubleDiamondPresentation PUnit)
      FiniteModel.carrier :=
  bcDiagnosticDirectTransportedData finiteAxisFoldBCPresentation
    finiteAxisFoldFiberwiseTransportData

/-- The same finite source datum transported along the actual via-base route. -/
noncomputable def finiteAxisFoldViaBaseTransportedData :
    AdmissibleTransportData (doubleDiamondPresentation PUnit)
      FiniteModel.carrier :=
  bcDiagnosticViaBaseTransportedData finiteAxisFoldBCPresentation
    finiteAxisFoldFiberwiseTransportData

/-- On the finite fixture, the canonical mate-generated endpoint comparison
identifies the direct and via-base generated comparator tables pointwise. -/
theorem finiteAxisFoldTransportedComparator_naturality
    (cell : (doubleDiamondPresentation PUnit).TwoCell) :
    bcDiagnosticEndpointComparison finiteAxisFoldBCPresentation
        (finiteAxisFoldFiberwiseTransportData.package
          ((doubleDiamondPresentation PUnit).twoTarget cell))
        (finiteAxisFoldDirectTransportedData.comparator cell) =
      finiteAxisFoldViaBaseTransportedData.comparator cell := by
  exact bcDiagnosticTransportedComparator_naturality
    finiteAxisFoldBCPresentation finiteAxisFoldFiberwiseTransportData cell

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
