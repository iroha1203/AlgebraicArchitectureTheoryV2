import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticQualifiedBaseChange
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticSourceFiberBridgeWitnesses

/-!
# Finite firing witness for qualified `(d1)`--`(d3)` diagnostic base change

The reviewed finite double-diamond interpretation supplies a concrete
source-fiber-qualified input.  Its two authored source comparators remain
distinct while the universal package generates both actual BC routes.
-/

namespace AAT.AG.DoctrineFiberProduct

open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteQualifiedBaseChangeAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- A concrete nondegenerate inhabitant of the universal qualified
`(d1)`--`(d3)` package. -/
noncomputable def finiteAxisFoldQualifiedDiagnosticBaseChangeD1D3 :
    QualifiedDiagnosticBaseChangeD1D3 finiteAxisFoldBCPresentation
      finiteAxisFoldPresentationInterpretation
      finiteAxisFoldSourceFiberIncidence :=
  qualifiedDiagnosticBaseChangeD1D3 finiteAxisFoldBCPresentation
    finiteAxisFoldPresentationInterpretation
    finiteAxisFoldSourceFiberIncidence

/-- The package does not obtain its firing witness by collapsing the authored
source diagnostic: the two reviewed source comparators remain distinct. -/
theorem finiteAxisFoldQualifiedDiagnosticBaseChangeD1D3_comparators_ne :
    finiteAxisFoldSourceFiberIncidence.toFiberwise.toTransportData.comparator
        DoubleDiamondTwoCell.first ≠
      finiteAxisFoldSourceFiberIncidence.toFiberwise.toTransportData.comparator
        DoubleDiamondTwoCell.second :=
  finiteAxisFoldSourceFiberBridge_comparators_ne

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
