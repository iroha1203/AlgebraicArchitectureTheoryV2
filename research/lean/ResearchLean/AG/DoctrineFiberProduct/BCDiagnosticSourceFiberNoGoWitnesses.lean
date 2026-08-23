import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticSourceFiberBridgeWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses

/-!
# Realized-schema no-go witness for universal source-fiber incidence

The ordinary `BCDiagnosticInterpretation` schema admits strongly cocartesian
diagnostic edges with nonidentity base transport.  Such an interpretation is
valid pre-base-change G-106 data, but it is not an object of the fixed
southwest core-fiber route.  This file places the existing finite transport
triangle inside an actual validated BC presentation and records that exact
domain mismatch.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteTriangleBCAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- A fully enumerated finite-code presentation of the existing transport
triangle geometry. -/
noncomputable def finiteTransportTriangleDiagnosticPresentation :
    FiniteDiagnosticPresentation.{0} where
  geometry := transportTrianglePresentation FiniteModel.carrier.Atom
  vertexDecidableEq := Classical.decEq _
  edgeDecidableEq := fun _ _ => Classical.decEq _
  twoCellDecidableEq := Classical.decEq _
  threeCellDecidableEq := Classical.decEq _
  vertices := Finset.univ.toList
  vertices_nodup := Finset.nodup_toList _
  vertices_complete := by simp
  edges := fun _ _ => Finset.univ.toList
  edges_nodup := fun _ _ => Finset.nodup_toList _
  edges_complete := by simp
  twoCells := Finset.univ.toList
  twoCells_nodup := Finset.nodup_toList _
  twoCells_complete := by simp
  threeCells := Finset.univ.toList
  threeCells_nodup := Finset.nodup_toList _
  threeCells_complete := by simp

/-- The reviewed constant cospan and compatible-point table with the transport
triangle as its authored pre-base-change diagnostic geometry. -/
noncomputable def finiteTransportTriangleBCRawCode :
    BCRawCode FiniteModel.carrier where
  cospan := finiteConstantBCCospan
  compatiblePoints := finiteConstantCompatiblePointCode
  diagnostic := finiteTransportTriangleDiagnosticPresentation

/-- The diagnostic geometry does not alter the cospan/point-table validation. -/
theorem finiteTransportTriangleBCRawCode_wellFormed :
    finiteTransportTriangleBCRawCode.WellFormed :=
  finiteConstantCompatiblePointCode_wellFormed

/-- A validated realized BC presentation whose ordinary diagnostic datum has
nonidentity base transport. -/
noncomputable def finiteTransportTriangleBCPresentation :
    BCPresentation FiniteModel.carrier :=
  ⟨finiteTransportTriangleBCRawCode,
    finiteTransportTriangleBCRawCode_wellFormed⟩

/-- The existing finite transport triangle as an ordinary interpretation of
the validated BC presentation. -/
noncomputable def finiteTransportTriangleBCInterpretation :
    BCDiagnosticInterpretation FiniteModel.carrier
      (toSemanticBC finiteTransportTriangleBCPresentation) where
  data := by
    simpa [toSemanticBC, finiteTransportTriangleBCPresentation,
      finiteTransportTriangleBCRawCode,
      finiteTransportTriangleDiagnosticPresentation] using
        finiteTransportTriangleData

/-- This valid ordinary interpretation cannot enter the actual southwest
core-fiber route: every triangle edge has nonidentity Atom transport. -/
theorem finiteTransportTriangleBC_not_sourceFiberIncident :
    ¬ BCDiagnosticSourceFiberIncidence finiteTransportTriangleBCPresentation
      finiteTransportTriangleBCInterpretation := by
  simpa [BCDiagnosticSourceFiberIncidence,
    finiteTransportTriangleBCInterpretation, toSemanticBC,
    finiteTransportTriangleBCPresentation, finiteTransportTriangleBCRawCode,
    finiteTransportTriangleDiagnosticPresentation] using
      (finiteTransportTriangle_not_sourceFiberIncident
        (toSemanticBC finiteTransportTriangleBCPresentation).square.southwest)

/-- Consequently, the current ordinary interpretation schema has no universal
generator into the fixed actual source-fiber domain. -/
theorem no_universalBCDiagnosticSourceFiberIncidence :
    ¬ (∀ (presentation : BCPresentation FiniteModel.carrier)
        (interpretation : BCDiagnosticInterpretation FiniteModel.carrier
          (toSemanticBC presentation)),
      BCDiagnosticSourceFiberIncidence presentation interpretation) := by
  intro generator
  exact finiteTransportTriangleBC_not_sourceFiberIncident
    (generator finiteTransportTriangleBCPresentation
      finiteTransportTriangleBCInterpretation)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
