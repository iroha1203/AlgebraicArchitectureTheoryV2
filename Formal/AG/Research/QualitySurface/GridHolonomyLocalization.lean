import Formal.AG.Research.QualitySurface.FiniteSquareCriterion
import Formal.AG.Research.QualitySurface.ProfileGridHolonomy

/-!
Cycle 20 evidence for `G-aat-quality-surface-01`.

This file localizes endpoint holonomy in the selected finite profile grid.  The
result is deliberately relative to the supplied two-cell decomposition, selected
visible reading, selected protected invariant, and shared-boundary compatibility.
It does not assert global grid flatness, arbitrary path pasting, canonical
transport, source extraction completeness, ArchMap correctness, or whole-codebase
traceability.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace GridHolonomyLocalization

open TraceLocus

/-! ## Selected endpoint pair and readings -/

/-- Endpoint type at the selected high/fine grid vertex. -/
abbrev GridEndpoint :=
  ProfileGridHolonomy.CertificateAt ProfileGridHolonomy.highFine

/-- Endpoint pair used by the selected upper-right grid cell. -/
abbrev GridCellEndpointPair :=
  FiniteSquareCriterion.EndpointPair GridEndpoint

/-- The selected upper-right cell endpoints, reached in the two path orders. -/
def gridUpperRightCellPair : GridCellEndpointPair where
  lawFirst := ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt
  coverFirst := ProfileGridHolonomy.coverFirstPath ProfileGridHolonomy.seedAt

/-- Visible grid surface: scalar, verdict, and selected support. -/
def SameGridVisibleSurface (left right : GridEndpoint) : Prop :=
  ProfileGridHolonomy.scalarReading left.val = ProfileGridHolonomy.scalarReading right.val ∧
    ProfileGridHolonomy.verdict left.val = ProfileGridHolonomy.verdict right.val ∧
    ProfileGridHolonomy.support left.val = ProfileGridHolonomy.support right.val

/-- Protected invariant given by the path-ordered trace missing locus. -/
def SameGridTraceMissingInvariant (left right : GridEndpoint) : Prop :=
  ∀ atom,
    ProfileGridHolonomy.traceMissingLocus left.val atom ↔
      ProfileGridHolonomy.traceMissingLocus right.val atom

/-- Protected invariant given by the path-ordered repair frontier. -/
def SameGridRepairInvariant (left right : GridEndpoint) : Prop :=
  ∀ atom,
    ProfileGridHolonomy.repairFrontier left.val atom ↔
      ProfileGridHolonomy.repairFrontier right.val atom

/-- Grid reading that hides the trace missing locus behind the visible surface. -/
def gridTraceCellReading :
    FiniteSquareCriterion.SquareReading GridEndpoint where
  VisibleEquivalent := SameGridVisibleSurface
  SameProtectedInvariant := SameGridTraceMissingInvariant

/-- Grid reading that hides the repair frontier behind the visible surface. -/
def gridRepairCellReading :
    FiniteSquareCriterion.SquareReading GridEndpoint where
  VisibleEquivalent := SameGridVisibleSurface
  SameProtectedInvariant := SameGridRepairInvariant

/-! ## Selected two-cell decomposition boundary -/

/--
Shared-boundary compatibility for the supplied two-cell grid: the common prefix
and the branch vertices before the endpoint are trace-complete and carry no
database repair frontier.  The localized obstruction is therefore isolated at
the selected upper-right cell endpoint.
-/
def SharedBoundaryProtectedCompatible : Prop :=
  TraceTransport.TraceAvailableOn
      (ProfileGridHolonomy.support (ProfileGridHolonomy.commonLawStage ProfileGridHolonomy.seedAt).val)
      (ProfileGridHolonomy.gridTuple (ProfileGridHolonomy.commonLawStage ProfileGridHolonomy.seedAt).val).traceField ∧
    TraceTransport.TraceAvailableOn
      (ProfileGridHolonomy.support (ProfileGridHolonomy.commonCenter ProfileGridHolonomy.seedAt).val)
      (ProfileGridHolonomy.gridTuple (ProfileGridHolonomy.commonCenter ProfileGridHolonomy.seedAt).val).traceField ∧
    TraceTransport.TraceAvailableOn
      (ProfileGridHolonomy.support (ProfileGridHolonomy.lawFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val)
      (ProfileGridHolonomy.gridTuple (ProfileGridHolonomy.lawFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val).traceField ∧
    TraceTransport.TraceAvailableOn
      (ProfileGridHolonomy.support (ProfileGridHolonomy.coverFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val)
      (ProfileGridHolonomy.gridTuple (ProfileGridHolonomy.coverFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val).traceField ∧
    TraceTransport.TraceAvailableOn
      (ProfileGridHolonomy.support (ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt).val)
      (ProfileGridHolonomy.gridTuple (ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt).val).traceField ∧
    ¬ ProfileGridHolonomy.repairFrontier (ProfileGridHolonomy.commonLawStage ProfileGridHolonomy.seedAt).val LocusAtom.database ∧
    ¬ ProfileGridHolonomy.repairFrontier (ProfileGridHolonomy.commonCenter ProfileGridHolonomy.seedAt).val LocusAtom.database ∧
    ¬ ProfileGridHolonomy.repairFrontier (ProfileGridHolonomy.lawFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val LocusAtom.database ∧
    ¬ ProfileGridHolonomy.repairFrontier (ProfileGridHolonomy.coverFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val LocusAtom.database ∧
    ¬ ProfileGridHolonomy.repairFrontier (ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt).val LocusAtom.database

/--
The selected two-cell decomposition remembers the shared prefix, the two
intermediate branch vertices, the named endpoint pair, and the protected
boundary compatibility that isolates the endpoint holonomy to the upper-right
cell.
-/
structure SelectedTwoCellDecomposition where
  commonLawStage_is_shared :
    (ProfileGridHolonomy.commonLawStage ProfileGridHolonomy.seedAt).val =
      ProfileGridHolonomy.GridCertificateName.sharedLawStage
  commonCenter_is_shared :
    (ProfileGridHolonomy.commonCenter ProfileGridHolonomy.seedAt).val =
      ProfileGridHolonomy.GridCertificateName.sharedCenter
  lawFirstBeforeEndpoint_is_highMiddle :
    (ProfileGridHolonomy.lawFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val =
      ProfileGridHolonomy.GridCertificateName.lawFirstHighMiddle
  coverFirstBeforeEndpoint_is_midFine :
    (ProfileGridHolonomy.coverFirstBeforeEndpoint ProfileGridHolonomy.seedAt).val =
      ProfileGridHolonomy.GridCertificateName.coverFirstMidFine
  lawFirstEndpoint_selected :
    gridUpperRightCellPair.lawFirst = ProfileGridHolonomy.lawFirstPath ProfileGridHolonomy.seedAt
  coverFirstEndpoint_selected :
    gridUpperRightCellPair.coverFirst = ProfileGridHolonomy.coverFirstPath ProfileGridHolonomy.seedAt
  sharedBoundaryCompatible : SharedBoundaryProtectedCompatible

/-- The supplied grid witness carries the selected two-cell decomposition. -/
theorem selectedTwoCellDecomposition_witness :
    SelectedTwoCellDecomposition where
  commonLawStage_is_shared := ProfileGridHolonomy.lawFirst_uses_middle_grid_vertices.1
  commonCenter_is_shared := ProfileGridHolonomy.lawFirst_uses_middle_grid_vertices.2.1
  lawFirstBeforeEndpoint_is_highMiddle :=
    ProfileGridHolonomy.lawFirst_uses_middle_grid_vertices.2.2.1
  coverFirstBeforeEndpoint_is_midFine :=
    ProfileGridHolonomy.coverFirst_uses_middle_grid_vertices.2.2.1
  lawFirstEndpoint_selected := rfl
  coverFirstEndpoint_selected := rfl
  sharedBoundaryCompatible := ProfileGridHolonomy.surrounding_steps_preserve_trace_frontier

/-! ## Cellwise flatness and endpoint holonomy -/

/-- All selected cells are visibly flat for a chosen reading. -/
def AllSelectedCellsVisibleFlat
    (reading : FiniteSquareCriterion.SquareReading GridEndpoint) : Prop :=
  SharedBoundaryProtectedCompatible ∧
    FiniteSquareCriterion.VisibleFlat reading gridUpperRightCellPair

/-- All selected cells are protected-flat for a chosen protected invariant. -/
def AllSelectedCellsProtectedFlat
    (reading : FiniteSquareCriterion.SquareReading GridEndpoint) : Prop :=
  SharedBoundaryProtectedCompatible ∧
    FiniteSquareCriterion.ProtectedInvariantFlat reading gridUpperRightCellPair

/--
For the selected two-cell decomposition, cellwise protected flatness rules out
endpoint protected holonomy for the chosen reading.
-/
theorem endpointProtectedFlat_of_allSelectedCellsFlat
    (reading : FiniteSquareCriterion.SquareReading GridEndpoint)
    (hflat : AllSelectedCellsProtectedFlat reading) :
    FiniteSquareCriterion.ProtectedInvariantFlat reading gridUpperRightCellPair :=
  hflat.2

/-- Endpoint trace holonomy is failure of trace protected-flatness. -/
def EndpointTraceHolonomy : Prop :=
  ¬ FiniteSquareCriterion.ProtectedInvariantFlat gridTraceCellReading gridUpperRightCellPair

/-- Endpoint repair holonomy is failure of repair protected-flatness. -/
def EndpointRepairHolonomy : Prop :=
  ¬ FiniteSquareCriterion.ProtectedInvariantFlat gridRepairCellReading gridUpperRightCellPair

/-- The selected upper-right grid cell is visibly flat for trace reading. -/
theorem gridUpperRightCell_visibleFlat :
    FiniteSquareCriterion.VisibleFlat gridTraceCellReading gridUpperRightCellPair :=
  ProfileGridHolonomy.gridHolonomy_visibleAgreement

/-- The selected upper-right grid cell is visibly flat for repair reading. -/
theorem gridUpperRightCell_repair_visibleFlat :
    FiniteSquareCriterion.VisibleFlat gridRepairCellReading gridUpperRightCellPair :=
  ProfileGridHolonomy.gridHolonomy_visibleAgreement

/-- All selected cells are visibly flat for trace reading. -/
theorem allSelectedCells_trace_visibleFlat :
    AllSelectedCellsVisibleFlat gridTraceCellReading :=
  ⟨ProfileGridHolonomy.surrounding_steps_preserve_trace_frontier,
    gridUpperRightCell_visibleFlat⟩

/-- All selected cells are visibly flat for repair reading. -/
theorem allSelectedCells_repair_visibleFlat :
    AllSelectedCellsVisibleFlat gridRepairCellReading :=
  ⟨ProfileGridHolonomy.surrounding_steps_preserve_trace_frontier,
    gridUpperRightCell_repair_visibleFlat⟩

/-! ## Concrete endpoint discrepancies -/

/-- The selected grid endpoints differ in trace missing locus. -/
theorem gridUpperRightCell_traceDiscrepancy :
    ¬ FiniteSquareCriterion.ProtectedInvariantFlat
      gridTraceCellReading gridUpperRightCellPair := by
  intro hsame
  have hmissingLaw :
      ProfileGridHolonomy.traceMissingLocus
        gridUpperRightCellPair.lawFirst.val
        LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      TraceLocus.partialTrace_database_missing_locus
  exact TraceLocus.fullTrace_has_no_missing_locus
    ⟨LocusAtom.database, hmissingLaw⟩

/-- The selected grid endpoints differ in repair frontier. -/
theorem gridUpperRightCell_repairDiscrepancy :
    ¬ FiniteSquareCriterion.ProtectedInvariantFlat
      gridRepairCellReading gridUpperRightCellPair := by
  intro hsame
  have hrepairLaw :
      ProfileGridHolonomy.repairFrontier
        gridUpperRightCellPair.lawFirst.val
        LocusAtom.database :=
    (hsame LocusAtom.database).mpr
      ProfileGridHolonomy.coverFirst_forces_database_repair_at_endpoint
  exact ProfileGridHolonomy.lawFirst_no_database_repair_at_endpoint hrepairLaw

/-- The concrete endpoint trace holonomy of the selected grid. -/
theorem gridUpperRightCell_endpointTraceHolonomy :
    EndpointTraceHolonomy :=
  gridUpperRightCell_traceDiscrepancy

/-- The concrete endpoint repair holonomy of the selected grid. -/
theorem gridUpperRightCell_endpointRepairHolonomy :
    EndpointRepairHolonomy :=
  gridUpperRightCell_repairDiscrepancy

/-! ## Holonomy localization to a selected curved cell -/

/--
If the selected decomposition has visible-flat cells and endpoint trace holonomy,
then a selected cell is trace-curved.
-/
theorem curvedCell_of_endpointTraceHolonomy
    (hvisible : AllSelectedCellsVisibleFlat gridTraceCellReading)
    (hholonomy : EndpointTraceHolonomy) :
    FiniteSquareCriterion.ReadingCurved gridTraceCellReading gridUpperRightCellPair :=
  FiniteSquareCriterion.finiteSquare_curvature_of_visible_agreement_protected_discrepancy
    gridTraceCellReading gridUpperRightCellPair hvisible.2 hholonomy

/--
If the selected decomposition has visible-flat cells and endpoint repair
holonomy, then a selected cell is repair-curved.
-/
theorem curvedCell_of_endpointRepairHolonomy
    (hvisible : AllSelectedCellsVisibleFlat gridRepairCellReading)
    (hholonomy : EndpointRepairHolonomy) :
    FiniteSquareCriterion.ReadingCurved gridRepairCellReading gridUpperRightCellPair :=
  FiniteSquareCriterion.finiteSquare_curvature_of_visible_agreement_protected_discrepancy
    gridRepairCellReading gridUpperRightCellPair hvisible.2 hholonomy

/-- The selected grid instantiates the trace holonomy localization criterion. -/
theorem gridUpperRightCell_instantiates_traceCriterion :
    FiniteSquareCriterion.ReadingCurved gridTraceCellReading gridUpperRightCellPair :=
  curvedCell_of_endpointTraceHolonomy
    allSelectedCells_trace_visibleFlat
    gridUpperRightCell_endpointTraceHolonomy

/-- The selected grid instantiates the repair holonomy localization criterion. -/
theorem gridUpperRightCell_instantiates_repairCriterion :
    FiniteSquareCriterion.ReadingCurved gridRepairCellReading gridUpperRightCellPair :=
  curvedCell_of_endpointRepairHolonomy
    allSelectedCells_repair_visibleFlat
    gridUpperRightCell_endpointRepairHolonomy

/--
Cycle-20 theorem package: the selected two-cell grid decomposition has
shared-boundary protected compatibility; all-cell protected flatness would
remove endpoint holonomy; the actual endpoint holonomy localizes to the selected
upper-right cell as trace and repair reading-curvature.
-/
theorem gridHolonomy_localization_package :
    SelectedTwoCellDecomposition ∧
      AllSelectedCellsVisibleFlat gridTraceCellReading ∧
      AllSelectedCellsVisibleFlat gridRepairCellReading ∧
      (AllSelectedCellsProtectedFlat gridTraceCellReading ->
        FiniteSquareCriterion.ProtectedInvariantFlat
          gridTraceCellReading gridUpperRightCellPair) ∧
      (AllSelectedCellsProtectedFlat gridRepairCellReading ->
        FiniteSquareCriterion.ProtectedInvariantFlat
          gridRepairCellReading gridUpperRightCellPair) ∧
      EndpointTraceHolonomy ∧
      EndpointRepairHolonomy ∧
      FiniteSquareCriterion.ReadingCurved gridTraceCellReading gridUpperRightCellPair ∧
      FiniteSquareCriterion.ReadingCurved gridRepairCellReading gridUpperRightCellPair ∧
      ProfileGridHolonomy.LocalizedCurvatureCell := by
  exact ⟨selectedTwoCellDecomposition_witness,
    allSelectedCells_trace_visibleFlat,
    allSelectedCells_repair_visibleFlat,
    endpointProtectedFlat_of_allSelectedCellsFlat gridTraceCellReading,
    endpointProtectedFlat_of_allSelectedCellsFlat gridRepairCellReading,
    gridUpperRightCell_endpointTraceHolonomy,
    gridUpperRightCell_endpointRepairHolonomy,
    gridUpperRightCell_instantiates_traceCriterion,
    gridUpperRightCell_instantiates_repairCriterion,
    ProfileGridHolonomy.localized_curvature_cell⟩

end GridHolonomyLocalization
end QualitySurface
end Formal.AG.Research
