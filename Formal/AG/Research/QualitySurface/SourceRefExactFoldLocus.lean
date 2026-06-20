import Formal.AG.Research.QualitySurface.SourceRefRepairHolonomy
import Formal.AG.Research.QualitySurface.ComponentDefectPropagation

/-!
Cycle 27 evidence for `G-aat-quality-surface-01`.

This file defines the source-ref exact fold locus for packet-induced tuple
visualizations: visible tuple data agrees while source-ref exact visualization
fails.  The locus is characterized by visible agreement plus packet holonomy
defect, propagates along source-ref exact legs, and is exited by the supplied
exact storage repair.  The claim is relative to supplied finite source-ref
packets, explicit packet-to-tuple bridges, and the declared repair action; it
does not assert a global fold theory, canonical extraction, source extraction
completeness, ArchMap correctness, arbitrary codebase traceability, or
whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SourceRefExactFoldLocusTheory

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open SourceRefRepairHolonomyAnnihilation
open ComponentHolonomyDefectPropagation

abbrev TupleProfile :=
  SourceRefExactVisualizationCriterion.TupleProfile

/-! ## Fold-locus definition and visible composition -/

/--
The source-ref exact fold locus: the packet-induced tuple visible surface
agrees, but source-ref exact visualization fails.
-/
def SourceRefExactFoldLocus {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) : Prop :=
  TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
    ¬ SourceRefExactVisualization gridLeft gridRight left right

/-- Visible packet-induced tuple equivalence is symmetric. -/
theorem tupleVisibleVisualizationEquivalent_symm {p : TupleProfile}
    {gridLeft gridRight : ProfileGridHolonomy.CertificateAt p}
    {left right : SourceRefPacket}
    (hvisible :
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right) :
    TupleVisibleVisualizationEquivalent gridRight gridLeft right left := by
  exact ⟨hvisible.1.symm, hvisible.2.1.symm, by
    intro atom
    exact Iff.symm (hvisible.2.2 atom)⟩

/-- Visible packet-induced tuple equivalence composes along a finite chain. -/
theorem tupleVisibleVisualizationEquivalent_trans {p : TupleProfile}
    {gridLeft gridMiddle gridRight : ProfileGridHolonomy.CertificateAt p}
    {left middle right : SourceRefPacket}
    (hleft :
      TupleVisibleVisualizationEquivalent gridLeft gridMiddle left middle)
    (hright :
      TupleVisibleVisualizationEquivalent gridMiddle gridRight middle right) :
    TupleVisibleVisualizationEquivalent gridLeft gridRight left right := by
  exact ⟨Eq.trans hleft.1 hright.1,
    Eq.trans hleft.2.1 hright.2.1,
    by
      intro atom
      exact Iff.trans (hleft.2.2 atom) (hright.2.2 atom)⟩

/-- Source-ref exact visualization gives packet-level zero holonomy. -/
theorem packetZero_of_sourceRefExactVisualization {p : TupleProfile}
    {gridLeft gridRight : ProfileGridHolonomy.CertificateAt p}
    {left right : SourceRefPacket}
    (hexact : SourceRefExactVisualization gridLeft gridRight left right) :
    NoSourceRefPacketHolonomyDefect left right :=
  tupleZeroHolonomy_reflects_packetZeroHolonomy
    gridLeft gridRight hexact.2

/-- Packet-level zero holonomy is symmetric. -/
theorem noSourceRefPacketHolonomyDefect_symm
    {left right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect left right) :
    NoSourceRefPacketHolonomyDefect right left :=
  ⟨hzero.1.symm,
    by
      intro atom
      exact Iff.symm (hzero.2.1 atom),
    by
      intro atom
      exact (hzero.2.2 atom).symm⟩

/-! ## Characterization and witnesses -/

/--
Inside a visible packet-induced tuple fiber, source-ref exact fold membership
is exactly packet-level protected holonomy.
-/
theorem sourceRefExactFold_iff_visible_packetDefect {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    (left right : SourceRefPacket) :
    SourceRefExactFoldLocus gridLeft gridRight left right ↔
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
        HasSourceRefPacketHolonomyDefect left right := by
  constructor
  · intro hfold
    refine ⟨hfold.1, ?_⟩
    intro hzero
    exact hfold.2
      ((sourceRefExactVisualization_iff_visible_packetZeroHolonomy
        gridLeft gridRight left right).mpr ⟨hfold.1, hzero⟩)
  · intro hvisibleDefect
    exact ⟨hvisibleDefect.1, by
      intro hexact
      exact hvisibleDefect.2
        (packetZero_of_sourceRefExactVisualization hexact)⟩

/-- The full/partial packet pair lies in the source-ref exact fold locus. -/
theorem full_partial_sourceRefExactFoldLocus :
    SourceRefExactFoldLocus
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket partialPacket :=
  ⟨full_partial_packetTuple_lossyVisualization.1,
    full_partial_packetTuple_not_sourceRefExact⟩

/-! ## Propagation along source-ref exact legs -/

/-- Fold-locus membership propagates across a source-ref exact leg on the left. -/
theorem sourceRefExactFoldLocus_propagates_left_of_exact {p : TupleProfile}
    {gridLeft gridMiddle gridRight : ProfileGridHolonomy.CertificateAt p}
    {left middle right : SourceRefPacket}
    (hexact : SourceRefExactVisualization gridLeft gridMiddle left middle)
    (hfold : SourceRefExactFoldLocus gridMiddle gridRight middle right) :
    SourceRefExactFoldLocus gridLeft gridRight left right := by
  refine ⟨tupleVisibleVisualizationEquivalent_trans hexact.1 hfold.1, ?_⟩
  intro hexactEndpoint
  have hzeroLeftMiddle :
      NoSourceRefPacketHolonomyDefect left middle :=
    packetZero_of_sourceRefExactVisualization hexact
  have hzeroLeftRight :
      NoSourceRefPacketHolonomyDefect left right :=
    packetZero_of_sourceRefExactVisualization hexactEndpoint
  have hzeroMiddleRight :
      NoSourceRefPacketHolonomyDefect middle right :=
    noSourceRefPacketHolonomyDefect_trans
      (noSourceRefPacketHolonomyDefect_symm hzeroLeftMiddle)
      hzeroLeftRight
  have hvisibleMiddleRight :
      TupleVisibleVisualizationEquivalent gridMiddle gridRight middle right :=
    tupleVisibleVisualizationEquivalent_trans
      (tupleVisibleVisualizationEquivalent_symm hexact.1)
      hexactEndpoint.1
  exact hfold.2
    ⟨hvisibleMiddleRight,
      noPacketHolonomy_projects_to_noTupleHolonomy
        gridMiddle gridRight hzeroMiddleRight⟩

/-- Fold-locus membership propagates across a source-ref exact leg on the right. -/
theorem sourceRefExactFoldLocus_propagates_right_of_exact {p : TupleProfile}
    {gridLeft gridMiddle gridRight : ProfileGridHolonomy.CertificateAt p}
    {left middle right : SourceRefPacket}
    (hfold : SourceRefExactFoldLocus gridLeft gridMiddle left middle)
    (hexact : SourceRefExactVisualization gridMiddle gridRight middle right) :
    SourceRefExactFoldLocus gridLeft gridRight left right := by
  refine ⟨tupleVisibleVisualizationEquivalent_trans hfold.1 hexact.1, ?_⟩
  intro hexactEndpoint
  have hzeroMiddleRight :
      NoSourceRefPacketHolonomyDefect middle right :=
    packetZero_of_sourceRefExactVisualization hexact
  have hzeroLeftRight :
      NoSourceRefPacketHolonomyDefect left right :=
    packetZero_of_sourceRefExactVisualization hexactEndpoint
  have hzeroLeftMiddle :
      NoSourceRefPacketHolonomyDefect left middle :=
    noSourceRefPacketHolonomyDefect_trans
      hzeroLeftRight
      (noSourceRefPacketHolonomyDefect_symm hzeroMiddleRight)
  have hvisibleLeftMiddle :
      TupleVisibleVisualizationEquivalent gridLeft gridMiddle left middle :=
    tupleVisibleVisualizationEquivalent_trans
      hexactEndpoint.1
      (tupleVisibleVisualizationEquivalent_symm hexact.1)
  exact hfold.2
    ⟨hvisibleLeftMiddle,
      noPacketHolonomy_projects_to_noTupleHolonomy
        gridLeft gridMiddle hzeroLeftMiddle⟩

/-! ## Component obstruction and repair exit -/

/-- A packet component defect inside a visible fiber creates a fold-locus point. -/
theorem packetComponentDefect_obstructs_sourceRefExactFold {p : TupleProfile}
    {gridLeft gridRight : ProfileGridHolonomy.CertificateAt p}
    {left right : SourceRefPacket}
    {component : SourceRefPacketProtectedComponent}
    (hvisible :
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right)
    (hdefect : SourceRefPacketHolonomyDefect left right component) :
    SourceRefExactFoldLocus gridLeft gridRight left right :=
  ⟨hvisible,
    packetHolonomyDefect_obstructs_sourceRefExactVisualization hdefect⟩

/-- The propagated packet component defect gives a tuple-level fold obstruction. -/
theorem propagatedPacketDefect_obstructs_sourceRefExactFold
    {p : TupleProfile}
    {gridLeft gridMiddle gridRight : ProfileGridHolonomy.CertificateAt p}
    {left middle right : SourceRefPacket}
    {component : SourceRefPacketProtectedComponent}
    (hexact : SourceRefExactVisualization gridLeft gridMiddle left middle)
    (hvisible :
      TupleVisibleVisualizationEquivalent gridLeft gridRight left right)
    (hdefect : SourceRefPacketHolonomyDefect middle right component) :
    SourceRefExactFoldLocus gridLeft gridRight left right := by
  have hzero :
      NoSourceRefPacketHolonomyDefect left middle :=
    packetZero_of_sourceRefExactVisualization hexact
  exact packetComponentDefect_obstructs_sourceRefExactFold hvisible
    ((packetComponentDefect_propagates_left_of_zero
      hzero component).mp hdefect)

/-- The supplied exact storage repair exits the full/partial fold locus. -/
theorem storageRepairPacket_exits_sourceRefExactFoldLocus :
    ¬ SourceRefExactFoldLocus
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket
      CodebaseTraceRepairTrajectory.storageRepairPacket := by
  intro hfold
  exact hfold.2 storageRepairPacket_sourceRefExactVisualization

/-! ## Theorem package -/

/--
Cycle-27 theorem package: source-ref exact fold-locus membership is visible
equivalence plus packet holonomy defect; it has the full/partial witness,
propagates along source-ref exact legs, is generated by component defects, and
is exited by the supplied exact storage repair.
-/
theorem sourceRefExactFoldLocus_package :
    (∀ {p : TupleProfile}
      (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
      (left right : SourceRefPacket),
      SourceRefExactFoldLocus gridLeft gridRight left right ↔
        TupleVisibleVisualizationEquivalent gridLeft gridRight left right ∧
          HasSourceRefPacketHolonomyDefect left right) ∧
      SourceRefExactFoldLocus
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket partialPacket ∧
      (∀ {p : TupleProfile}
        {gridLeft gridMiddle gridRight : ProfileGridHolonomy.CertificateAt p}
        {left middle right : SourceRefPacket},
        SourceRefExactVisualization gridLeft gridMiddle left middle ->
        SourceRefExactFoldLocus gridMiddle gridRight middle right ->
        SourceRefExactFoldLocus gridLeft gridRight left right) ∧
      (∀ {p : TupleProfile}
        {gridLeft gridMiddle gridRight : ProfileGridHolonomy.CertificateAt p}
        {left middle right : SourceRefPacket},
        SourceRefExactFoldLocus gridLeft gridMiddle left middle ->
        SourceRefExactVisualization gridMiddle gridRight middle right ->
        SourceRefExactFoldLocus gridLeft gridRight left right) ∧
      (∀ {p : TupleProfile}
        {gridLeft gridRight : ProfileGridHolonomy.CertificateAt p}
        {left right : SourceRefPacket}
        {component : SourceRefPacketProtectedComponent},
        TupleVisibleVisualizationEquivalent gridLeft gridRight left right ->
        SourceRefPacketHolonomyDefect left right component ->
        SourceRefExactFoldLocus gridLeft gridRight left right) ∧
      ¬ SourceRefExactFoldLocus
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket
        CodebaseTraceRepairTrajectory.storageRepairPacket := by
  exact ⟨by
      intro p gridLeft gridRight left right
      exact sourceRefExactFold_iff_visible_packetDefect
        gridLeft gridRight left right,
    full_partial_sourceRefExactFoldLocus,
    by
      intro p gridLeft gridMiddle gridRight left middle right hexact hfold
      exact sourceRefExactFoldLocus_propagates_left_of_exact hexact hfold,
    by
      intro p gridLeft gridMiddle gridRight left middle right hfold hexact
      exact sourceRefExactFoldLocus_propagates_right_of_exact hfold hexact,
    by
      intro p gridLeft gridRight left right component hvisible hdefect
      exact packetComponentDefect_obstructs_sourceRefExactFold
        hvisible hdefect,
    storageRepairPacket_exits_sourceRefExactFoldLocus⟩

end SourceRefExactFoldLocusTheory
end QualitySurface
end Formal.AG.Research
