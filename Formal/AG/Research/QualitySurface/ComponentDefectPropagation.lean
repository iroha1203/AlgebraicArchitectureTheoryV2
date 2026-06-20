import Formal.AG.Research.QualitySurface.CodebaseTraceHolonomyPacket

/-!
Cycle 26 evidence for `G-aat-quality-surface-01`.

This file turns tuple-level and source-ref packet-level component holonomy
defects into a finite propagation calculus.  A zero-holonomy leg preserves and
reflects component defects on either side, while concrete full/partial/full
witnesses show that two nonzero component-defect legs may cancel at the
endpoint.  The results are relative to supplied finite tuple certificates,
source-ref packets, and the explicit packet-to-tuple bridge; they do not assert
a global additive defect group, canonical extraction, source extraction
completeness, ArchMap correctness, arbitrary codebase traceability, or
whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace ComponentHolonomyDefectPropagation

open TraceLocus
open TupleHolonomyDefectInvariant
open CodebaseTracePacket
open CodebaseTraceHolonomyPacket

abbrev TupleProfile :=
  TupleHolonomyDefectInvariant.TupleProfile

abbrev TupleCertificateAt :=
  TupleHolonomyDefectInvariant.TupleCertificateAt

/-! ## Elementary transport lemmas -/

private theorem ne_eq_left_iff {α : Sort _} {a b c : α}
    (hab : a = b) : b ≠ c ↔ a ≠ c := by
  constructor
  · intro hbc hac
    exact hbc (by
      rw [← hab]
      exact hac)
  · intro hac hbc
    exact hac (by
      rw [hab]
      exact hbc)

private theorem ne_eq_right_iff {α : Sort _} {a b c : α}
    (hbc : b = c) : a ≠ b ↔ a ≠ c := by
  constructor
  · intro hab hac
    exact hab (by
      rw [hbc]
      exact hac)
  · intro hac hab
    exact hac (by
      rw [← hbc]
      exact hab)

private theorem not_iff_left_iff {a b c : Prop}
    (hab : a ↔ b) : (¬ (b ↔ c)) ↔ (¬ (a ↔ c)) := by
  constructor
  · intro hbc hac
    exact hbc (Iff.trans (Iff.symm hab) hac)
  · intro hac hbc
    exact hac (Iff.trans hab hbc)

private theorem not_iff_right_iff {a b c : Prop}
    (hbc : b ↔ c) : (¬ (a ↔ b)) ↔ (¬ (a ↔ c)) := by
  constructor
  · intro hab hac
    exact hab (Iff.trans hac (Iff.symm hbc))
  · intro hac hab
    exact hac (Iff.trans hab hbc)

/-! ## Tuple zero-defect calculus -/

/-- Tuple zero holonomy is reflexive. -/
theorem noTupleHolonomyDefect_refl {p : TupleProfile}
    (c : TupleCertificateAt p) :
    NoTupleHolonomyDefect c c :=
  ⟨rfl, by intro atom; rfl, by intro atom; rfl⟩

/-- Tuple zero holonomy composes along finite chains. -/
theorem noTupleHolonomyDefect_trans {p : TupleProfile}
    {left middle right : TupleCertificateAt p}
    (hleft : NoTupleHolonomyDefect left middle)
    (hright : NoTupleHolonomyDefect middle right) :
    NoTupleHolonomyDefect left right :=
  ⟨Eq.trans hleft.1 hright.1,
    by
      intro atom
      exact Iff.trans (hleft.2.1 atom) (hright.2.1 atom),
    by
      intro atom
      exact Eq.trans (hleft.2.2 atom) (hright.2.2 atom)⟩

/-- A zero tuple-holonomy leg on the left preserves and reflects defects. -/
theorem tupleComponentDefect_propagates_left_of_zero {p : TupleProfile}
    {left middle right : TupleCertificateAt p}
    (hzero : NoTupleHolonomyDefect left middle)
    (component : TupleProtectedComponent) :
    TupleHolonomyDefect middle right component ↔
      TupleHolonomyDefect left right component := by
  cases component with
  | obligation =>
      exact ne_eq_left_iff hzero.1
  | repairFrontier atom =>
      exact not_iff_left_iff (hzero.2.1 atom)
  | traceField atom =>
      exact ne_eq_left_iff (hzero.2.2 atom)

/-- A zero tuple-holonomy leg on the right preserves and reflects defects. -/
theorem tupleComponentDefect_propagates_right_of_zero {p : TupleProfile}
    {left middle right : TupleCertificateAt p}
    (hzero : NoTupleHolonomyDefect middle right)
    (component : TupleProtectedComponent) :
    TupleHolonomyDefect left middle component ↔
      TupleHolonomyDefect left right component := by
  cases component with
  | obligation =>
      exact ne_eq_right_iff hzero.1
  | repairFrontier atom =>
      exact not_iff_right_iff (hzero.2.1 atom)
  | traceField atom =>
      exact ne_eq_right_iff (hzero.2.2 atom)

/-! ## Packet zero-defect calculus -/

/-- Packet zero holonomy is reflexive. -/
theorem noSourceRefPacketHolonomyDefect_refl
    (packet : SourceRefPacket) :
    NoSourceRefPacketHolonomyDefect packet packet :=
  ⟨rfl, by intro atom; rfl, by intro atom; rfl⟩

/-- Packet zero holonomy composes along finite chains. -/
theorem noSourceRefPacketHolonomyDefect_trans
    {left middle right : SourceRefPacket}
    (hleft : NoSourceRefPacketHolonomyDefect left middle)
    (hright : NoSourceRefPacketHolonomyDefect middle right) :
    NoSourceRefPacketHolonomyDefect left right :=
  ⟨Eq.trans hleft.1 hright.1,
    by
      intro atom
      exact Iff.trans (hleft.2.1 atom) (hright.2.1 atom),
    by
      intro atom
      exact Eq.trans (hleft.2.2 atom) (hright.2.2 atom)⟩

/-- A zero packet-holonomy leg on the left preserves and reflects defects. -/
theorem packetComponentDefect_propagates_left_of_zero
    {left middle right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect left middle)
    (component : SourceRefPacketProtectedComponent) :
    SourceRefPacketHolonomyDefect middle right component ↔
      SourceRefPacketHolonomyDefect left right component := by
  cases component with
  | obligation =>
      exact ne_eq_left_iff hzero.1
  | repairFrontier atom =>
      exact not_iff_left_iff (hzero.2.1 atom)
  | sourceRefTable atom =>
      exact ne_eq_left_iff (hzero.2.2 atom)

/-- A zero packet-holonomy leg on the right preserves and reflects defects. -/
theorem packetComponentDefect_propagates_right_of_zero
    {left middle right : SourceRefPacket}
    (hzero : NoSourceRefPacketHolonomyDefect middle right)
    (component : SourceRefPacketProtectedComponent) :
    SourceRefPacketHolonomyDefect left middle component ↔
      SourceRefPacketHolonomyDefect left right component := by
  cases component with
  | obligation =>
      exact ne_eq_right_iff hzero.1
  | repairFrontier atom =>
      exact not_iff_right_iff (hzero.2.1 atom)
  | sourceRefTable atom =>
      exact ne_eq_right_iff (hzero.2.2 atom)

/--
Packet component defects that propagate across a zero packet leg still project
to tuple component defects.
-/
theorem packetComponentDefect_projects_after_left_zero
    {p : TupleProfile}
    (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
    {left middle right : SourceRefPacket}
    {component : SourceRefPacketProtectedComponent}
    (hzero : NoSourceRefPacketHolonomyDefect left middle)
    (hdefect : SourceRefPacketHolonomyDefect middle right component) :
    TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple gridLeft left)
      (SourceRefTupleBridge.packetToTuple gridRight right)
      (packetComponentToTupleComponent component) :=
  sourceRefPacketHolonomy_projects_to_tupleHolonomy
    gridLeft gridRight
    ((packetComponentDefect_propagates_left_of_zero
      hzero component).mp hdefect)

/-! ## Cancellation witnesses -/

/-- The reverse endpoint obligation defect also holds. -/
theorem endpointTuple_obligationReverseComponentDefect :
    TupleHolonomyDefect
      ProfileTupleIntegration.traceMissingEndpointTuple
      ProfileTupleIntegration.fullEndpointTuple
      TupleProtectedComponent.obligation := by
  intro hsame
  cases hsame

/-- The reverse endpoint repair-frontier defect also holds. -/
theorem endpointTuple_databaseRepairReverseComponentDefect :
    TupleHolonomyDefect
      ProfileTupleIntegration.traceMissingEndpointTuple
      ProfileTupleIntegration.fullEndpointTuple
      (TupleProtectedComponent.repairFrontier LocusAtom.database) := by
  intro hsame
  have hrepairFull :
      ProfileTupleIntegration.fullEndpointTuple.repairFrontier
        LocusAtom.database :=
    hsame.mp
      ProfileTupleIntegration.traceMissingEndpoint_forces_database_repair
  exact ProfileTupleIntegration.fullEndpoint_no_database_repair hrepairFull

/-- The reverse endpoint trace-field defect also holds. -/
theorem endpointTuple_databaseTraceFieldReverseComponentDefect :
    TupleHolonomyDefect
      ProfileTupleIntegration.traceMissingEndpointTuple
      ProfileTupleIntegration.fullEndpointTuple
      (TupleProtectedComponent.traceField LocusAtom.database) := by
  intro hsame
  cases hsame

/--
Tuple component defects may cancel along a full/partial/full chain, so
unrestricted "defect plus defect implies endpoint defect" is false.
-/
theorem tupleComponentDefects_can_cancel :
    TupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        TupleProtectedComponent.obligation ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.traceMissingEndpointTuple
        ProfileTupleIntegration.fullEndpointTuple
        TupleProtectedComponent.obligation ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        (TupleProtectedComponent.repairFrontier LocusAtom.database) ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.traceMissingEndpointTuple
        ProfileTupleIntegration.fullEndpointTuple
        (TupleProtectedComponent.repairFrontier LocusAtom.database) ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        (TupleProtectedComponent.traceField LocusAtom.database) ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.traceMissingEndpointTuple
        ProfileTupleIntegration.fullEndpointTuple
        (TupleProtectedComponent.traceField LocusAtom.database) ∧
      NoTupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.fullEndpointTuple :=
  ⟨endpointTuple_obligationComponentDefect,
    endpointTuple_obligationReverseComponentDefect,
    endpointTuple_databaseRepairComponentDefect,
    endpointTuple_databaseRepairReverseComponentDefect,
    endpointTuple_databaseTraceFieldComponentDefect,
    endpointTuple_databaseTraceFieldReverseComponentDefect,
    noTupleHolonomyDefect_refl
      ProfileTupleIntegration.fullEndpointTuple⟩

/-- The reverse packet obligation defect also holds. -/
theorem full_partial_packet_obligationReverseComponentDefect :
    SourceRefPacketHolonomyDefect partialPacket fullPacket
      SourceRefPacketProtectedComponent.obligation := by
  intro hsame
  cases hsame

/-- The reverse packet repair-frontier defect also holds. -/
theorem full_partial_packet_storageRepairReverseComponentDefect :
    SourceRefPacketHolonomyDefect partialPacket fullPacket
      (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) := by
  intro hsame
  have hrepairFull : fullPacket.repairFrontier CodeAtom.storage :=
    hsame.mp partialTrace_forces_storage_repair
  exact fullTrace_repair_frontier_excludes_storage hrepairFull

/-- The reverse packet source-ref-table defect also holds. -/
theorem full_partial_packet_storageSourceRefReverseComponentDefect :
    SourceRefPacketHolonomyDefect partialPacket fullPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) := by
  intro hsame
  cases hsame

/--
Packet component defects may also cancel along a full/partial/full chain.
-/
theorem packetComponentDefects_can_cancel :
    SourceRefPacketHolonomyDefect fullPacket partialPacket
        SourceRefPacketProtectedComponent.obligation ∧
      SourceRefPacketHolonomyDefect partialPacket fullPacket
        SourceRefPacketProtectedComponent.obligation ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) ∧
      SourceRefPacketHolonomyDefect partialPacket fullPacket
        (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
      SourceRefPacketHolonomyDefect partialPacket fullPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) ∧
      NoSourceRefPacketHolonomyDefect fullPacket fullPacket :=
  ⟨full_partial_packet_obligationComponentDefect,
    full_partial_packet_obligationReverseComponentDefect,
    full_partial_packet_storageRepairComponentDefect,
    full_partial_packet_storageRepairReverseComponentDefect,
    full_partial_packet_storageSourceRefComponentDefect,
    full_partial_packet_storageSourceRefReverseComponentDefect,
    noSourceRefPacketHolonomyDefect_refl fullPacket⟩

/-! ## Theorem package -/

/--
Cycle-26 theorem package: zero tuple/packet holonomy legs compose and propagate
component defects, packet propagation is compatible with the packet-to-tuple
projection, and concrete full/partial/full witnesses show that unrestricted
defect composition can cancel at the endpoint.
-/
theorem componentHolonomyDefectPropagation_package :
    (∀ {p : TupleProfile} (c : TupleCertificateAt p),
      NoTupleHolonomyDefect c c) ∧
      (∀ {p : TupleProfile}
        {left middle right : TupleCertificateAt p},
        NoTupleHolonomyDefect left middle ->
        NoTupleHolonomyDefect middle right ->
        NoTupleHolonomyDefect left right) ∧
      (∀ {p : TupleProfile}
        {left middle right : TupleCertificateAt p}
        (_hzero : NoTupleHolonomyDefect left middle)
        (component : TupleProtectedComponent),
        TupleHolonomyDefect middle right component ↔
          TupleHolonomyDefect left right component) ∧
      (∀ {p : TupleProfile}
        {left middle right : TupleCertificateAt p}
        (_hzero : NoTupleHolonomyDefect middle right)
        (component : TupleProtectedComponent),
        TupleHolonomyDefect left middle component ↔
          TupleHolonomyDefect left right component) ∧
      (∀ packet : SourceRefPacket,
        NoSourceRefPacketHolonomyDefect packet packet) ∧
      (∀ {left middle right : SourceRefPacket},
        NoSourceRefPacketHolonomyDefect left middle ->
        NoSourceRefPacketHolonomyDefect middle right ->
        NoSourceRefPacketHolonomyDefect left right) ∧
      (∀ {left middle right : SourceRefPacket}
        (_hzero : NoSourceRefPacketHolonomyDefect left middle)
        (component : SourceRefPacketProtectedComponent),
        SourceRefPacketHolonomyDefect middle right component ↔
          SourceRefPacketHolonomyDefect left right component) ∧
      (∀ {left middle right : SourceRefPacket}
        (_hzero : NoSourceRefPacketHolonomyDefect middle right)
        (component : SourceRefPacketProtectedComponent),
        SourceRefPacketHolonomyDefect left middle component ↔
          SourceRefPacketHolonomyDefect left right component) ∧
      (∀ {p : TupleProfile}
        (gridLeft gridRight : ProfileGridHolonomy.CertificateAt p)
        {left middle right : SourceRefPacket}
        {component : SourceRefPacketProtectedComponent},
        NoSourceRefPacketHolonomyDefect left middle ->
        SourceRefPacketHolonomyDefect middle right component ->
        TupleHolonomyDefect
          (SourceRefTupleBridge.packetToTuple gridLeft left)
          (SourceRefTupleBridge.packetToTuple gridRight right)
          (packetComponentToTupleComponent component)) ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.traceMissingEndpointTuple
        TupleProtectedComponent.obligation ∧
      TupleHolonomyDefect
        ProfileTupleIntegration.traceMissingEndpointTuple
        ProfileTupleIntegration.fullEndpointTuple
        TupleProtectedComponent.obligation ∧
      NoTupleHolonomyDefect
        ProfileTupleIntegration.fullEndpointTuple
        ProfileTupleIntegration.fullEndpointTuple ∧
      SourceRefPacketHolonomyDefect fullPacket partialPacket
        SourceRefPacketProtectedComponent.obligation ∧
      SourceRefPacketHolonomyDefect partialPacket fullPacket
        SourceRefPacketProtectedComponent.obligation ∧
      NoSourceRefPacketHolonomyDefect fullPacket fullPacket := by
  exact ⟨by
      intro p c
      exact noTupleHolonomyDefect_refl c,
    by
      intro p left middle right hleft hright
      exact noTupleHolonomyDefect_trans hleft hright,
    by
      intro p left middle right hzero component
      exact tupleComponentDefect_propagates_left_of_zero hzero component,
    by
      intro p left middle right hzero component
      exact tupleComponentDefect_propagates_right_of_zero hzero component,
    noSourceRefPacketHolonomyDefect_refl,
    by
      intro left middle right hleft hright
      exact noSourceRefPacketHolonomyDefect_trans hleft hright,
    by
      intro left middle right hzero component
      exact packetComponentDefect_propagates_left_of_zero hzero component,
    by
      intro left middle right hzero component
      exact packetComponentDefect_propagates_right_of_zero hzero component,
    by
      intro p gridLeft gridRight left middle right component hzero hdefect
      exact packetComponentDefect_projects_after_left_zero
        gridLeft gridRight hzero hdefect,
    endpointTuple_obligationComponentDefect,
    endpointTuple_obligationReverseComponentDefect,
    noTupleHolonomyDefect_refl
      ProfileTupleIntegration.fullEndpointTuple,
    full_partial_packet_obligationComponentDefect,
    full_partial_packet_obligationReverseComponentDefect,
    noSourceRefPacketHolonomyDefect_refl fullPacket⟩

end ComponentHolonomyDefectPropagation
end QualitySurface
end Formal.AG.Research
