import ResearchLean.AG.QualitySurface.SourceRefPacketTransport
import ResearchLean.AG.QualitySurface.SourceRefExactFoldLocus

/-!
Cycle 29 evidence for `G-aat-quality-surface-01`.

This file isolates source-ref table preservation as an independent transport
law.  A finite token-swap packet update preserves visible packet data, support,
missing-locus shape, repair frontier, and obligation, but changes non-missing
source-ref token identity.  The update therefore fails `PreservesSourceRefTable`
and lawful bidirectional source-ref packet transport, while producing packet
holonomy, tuple trace-field defect, source-ref exact visualization failure, and
a fold-locus point.  The claim is relative to the supplied finite source-ref
token vocabulary and explicit packet-to-tuple bridge; it does not assert a
global source-reference namespace, source extraction completeness, ArchMap
correctness, or whole-codebase traceability.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SourceRefTableLawObstruction

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefPacketTransport
open SourceRefExactVisualizationCriterion
open SourceRefExactFoldLocusTheory

/-! ## Token-swap transport -/

/-- A nontrivial finite permutation of supplied source-ref tokens. -/
def sourceRefTokenSwap : SourceRefToken -> SourceRefToken
  | SourceRefToken.endpointRef => SourceRefToken.workerRef
  | SourceRefToken.storageRef => SourceRefToken.storageRef
  | SourceRefToken.workerRef => SourceRefToken.endpointRef

/-- The token swap is involutive on the supplied finite token vocabulary. -/
theorem sourceRefTokenSwap_involutive
    (token : SourceRefToken) :
    sourceRefTokenSwap (sourceRefTokenSwap token) = token := by
  cases token <;> rfl

/-- Apply the finite token swap pointwise to a packet source-ref table. -/
def tokenSwapTable (packet : SourceRefPacket) :
    CodeAtom -> Option SourceRefToken :=
  fun atom => Option.map sourceRefTokenSwap (packet.sourceRefTable atom)

/--
Packet update that changes only non-missing source-ref token identity; all
visible and non-table protected components are copied from the input packet.
-/
def sourceRefTokenSwapTransport : PacketUpdate where
  map := fun packet =>
    { visibleScalarReading := packet.visibleScalarReading
      verdict := packet.verdict
      codeSupport := packet.codeSupport
      sourceRefTable := tokenSwapTable packet
      repairFrontier := packet.repairFrontier
      obligation := packet.obligation }

/-- The selected full packet after applying the token-swap transport. -/
def tokenSwappedFullPacket : SourceRefPacket :=
  sourceRefTokenSwapTransport.map fullPacket

/-! ## Non-table transport laws -/

/-- The token-swap update preserves code support. -/
theorem tokenSwapTransport_preservesCodeSupport :
    PreservesCodeSupport sourceRefTokenSwapTransport := by
  intro packet atom hsupport
  exact hsupport

/-- The token-swap update reflects code support. -/
theorem tokenSwapTransport_reflectsCodeSupport :
    ReflectsCodeSupport sourceRefTokenSwapTransport := by
  intro packet atom hsupport
  exact hsupport

/-- The token-swap update preserves missing source-ref loci. -/
theorem tokenSwapTransport_preservesMissingLocus :
    PreservesSourceRefMissingLocus sourceRefTokenSwapTransport := by
  intro packet atom hmissing
  rcases hmissing with ⟨hsupport, hnone⟩
  exact ⟨hsupport, by
    change Option.map sourceRefTokenSwap (packet.sourceRefTable atom) = none
    rw [hnone]
    rfl⟩

/-- The token-swap update reflects missing source-ref loci. -/
theorem tokenSwapTransport_reflectsMissingLocus :
    ReflectsSourceRefMissingLocus sourceRefTokenSwapTransport := by
  intro packet atom hmissing
  rcases hmissing with ⟨hsupport, hnone⟩
  refine ⟨hsupport, ?_⟩
  cases hsource : packet.sourceRefTable atom with
  | none => rfl
  | some token =>
      change Option.map sourceRefTokenSwap (packet.sourceRefTable atom) = none
        at hnone
      rw [hsource] at hnone
      cases hnone

/-- The token-swap update preserves repair-frontier membership. -/
theorem tokenSwapTransport_preservesRepairFrontier :
    PreservesSourceRefRepairFrontier sourceRefTokenSwapTransport := by
  intro packet atom hrepair
  exact hrepair

/-- The token-swap update reflects repair-frontier membership. -/
theorem tokenSwapTransport_reflectsRepairFrontier :
    ReflectsSourceRefRepairFrontier sourceRefTokenSwapTransport := by
  intro packet atom hrepair
  exact hrepair

/-! ## Visible and non-table flatness on the selected full packet -/

/-- The full packet and its token-swapped image agree visibly. -/
theorem tokenSwap_visiblePacketSurface :
    supportSurfaceReading.Equivalent fullPacket tokenSwappedFullPacket := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro hsupport <;> exact hsupport

/-- The visible packet agreement projects to visible tuple agreement. -/
theorem tokenSwap_visibleTupleSurface :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket tokenSwappedFullPacket :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    tokenSwap_visiblePacketSurface

/-- The token swap does not change the selected obligation. -/
theorem tokenSwap_obligation_flat :
    fullPacket.obligation = tokenSwappedFullPacket.obligation :=
  rfl

/-- The token swap does not change the repair-frontier component. -/
theorem tokenSwap_repairFrontier_flat :
    SameCodebaseRepairFrontier fullPacket tokenSwappedFullPacket := by
  intro atom
  constructor <;> intro hrepair <;> exact hrepair

/-- The token swap does not change the source-ref missing locus. -/
theorem tokenSwap_missingLocus_flat :
    SameSourceRefMissingLocus fullPacket tokenSwappedFullPacket := by
  intro atom
  constructor
  · exact tokenSwapTransport_preservesMissingLocus fullPacket atom
  · exact tokenSwapTransport_reflectsMissingLocus fullPacket atom

/-! ## Source-ref table obstruction -/

/-- The endpoint token identity changes under the token-swap transport. -/
theorem tokenSwap_sourceRefTableDefect :
    SourceRefTableDefectAt
      fullPacket tokenSwappedFullPacket CodeAtom.endpoint := by
  intro hsame
  change
    some SourceRefToken.endpointRef = some SourceRefToken.workerRef at hsame
  cases hsame

/-- The token-swap table defect as a component-indexed packet defect. -/
theorem tokenSwap_sourceRefTable_componentDefect :
    SourceRefPacketHolonomyDefect
      fullPacket tokenSwappedFullPacket
      (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) :=
  tokenSwap_sourceRefTableDefect

/-- The token-swap update creates nonzero packet holonomy. -/
theorem tokenSwap_hasPacketHolonomyDefect :
    HasSourceRefPacketHolonomyDefect
      fullPacket tokenSwappedFullPacket :=
  sourceRefPacketHolonomyDefect_obstructs_noPacketHolonomy
    tokenSwap_sourceRefTable_componentDefect

/-- The source-ref table defect is visible as a tuple trace-field defect. -/
theorem tokenSwap_tupleTraceFieldDefect :
    TupleHolonomyDefectInvariant.TupleHolonomyDefect
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate fullPacket)
      (SourceRefTupleBridge.packetToTuple
        SourceRefTupleBridge.endpointGridCertificate tokenSwappedFullPacket)
      (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
        (toLocusAtom CodeAtom.endpoint)) :=
  sourceRefTableDefect_detected_as_tupleTraceFieldDefect
    SourceRefTupleBridge.endpointGridCertificate
    SourceRefTupleBridge.endpointGridCertificate
    tokenSwap_sourceRefTableDefect

/-- The token-swap update does not preserve the supplied source-ref table. -/
theorem tokenSwap_not_preservesSourceRefTable :
    ¬ PreservesSourceRefTable sourceRefTokenSwapTransport := by
  intro hpreserves
  have htable := hpreserves fullPacket CodeAtom.endpoint
  change
    some SourceRefToken.workerRef = some SourceRefToken.endpointRef at htable
  cases htable

/-- Therefore the token-swap update is not a lawful bidirectional packet transport. -/
theorem tokenSwap_not_bidirectionalTransport :
    ¬ BidirectionalSourceRefPacketTransport sourceRefTokenSwapTransport := by
  intro hlaws
  exact tokenSwap_not_preservesSourceRefTable
    hlaws.preservesSourceRefTable

/-- The token-identity defect obstructs source-ref exact visualization. -/
theorem tokenSwap_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket tokenSwappedFullPacket :=
  packetHolonomyDefect_obstructs_sourceRefExactVisualization
    tokenSwap_sourceRefTable_componentDefect

/-- The full/token-swapped pair lies in the source-ref exact fold locus. -/
theorem tokenSwap_foldLocus :
    SourceRefExactFoldLocus
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      fullPacket tokenSwappedFullPacket :=
  ⟨tokenSwap_visibleTupleSurface,
    tokenSwap_not_sourceRefExactVisualization⟩

/-! ## Theorem package -/

/--
Cycle-29 theorem package: the finite token-swap transport preserves support,
missing-locus shape, repair frontier, obligation, and visible packet/tuple
surfaces, but it changes source-ref token identity.  Thus source-ref table
preservation is an independent protected transport law needed for packet
holonomy zero and source-ref exact visualization.
-/
theorem sourceRefTableLawSharpObstruction_package :
    PreservesCodeSupport sourceRefTokenSwapTransport ∧
      ReflectsCodeSupport sourceRefTokenSwapTransport ∧
      PreservesSourceRefMissingLocus sourceRefTokenSwapTransport ∧
      ReflectsSourceRefMissingLocus sourceRefTokenSwapTransport ∧
      PreservesSourceRefRepairFrontier sourceRefTokenSwapTransport ∧
      ReflectsSourceRefRepairFrontier sourceRefTokenSwapTransport ∧
      supportSurfaceReading.Equivalent fullPacket tokenSwappedFullPacket ∧
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket tokenSwappedFullPacket ∧
      fullPacket.obligation = tokenSwappedFullPacket.obligation ∧
      SameCodebaseRepairFrontier fullPacket tokenSwappedFullPacket ∧
      SameSourceRefMissingLocus fullPacket tokenSwappedFullPacket ∧
      SourceRefPacketHolonomyDefect
        fullPacket tokenSwappedFullPacket
        (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) ∧
      TupleHolonomyDefectInvariant.TupleHolonomyDefect
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate fullPacket)
        (SourceRefTupleBridge.packetToTuple
          SourceRefTupleBridge.endpointGridCertificate tokenSwappedFullPacket)
        (TupleHolonomyDefectInvariant.TupleProtectedComponent.traceField
          (toLocusAtom CodeAtom.endpoint)) ∧
      HasSourceRefPacketHolonomyDefect
        fullPacket tokenSwappedFullPacket ∧
      ¬ PreservesSourceRefTable sourceRefTokenSwapTransport ∧
      ¬ BidirectionalSourceRefPacketTransport sourceRefTokenSwapTransport ∧
      ¬ SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket tokenSwappedFullPacket ∧
      SourceRefExactFoldLocus
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        fullPacket tokenSwappedFullPacket := by
  exact ⟨tokenSwapTransport_preservesCodeSupport,
    tokenSwapTransport_reflectsCodeSupport,
    tokenSwapTransport_preservesMissingLocus,
    tokenSwapTransport_reflectsMissingLocus,
    tokenSwapTransport_preservesRepairFrontier,
    tokenSwapTransport_reflectsRepairFrontier,
    tokenSwap_visiblePacketSurface,
    tokenSwap_visibleTupleSurface,
    tokenSwap_obligation_flat,
    tokenSwap_repairFrontier_flat,
    tokenSwap_missingLocus_flat,
    tokenSwap_sourceRefTable_componentDefect,
    tokenSwap_tupleTraceFieldDefect,
    tokenSwap_hasPacketHolonomyDefect,
    tokenSwap_not_preservesSourceRefTable,
    tokenSwap_not_bidirectionalTransport,
    tokenSwap_not_sourceRefExactVisualization,
    tokenSwap_foldLocus⟩

end SourceRefTableLawObstruction
end QualitySurface
end ResearchLean.AG
