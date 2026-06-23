import Formal.AG.Research.QualitySurface.SemanticResidualMappedRepairHitting

/-!
Cycle 98 evidence for `G-aat-quality-surface-01`.

This file builds a finite residual status-drop adapter.  A supplied exact
boolean residual status reading records residual-present indices as `true` and
residual-free indices as `false`.  Under such a reading, residual transition
cuts are exactly active edges whose status drops from `true` to `false`.

The adapter is deliberately finite and status-based.  It is not a true H1
class, does not construct a Cech or coboundary quotient, does not prove
vanishing-to-closure, and does not assert source extraction completeness,
repair synthesis, ArchMap correctness, runtime/tooling/UI correctness, or
whole-codebase quality.
-/

universe u w

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualStatusDropAdapter

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualIndexedTransport
open SemanticResidualEdgeTransitionObstruction
open VisibleLocalSemanticGluingObstruction
open RefinedSemanticRepairAtom
open SemanticResidualTransitionCut
open SemanticResidualTransitionCutScanner
open SemanticResidualObstructionClass
open SemanticResidualAtlasGauge
open SemanticResidualCutRepairHitting
open SemanticResidualMappedRepairHitting

/-! ## Exact boolean residual status readings -/

/-- Residual-present and residual-free are mutually exclusive at an index. -/
theorem indexedResidualPresent_not_free
    {Index : Type w}
    {Atom : Type u}
    {projection : Index -> Atom -> BridgeComponent}
    {cover : Index -> HandoffCechCover}
    {index : Index}
    (hpresent : IndexedResidualPresentAt projection cover index) :
    Not (IndexedResidualFreeAt projection cover index) := by
  intro hfree
  rcases hpresent with ⟨residual, hresidual⟩
  exact hfree residual hresidual

/--
A supplied exact boolean residual status reading for a finite atlas.
`true` means residual-present; `false` means residual-free.
-/
structure ResidualBooleanStatusReading
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom) where
  status : Index -> Bool
  present_iff_true :
    forall index,
      IndexedResidualPresentAt atlas.projection atlas.cover index <->
        status index = true
  free_iff_false :
    forall index,
      IndexedResidualFreeAt atlas.projection atlas.cover index <->
        status index = false

/-- An active edge whose supplied residual status drops from true to false. -/
def ResidualStatusDropPair
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    (pair : Index × Index) : Prop :=
  atlas.edge pair.1 pair.2 /\
    reading.status pair.1 = true /\
      reading.status pair.2 = false

/-- A cochain supported on status-drop active edges. -/
def residualStatusDropCochain
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) :
    ResidualCutCochain atlas where
  support := ResidualStatusDropPair reading

/-- Exact status-drop pairs are exactly residual transition cut pairs. -/
theorem residualStatusDropPair_iff_residualCutPair
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    (pair : Index × Index) :
    ResidualStatusDropPair reading pair <->
      IsResidualTransitionCutPair atlas pair := by
  constructor
  · intro hdrop
    exact
      ⟨hdrop.1,
        (reading.present_iff_true pair.1).mpr hdrop.2.1,
        (reading.free_iff_false pair.2).mpr hdrop.2.2⟩
  · intro hcut
    exact
      ⟨hcut.1,
        (reading.present_iff_true pair.1).mp hcut.2.1,
        (reading.free_iff_false pair.2).mp hcut.2.2⟩

/-- The status-drop cochain is cut-noise equivalent to the canonical cochain. -/
theorem canonicalResidualCutCochain_cutNoiseEquivalent_statusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) :
    CutNoiseEquivalent
      (canonicalResidualCutCochain atlas)
      (residualStatusDropCochain reading) := by
  intro pair hcut
  constructor
  · intro _hsupport
    exact
      (residualStatusDropPair_iff_residualCutPair
        reading pair).mpr hcut
  · intro _hdrop
    exact hcut

/-! ## Vanishing and nonzero status-drop criteria -/

/-- No active edge has a true-to-false residual status drop. -/
def NoResidualStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) : Prop :=
  forall pair : Index × Index,
    atlas.edge pair.1 pair.2 ->
      Not
        (reading.status pair.1 = true /\
          reading.status pair.2 = false)

/-- Some active edge has a true-to-false residual status drop. -/
def ExistsResidualStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) : Prop :=
  exists pair : Index × Index,
    atlas.edge pair.1 pair.2 /\
      reading.status pair.1 = true /\
        reading.status pair.2 = false

/-- Status-drop cochain vanishing is exactly absence of active true-to-false drops. -/
theorem residualStatusDropCochain_vanishes_iff_noStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) :
    (residualStatusDropCochain reading).CutVanishes <->
      NoResidualStatusDrop reading := by
  constructor
  · intro hvanish pair hedge hdrop
    have hsupport : (residualStatusDropCochain reading).support pair :=
      ⟨hedge, hdrop⟩
    have hcut :
        IsResidualTransitionCutPair atlas pair :=
      (residualStatusDropPair_iff_residualCutPair
        reading pair).mp hsupport
    exact hvanish pair hcut hsupport
  · intro hno pair _hcut hsupport
    exact hno pair hsupport.1 hsupport.2

/-- Status-drop cochain nonzero is exactly existence of an active true-to-false drop. -/
theorem residualStatusDropCochain_nonzero_iff_existsStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) :
    (residualStatusDropCochain reading).CutNonzero <->
      ExistsResidualStatusDrop reading := by
  constructor
  · intro hnonzero
    rcases hnonzero with ⟨pair, _hcut, hsupport⟩
    exact ⟨pair, hsupport.1, hsupport.2.1, hsupport.2.2⟩
  · intro hdrop
    rcases hdrop with ⟨pair, hedge, hsource, htarget⟩
    have hsupport : (residualStatusDropCochain reading).support pair :=
      ⟨hedge, hsource, htarget⟩
    have hcut :
        IsResidualTransitionCutPair atlas pair :=
      (residualStatusDropPair_iff_residualCutPair
        reading pair).mp hsupport
    exact ⟨pair, hcut, hsupport⟩

/-- Canonical residual cut-class vanishing is no true-to-false status drop. -/
theorem canonicalResidualCutClass_vanishes_iff_noStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) :
    (canonicalResidualCutCochain atlas).CutVanishes <->
      NoResidualStatusDrop reading := by
  exact
    (cutNoiseEquivalent_preserves_cutVanishes
      (canonicalResidualCutCochain_cutNoiseEquivalent_statusDrop reading)).trans
      (residualStatusDropCochain_vanishes_iff_noStatusDrop reading)

/-- Canonical residual cut-class nonzero is existence of a true-to-false status drop. -/
theorem canonicalResidualCutClass_nonzero_iff_existsStatusDrop
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas) :
    (canonicalResidualCutCochain atlas).CutNonzero <->
      ExistsResidualStatusDrop reading := by
  exact
    (cutNoiseEquivalent_preserves_cutNonzero
      (canonicalResidualCutCochain_cutNoiseEquivalent_statusDrop reading)).trans
      (residualStatusDropCochain_nonzero_iff_existsStatusDrop reading)

/-- A status drop obstructs residual transition closure. -/
theorem existsStatusDrop_obstructs_atlasTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    (hdrop : ExistsResidualStatusDrop reading)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed atlas transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain atlas)
      ((canonicalResidualCutClass_nonzero_iff_existsStatusDrop
        reading).mpr hdrop)
      transition

/-- A status drop rules out transition-coherent atlas data. -/
theorem existsStatusDrop_obstructs_transitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (reading : ResidualBooleanStatusReading atlas)
    (hdrop : ExistsResidualStatusDrop reading)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData atlas transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain atlas)
      ((canonicalResidualCutClass_nonzero_iff_existsStatusDrop
        reading).mpr hdrop)
      transition

/-! ## Selected status-drop witness -/

/-- The selected residual status reads repair-frontier as present and flat as free. -/
def selectedFrontierFlatResidualStatus :
    SelectedSemanticOverlapIndex -> Bool
  | SelectedSemanticOverlapIndex.flat => false
  | SelectedSemanticOverlapIndex.repairFrontier => true

/-- The selected frontier-to-flat atlas has an exact boolean status reading. -/
def selectedFrontierFlatResidualStatusReading :
    ResidualBooleanStatusReading selectedFrontierFlatAtlasSkeleton where
  status := selectedFrontierFlatResidualStatus
  present_iff_true := by
    intro index
    cases index with
    | flat =>
        constructor
        · intro hpresent
          exact False.elim
            (selected_flatIndexedResidualNotPresent hpresent)
        · intro htrue
          cases htrue
    | repairFrontier =>
        constructor
        · intro _hpresent
          rfl
        · intro _htrue
          exact selected_repairFrontierResidualPresent
  free_iff_false := by
    intro index
    cases index with
    | flat =>
        constructor
        · intro _hfree
          rfl
        · intro _hfalse
          exact selected_flatIndexedResidualFree
    | repairFrontier =>
        constructor
        · intro hfree
          exact False.elim
            ((indexedResidualPresent_not_free
              selected_repairFrontierResidualPresent) hfree)
        · intro hfalse
          cases hfalse

/-- The selected frontier-to-flat edge is a true-to-false status drop. -/
theorem selectedFrontierFlat_existsStatusDrop :
    ExistsResidualStatusDrop selectedFrontierFlatResidualStatusReading := by
  exact
    ⟨selectedFrontierFlatResidualCutPair,
      selected_frontierToFlatEdge,
      rfl,
      rfl⟩

/-- The selected status drop gives nonzero canonical residual cut class. -/
theorem selectedFrontierFlat_statusDrop_canonicalNonzero :
    (canonicalResidualCutCochain
      selectedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    (canonicalResidualCutClass_nonzero_iff_existsStatusDrop
      selectedFrontierFlatResidualStatusReading).mpr
      selectedFrontierFlat_existsStatusDrop

/-- The selected status drop obstructs transition closure. -/
theorem selectedFrontierFlat_statusDrop_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    existsStatusDrop_obstructs_atlasTransitionClosure
      selectedFrontierFlatResidualStatusReading
      selectedFrontierFlat_existsStatusDrop
      transition

/-- The selected status drop rules out transition-coherent atlas data. -/
theorem selectedFrontierFlat_statusDrop_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    existsStatusDrop_obstructs_transitionCoherentData
      selectedFrontierFlatResidualStatusReading
      selectedFrontierFlat_existsStatusDrop
      transition

/-! ## Theorem package -/

/--
Cycle-98 theorem package: exact finite residual boolean status readings turn
canonical residual cut classes into active true-to-false status-drop classes.
-/
theorem semanticResidualStatusDropAdapter_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
      forall reading : ResidualBooleanStatusReading atlas,
      forall pair : Index × Index,
        ResidualStatusDropPair reading pair <->
          IsResidualTransitionCutPair atlas pair) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall reading : ResidualBooleanStatusReading atlas,
        CutNoiseEquivalent
          (canonicalResidualCutCochain atlas)
          (residualStatusDropCochain reading)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall reading : ResidualBooleanStatusReading atlas,
        (canonicalResidualCutCochain atlas).CutVanishes <->
          NoResidualStatusDrop reading) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall reading : ResidualBooleanStatusReading atlas,
        (canonicalResidualCutCochain atlas).CutNonzero <->
          ExistsResidualStatusDrop reading) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall reading : ResidualBooleanStatusReading atlas,
        ExistsResidualStatusDrop reading ->
          forall transition : Index -> Index -> Atom -> Atom,
            Not (AtlasResidualTransitionClosed atlas transition)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall reading : ResidualBooleanStatusReading atlas,
        ExistsResidualStatusDrop reading ->
          forall transition : Index -> Index -> Atom -> Atom,
            Not
              (Nonempty
                (TransitionCoherentAtlasData atlas transition))) /\
      ExistsResidualStatusDrop selectedFrontierFlatResidualStatusReading /\
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton).CutNonzero /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (AtlasResidualTransitionClosed
            selectedFrontierFlatAtlasSkeleton
            transition)) /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (Nonempty
            (TransitionCoherentAtlasData
              selectedFrontierFlatAtlasSkeleton
              transition))) := by
  exact
    ⟨fun {_Index} {_Atom} {_atlas} reading pair =>
        residualStatusDropPair_iff_residualCutPair reading pair,
      fun {_Index} {_Atom} {_atlas} reading =>
        canonicalResidualCutCochain_cutNoiseEquivalent_statusDrop reading,
      fun {_Index} {_Atom} {_atlas} reading =>
        canonicalResidualCutClass_vanishes_iff_noStatusDrop reading,
      fun {_Index} {_Atom} {_atlas} reading =>
        canonicalResidualCutClass_nonzero_iff_existsStatusDrop reading,
      fun {_Index} {_Atom} {_atlas} reading hdrop transition =>
        existsStatusDrop_obstructs_atlasTransitionClosure
          reading hdrop transition,
      fun {_Index} {_Atom} {_atlas} reading hdrop transition =>
        existsStatusDrop_obstructs_transitionCoherentData
          reading hdrop transition,
      selectedFrontierFlat_existsStatusDrop,
      selectedFrontierFlat_statusDrop_canonicalNonzero,
      selectedFrontierFlat_statusDrop_obstructs_transitionClosure,
      selectedFrontierFlat_statusDrop_obstructs_transitionCoherentData⟩

end SemanticResidualStatusDropAdapter
end QualitySurface
end Formal.AG.Research
