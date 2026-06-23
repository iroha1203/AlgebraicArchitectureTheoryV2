import Formal.AG.Research.QualitySurface.SemanticResidualAtlasGauge

/-!
Cycle 94 evidence for `G-aat-quality-surface-01`.

This file transports finite residual obstruction classes across explicitly
supplied residual cut-locus maps between finite semantic repair atlas
skeletons with possibly different index carriers.  A cut-locus embedding maps
source residual cut pairs to target residual cut pairs; a cut-locus
equivalence additionally covers every target residual cut.  Under these
finite hypotheses, cut-supported cochains push forward, nonzero obstruction
readings transport, and canonical vanishing/nonzero is invariant for
cut-surjective equivalences.

The result is cut-locus transport for supplied finite maps.  It does not
construct a category of atlases, arbitrary atlas morphisms, functorial sheaf
transport, a Cech `H^1` class, a coboundary quotient, a vanishing-to-closure
theorem, source extraction completeness, ArchMap correctness, runtime repair
synthesis, tooling runtime extraction, UI correctness, or whole-codebase
quality.
-/

universe u v w x

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualAtlasMorphism

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

/-! ## Residual cut-locus maps -/

/-- Map an index pair along an index map. -/
def mapResidualPair
    {LeftIndex : Type w}
    {RightIndex : Type x}
    (mapIndex : LeftIndex -> RightIndex)
    (pair : LeftIndex × LeftIndex) :
    RightIndex × RightIndex :=
  (mapIndex pair.1, mapIndex pair.2)

/--
A finite residual cut-locus embedding transports every source residual cut pair
to a target residual cut pair.
-/
structure ResidualCutLocusEmbedding
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    (left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom)
    (right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom) where
  mapIndex : LeftIndex -> RightIndex
  cut_preserving :
    forall pair,
      IsResidualTransitionCutPair left pair ->
        IsResidualTransitionCutPair right
          (mapResidualPair mapIndex pair)

/--
A finite residual cut-locus equivalence is a cut-locus embedding whose image
covers every target residual cut pair.
-/
structure ResidualCutLocusEquivalence
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    (left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom)
    (right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom)
    extends ResidualCutLocusEmbedding left right where
  cut_surjective :
    forall targetPair,
      IsResidualTransitionCutPair right targetPair ->
        exists sourcePair,
          IsResidualTransitionCutPair left sourcePair /\
            mapResidualPair mapIndex sourcePair = targetPair

/-! ## Pushforward of cut-supported cochains -/

/-- Push a raw residual cut cochain along a residual cut-locus embedding. -/
def pushResidualCutCochain
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    (sourceC : ResidualCutCochain left) :
    ResidualCutCochain right where
  support targetPair :=
    exists sourcePair,
      IsResidualTransitionCutPair left sourcePair /\
        sourceC.support sourcePair /\
          mapResidualPair embedding.mapIndex sourcePair = targetPair

/-- Source nonzero support pushes forward to target nonzero support. -/
theorem pushResidualCutCochain_nonzero_of_sourceNonzero
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    {sourceC : ResidualCutCochain left}
    (hnonzero : sourceC.CutNonzero) :
    (pushResidualCutCochain embedding sourceC).CutNonzero := by
  rcases hnonzero with ⟨sourcePair, hsourceCut, hsourceSupport⟩
  exact
    ⟨mapResidualPair embedding.mapIndex sourcePair,
      embedding.cut_preserving sourcePair hsourceCut,
      ⟨sourcePair, hsourceCut, hsourceSupport, rfl⟩⟩

/-- If the pushed target class vanishes, then the source class vanishes. -/
theorem pushResidualCutCochain_targetVanishes_to_sourceVanishes
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    {sourceC : ResidualCutCochain left}
    (htarget :
      (pushResidualCutCochain embedding sourceC).CutVanishes) :
    sourceC.CutVanishes := by
  intro sourcePair hsourceCut hsourceSupport
  exact
    htarget
      (mapResidualPair embedding.mapIndex sourcePair)
      (embedding.cut_preserving sourcePair hsourceCut)
      ⟨sourcePair, hsourceCut, hsourceSupport, rfl⟩

/-- If the source class vanishes, then its pushed target class vanishes. -/
theorem pushResidualCutCochain_sourceVanishes_to_targetVanishes
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    {sourceC : ResidualCutCochain left}
    (hsource : sourceC.CutVanishes) :
    (pushResidualCutCochain embedding sourceC).CutVanishes := by
  intro _targetPair _htargetCut hpush
  rcases hpush with ⟨sourcePair, hsourceCut, hsourceSupport, _hmap⟩
  exact hsource sourcePair hsourceCut hsourceSupport

/-- Pushforward preserves cut-locus vanishing exactly. -/
theorem pushResidualCutCochain_cutVanishes_iff
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    {sourceC : ResidualCutCochain left} :
    (pushResidualCutCochain embedding sourceC).CutVanishes <->
      sourceC.CutVanishes := by
  constructor
  · exact pushResidualCutCochain_targetVanishes_to_sourceVanishes
      embedding
  · exact pushResidualCutCochain_sourceVanishes_to_targetVanishes
      embedding

/-- Pushforward preserves cut-locus nonzero support exactly. -/
theorem pushResidualCutCochain_cutNonzero_iff
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    {sourceC : ResidualCutCochain left} :
    (pushResidualCutCochain embedding sourceC).CutNonzero <->
      sourceC.CutNonzero := by
  constructor
  · intro htarget
    rcases htarget with ⟨_targetPair, _htargetCut, hpush⟩
    rcases hpush with ⟨sourcePair, hsourceCut, hsourceSupport, _hmap⟩
    exact ⟨sourcePair, hsourceCut, hsourceSupport⟩
  · exact pushResidualCutCochain_nonzero_of_sourceNonzero
      embedding

/-- Source nonzero support obstructs target transition closure after pushforward. -/
theorem pushResidualCutCochain_nonzero_obstructs_targetTransitionClosure
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    {sourceC : ResidualCutCochain left}
    (hnonzero : sourceC.CutNonzero)
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (AtlasResidualTransitionClosed right transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (pushResidualCutCochain embedding sourceC)
      (pushResidualCutCochain_nonzero_of_sourceNonzero
        embedding hnonzero)
      transition

/-- Source nonzero support rules out target transition-coherent data after pushforward. -/
theorem pushResidualCutCochain_nonzero_obstructs_targetTransitionCoherentData
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (embedding : ResidualCutLocusEmbedding left right)
    {sourceC : ResidualCutCochain left}
    (hnonzero : sourceC.CutNonzero)
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (Nonempty (TransitionCoherentAtlasData right transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (pushResidualCutCochain embedding sourceC)
      (pushResidualCutCochain_nonzero_of_sourceNonzero
        embedding hnonzero)
      transition

/-! ## Canonical class transport under cut-surjective equivalences -/

/--
Under a cut-surjective equivalence, the pushforward of the canonical source
cochain agrees with the canonical target cochain on target cut pairs.
-/
theorem residualCutLocusEquivalence_pushCanonical_agrees_targetCanonical_onCut
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (equiv : ResidualCutLocusEquivalence left right)
    {targetPair : RightIndex × RightIndex}
    (htargetCut : IsResidualTransitionCutPair right targetPair) :
    (pushResidualCutCochain
        equiv.toResidualCutLocusEmbedding
        (canonicalResidualCutCochain left)).support targetPair <->
      (canonicalResidualCutCochain right).support targetPair := by
  constructor
  · intro hpush
    rcases hpush with ⟨sourcePair, hsourceCut, _hsourceSupport, hmap⟩
    exact
      by
        simpa [hmap] using
          equiv.cut_preserving sourcePair hsourceCut
  · intro _htargetSupport
    rcases equiv.cut_surjective targetPair htargetCut with
      ⟨sourcePair, hsourceCut, hmap⟩
    exact ⟨sourcePair, hsourceCut, hsourceCut, hmap⟩

/-- A cut-surjective equivalence preserves canonical cut-class vanishing. -/
theorem residualCutLocusEquivalence_preserves_canonicalCutVanishes
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (equiv : ResidualCutLocusEquivalence left right) :
    (canonicalResidualCutCochain left).CutVanishes <->
      (canonicalResidualCutCochain right).CutVanishes := by
  constructor
  · intro hleft targetPair htargetCut _htargetSupport
    rcases equiv.cut_surjective targetPair htargetCut with
      ⟨sourcePair, hsourceCut, _hmap⟩
    exact hleft sourcePair hsourceCut hsourceCut
  · intro hright sourcePair hsourceCut _hsourceSupport
    exact
      hright
        (mapResidualPair equiv.mapIndex sourcePair)
        (equiv.cut_preserving sourcePair hsourceCut)
        (equiv.cut_preserving sourcePair hsourceCut)

/-- A cut-surjective equivalence preserves canonical cut-class nonzero support. -/
theorem residualCutLocusEquivalence_preserves_canonicalCutNonzero
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (equiv : ResidualCutLocusEquivalence left right) :
    (canonicalResidualCutCochain left).CutNonzero <->
      (canonicalResidualCutCochain right).CutNonzero := by
  constructor
  · intro hleft
    rcases hleft with ⟨sourcePair, hsourceCut, _hsourceSupport⟩
    exact
      ⟨mapResidualPair equiv.mapIndex sourcePair,
        equiv.cut_preserving sourcePair hsourceCut,
        equiv.cut_preserving sourcePair hsourceCut⟩
  · intro hright
    rcases hright with ⟨targetPair, htargetCut, _htargetSupport⟩
    rcases equiv.cut_surjective targetPair htargetCut with
      ⟨sourcePair, hsourceCut, _hmap⟩
    exact ⟨sourcePair, hsourceCut, hsourceCut⟩

/-! ## Selected extended-carrier witness -/

/-- A selected atlas carrier with one isolated extra presentation index. -/
abbrev SelectedExtendedOverlapIndex :=
  Option SelectedSemanticOverlapIndex

/-- Embed the selected two-index carrier into the extended carrier. -/
def selectedToExtendedIndex
    (index : SelectedSemanticOverlapIndex) :
    SelectedExtendedOverlapIndex :=
  some index

/-- Read an extended index back through the selected presentation. -/
def selectedExtendedToSelectedIndex :
    SelectedExtendedOverlapIndex -> SelectedSemanticOverlapIndex
  | none => SelectedSemanticOverlapIndex.flat
  | some index => index

/-- The extended selected edge family has no active edges involving `none`. -/
def selectedExtendedFrontierFlatEdge
    (source target : SelectedExtendedOverlapIndex) : Prop :=
  match source, target with
  | some sourceIndex, some targetIndex =>
      selectedFrontierToFlatEdge sourceIndex targetIndex
  | _, _ => False

/--
The selected extended-carrier atlas adds an isolated presentation index while
reusing the selected projection and cover through `selectedExtendedToSelectedIndex`.
-/
def selectedExtendedFrontierFlatAtlasSkeleton :
    FiniteSemanticRepairAtlasSkeleton
      SelectedExtendedOverlapIndex
      RefinedSemanticRepairAtom where
  indexOrder :=
    [none,
      some SelectedSemanticOverlapIndex.flat,
      some SelectedSemanticOverlapIndex.repairFrontier]
  index_complete := by
    intro index
    cases index with
    | none => simp
    | some selected =>
        cases selected <;> simp
  atomOrder := selectedFrontierFlatAtlasSkeleton.atomOrder
  atom_complete := selectedFrontierFlatAtlasSkeleton.atom_complete
  edge := selectedExtendedFrontierFlatEdge
  projection index :=
    selectedIndexedProjection (selectedExtendedToSelectedIndex index)
  cover index :=
    selectedIndexedCover (selectedExtendedToSelectedIndex index)

/-- The isolated `none` index has no outgoing active edge. -/
theorem selectedExtended_none_no_outgoing_edge
    (target : SelectedExtendedOverlapIndex) :
    Not (selectedExtendedFrontierFlatAtlasSkeleton.edge none target) := by
  cases target <;> simp [selectedExtendedFrontierFlatAtlasSkeleton,
    selectedExtendedFrontierFlatEdge]

/-- The isolated `none` index has no incoming active edge. -/
theorem selectedExtended_none_no_incoming_edge
    (source : SelectedExtendedOverlapIndex) :
    Not (selectedExtendedFrontierFlatAtlasSkeleton.edge source none) := by
  cases source <;> simp [selectedExtendedFrontierFlatAtlasSkeleton,
    selectedExtendedFrontierFlatEdge]

/-- The isolated `none` index is never the source of a residual cut pair. -/
theorem selectedExtended_none_not_cut_source
    (target : SelectedExtendedOverlapIndex) :
    Not
      (IsResidualTransitionCutPair
        selectedExtendedFrontierFlatAtlasSkeleton
        (none, target)) := by
  intro hcut
  exact selectedExtended_none_no_outgoing_edge target hcut.1

/-- The isolated `none` index is never the target of a residual cut pair. -/
theorem selectedExtended_none_not_cut_target
    (source : SelectedExtendedOverlapIndex) :
    Not
      (IsResidualTransitionCutPair
        selectedExtendedFrontierFlatAtlasSkeleton
        (source, none)) := by
  intro hcut
  exact selectedExtended_none_no_incoming_edge source hcut.1

/-- The selected source cut locus embeds into the extended-carrier target. -/
def selectedToExtendedResidualCutEmbedding :
    ResidualCutLocusEmbedding
      selectedFrontierFlatAtlasSkeleton
      selectedExtendedFrontierFlatAtlasSkeleton where
  mapIndex := selectedToExtendedIndex
  cut_preserving := by
    intro pair hcut
    cases pair with
    | mk source target =>
        exact
          ⟨by
              simpa [mapResidualPair, selectedToExtendedIndex,
                selectedFrontierFlatAtlasSkeleton,
                selectedExtendedFrontierFlatAtlasSkeleton,
                selectedExtendedFrontierFlatEdge]
                using hcut.1,
            by
              simpa [mapResidualPair, selectedToExtendedIndex,
                selectedFrontierFlatAtlasSkeleton,
                selectedExtendedFrontierFlatAtlasSkeleton,
                selectedExtendedToSelectedIndex]
                using hcut.2.1,
            by
              simpa [mapResidualPair, selectedToExtendedIndex,
                selectedFrontierFlatAtlasSkeleton,
                selectedExtendedFrontierFlatAtlasSkeleton,
                selectedExtendedToSelectedIndex]
                using hcut.2.2⟩

/-- Every extended target residual cut comes from a selected source cut. -/
theorem selectedToExtended_cut_surjective :
    forall targetPair,
      IsResidualTransitionCutPair
        selectedExtendedFrontierFlatAtlasSkeleton targetPair ->
        exists sourcePair,
          IsResidualTransitionCutPair
            selectedFrontierFlatAtlasSkeleton sourcePair /\
            mapResidualPair selectedToExtendedIndex sourcePair =
              targetPair := by
  intro targetPair htargetCut
  cases targetPair with
  | mk source target =>
      cases source with
      | none =>
          exact False.elim
            ((selectedExtended_none_no_outgoing_edge target)
              htargetCut.1)
      | some sourceIndex =>
          cases target with
          | none =>
              exact False.elim
                ((selectedExtended_none_no_incoming_edge
                  (some sourceIndex)) htargetCut.1)
          | some targetIndex =>
              refine ⟨(sourceIndex, targetIndex), ?_, ?_⟩
              · exact
                  ⟨by
                      simpa [selectedFrontierFlatAtlasSkeleton,
                        selectedExtendedFrontierFlatAtlasSkeleton,
                        selectedExtendedFrontierFlatEdge]
                        using htargetCut.1,
                    by
                      simpa [selectedFrontierFlatAtlasSkeleton,
                        selectedExtendedFrontierFlatAtlasSkeleton,
                        selectedExtendedToSelectedIndex]
                        using htargetCut.2.1,
                    by
                      simpa [selectedFrontierFlatAtlasSkeleton,
                        selectedExtendedFrontierFlatAtlasSkeleton,
                        selectedExtendedToSelectedIndex]
                        using htargetCut.2.2⟩
              · rfl

/-- The selected source and extended target have equivalent residual cut loci. -/
def selectedToExtendedResidualCutEquivalence :
    ResidualCutLocusEquivalence
      selectedFrontierFlatAtlasSkeleton
      selectedExtendedFrontierFlatAtlasSkeleton where
  mapIndex := selectedToExtendedIndex
  cut_preserving :=
    selectedToExtendedResidualCutEmbedding.cut_preserving
  cut_surjective :=
    selectedToExtended_cut_surjective

/-- The selected nonzero canonical class pushes to the extended target. -/
theorem selectedExtended_pushCanonicalCutClass_nonzero :
    (pushResidualCutCochain
      selectedToExtendedResidualCutEmbedding
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton)).CutNonzero := by
  exact
    pushResidualCutCochain_nonzero_of_sourceNonzero
      selectedToExtendedResidualCutEmbedding
      selected_canonicalResidualCutClass_nonzero

/-- The selected extended canonical cut class is nonzero. -/
theorem selectedExtended_canonicalCutClass_nonzero :
    (canonicalResidualCutCochain
      selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    (residualCutLocusEquivalence_preserves_canonicalCutNonzero
      selectedToExtendedResidualCutEquivalence).mp
      selected_canonicalResidualCutClass_nonzero

/-- The selected extended canonical class obstructs target transition closure. -/
theorem selectedExtended_canonicalCutClass_obstructs_transitionClosure
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedExtendedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton)
      selectedExtended_canonicalCutClass_nonzero
      transition

/-- The selected extended canonical class rules out transition-coherent data. -/
theorem selectedExtended_canonicalCutClass_obstructs_transitionCoherentData
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedExtendedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton)
      selectedExtended_canonicalCutClass_nonzero
      transition

/-! ## Theorem package -/

/--
Cycle-94 theorem package: finite residual cut-locus embeddings push nonzero
cut-supported obstruction classes to target obstructions, and cut-surjective
equivalences preserve canonical vanishing/nonzero.  The selected extended
carrier witness adds an isolated index and transports the selected
frontier-to-flat obstruction across the carrier change.
-/
theorem semanticResidualAtlasMorphism_package :
    (forall {LeftIndex : Type w}
      {LeftAtom : Type u}
      {RightIndex : Type x}
      {RightAtom : Type v}
      {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
      {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
      forall embedding : ResidualCutLocusEmbedding left right,
      forall sourceC : ResidualCutCochain left,
        sourceC.CutNonzero ->
          (pushResidualCutCochain embedding sourceC).CutNonzero) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall embedding : ResidualCutLocusEmbedding left right,
        forall sourceC : ResidualCutCochain left,
          (pushResidualCutCochain embedding sourceC).CutVanishes ->
            sourceC.CutVanishes) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall embedding : ResidualCutLocusEmbedding left right,
        forall sourceC : ResidualCutCochain left,
          sourceC.CutVanishes ->
            (pushResidualCutCochain embedding sourceC).CutVanishes) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall embedding : ResidualCutLocusEmbedding left right,
        forall sourceC : ResidualCutCochain left,
          ((pushResidualCutCochain embedding sourceC).CutNonzero <->
            sourceC.CutNonzero)) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall _embedding : ResidualCutLocusEmbedding left right,
        forall sourceC : ResidualCutCochain left,
          sourceC.CutNonzero ->
            forall transition : RightIndex -> RightIndex -> RightAtom -> RightAtom,
              Not (AtlasResidualTransitionClosed right transition)) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall _embedding : ResidualCutLocusEmbedding left right,
        forall sourceC : ResidualCutCochain left,
          sourceC.CutNonzero ->
            forall transition : RightIndex -> RightIndex -> RightAtom -> RightAtom,
              Not (Nonempty (TransitionCoherentAtlasData right transition))) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall _equiv : ResidualCutLocusEquivalence left right,
        (canonicalResidualCutCochain left).CutVanishes <->
          (canonicalResidualCutCochain right).CutVanishes) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall _equiv : ResidualCutLocusEquivalence left right,
        (canonicalResidualCutCochain left).CutNonzero <->
          (canonicalResidualCutCochain right).CutNonzero) /\
      (forall target : SelectedExtendedOverlapIndex,
        Not (selectedExtendedFrontierFlatAtlasSkeleton.edge none target)) /\
      (forall source : SelectedExtendedOverlapIndex,
        Not (selectedExtendedFrontierFlatAtlasSkeleton.edge source none)) /\
      (forall target : SelectedExtendedOverlapIndex,
        Not
          (IsResidualTransitionCutPair
            selectedExtendedFrontierFlatAtlasSkeleton
            (none, target))) /\
      (forall source : SelectedExtendedOverlapIndex,
        Not
          (IsResidualTransitionCutPair
            selectedExtendedFrontierFlatAtlasSkeleton
            (source, none))) /\
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero /\
      (pushResidualCutCochain
        selectedToExtendedResidualCutEmbedding
        (canonicalResidualCutCochain
          selectedFrontierFlatAtlasSkeleton)).CutNonzero /\
      (forall
        transition :
          SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (AtlasResidualTransitionClosed
            selectedExtendedFrontierFlatAtlasSkeleton
            transition)) /\
      (forall
        transition :
          SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (Nonempty
            (TransitionCoherentAtlasData
              selectedExtendedFrontierFlatAtlasSkeleton
              transition))) := by
  exact
    ⟨fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} embedding sourceC hnonzero =>
        pushResidualCutCochain_nonzero_of_sourceNonzero
          embedding hnonzero,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} embedding sourceC htarget =>
        pushResidualCutCochain_targetVanishes_to_sourceVanishes
          embedding htarget,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} embedding sourceC hsource =>
        pushResidualCutCochain_sourceVanishes_to_targetVanishes
          embedding hsource,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} embedding sourceC =>
        pushResidualCutCochain_cutNonzero_iff
          (sourceC := sourceC) embedding,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} embedding sourceC hnonzero transition =>
        pushResidualCutCochain_nonzero_obstructs_targetTransitionClosure
          embedding hnonzero transition,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} embedding sourceC hnonzero transition =>
        pushResidualCutCochain_nonzero_obstructs_targetTransitionCoherentData
          embedding hnonzero transition,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} equiv =>
        residualCutLocusEquivalence_preserves_canonicalCutVanishes
          equiv,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} equiv =>
      residualCutLocusEquivalence_preserves_canonicalCutNonzero
          equiv,
      selectedExtended_none_no_outgoing_edge,
      selectedExtended_none_no_incoming_edge,
      selectedExtended_none_not_cut_source,
      selectedExtended_none_not_cut_target,
      selectedExtended_canonicalCutClass_nonzero,
      selectedExtended_pushCanonicalCutClass_nonzero,
      selectedExtended_canonicalCutClass_obstructs_transitionClosure,
      selectedExtended_canonicalCutClass_obstructs_transitionCoherentData⟩

end SemanticResidualAtlasMorphism
end QualitySurface
end Formal.AG.Research
