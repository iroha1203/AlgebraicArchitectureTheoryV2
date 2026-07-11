import ResearchLean.AG.QualitySurface.SemanticResidualAtlasMorphism

/-!
Cycle 95 evidence for `G-aat-quality-surface-01`.

This file derives the Cycle 94 residual cut-locus transport from decomposed
finite atlas laws.  A residual cut-inducing atlas map preserves active edges,
residual-present indices, and residual-free indices; these three laws imply
that residual cut pairs transport.  A residual cut-covering atlas map also
lifts target edge/present/free cut data to source data; this induces the
cut-surjectivity needed for canonical vanishing/nonzero equivalence.

The result is an induction layer for finite cut-locus transport.  It does not
construct arbitrary atlas categories, atom maps, projection/cover naturality,
functorial sheaf transport, a Cech `H^1` class, a coboundary quotient,
vanishing-to-closure, source extraction completeness, ArchMap correctness,
runtime repair synthesis, tooling runtime extraction, UI correctness, or
whole-codebase quality.
-/

universe u v w x

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualAtlasMapLaws

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
open SemanticResidualAtlasMorphism

/-! ## Atlas laws inducing residual cut transport -/

/--
A residual cut-inducing atlas map preserves the three pieces of residual cut
data: active edge, residual-present source, and residual-free target.
-/
structure ResidualCutInducingAtlasMap
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    (left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom)
    (right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom) where
  mapIndex : LeftIndex -> RightIndex
  edge_preserving :
    forall source target,
      left.edge source target ->
        right.edge (mapIndex source) (mapIndex target)
  residual_present_preserving :
    forall index,
      IndexedResidualPresentAt left.projection left.cover index ->
        IndexedResidualPresentAt right.projection right.cover
          (mapIndex index)
  residual_free_preserving :
    forall index,
      IndexedResidualFreeAt left.projection left.cover index ->
        IndexedResidualFreeAt right.projection right.cover
          (mapIndex index)

/-- The three preservation laws induce residual cut-pair preservation. -/
theorem residualCutInducingAtlasMap_preserves_residualCutPair
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap left right)
    {pair : LeftIndex × LeftIndex}
    (hcut : IsResidualTransitionCutPair left pair) :
    IsResidualTransitionCutPair right
      (mapResidualPair atlasMap.mapIndex pair) := by
  exact
    ⟨atlasMap.edge_preserving pair.1 pair.2 hcut.1,
      atlasMap.residual_present_preserving pair.1 hcut.2.1,
      atlasMap.residual_free_preserving pair.2 hcut.2.2⟩

/-- A residual cut-inducing atlas map gives a Cycle-94 cut-locus embedding. -/
def residualCutInducingAtlasMap_to_cutLocusEmbedding
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap left right) :
    ResidualCutLocusEmbedding left right where
  mapIndex := atlasMap.mapIndex
  cut_preserving := by
    intro pair hcut
    exact residualCutInducingAtlasMap_preserves_residualCutPair
      atlasMap hcut

/-- A cut-inducing map pushes source nonzero support to target nonzero support. -/
theorem residualCutInducingAtlasMap_push_nonzero
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap left right)
    {sourceC : ResidualCutCochain left}
    (hnonzero : sourceC.CutNonzero) :
    (pushResidualCutCochain
      (residualCutInducingAtlasMap_to_cutLocusEmbedding atlasMap)
      sourceC).CutNonzero := by
  exact
    pushResidualCutCochain_nonzero_of_sourceNonzero
      (residualCutInducingAtlasMap_to_cutLocusEmbedding atlasMap)
      hnonzero

/-- A cut-inducing map transports source nonzero support to target closure obstruction. -/
theorem residualCutInducingAtlasMap_nonzero_obstructs_targetTransitionClosure
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap left right)
    {sourceC : ResidualCutCochain left}
    (hnonzero : sourceC.CutNonzero)
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (AtlasResidualTransitionClosed right transition) := by
  exact
    pushResidualCutCochain_nonzero_obstructs_targetTransitionClosure
      (residualCutInducingAtlasMap_to_cutLocusEmbedding atlasMap)
      hnonzero
      transition

/-- A cut-inducing map transports source nonzero support to target data obstruction. -/
theorem residualCutInducingAtlasMap_nonzero_obstructs_targetTransitionCoherentData
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutInducingAtlasMap left right)
    {sourceC : ResidualCutCochain left}
    (hnonzero : sourceC.CutNonzero)
    (transition : RightIndex -> RightIndex -> RightAtom -> RightAtom) :
    Not (Nonempty (TransitionCoherentAtlasData right transition)) := by
  exact
    pushResidualCutCochain_nonzero_obstructs_targetTransitionCoherentData
      (residualCutInducingAtlasMap_to_cutLocusEmbedding atlasMap)
      hnonzero
      transition

/-! ## Covering laws inducing cut-surjective equivalences -/

/--
A residual cut-covering atlas map also lifts each target edge/present/free cut
datum to source edge/present/free data.
-/
structure ResidualCutCoveringAtlasMap
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    (left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom)
    (right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom)
    extends ResidualCutInducingAtlasMap left right where
  target_cut_data_lift :
    forall targetSource targetTarget,
      right.edge targetSource targetTarget ->
        IndexedResidualPresentAt right.projection right.cover targetSource ->
          IndexedResidualFreeAt right.projection right.cover targetTarget ->
            exists sourceSource sourceTarget,
              left.edge sourceSource sourceTarget /\
                IndexedResidualPresentAt left.projection left.cover sourceSource /\
                  IndexedResidualFreeAt left.projection left.cover sourceTarget /\
                    mapIndex sourceSource = targetSource /\
                      mapIndex sourceTarget = targetTarget

/-- The covering law supplies target cut-surjectivity. -/
theorem residualCutCoveringAtlasMap_cut_surjective
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutCoveringAtlasMap left right) :
    forall targetPair,
      IsResidualTransitionCutPair right targetPair ->
        exists sourcePair,
          IsResidualTransitionCutPair left sourcePair /\
            mapResidualPair atlasMap.mapIndex sourcePair =
              targetPair := by
  intro targetPair htargetCut
  rcases
      atlasMap.target_cut_data_lift
        targetPair.1 targetPair.2
        htargetCut.1 htargetCut.2.1 htargetCut.2.2 with
    ⟨sourceSource, sourceTarget, hedge, hpresent, hfree, hsource, htarget⟩
  refine
    ⟨(sourceSource, sourceTarget),
      ⟨hedge, hpresent, hfree⟩, ?_⟩
  simp [mapResidualPair, hsource, htarget]

/-- A cut-covering map gives a Cycle-94 cut-locus equivalence. -/
def residualCutCoveringAtlasMap_to_cutLocusEquivalence
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutCoveringAtlasMap left right) :
    ResidualCutLocusEquivalence left right where
  mapIndex := atlasMap.mapIndex
  cut_preserving := by
    intro pair hcut
    exact residualCutInducingAtlasMap_preserves_residualCutPair
      atlasMap.toResidualCutInducingAtlasMap hcut
  cut_surjective :=
    residualCutCoveringAtlasMap_cut_surjective atlasMap

/-- A cut-covering map preserves canonical cut-class vanishing. -/
theorem residualCutCoveringAtlasMap_preserves_canonicalCutVanishes
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutCoveringAtlasMap left right) :
    (canonicalResidualCutCochain left).CutVanishes <->
      (canonicalResidualCutCochain right).CutVanishes := by
  exact
    residualCutLocusEquivalence_preserves_canonicalCutVanishes
      (residualCutCoveringAtlasMap_to_cutLocusEquivalence atlasMap)

/-- A cut-covering map preserves canonical cut-class nonzero support. -/
theorem residualCutCoveringAtlasMap_preserves_canonicalCutNonzero
    {LeftIndex : Type w}
    {LeftAtom : Type u}
    {RightIndex : Type x}
    {RightAtom : Type v}
    {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
    {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom}
    (atlasMap : ResidualCutCoveringAtlasMap left right) :
    (canonicalResidualCutCochain left).CutNonzero <->
      (canonicalResidualCutCochain right).CutNonzero := by
  exact
    residualCutLocusEquivalence_preserves_canonicalCutNonzero
      (residualCutCoveringAtlasMap_to_cutLocusEquivalence atlasMap)

/-! ## Selected extended-carrier structural map -/

/-- The selected-to-extended index map preserves raw edges. -/
theorem selectedToExtended_edge_preserving :
    forall source target,
      selectedFrontierFlatAtlasSkeleton.edge source target ->
        selectedExtendedFrontierFlatAtlasSkeleton.edge
          (selectedToExtendedIndex source)
          (selectedToExtendedIndex target) := by
  intro source target hedge
  simpa [selectedFrontierFlatAtlasSkeleton,
    selectedExtendedFrontierFlatAtlasSkeleton,
    selectedExtendedFrontierFlatEdge,
    selectedToExtendedIndex]
    using hedge

/-- The selected-to-extended map preserves residual-present indices. -/
theorem selectedToExtended_residual_present_preserving :
    forall index,
      IndexedResidualPresentAt
          selectedFrontierFlatAtlasSkeleton.projection
          selectedFrontierFlatAtlasSkeleton.cover
          index ->
        IndexedResidualPresentAt
          selectedExtendedFrontierFlatAtlasSkeleton.projection
          selectedExtendedFrontierFlatAtlasSkeleton.cover
          (selectedToExtendedIndex index) := by
  intro index hpresent
  simpa [selectedFrontierFlatAtlasSkeleton,
    selectedExtendedFrontierFlatAtlasSkeleton,
    selectedExtendedToSelectedIndex,
    selectedToExtendedIndex]
    using hpresent

/-- The selected-to-extended map preserves residual-free indices. -/
theorem selectedToExtended_residual_free_preserving :
    forall index,
      IndexedResidualFreeAt
          selectedFrontierFlatAtlasSkeleton.projection
          selectedFrontierFlatAtlasSkeleton.cover
          index ->
        IndexedResidualFreeAt
          selectedExtendedFrontierFlatAtlasSkeleton.projection
          selectedExtendedFrontierFlatAtlasSkeleton.cover
          (selectedToExtendedIndex index) := by
  intro index hfree
  simpa [selectedFrontierFlatAtlasSkeleton,
    selectedExtendedFrontierFlatAtlasSkeleton,
    selectedExtendedToSelectedIndex,
    selectedToExtendedIndex]
    using hfree

/-- The selected-to-extended map is cut-inducing by structural laws. -/
def selectedToExtendedResidualCutInducingMap :
    ResidualCutInducingAtlasMap
      selectedFrontierFlatAtlasSkeleton
      selectedExtendedFrontierFlatAtlasSkeleton where
  mapIndex := selectedToExtendedIndex
  edge_preserving := selectedToExtended_edge_preserving
  residual_present_preserving :=
    selectedToExtended_residual_present_preserving
  residual_free_preserving :=
    selectedToExtended_residual_free_preserving

/-- The selected-to-extended map lifts every target cut datum to source data. -/
theorem selectedToExtended_target_cut_data_lift :
    forall targetSource targetTarget,
      selectedExtendedFrontierFlatAtlasSkeleton.edge targetSource targetTarget ->
        IndexedResidualPresentAt
          selectedExtendedFrontierFlatAtlasSkeleton.projection
          selectedExtendedFrontierFlatAtlasSkeleton.cover
          targetSource ->
          IndexedResidualFreeAt
            selectedExtendedFrontierFlatAtlasSkeleton.projection
            selectedExtendedFrontierFlatAtlasSkeleton.cover
            targetTarget ->
            exists sourceSource sourceTarget,
              selectedFrontierFlatAtlasSkeleton.edge sourceSource sourceTarget /\
                IndexedResidualPresentAt
                  selectedFrontierFlatAtlasSkeleton.projection
                  selectedFrontierFlatAtlasSkeleton.cover
                  sourceSource /\
                  IndexedResidualFreeAt
                    selectedFrontierFlatAtlasSkeleton.projection
                    selectedFrontierFlatAtlasSkeleton.cover
                    sourceTarget /\
                    selectedToExtendedIndex sourceSource = targetSource /\
                      selectedToExtendedIndex sourceTarget = targetTarget := by
  intro targetSource targetTarget hedge hpresent hfree
  cases targetSource with
  | none =>
      exact False.elim
        ((selectedExtended_none_no_outgoing_edge targetTarget) hedge)
  | some sourceSource =>
      cases targetTarget with
      | none =>
          exact False.elim
            ((selectedExtended_none_no_incoming_edge
              (some sourceSource)) hedge)
      | some sourceTarget =>
          refine ⟨sourceSource, sourceTarget, ?_, ?_, ?_, rfl, rfl⟩
          · simpa [selectedFrontierFlatAtlasSkeleton,
              selectedExtendedFrontierFlatAtlasSkeleton,
              selectedExtendedFrontierFlatEdge]
              using hedge
          · simpa [selectedFrontierFlatAtlasSkeleton,
              selectedExtendedFrontierFlatAtlasSkeleton,
              selectedExtendedToSelectedIndex]
              using hpresent
          · simpa [selectedFrontierFlatAtlasSkeleton,
              selectedExtendedFrontierFlatAtlasSkeleton,
              selectedExtendedToSelectedIndex]
              using hfree

/-- The selected-to-extended map is cut-covering by structural laws. -/
def selectedToExtendedResidualCutCoveringMap :
    ResidualCutCoveringAtlasMap
      selectedFrontierFlatAtlasSkeleton
      selectedExtendedFrontierFlatAtlasSkeleton where
  mapIndex := selectedToExtendedIndex
  edge_preserving := selectedToExtended_edge_preserving
  residual_present_preserving :=
    selectedToExtended_residual_present_preserving
  residual_free_preserving :=
    selectedToExtended_residual_free_preserving
  target_cut_data_lift :=
    selectedToExtended_target_cut_data_lift

/-- The structural selected map induces the Cycle-94 cut-locus embedding. -/
theorem selectedToExtended_structural_push_nonzero :
    (pushResidualCutCochain
      (residualCutInducingAtlasMap_to_cutLocusEmbedding
        selectedToExtendedResidualCutInducingMap)
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton)).CutNonzero := by
  exact
    residualCutInducingAtlasMap_push_nonzero
      selectedToExtendedResidualCutInducingMap
      selected_canonicalResidualCutClass_nonzero

/-- The structural selected map preserves canonical nonzero support. -/
theorem selectedToExtended_structural_canonicalCutClass_nonzero :
    (canonicalResidualCutCochain
      selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    (residualCutCoveringAtlasMap_preserves_canonicalCutNonzero
      selectedToExtendedResidualCutCoveringMap).mp
      selected_canonicalResidualCutClass_nonzero

/-- The structurally induced extended canonical class obstructs closure. -/
theorem selectedToExtended_structural_obstructs_transitionClosure
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedExtendedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    residualCutInducingAtlasMap_nonzero_obstructs_targetTransitionClosure
      selectedToExtendedResidualCutInducingMap
      selected_canonicalResidualCutClass_nonzero
      transition

/-- The structurally induced extended canonical class rules out coherent data. -/
theorem selectedToExtended_structural_obstructs_transitionCoherentData
    (transition :
      SelectedExtendedOverlapIndex -> SelectedExtendedOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedExtendedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    residualCutInducingAtlasMap_nonzero_obstructs_targetTransitionCoherentData
      selectedToExtendedResidualCutInducingMap
      selected_canonicalResidualCutClass_nonzero
      transition

/-! ## Theorem package -/

/--
Cycle-95 theorem package: edge preservation, residual-present preservation,
and residual-free preservation induce Cycle-94 cut-locus transport.  A
covering law for target edge/present/free data induces cut-surjectivity and
canonical vanishing/nonzero equivalence.  The selected extended-carrier map
realizes these structural laws.
-/
theorem semanticResidualAtlasMapLaws_package :
    (forall {LeftIndex : Type w}
      {LeftAtom : Type u}
      {RightIndex : Type x}
      {RightAtom : Type v}
      {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
      {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
      forall atlasMap : ResidualCutInducingAtlasMap left right,
      forall pair : LeftIndex × LeftIndex,
        IsResidualTransitionCutPair left pair ->
          IsResidualTransitionCutPair right
            (mapResidualPair atlasMap.mapIndex pair)) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall atlasMap : ResidualCutInducingAtlasMap left right,
        forall sourceC : ResidualCutCochain left,
          sourceC.CutNonzero ->
            (pushResidualCutCochain
              (residualCutInducingAtlasMap_to_cutLocusEmbedding atlasMap)
              sourceC).CutNonzero) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall _atlasMap : ResidualCutInducingAtlasMap left right,
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
        forall _atlasMap : ResidualCutInducingAtlasMap left right,
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
        forall _atlasMap : ResidualCutCoveringAtlasMap left right,
        (canonicalResidualCutCochain left).CutVanishes <->
          (canonicalResidualCutCochain right).CutVanishes) /\
      (forall {LeftIndex : Type w}
        {LeftAtom : Type u}
        {RightIndex : Type x}
        {RightAtom : Type v}
        {left : FiniteSemanticRepairAtlasSkeleton LeftIndex LeftAtom}
        {right : FiniteSemanticRepairAtlasSkeleton RightIndex RightAtom},
        forall _atlasMap : ResidualCutCoveringAtlasMap left right,
        (canonicalResidualCutCochain left).CutNonzero <->
          (canonicalResidualCutCochain right).CutNonzero) /\
      (canonicalResidualCutCochain
        selectedExtendedFrontierFlatAtlasSkeleton).CutNonzero /\
      (pushResidualCutCochain
        (residualCutInducingAtlasMap_to_cutLocusEmbedding
          selectedToExtendedResidualCutInducingMap)
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
        {_left} {_right} atlasMap pair hcut =>
        residualCutInducingAtlasMap_preserves_residualCutPair
          atlasMap hcut,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} atlasMap sourceC hnonzero =>
        residualCutInducingAtlasMap_push_nonzero
          atlasMap hnonzero,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} atlasMap sourceC hnonzero transition =>
        residualCutInducingAtlasMap_nonzero_obstructs_targetTransitionClosure
          atlasMap hnonzero transition,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} atlasMap sourceC hnonzero transition =>
        residualCutInducingAtlasMap_nonzero_obstructs_targetTransitionCoherentData
          atlasMap hnonzero transition,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} atlasMap =>
        residualCutCoveringAtlasMap_preserves_canonicalCutVanishes
          atlasMap,
      fun {_LeftIndex} {_LeftAtom} {_RightIndex} {_RightAtom}
        {_left} {_right} atlasMap =>
        residualCutCoveringAtlasMap_preserves_canonicalCutNonzero
          atlasMap,
      selectedToExtended_structural_canonicalCutClass_nonzero,
      selectedToExtended_structural_push_nonzero,
      selectedToExtended_structural_obstructs_transitionClosure,
      selectedToExtended_structural_obstructs_transitionCoherentData⟩

end SemanticResidualAtlasMapLaws
end QualitySurface
end ResearchLean.AG
