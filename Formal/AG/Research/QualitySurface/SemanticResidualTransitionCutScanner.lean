import Formal.AG.Research.QualitySurface.SemanticResidualTransitionCut

/-!
Cycle 90 evidence for `G-aat-quality-surface-01`.

This file turns the Cycle 89 residual transition cut certificate into a finite
scanner exactness theorem.  A supplied finite edge order can return the first
residual-present to residual-free active edge, and `none` is exact for absence
of such cut witnesses when the edge order covers the active edge family.

The result is edge-order-relative and cut-relative.  It does not assert that
absence of residual transition cuts implies residual transition closure, does
not assert a canonical global edge order, does not assert arbitrary sheaf
gluing or a Cech cohomology class, and does not assert source extraction
completeness, ArchMap correctness, runtime repair synthesis, UI correctness,
or whole-codebase quality.
-/

universe u w

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualTransitionCutScanner

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

/-! ## Finite cut scanner -/

/-- A pair of indices is a residual transition cut pair for the atlas. -/
def IsResidualTransitionCutPair
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (pair : Index × Index) : Prop :=
  atlas.edge pair.1 pair.2 /\
    IndexedResidualPresentAt atlas.projection atlas.cover pair.1 /\
      IndexedResidualFreeAt atlas.projection atlas.cover pair.2

/-- The supplied edge order contains every active atlas edge. -/
def ListedAtlasEdgesComplete
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (edgeOrder : List (Index × Index)) : Prop :=
  forall source target,
    atlas.edge source target ->
      (source, target) ∈ edgeOrder

/-- No listed edge pair is a residual transition cut. -/
def ListedResidualTransitionCutsClear
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (edgeOrder : List (Index × Index)) : Prop :=
  forall pair,
    pair ∈ edgeOrder ->
      Not (IsResidualTransitionCutPair atlas pair)

/-- A cut pair gives the structured residual transition cut certificate. -/
def residualTransitionCut_of_pair
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {pair : Index × Index}
    (hpair : IsResidualTransitionCutPair atlas pair) :
    ResidualTransitionCut atlas where
  sourceIndex := pair.1
  targetIndex := pair.2
  edge_active := hpair.1
  source_residual_present := hpair.2.1
  target_residual_free := hpair.2.2

/-- A structured residual transition cut determines its listed pair predicate. -/
theorem residualTransitionCut_pair_isCut
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cut : ResidualTransitionCut atlas) :
    IsResidualTransitionCutPair atlas
      (cut.sourceIndex, cut.targetIndex) := by
  exact
    ⟨cut.edge_active,
      cut.source_residual_present,
      cut.target_residual_free⟩

/-- The first residual transition cut in a supplied finite edge order. -/
def firstResidualTransitionCut?
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    [DecidablePred (IsResidualTransitionCutPair atlas)] :
    List (Index × Index) -> Option (Index × Index)
  | [] => none
  | pair :: rest =>
      if IsResidualTransitionCutPair atlas pair then
        some pair
      else
        firstResidualTransitionCut? atlas rest

/-- A returned pair is in the supplied edge order. -/
theorem firstResidualTransitionCut?_some_mem
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    [DecidablePred (IsResidualTransitionCutPair atlas)] :
    forall {edgeOrder : List (Index × Index)} {pair : Index × Index},
      firstResidualTransitionCut? atlas edgeOrder = some pair ->
        pair ∈ edgeOrder
  | [], _pair, hsome => by
      cases hsome
  | head :: rest, pair, hsome => by
      by_cases hcut : IsResidualTransitionCutPair atlas head
      · have hpair : pair = head := by
          simpa [firstResidualTransitionCut?, hcut] using hsome.symm
        subst pair
        simp
      · have htail :
          firstResidualTransitionCut? atlas rest = some pair := by
          simpa [firstResidualTransitionCut?, hcut] using hsome
        exact List.mem_cons_of_mem head
          (firstResidualTransitionCut?_some_mem atlas htail)

/-- A returned pair is an actual residual transition cut pair. -/
theorem firstResidualTransitionCut?_some_pairCut
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    [DecidablePred (IsResidualTransitionCutPair atlas)] :
    forall {edgeOrder : List (Index × Index)} {pair : Index × Index},
      firstResidualTransitionCut? atlas edgeOrder = some pair ->
        IsResidualTransitionCutPair atlas pair
  | [], _pair, hsome => by
      cases hsome
  | head :: rest, pair, hsome => by
      by_cases hcut : IsResidualTransitionCutPair atlas head
      · have hpair : pair = head := by
          simpa [firstResidualTransitionCut?, hcut] using hsome.symm
        subst pair
        exact hcut
      · have htail :
          firstResidualTransitionCut? atlas rest = some pair := by
          simpa [firstResidualTransitionCut?, hcut] using hsome
        exact firstResidualTransitionCut?_some_pairCut atlas htail

/-- A returned pair gives the structured residual transition cut certificate. -/
def firstResidualTransitionCut?_some_cut
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan :
      firstResidualTransitionCut? atlas edgeOrder = some pair) :
    ResidualTransitionCut atlas :=
  residualTransitionCut_of_pair
    (firstResidualTransitionCut?_some_pairCut atlas hscan)

/-- A returned scanner cut obstructs atlas-wide residual transition closure. -/
theorem firstResidualTransitionCut?_some_obstructs_atlasTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan :
      firstResidualTransitionCut? atlas edgeOrder = some pair)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed atlas transition) := by
  exact
    residualTransitionCut_obstructs_atlasTransitionClosure
      (firstResidualTransitionCut?_some_cut hscan)
      transition

/-- A returned scanner cut obstructs transition-coherent atlas data. -/
theorem firstResidualTransitionCut?_some_obstructs_transitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan :
      firstResidualTransitionCut? atlas edgeOrder = some pair)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData atlas transition)) := by
  exact
    residualTransitionCut_obstructs_transitionCoherentData
      (firstResidualTransitionCut?_some_cut hscan)
      transition

/--
The returned pair is preceded only by listed non-cuts in the supplied order.
This is order-relative minimality, not an absolute minimal cut claim.
-/
def PrefixBeforeFirstCut
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (pair : Index × Index)
    (edgeOrder : List (Index × Index)) : Prop :=
  exists front back,
    edgeOrder = front ++ (pair :: back) /\
      ListedResidualTransitionCutsClear atlas front

/-- A returned scanner pair is order-minimal relative to the supplied list. -/
theorem firstResidualTransitionCut?_some_prefixClear
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    [DecidablePred (IsResidualTransitionCutPair atlas)] :
    forall {edgeOrder : List (Index × Index)} {pair : Index × Index},
      firstResidualTransitionCut? atlas edgeOrder = some pair ->
        PrefixBeforeFirstCut atlas pair edgeOrder
  | [], _pair, hsome => by
      cases hsome
  | head :: rest, pair, hsome => by
      by_cases hcut : IsResidualTransitionCutPair atlas head
      · have hpair : pair = head := by
          simpa [firstResidualTransitionCut?, hcut] using hsome.symm
        subst pair
        refine ⟨[], rest, by simp, ?_⟩
        intro candidate hmem _hcandidate
        cases hmem
      · have htail :
          firstResidualTransitionCut? atlas rest = some pair := by
          simpa [firstResidualTransitionCut?, hcut] using hsome
        rcases firstResidualTransitionCut?_some_prefixClear atlas htail with
          ⟨front, back, hrest, hfrontClear⟩
        refine ⟨head :: front, back, ?_, ?_⟩
        · simp [hrest]
        · intro candidate hmem hcandidate
          cases hmem with
          | head =>
              exact hcut hcandidate
          | tail _ hfront =>
              exact hfrontClear candidate hfront hcandidate

/--
The scanner returns `none` exactly when the supplied edge order is clear of
residual transition cut pairs.
-/
theorem firstResidualTransitionCut?_none_iff_listedCutsClear
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    [DecidablePred (IsResidualTransitionCutPair atlas)] :
    forall edgeOrder,
      firstResidualTransitionCut? atlas edgeOrder = none <->
        ListedResidualTransitionCutsClear atlas edgeOrder
  | [] => by
      constructor
      · intro _ pair hmem _hpair
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone pair hmem hpair
        by_cases hcut : IsResidualTransitionCutPair atlas head
        · have hsome :
            firstResidualTransitionCut? atlas (head :: rest) =
              some head := by
            simp [firstResidualTransitionCut?, hcut]
          rw [hsome] at hnone
          cases hnone
        · have htail :
            firstResidualTransitionCut? atlas rest = none := by
            simpa [firstResidualTransitionCut?, hcut] using hnone
          cases hmem with
          | head =>
              exact hcut hpair
          | tail _ hlisted =>
              exact
                ((firstResidualTransitionCut?_none_iff_listedCutsClear
                  atlas rest).mp htail) pair hlisted hpair
      · intro hclear
        by_cases hcut : IsResidualTransitionCutPair atlas head
        · have hnot :
            Not (IsResidualTransitionCutPair atlas head) :=
            hclear head (by simp)
          exact False.elim (hnot hcut)
        · have hrestClear :
            ListedResidualTransitionCutsClear atlas rest := by
            intro pair hmem hpair
            exact hclear pair (by simp [hmem]) hpair
          have htailNone :
            firstResidualTransitionCut? atlas rest = none :=
            (firstResidualTransitionCut?_none_iff_listedCutsClear
              atlas rest).mpr hrestClear
          simp [firstResidualTransitionCut?, hcut, htailNone]

/--
For a complete supplied edge order, `none` is exact for absence of residual
transition cut certificates.
-/
theorem firstResidualTransitionCut?_none_iff_noResidualTransitionCut
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    (hcomplete : ListedAtlasEdgesComplete atlas edgeOrder) :
    firstResidualTransitionCut? atlas edgeOrder = none <->
      Not (Nonempty (ResidualTransitionCut atlas)) := by
  constructor
  · intro hnone hcut
    rcases hcut with ⟨cut⟩
    have hclear :
        ListedResidualTransitionCutsClear atlas edgeOrder :=
      (firstResidualTransitionCut?_none_iff_listedCutsClear
        atlas edgeOrder).mp hnone
    exact
      hclear
        (cut.sourceIndex, cut.targetIndex)
        (hcomplete cut.sourceIndex cut.targetIndex cut.edge_active)
        (residualTransitionCut_pair_isCut cut)
  · intro hnocut
    apply
      (firstResidualTransitionCut?_none_iff_listedCutsClear
        atlas edgeOrder).mpr
    intro pair _hmem hpair
    exact hnocut ⟨residualTransitionCut_of_pair hpair⟩

/-! ## Selected frontier-to-flat scanner witness -/

/-- A selected edge order whose second edge is the frontier-to-flat cut. -/
def selectedFrontierFlatScanOrder :
    List
      (SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex) :=
  [(SelectedSemanticOverlapIndex.flat,
      SelectedSemanticOverlapIndex.repairFrontier),
    (SelectedSemanticOverlapIndex.repairFrontier,
      SelectedSemanticOverlapIndex.flat)]

/-- The selected scanner predicate is decidable without classical choice. -/
instance selectedFrontierFlatCutPairDecidable :
    DecidablePred
      (IsResidualTransitionCutPair selectedFrontierFlatAtlasSkeleton) := by
  intro pair
  cases pair with
  | mk source target =>
      cases source <;> cases target
      · apply isFalse
        intro hcut
        exact
          (by
            simpa [IsResidualTransitionCutPair,
              selectedFrontierFlatAtlasSkeleton,
              selectedFrontierToFlatEdge] using hcut.1)
      · apply isFalse
        intro hcut
        exact
          (by
            simpa [IsResidualTransitionCutPair,
              selectedFrontierFlatAtlasSkeleton,
              selectedFrontierToFlatEdge] using hcut.1)
      · apply isTrue
        exact
          residualTransitionCut_pair_isCut
            selectedFrontierFlatResidualTransitionCut
      · apply isFalse
        intro hcut
        exact
          (by
            simpa [IsResidualTransitionCutPair,
              selectedFrontierFlatAtlasSkeleton,
              selectedFrontierToFlatEdge] using hcut.1)

/-- The selected finite scanner returns the frontier-to-flat cut. -/
theorem selected_firstResidualTransitionCut :
    firstResidualTransitionCut?
        selectedFrontierFlatAtlasSkeleton
        selectedFrontierFlatScanOrder =
      some
        (SelectedSemanticOverlapIndex.repairFrontier,
          SelectedSemanticOverlapIndex.flat) := by
  have hfirst :
      Not
        (IsResidualTransitionCutPair
          selectedFrontierFlatAtlasSkeleton
          (SelectedSemanticOverlapIndex.flat,
            SelectedSemanticOverlapIndex.repairFrontier)) := by
    intro hcut
    exact
      (by
        simpa [IsResidualTransitionCutPair,
          selectedFrontierFlatAtlasSkeleton,
          selectedFrontierToFlatEdge] using hcut.1)
  have hsecond :
      IsResidualTransitionCutPair
        selectedFrontierFlatAtlasSkeleton
        (SelectedSemanticOverlapIndex.repairFrontier,
          SelectedSemanticOverlapIndex.flat) :=
    residualTransitionCut_pair_isCut
      selectedFrontierFlatResidualTransitionCut
  simp [selectedFrontierFlatScanOrder, firstResidualTransitionCut?,
    hfirst, hsecond]

/-- The selected scanner result is order-minimal relative to the supplied list. -/
theorem selected_firstResidualTransitionCut_prefixClear :
    PrefixBeforeFirstCut
      selectedFrontierFlatAtlasSkeleton
      (SelectedSemanticOverlapIndex.repairFrontier,
        SelectedSemanticOverlapIndex.flat)
      selectedFrontierFlatScanOrder := by
  exact
    firstResidualTransitionCut?_some_prefixClear
      selectedFrontierFlatAtlasSkeleton
      selected_firstResidualTransitionCut

/-- The selected scanner result obstructs frontier-to-flat transition closure. -/
theorem selected_firstResidualTransitionCut_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    firstResidualTransitionCut?_some_obstructs_atlasTransitionClosure
      selected_firstResidualTransitionCut
      transition

/-- The selected scanner result obstructs transition-coherent atlas data. -/
theorem selected_firstResidualTransitionCut_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    firstResidualTransitionCut?_some_obstructs_transitionCoherentData
      selected_firstResidualTransitionCut
      transition

/-! ## Theorem package -/

/--
Cycle-90 theorem package: a finite edge-order scanner returns proof-carrying
residual transition cut certificates, `none` is exact for absence of such cuts
under edge-order completeness, and the selected frontier-to-flat atlas realizes
the order-minimal scanner witness.
-/
theorem semanticResidualTransitionCutScanner_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
      [DecidablePred (IsResidualTransitionCutPair atlas)]
      {edgeOrder : List (Index × Index)}
      {pair : Index × Index},
      firstResidualTransitionCut? atlas edgeOrder = some pair ->
        Nonempty (ResidualTransitionCut atlas)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        [DecidablePred (IsResidualTransitionCutPair atlas)]
        {edgeOrder : List (Index × Index)}
        {pair : Index × Index},
        firstResidualTransitionCut? atlas edgeOrder = some pair ->
          PrefixBeforeFirstCut atlas pair edgeOrder) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        [DecidablePred (IsResidualTransitionCutPair atlas)]
        {edgeOrder : List (Index × Index)},
        ListedAtlasEdgesComplete atlas edgeOrder ->
          (firstResidualTransitionCut? atlas edgeOrder = none <->
            Not (Nonempty (ResidualTransitionCut atlas)))) /\
      firstResidualTransitionCut?
          selectedFrontierFlatAtlasSkeleton
          selectedFrontierFlatScanOrder =
        some
          (SelectedSemanticOverlapIndex.repairFrontier,
            SelectedSemanticOverlapIndex.flat) /\
      PrefixBeforeFirstCut
        selectedFrontierFlatAtlasSkeleton
        (SelectedSemanticOverlapIndex.repairFrontier,
          SelectedSemanticOverlapIndex.flat)
        selectedFrontierFlatScanOrder /\
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
    ⟨fun {_Index} {_Atom} {_atlas} {_inst} {_edgeOrder} {_pair} hscan =>
        ⟨firstResidualTransitionCut?_some_cut hscan⟩,
      fun {_Index} {_Atom} {_atlas} {_inst} {_edgeOrder} {_pair} hscan =>
        firstResidualTransitionCut?_some_prefixClear _ hscan,
      fun {_Index} {_Atom} {_atlas} {_inst} {_edgeOrder} hcomplete =>
        firstResidualTransitionCut?_none_iff_noResidualTransitionCut
          hcomplete,
      selected_firstResidualTransitionCut,
      selected_firstResidualTransitionCut_prefixClear,
      selected_firstResidualTransitionCut_obstructs_transitionClosure,
      selected_firstResidualTransitionCut_obstructs_transitionCoherentData⟩

end SemanticResidualTransitionCutScanner
end QualitySurface
end Formal.AG.Research
