import Formal.AG.Research.QualitySurface.SemanticResidualTransitionCutScanner

/-!
Cycle 91 evidence for `G-aat-quality-surface-01`.

This file turns residual transition cuts into a finite degree-one obstruction
preclass for semantic repair atlases.  The preclass is an edge-supported
predicate exact for residual transition cut pairs.  Its vanishing is exactly
absence of residual transition cut certificates, and its nonzero support
obstructs residual transition closure and transition-coherent atlas data.

The result is a preclass criterion, not a Cech cohomology class.  It does not
construct a coboundary quotient, does not assert arbitrary sheaf gluing, does
not assert that vanishing implies residual transition closure, and does not
assert source extraction completeness, ArchMap correctness, runtime repair
synthesis, UI correctness, or whole-codebase quality.
-/

universe u w

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualObstructionPreclass

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

/-! ## Residual obstruction one-preclass -/

/--
A finite degree-one obstruction preclass for a semantic repair atlas.
Its support predicate is exact for residual transition cut pairs.
-/
structure ResidualObstructionOnePreclass
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom) where
  support : Index × Index -> Prop
  support_exact :
    forall pair,
      support pair <-> IsResidualTransitionCutPair atlas pair

/-- The canonical residual obstruction one-preclass of an atlas. -/
def residualObstructionOnePreclass
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom) :
    ResidualObstructionOnePreclass atlas where
  support := IsResidualTransitionCutPair atlas
  support_exact := by
    intro pair
    rfl

/-- A residual obstruction one-preclass vanishes when its support is empty. -/
def ResidualObstructionOnePreclass.Vanishes
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (preclass : ResidualObstructionOnePreclass atlas) : Prop :=
  forall pair, Not (preclass.support pair)

/-- A residual obstruction one-preclass is nonzero when its support is nonempty. -/
def ResidualObstructionOnePreclass.Nonzero
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (preclass : ResidualObstructionOnePreclass atlas) : Prop :=
  exists pair, preclass.support pair

/-- Two one-preclasses expose the same obstruction support. -/
def SameResidualObstructionSupport
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (left right : ResidualObstructionOnePreclass atlas) : Prop :=
  forall pair, left.support pair <-> right.support pair

/-- The canonical one-preclass support is exactly the residual cut-pair predicate. -/
theorem residualObstructionOnePreclass_support_exact
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (pair : Index × Index) :
    (residualObstructionOnePreclass atlas).support pair <->
      IsResidualTransitionCutPair atlas pair := by
  rfl

/-- Same support preserves one-preclass vanishing. -/
theorem sameResidualObstructionSupport_preserves_vanishes
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {left right : ResidualObstructionOnePreclass atlas}
    (hsame : SameResidualObstructionSupport left right) :
    left.Vanishes <-> right.Vanishes := by
  constructor
  · intro hleft pair hright
    exact hleft pair ((hsame pair).mpr hright)
  · intro hright pair hleft
    exact hright pair ((hsame pair).mp hleft)

/-- Same support preserves one-preclass nonzero support. -/
theorem sameResidualObstructionSupport_preserves_nonzero
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {left right : ResidualObstructionOnePreclass atlas}
    (hsame : SameResidualObstructionSupport left right) :
    left.Nonzero <-> right.Nonzero := by
  constructor
  · intro hleft
    rcases hleft with ⟨pair, hsupport⟩
    exact ⟨pair, (hsame pair).mp hsupport⟩
  · intro hright
    rcases hright with ⟨pair, hsupport⟩
    exact ⟨pair, (hsame pair).mpr hsupport⟩

/--
Vanishing of a residual obstruction one-preclass is exactly absence of
residual transition cut certificates.
-/
theorem residualObstructionOnePreclass_vanishes_iff_no_cut
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (preclass : ResidualObstructionOnePreclass atlas) :
    preclass.Vanishes <->
      Not (Nonempty (ResidualTransitionCut atlas)) := by
  constructor
  · intro hvanish hcut
    rcases hcut with ⟨cut⟩
    exact
      hvanish
        (cut.sourceIndex, cut.targetIndex)
        ((preclass.support_exact
          (cut.sourceIndex, cut.targetIndex)).mpr
          (residualTransitionCut_pair_isCut cut))
  · intro hnocut pair hsupport
    exact
      hnocut
        ⟨residualTransitionCut_of_pair
          ((preclass.support_exact pair).mp hsupport)⟩

/-- Nonzero one-preclass support is exactly existence of a residual cut. -/
theorem residualObstructionOnePreclass_nonzero_iff_cut
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (preclass : ResidualObstructionOnePreclass atlas) :
    preclass.Nonzero <->
      Nonempty (ResidualTransitionCut atlas) := by
  constructor
  · intro hnonzero
    rcases hnonzero with ⟨pair, hsupport⟩
    exact
      ⟨residualTransitionCut_of_pair
        ((preclass.support_exact pair).mp hsupport)⟩
  · intro hcut
    rcases hcut with ⟨cut⟩
    exact
      ⟨(cut.sourceIndex, cut.targetIndex),
        (preclass.support_exact
          (cut.sourceIndex, cut.targetIndex)).mpr
          (residualTransitionCut_pair_isCut cut)⟩

/-- A nonzero residual obstruction one-preclass obstructs transition closure. -/
theorem residualObstructionOnePreclass_nonzero_obstructs_atlasTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (preclass : ResidualObstructionOnePreclass atlas)
    (hnonzero : preclass.Nonzero)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed atlas transition) := by
  rcases
      (residualObstructionOnePreclass_nonzero_iff_cut preclass).mp
        hnonzero with
    ⟨cut⟩
  exact
    residualTransitionCut_obstructs_atlasTransitionClosure
      cut transition

/-- A nonzero residual obstruction one-preclass rules out transition-coherent data. -/
theorem residualObstructionOnePreclass_nonzero_obstructs_transitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (preclass : ResidualObstructionOnePreclass atlas)
    (hnonzero : preclass.Nonzero)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData atlas transition)) := by
  rcases
      (residualObstructionOnePreclass_nonzero_iff_cut preclass).mp
        hnonzero with
    ⟨cut⟩
  exact
    residualTransitionCut_obstructs_transitionCoherentData
      cut transition

/-! ## Scanner measurements of the preclass -/

/-- A returned scanner pair lies in the canonical one-preclass support. -/
theorem firstResidualTransitionCut?_some_preclassSupport
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan :
      firstResidualTransitionCut? atlas edgeOrder = some pair) :
    (residualObstructionOnePreclass atlas).support pair := by
  exact
    firstResidualTransitionCut?_some_pairCut
      atlas hscan

/-- A returned scanner pair makes the canonical one-preclass nonzero. -/
theorem firstResidualTransitionCut?_some_preclassNonzero
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan :
      firstResidualTransitionCut? atlas edgeOrder = some pair) :
    (residualObstructionOnePreclass atlas).Nonzero :=
  ⟨pair, firstResidualTransitionCut?_some_preclassSupport hscan⟩

/--
For a complete supplied edge order, scanner `none` is exact for vanishing of
the canonical one-preclass.
-/
theorem firstResidualTransitionCut?_none_iff_preclassVanishes
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    (hcomplete : ListedAtlasEdgesComplete atlas edgeOrder) :
    firstResidualTransitionCut? atlas edgeOrder = none <->
      (residualObstructionOnePreclass atlas).Vanishes := by
  exact
    (firstResidualTransitionCut?_none_iff_noResidualTransitionCut
      hcomplete).trans
      (residualObstructionOnePreclass_vanishes_iff_no_cut
        (residualObstructionOnePreclass atlas)).symm

/--
For any supplied edge order, a scanner hit is a measured nonzero support of the
canonical one-preclass.  This is a measurement statement, not a cohomology
class construction.
-/
theorem firstResidualTransitionCut?_some_obstructs_via_preclass
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
    residualObstructionOnePreclass_nonzero_obstructs_atlasTransitionClosure
      (residualObstructionOnePreclass atlas)
      (firstResidualTransitionCut?_some_preclassNonzero hscan)
      transition

/-! ## Selected frontier-to-flat one-preclass -/

/-- The selected frontier-to-flat pair lies in the canonical one-preclass support. -/
theorem selected_frontierFlat_residualObstructionOnePreclass_support :
    (residualObstructionOnePreclass selectedFrontierFlatAtlasSkeleton).support
      (SelectedSemanticOverlapIndex.repairFrontier,
        SelectedSemanticOverlapIndex.flat) := by
  exact
    residualTransitionCut_pair_isCut
      selectedFrontierFlatResidualTransitionCut

/-- The selected frontier-to-flat atlas has a nonzero residual obstruction one-preclass. -/
theorem selected_residualObstructionOnePreclass_nonzero :
    (residualObstructionOnePreclass
      selectedFrontierFlatAtlasSkeleton).Nonzero := by
  exact
    firstResidualTransitionCut?_some_preclassNonzero
      selected_firstResidualTransitionCut

/-- The selected one-preclass obstructs frontier-to-flat transition closure. -/
theorem selected_residualObstructionOnePreclass_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    residualObstructionOnePreclass_nonzero_obstructs_atlasTransitionClosure
      (residualObstructionOnePreclass selectedFrontierFlatAtlasSkeleton)
      selected_residualObstructionOnePreclass_nonzero
      transition

/-- The selected one-preclass obstructs transition-coherent atlas data. -/
theorem selected_residualObstructionOnePreclass_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    residualObstructionOnePreclass_nonzero_obstructs_transitionCoherentData
      (residualObstructionOnePreclass selectedFrontierFlatAtlasSkeleton)
      selected_residualObstructionOnePreclass_nonzero
      transition

/-! ## Theorem package -/

/--
Cycle-91 theorem package: residual transition cuts form a finite obstruction
one-preclass.  Vanishing is exactly no residual cut certificate, nonzero
support obstructs residual transition closure and transition-coherent data,
and the selected frontier-to-flat atlas realizes the nonzero case.
-/
theorem semanticResidualObstructionPreclass_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
      forall pair : Index × Index,
        (residualObstructionOnePreclass atlas).support pair <->
          IsResidualTransitionCutPair atlas pair) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall left right : ResidualObstructionOnePreclass atlas,
          SameResidualObstructionSupport left right ->
            (left.Vanishes <-> right.Vanishes)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall left right : ResidualObstructionOnePreclass atlas,
          SameResidualObstructionSupport left right ->
            (left.Nonzero <-> right.Nonzero)) /\
      (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
      (residualObstructionOnePreclass atlas).Vanishes <->
        Not (Nonempty (ResidualTransitionCut atlas))) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        (residualObstructionOnePreclass atlas).Nonzero <->
          Nonempty (ResidualTransitionCut atlas)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        (residualObstructionOnePreclass atlas).Nonzero ->
          forall transition : Index -> Index -> Atom -> Atom,
            Not (AtlasResidualTransitionClosed atlas transition)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        (residualObstructionOnePreclass atlas).Nonzero ->
          forall transition : Index -> Index -> Atom -> Atom,
            Not (Nonempty (TransitionCoherentAtlasData atlas transition))) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        [DecidablePred (IsResidualTransitionCutPair atlas)]
        {edgeOrder : List (Index × Index)},
        ListedAtlasEdgesComplete atlas edgeOrder ->
          (firstResidualTransitionCut? atlas edgeOrder = none <->
            (residualObstructionOnePreclass atlas).Vanishes)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        [DecidablePred (IsResidualTransitionCutPair atlas)]
        {edgeOrder : List (Index × Index)}
        {pair : Index × Index},
        firstResidualTransitionCut? atlas edgeOrder = some pair ->
          (residualObstructionOnePreclass atlas).support pair /\
            (residualObstructionOnePreclass atlas).Nonzero) /\
      (residualObstructionOnePreclass selectedFrontierFlatAtlasSkeleton).support
        (SelectedSemanticOverlapIndex.repairFrontier,
          SelectedSemanticOverlapIndex.flat) /\
      (residualObstructionOnePreclass
        selectedFrontierFlatAtlasSkeleton).Nonzero /\
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
    ⟨fun {_Index} {_Atom} {_atlas} pair =>
        residualObstructionOnePreclass_support_exact _ pair,
      fun {_Index} {_Atom} {_atlas} left right hsame =>
        sameResidualObstructionSupport_preserves_vanishes
          (left := left) (right := right) hsame,
      fun {_Index} {_Atom} {_atlas} left right hsame =>
        sameResidualObstructionSupport_preserves_nonzero
          (left := left) (right := right) hsame,
      fun {_Index} {_Atom} {_atlas} =>
        residualObstructionOnePreclass_vanishes_iff_no_cut
          (residualObstructionOnePreclass _),
      fun {_Index} {_Atom} {_atlas} =>
        residualObstructionOnePreclass_nonzero_iff_cut
          (residualObstructionOnePreclass _),
      fun {_Index} {_Atom} {_atlas} hnonzero transition =>
        residualObstructionOnePreclass_nonzero_obstructs_atlasTransitionClosure
          (residualObstructionOnePreclass _) hnonzero transition,
      fun {_Index} {_Atom} {_atlas} hnonzero transition =>
        residualObstructionOnePreclass_nonzero_obstructs_transitionCoherentData
          (residualObstructionOnePreclass _) hnonzero transition,
      fun {_Index} {_Atom} {_atlas} {_inst} {_edgeOrder} hcomplete =>
        firstResidualTransitionCut?_none_iff_preclassVanishes
          hcomplete,
      fun {_Index} {_Atom} {_atlas} {_inst} {_edgeOrder} {_pair} hscan =>
        ⟨firstResidualTransitionCut?_some_preclassSupport hscan,
          firstResidualTransitionCut?_some_preclassNonzero hscan⟩,
      selected_frontierFlat_residualObstructionOnePreclass_support,
      selected_residualObstructionOnePreclass_nonzero,
      selected_residualObstructionOnePreclass_obstructs_transitionClosure,
      selected_residualObstructionOnePreclass_obstructs_transitionCoherentData⟩

end SemanticResidualObstructionPreclass
end QualitySurface
end Formal.AG.Research
