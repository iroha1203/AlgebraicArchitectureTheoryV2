import Formal.AG.Research.QualitySurface.SemanticResidualObstructionPreclass

/-!
Cycle 92 evidence for `G-aat-quality-surface-01`.

This file turns the Cycle 91 residual obstruction preclass into a finite
cut-locus obstruction class reading.  A raw cochain may carry support away
from residual transition cuts; the class equivalence ignores that off-cut
noise and compares representatives only on the residual cut locus.

The result is a cut-locus quotient-style criterion, not a Cech `H^1` class.
It does not construct a coboundary quotient, does not assert arbitrary sheaf
gluing, does not assert that class vanishing implies residual transition
closure, and does not assert source extraction completeness, ArchMap
correctness, runtime repair synthesis, UI correctness, or whole-codebase
quality.
-/

universe u w

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualObstructionClass

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
open SemanticResidualObstructionPreclass

/-! ## Cut-locus residual obstruction cochains -/

/--
A raw residual cut cochain over a finite semantic repair atlas.
The support may contain off-cut diagnostic noise; class predicates below
restrict it to the residual transition cut locus.
-/
structure ResidualCutCochain
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom) where
  support : Index × Index -> Prop

/-- The canonical raw cochain supported exactly on residual transition cuts. -/
def canonicalResidualCutCochain
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom) :
    ResidualCutCochain atlas where
  support := IsResidualTransitionCutPair atlas

/--
Cut-noise equivalence compares raw cochain representatives only on the
residual transition cut locus.
-/
def CutNoiseEquivalent
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (left right : ResidualCutCochain atlas) : Prop :=
  forall pair,
    IsResidualTransitionCutPair atlas pair ->
      (left.support pair <-> right.support pair)

namespace ResidualCutCochain

/-- A cochain class vanishes when it has no support on residual cut pairs. -/
def CutVanishes
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cochain : ResidualCutCochain atlas) : Prop :=
  forall pair,
    IsResidualTransitionCutPair atlas pair ->
      Not (cochain.support pair)

/-- A cochain class is nonzero when it has support on some residual cut pair. -/
def CutNonzero
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cochain : ResidualCutCochain atlas) : Prop :=
  exists pair,
    IsResidualTransitionCutPair atlas pair /\ cochain.support pair

end ResidualCutCochain

/-! ## Equivalence laws and class predicates -/

/-- Cut-noise equivalence is reflexive. -/
theorem cutNoiseEquivalent_refl
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cochain : ResidualCutCochain atlas) :
    CutNoiseEquivalent cochain cochain := by
  intro pair _hcut
  rfl

/-- Cut-noise equivalence is symmetric. -/
theorem cutNoiseEquivalent_symm
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {left right : ResidualCutCochain atlas}
    (hequiv : CutNoiseEquivalent left right) :
    CutNoiseEquivalent right left := by
  intro pair hcut
  exact (hequiv pair hcut).symm

/-- Cut-noise equivalence is transitive. -/
theorem cutNoiseEquivalent_trans
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {left middle right : ResidualCutCochain atlas}
    (hleft : CutNoiseEquivalent left middle)
    (hright : CutNoiseEquivalent middle right) :
    CutNoiseEquivalent left right := by
  intro pair hcut
  exact (hleft pair hcut).trans (hright pair hcut)

/-- Cut-noise equivalence preserves cut-locus vanishing. -/
theorem cutNoiseEquivalent_preserves_cutVanishes
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {left right : ResidualCutCochain atlas}
    (hequiv : CutNoiseEquivalent left right) :
    left.CutVanishes <-> right.CutVanishes := by
  constructor
  · intro hleft pair hcut hright
    exact hleft pair hcut ((hequiv pair hcut).mpr hright)
  · intro hright pair hcut hleft
    exact hright pair hcut ((hequiv pair hcut).mp hleft)

/-- Cut-noise equivalence preserves cut-locus nonzero support. -/
theorem cutNoiseEquivalent_preserves_cutNonzero
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {left right : ResidualCutCochain atlas}
    (hequiv : CutNoiseEquivalent left right) :
    left.CutNonzero <-> right.CutNonzero := by
  constructor
  · intro hleft
    rcases hleft with ⟨pair, hcut, hsupport⟩
    exact ⟨pair, hcut, (hequiv pair hcut).mp hsupport⟩
  · intro hright
    rcases hright with ⟨pair, hcut, hsupport⟩
    exact ⟨pair, hcut, (hequiv pair hcut).mpr hsupport⟩

/-! ## Canonical cut class criteria -/

/-- The canonical cochain support is exactly the residual cut-pair predicate. -/
theorem canonicalResidualCutCochain_support_exact
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (pair : Index × Index) :
    (canonicalResidualCutCochain atlas).support pair <->
      IsResidualTransitionCutPair atlas pair := by
  rfl

/--
Vanishing of the canonical cut class is exactly absence of residual transition
cut certificates.
-/
theorem canonicalResidualCutClass_vanishes_iff_no_cut
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom} :
    (canonicalResidualCutCochain atlas).CutVanishes <->
      Not (Nonempty (ResidualTransitionCut atlas)) := by
  constructor
  · intro hvanish hcut
    rcases hcut with ⟨cut⟩
    exact
      hvanish
        (cut.sourceIndex, cut.targetIndex)
        (residualTransitionCut_pair_isCut cut)
        (residualTransitionCut_pair_isCut cut)
  · intro hnocut pair hcut _hsupport
    exact hnocut ⟨residualTransitionCut_of_pair hcut⟩

/-- Nonzero canonical cut class support is exactly existence of a residual cut. -/
theorem canonicalResidualCutClass_nonzero_iff_cut
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom} :
    (canonicalResidualCutCochain atlas).CutNonzero <->
      Nonempty (ResidualTransitionCut atlas) := by
  constructor
  · intro hnonzero
    rcases hnonzero with ⟨pair, hcut, _hsupport⟩
    exact ⟨residualTransitionCut_of_pair hcut⟩
  · intro hcut
    rcases hcut with ⟨cut⟩
    exact
      ⟨(cut.sourceIndex, cut.targetIndex),
        residualTransitionCut_pair_isCut cut,
        residualTransitionCut_pair_isCut cut⟩

/-- Any nonzero cut class obstructs residual transition closure. -/
theorem residualCutClass_nonzero_obstructs_atlasTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cochain : ResidualCutCochain atlas)
    (hnonzero : cochain.CutNonzero)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed atlas transition) := by
  rcases hnonzero with ⟨pair, hcut, _hsupport⟩
  exact
    residualTransitionCut_obstructs_atlasTransitionClosure
      (residualTransitionCut_of_pair hcut)
      transition

/-- Any nonzero cut class rules out transition-coherent atlas data. -/
theorem residualCutClass_nonzero_obstructs_transitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (cochain : ResidualCutCochain atlas)
    (hnonzero : cochain.CutNonzero)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData atlas transition)) := by
  rcases hnonzero with ⟨pair, hcut, _hsupport⟩
  exact
    residualTransitionCut_obstructs_transitionCoherentData
      (residualTransitionCut_of_pair hcut)
      transition

/-! ## Scanner measurements of the canonical cut class -/

/-- A scanner hit makes the canonical cut class nonzero. -/
theorem firstResidualTransitionCut?_some_cutClassNonzero
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    {pair : Index × Index}
    (hscan :
      firstResidualTransitionCut? atlas edgeOrder = some pair) :
    (canonicalResidualCutCochain atlas).CutNonzero := by
  have hcut :
      IsResidualTransitionCutPair atlas pair :=
    firstResidualTransitionCut?_some_pairCut atlas hscan
  exact ⟨pair, hcut, hcut⟩

/--
For a complete supplied edge order, scanner `none` is exact for vanishing of
the canonical cut class.
-/
theorem firstResidualTransitionCut?_none_iff_canonicalCutClassVanishes
    {Index : Type w}
    {Atom : Type u}
    {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
    [DecidablePred (IsResidualTransitionCutPair atlas)]
    {edgeOrder : List (Index × Index)}
    (hcomplete : ListedAtlasEdgesComplete atlas edgeOrder) :
    firstResidualTransitionCut? atlas edgeOrder = none <->
      (canonicalResidualCutCochain atlas).CutVanishes := by
  exact
    (firstResidualTransitionCut?_none_iff_noResidualTransitionCut
      hcomplete).trans
      (canonicalResidualCutClass_vanishes_iff_no_cut).symm

/-- A scanner hit obstructs residual transition closure via the cut class. -/
theorem firstResidualTransitionCut?_some_obstructs_via_cutClass
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
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain atlas)
      (firstResidualTransitionCut?_some_cutClassNonzero hscan)
      transition

/-! ## Selected noisy representative -/

/-- The selected reverse edge is not a residual transition cut pair. -/
theorem selected_flatFrontier_not_residualCutPair :
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

/--
The selected noisy representative adds raw support on the reverse, non-cut
pair.  This raw support is diagnostic noise killed by cut-noise equivalence.
-/
def selectedBoundaryNoisyResidualCutCochain :
    ResidualCutCochain selectedFrontierFlatAtlasSkeleton where
  support pair :=
    (canonicalResidualCutCochain
      selectedFrontierFlatAtlasSkeleton).support pair \/
      pair =
        (SelectedSemanticOverlapIndex.flat,
          SelectedSemanticOverlapIndex.repairFrontier)

/--
The selected noisy representative differs from the canonical raw support on
the reverse non-cut pair.
-/
theorem selectedBoundaryNoisy_rawSupport_differs_from_canonical :
    selectedBoundaryNoisyResidualCutCochain.support
        (SelectedSemanticOverlapIndex.flat,
          SelectedSemanticOverlapIndex.repairFrontier) /\
      Not
        ((canonicalResidualCutCochain
          selectedFrontierFlatAtlasSkeleton).support
          (SelectedSemanticOverlapIndex.flat,
            SelectedSemanticOverlapIndex.repairFrontier)) := by
  constructor
  · dsimp [selectedBoundaryNoisyResidualCutCochain]
    exact Or.inr rfl
  · exact selected_flatFrontier_not_residualCutPair

/--
The selected noisy representative has the same residual cut class as the
canonical representative.
-/
theorem selectedBoundaryNoisy_cutNoiseEquivalent_canonical :
    CutNoiseEquivalent
      selectedBoundaryNoisyResidualCutCochain
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton) := by
  intro pair hcut
  constructor
  · intro _hsupport
    exact hcut
  · intro hcanonical
    dsimp [selectedBoundaryNoisyResidualCutCochain]
    exact Or.inl hcanonical

/-- The selected canonical cut class is nonzero. -/
theorem selected_canonicalResidualCutClass_nonzero :
    (canonicalResidualCutCochain
      selectedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    firstResidualTransitionCut?_some_cutClassNonzero
      selected_firstResidualTransitionCut

/-- The selected noisy cut class is nonzero. -/
theorem selectedBoundaryNoisy_residualCutClass_nonzero :
    selectedBoundaryNoisyResidualCutCochain.CutNonzero := by
  exact
    (cutNoiseEquivalent_preserves_cutNonzero
      selectedBoundaryNoisy_cutNoiseEquivalent_canonical).mpr
      selected_canonicalResidualCutClass_nonzero

/-- The selected noisy cut class obstructs frontier-to-flat transition closure. -/
theorem selectedBoundaryNoisy_residualCutClass_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      selectedBoundaryNoisyResidualCutCochain
      selectedBoundaryNoisy_residualCutClass_nonzero
      transition

/-- The selected noisy cut class obstructs transition-coherent atlas data. -/
theorem selectedBoundaryNoisy_residualCutClass_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      selectedBoundaryNoisyResidualCutCochain
      selectedBoundaryNoisy_residualCutClass_nonzero
      transition

/-! ## Theorem package -/

/--
Cycle-92 theorem package: residual cut cochains have a cut-locus class reading
that ignores off-cut raw support noise.  The canonical class vanishes exactly
when there is no residual cut certificate; nonzero class support obstructs
transition closure and transition-coherent data; the selected noisy
representative differs from canonical raw support while remaining class
equivalent.
-/
theorem semanticResidualObstructionClass_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
      forall cochain : ResidualCutCochain atlas,
        CutNoiseEquivalent cochain cochain) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall left right : ResidualCutCochain atlas,
          CutNoiseEquivalent left right ->
            CutNoiseEquivalent right left) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall left middle right : ResidualCutCochain atlas,
          CutNoiseEquivalent left middle ->
            CutNoiseEquivalent middle right ->
              CutNoiseEquivalent left right) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall left right : ResidualCutCochain atlas,
          CutNoiseEquivalent left right ->
            (left.CutVanishes <-> right.CutVanishes)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall left right : ResidualCutCochain atlas,
          CutNoiseEquivalent left right ->
            (left.CutNonzero <-> right.CutNonzero)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        (canonicalResidualCutCochain atlas).CutVanishes <->
          Not (Nonempty (ResidualTransitionCut atlas))) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        (canonicalResidualCutCochain atlas).CutNonzero <->
          Nonempty (ResidualTransitionCut atlas)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall cochain : ResidualCutCochain atlas,
          cochain.CutNonzero ->
            forall transition : Index -> Index -> Atom -> Atom,
              Not (AtlasResidualTransitionClosed atlas transition)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
        forall cochain : ResidualCutCochain atlas,
          cochain.CutNonzero ->
            forall transition : Index -> Index -> Atom -> Atom,
              Not (Nonempty (TransitionCoherentAtlasData atlas transition))) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        [DecidablePred (IsResidualTransitionCutPair atlas)]
        {edgeOrder : List (Index × Index)}
        {pair : Index × Index},
        firstResidualTransitionCut? atlas edgeOrder = some pair ->
          (canonicalResidualCutCochain atlas).CutNonzero) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom}
        [DecidablePred (IsResidualTransitionCutPair atlas)]
        {edgeOrder : List (Index × Index)},
        ListedAtlasEdgesComplete atlas edgeOrder ->
          (firstResidualTransitionCut? atlas edgeOrder = none <->
            (canonicalResidualCutCochain atlas).CutVanishes)) /\
      selectedBoundaryNoisyResidualCutCochain.support
        (SelectedSemanticOverlapIndex.flat,
          SelectedSemanticOverlapIndex.repairFrontier) /\
      Not
        ((canonicalResidualCutCochain
          selectedFrontierFlatAtlasSkeleton).support
          (SelectedSemanticOverlapIndex.flat,
            SelectedSemanticOverlapIndex.repairFrontier)) /\
      CutNoiseEquivalent
        selectedBoundaryNoisyResidualCutCochain
        (canonicalResidualCutCochain
          selectedFrontierFlatAtlasSkeleton) /\
      selectedBoundaryNoisyResidualCutCochain.CutNonzero /\
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
    ⟨fun {_Index} {_Atom} {_atlas} cochain =>
        cutNoiseEquivalent_refl cochain,
      fun {_Index} {_Atom} {_atlas} left right hequiv =>
        cutNoiseEquivalent_symm (left := left) (right := right) hequiv,
      fun {_Index} {_Atom} {_atlas} left middle right hleft hright =>
        cutNoiseEquivalent_trans
          (left := left) (middle := middle) (right := right)
          hleft hright,
      fun {_Index} {_Atom} {_atlas} left right hequiv =>
        cutNoiseEquivalent_preserves_cutVanishes
          (left := left) (right := right) hequiv,
      fun {_Index} {_Atom} {_atlas} left right hequiv =>
        cutNoiseEquivalent_preserves_cutNonzero
          (left := left) (right := right) hequiv,
      fun {_Index} {_Atom} {_atlas} =>
        canonicalResidualCutClass_vanishes_iff_no_cut,
      fun {_Index} {_Atom} {_atlas} =>
        canonicalResidualCutClass_nonzero_iff_cut,
      fun {_Index} {_Atom} {_atlas} cochain hnonzero transition =>
        residualCutClass_nonzero_obstructs_atlasTransitionClosure
          cochain hnonzero transition,
      fun {_Index} {_Atom} {_atlas} cochain hnonzero transition =>
        residualCutClass_nonzero_obstructs_transitionCoherentData
          cochain hnonzero transition,
      fun {_Index} {_Atom} {_atlas} {_inst} {_edgeOrder} {_pair} hscan =>
        firstResidualTransitionCut?_some_cutClassNonzero hscan,
      fun {_Index} {_Atom} {_atlas} {_inst} {_edgeOrder} hcomplete =>
        firstResidualTransitionCut?_none_iff_canonicalCutClassVanishes
          hcomplete,
      selectedBoundaryNoisy_rawSupport_differs_from_canonical.1,
      selectedBoundaryNoisy_rawSupport_differs_from_canonical.2,
      selectedBoundaryNoisy_cutNoiseEquivalent_canonical,
      selectedBoundaryNoisy_residualCutClass_nonzero,
      selectedBoundaryNoisy_residualCutClass_obstructs_transitionClosure,
      selectedBoundaryNoisy_residualCutClass_obstructs_transitionCoherentData⟩

end SemanticResidualObstructionClass
end QualitySurface
end Formal.AG.Research
