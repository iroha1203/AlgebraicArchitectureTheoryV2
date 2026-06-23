import Formal.AG.Research.QualitySurface.SemanticResidualObstructionClass

/-!
Cycle 93 evidence for `G-aat-quality-surface-01`.

This file lifts the Cycle 92 cut-noise class reading from raw cochain
representatives to same-carrier atlas presentations.  Two finite semantic
repair atlas skeletons may have different raw edge families while exposing
the same residual transition cut locus.  Under that explicit same-carrier
cut-locus gauge, cut-locus class vanishing, nonzero support, and nonzero
obstruction readings are invariant.

The result is a same-carrier cut-locus invariance theorem.  It does not
construct arbitrary atlas morphisms, functorial sheaf transport, a Cech `H^1`
class, a coboundary quotient, a vanishing-to-closure theorem, source extraction
completeness, ArchMap correctness, runtime repair synthesis, tooling runtime
extraction, UI correctness, or whole-codebase quality.
-/

universe u w

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualAtlasGauge

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

/-! ## Same-carrier residual cut-locus gauges -/

/--
Two same-carrier atlas skeletons expose the same residual transition cut locus
when every index pair is a cut in one exactly when it is a cut in the other.
-/
def SameResidualCutLocus
    {Index : Type w}
    {Atom : Type u}
    (left right : FiniteSemanticRepairAtlasSkeleton Index Atom) : Prop :=
  forall pair,
    IsResidualTransitionCutPair left pair <->
      IsResidualTransitionCutPair right pair

/--
Two raw residual cut cochains over same-carrier atlases are gauge-related when
their support agrees on the left residual cut locus.  A matching
`SameResidualCutLocus` hypothesis is needed to transfer right-side class
predicates.
-/
def SameResidualCutClassGaugeRelated
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (leftC : ResidualCutCochain left)
    (rightC : ResidualCutCochain right) : Prop :=
  forall pair,
    IsResidualTransitionCutPair left pair ->
      (leftC.support pair <-> rightC.support pair)

/-- Same residual cut locus is reflexive. -/
theorem sameResidualCutLocus_refl
    {Index : Type w}
    {Atom : Type u}
    (atlas : FiniteSemanticRepairAtlasSkeleton Index Atom) :
    SameResidualCutLocus atlas atlas := by
  intro pair
  rfl

/-- Same residual cut locus is symmetric. -/
theorem sameResidualCutLocus_symm
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (hsame : SameResidualCutLocus left right) :
    SameResidualCutLocus right left := by
  intro pair
  exact (hsame pair).symm

/-- Same residual cut locus is transitive. -/
theorem sameResidualCutLocus_trans
    {Index : Type w}
    {Atom : Type u}
    {left middle right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (hleft : SameResidualCutLocus left middle)
    (hright : SameResidualCutLocus middle right) :
    SameResidualCutLocus left right := by
  intro pair
  exact (hleft pair).trans (hright pair)

/-- Gauge-related classes preserve cut-locus vanishing across same cut loci. -/
theorem sameResidualCutClassGaugeRelated_preserves_cutVanishes
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {leftC : ResidualCutCochain left}
    {rightC : ResidualCutCochain right}
    (hsame : SameResidualCutLocus left right)
    (hrelated : SameResidualCutClassGaugeRelated leftC rightC) :
    leftC.CutVanishes <-> rightC.CutVanishes := by
  constructor
  · intro hleft pair hrightCut hrightSupport
    have hleftCut :
        IsResidualTransitionCutPair left pair :=
      (hsame pair).mpr hrightCut
    exact hleft pair hleftCut ((hrelated pair hleftCut).mpr hrightSupport)
  · intro hright pair hleftCut hleftSupport
    have hrightCut :
        IsResidualTransitionCutPair right pair :=
      (hsame pair).mp hleftCut
    exact hright pair hrightCut ((hrelated pair hleftCut).mp hleftSupport)

/-- Gauge-related classes preserve cut-locus nonzero support across same cut loci. -/
theorem sameResidualCutClassGaugeRelated_preserves_cutNonzero
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {leftC : ResidualCutCochain left}
    {rightC : ResidualCutCochain right}
    (hsame : SameResidualCutLocus left right)
    (hrelated : SameResidualCutClassGaugeRelated leftC rightC) :
    leftC.CutNonzero <-> rightC.CutNonzero := by
  constructor
  · intro hleft
    rcases hleft with ⟨pair, hleftCut, hleftSupport⟩
    exact
      ⟨pair,
        (hsame pair).mp hleftCut,
        (hrelated pair hleftCut).mp hleftSupport⟩
  · intro hright
    rcases hright with ⟨pair, hrightCut, hrightSupport⟩
    have hleftCut :
        IsResidualTransitionCutPair left pair :=
      (hsame pair).mpr hrightCut
    exact
      ⟨pair,
        hleftCut,
        (hrelated pair hleftCut).mpr hrightSupport⟩

/-! ## Canonical class invariance -/

/-- Canonical residual cut cochains are gauge-related under same cut locus. -/
theorem sameResidualCutLocus_gaugeRelated_canonical
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (hsame : SameResidualCutLocus left right) :
    SameResidualCutClassGaugeRelated
      (canonicalResidualCutCochain left)
      (canonicalResidualCutCochain right) := by
  intro pair _hleftCut
  exact hsame pair

/-- Same residual cut locus preserves canonical cut-class vanishing. -/
theorem sameResidualCutLocus_preserves_canonicalCutVanishes
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (hsame : SameResidualCutLocus left right) :
    (canonicalResidualCutCochain left).CutVanishes <->
      (canonicalResidualCutCochain right).CutVanishes := by
  exact
    sameResidualCutClassGaugeRelated_preserves_cutVanishes
      hsame
      (sameResidualCutLocus_gaugeRelated_canonical hsame)

/-- Same residual cut locus preserves canonical cut-class nonzero support. -/
theorem sameResidualCutLocus_preserves_canonicalCutNonzero
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    (hsame : SameResidualCutLocus left right) :
    (canonicalResidualCutCochain left).CutNonzero <->
      (canonicalResidualCutCochain right).CutNonzero := by
  exact
    sameResidualCutClassGaugeRelated_preserves_cutNonzero
      hsame
      (sameResidualCutLocus_gaugeRelated_canonical hsame)

/-- A nonzero gauge-related source class obstructs target transition closure. -/
theorem gaugeRelated_nonzero_obstructs_targetTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {leftC : ResidualCutCochain left}
    {rightC : ResidualCutCochain right}
    (hsame : SameResidualCutLocus left right)
    (hrelated : SameResidualCutClassGaugeRelated leftC rightC)
    (hnonzero : leftC.CutNonzero)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed right transition) := by
  have htarget : rightC.CutNonzero :=
    (sameResidualCutClassGaugeRelated_preserves_cutNonzero
      hsame hrelated).mp hnonzero
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      rightC htarget transition

/-- A nonzero gauge-related source class rules out target transition-coherent data. -/
theorem gaugeRelated_nonzero_obstructs_targetTransitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {leftC : ResidualCutCochain left}
    {rightC : ResidualCutCochain right}
    (hsame : SameResidualCutLocus left right)
    (hrelated : SameResidualCutClassGaugeRelated leftC rightC)
    (hnonzero : leftC.CutNonzero)
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData right transition)) := by
  have htarget : rightC.CutNonzero :=
    (sameResidualCutClassGaugeRelated_preserves_cutNonzero
      hsame hrelated).mp hnonzero
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      rightC htarget transition

/-! ## Selected raw-edge noisy atlas gauge -/

/-- The selected raw-edge noisy atlas adds the reverse edge as presentation noise. -/
def selectedEdgeNoisyFrontierFlatEdge
    (source target : SelectedSemanticOverlapIndex) : Prop :=
  selectedFrontierToFlatEdge source target \/
    (source = SelectedSemanticOverlapIndex.flat /\
      target = SelectedSemanticOverlapIndex.repairFrontier)

/--
The selected raw-edge noisy atlas has the same finite carrier, projection, and
cover as the selected frontier-to-flat atlas, but a larger raw edge family.
-/
def selectedEdgeNoisyFrontierFlatAtlasSkeleton :
    FiniteSemanticRepairAtlasSkeleton
      SelectedSemanticOverlapIndex
      RefinedSemanticRepairAtom where
  indexOrder := selectedFrontierFlatAtlasSkeleton.indexOrder
  index_complete := selectedFrontierFlatAtlasSkeleton.index_complete
  atomOrder := selectedFrontierFlatAtlasSkeleton.atomOrder
  atom_complete := selectedFrontierFlatAtlasSkeleton.atom_complete
  edge := selectedEdgeNoisyFrontierFlatEdge
  projection := selectedFrontierFlatAtlasSkeleton.projection
  cover := selectedFrontierFlatAtlasSkeleton.cover

/-- The selected noisy atlas has a reverse raw edge not present in the original atlas. -/
theorem selectedEdgeNoisy_rawEdge_differs_from_selected :
    selectedEdgeNoisyFrontierFlatAtlasSkeleton.edge
        SelectedSemanticOverlapIndex.flat
        SelectedSemanticOverlapIndex.repairFrontier /\
      Not
        (selectedFrontierFlatAtlasSkeleton.edge
          SelectedSemanticOverlapIndex.flat
          SelectedSemanticOverlapIndex.repairFrontier) := by
  constructor
  · dsimp [selectedEdgeNoisyFrontierFlatAtlasSkeleton,
      selectedEdgeNoisyFrontierFlatEdge]
    exact Or.inr ⟨rfl, rfl⟩
  · intro hedge
    simp [selectedFrontierFlatAtlasSkeleton,
      selectedFrontierToFlatEdge] at hedge

/-- The selected flat index is not residual-present. -/
theorem selected_flatIndexedResidualNotPresent :
    Not
      (IndexedResidualPresentAt
        selectedIndexedProjection
        selectedIndexedCover
        SelectedSemanticOverlapIndex.flat) := by
  intro hpresent
  rcases hpresent with ⟨residual, hresidual⟩
  exact selected_flatIndexedResidualFree residual hresidual

/--
The reverse noisy edge is not a residual cut pair: it starts at the flat index,
which is residual-free.
-/
theorem selectedEdgeNoisy_reverse_not_residualCutPair :
    Not
      (IsResidualTransitionCutPair
        selectedEdgeNoisyFrontierFlatAtlasSkeleton
        (SelectedSemanticOverlapIndex.flat,
          SelectedSemanticOverlapIndex.repairFrontier)) := by
  intro hcut
  exact
    selected_flatIndexedResidualNotPresent
      (by
        simpa [selectedEdgeNoisyFrontierFlatAtlasSkeleton]
          using hcut.2.1)

/--
The selected raw-edge noisy atlas has the same residual cut locus as the
original selected frontier-to-flat atlas.
-/
theorem selectedEdgeNoisy_sameResidualCutLocus_selected :
    SameResidualCutLocus
      selectedFrontierFlatAtlasSkeleton
      selectedEdgeNoisyFrontierFlatAtlasSkeleton := by
  intro pair
  cases pair with
  | mk source target =>
      constructor
      · intro hcut
        exact
          ⟨Or.inl
              (by
                simpa [selectedFrontierFlatAtlasSkeleton]
                  using hcut.1),
            by
              simpa [selectedFrontierFlatAtlasSkeleton,
                selectedEdgeNoisyFrontierFlatAtlasSkeleton]
                using hcut.2.1,
            by
              simpa [selectedFrontierFlatAtlasSkeleton,
                selectedEdgeNoisyFrontierFlatAtlasSkeleton]
                using hcut.2.2⟩
      · intro hcut
        have hselectedEdge :
            selectedFrontierFlatAtlasSkeleton.edge source target := by
          rcases hcut.1 with hselected | hreverse
          · simpa [selectedFrontierFlatAtlasSkeleton] using hselected
          · rcases hreverse with ⟨hsource, htarget⟩
            have hsource' :
                source = SelectedSemanticOverlapIndex.flat := by
              simpa using hsource
            have htarget' :
                target = SelectedSemanticOverlapIndex.repairFrontier := by
              simpa using htarget
            subst source
            subst target
            have hflatPresent :
                IndexedResidualPresentAt
                  selectedIndexedProjection
                  selectedIndexedCover
                  SelectedSemanticOverlapIndex.flat := by
              simpa [selectedEdgeNoisyFrontierFlatAtlasSkeleton]
                using hcut.2.1
            exact False.elim
              (selected_flatIndexedResidualNotPresent hflatPresent)
        exact
          ⟨hselectedEdge,
            by
              simpa [selectedFrontierFlatAtlasSkeleton,
                selectedEdgeNoisyFrontierFlatAtlasSkeleton]
                using hcut.2.1,
            by
              simpa [selectedFrontierFlatAtlasSkeleton,
                selectedEdgeNoisyFrontierFlatAtlasSkeleton]
                using hcut.2.2⟩

/-- The selected noisy atlas canonical class is gauge-related to the original one. -/
theorem selectedEdgeNoisy_canonicalGaugeRelated_selected :
    SameResidualCutClassGaugeRelated
      (canonicalResidualCutCochain selectedFrontierFlatAtlasSkeleton)
      (canonicalResidualCutCochain selectedEdgeNoisyFrontierFlatAtlasSkeleton) := by
  exact
    sameResidualCutLocus_gaugeRelated_canonical
      selectedEdgeNoisy_sameResidualCutLocus_selected

/-- The selected noisy atlas has nonzero canonical residual cut class. -/
theorem selectedEdgeNoisy_canonicalCutClass_nonzero :
    (canonicalResidualCutCochain
      selectedEdgeNoisyFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    (sameResidualCutLocus_preserves_canonicalCutNonzero
      selectedEdgeNoisy_sameResidualCutLocus_selected).mp
      selected_canonicalResidualCutClass_nonzero

/-- The selected noisy canonical class obstructs residual transition closure. -/
theorem selectedEdgeNoisy_canonicalCutClass_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedEdgeNoisyFrontierFlatAtlasSkeleton
        transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain
        selectedEdgeNoisyFrontierFlatAtlasSkeleton)
      selectedEdgeNoisy_canonicalCutClass_nonzero
      transition

/-- The selected noisy canonical class rules out transition-coherent atlas data. -/
theorem selectedEdgeNoisy_canonicalCutClass_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedEdgeNoisyFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain
        selectedEdgeNoisyFrontierFlatAtlasSkeleton)
      selectedEdgeNoisy_canonicalCutClass_nonzero
      transition

/-! ## Theorem package -/

/--
Cycle-93 theorem package: same-carrier atlas presentations with the same
residual cut locus preserve gauge-related cut-class vanishing, nonzero
support, and nonzero obstruction readings.  The selected raw-edge noisy atlas
changes the raw edge family while preserving the residual cut locus.
-/
theorem semanticResidualAtlasGauge_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {atlas : FiniteSemanticRepairAtlasSkeleton Index Atom},
      SameResidualCutLocus atlas atlas) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom},
        SameResidualCutLocus left right ->
          SameResidualCutLocus right left) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left middle right : FiniteSemanticRepairAtlasSkeleton Index Atom},
        SameResidualCutLocus left middle ->
          SameResidualCutLocus middle right ->
            SameResidualCutLocus left right) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {leftC : ResidualCutCochain left}
        {rightC : ResidualCutCochain right},
        SameResidualCutLocus left right ->
          SameResidualCutClassGaugeRelated leftC rightC ->
            (leftC.CutVanishes <-> rightC.CutVanishes)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {leftC : ResidualCutCochain left}
        {rightC : ResidualCutCochain right},
        SameResidualCutLocus left right ->
          SameResidualCutClassGaugeRelated leftC rightC ->
            (leftC.CutNonzero <-> rightC.CutNonzero)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom},
        SameResidualCutLocus left right ->
          SameResidualCutClassGaugeRelated
            (canonicalResidualCutCochain left)
            (canonicalResidualCutCochain right)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom},
        SameResidualCutLocus left right ->
          ((canonicalResidualCutCochain left).CutVanishes <->
            (canonicalResidualCutCochain right).CutVanishes)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom},
        SameResidualCutLocus left right ->
          ((canonicalResidualCutCochain left).CutNonzero <->
            (canonicalResidualCutCochain right).CutNonzero)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {leftC : ResidualCutCochain left}
        {rightC : ResidualCutCochain right},
        SameResidualCutLocus left right ->
          SameResidualCutClassGaugeRelated leftC rightC ->
            leftC.CutNonzero ->
              forall transition : Index -> Index -> Atom -> Atom,
                Not (AtlasResidualTransitionClosed right transition)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {left right : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {leftC : ResidualCutCochain left}
        {rightC : ResidualCutCochain right},
        SameResidualCutLocus left right ->
          SameResidualCutClassGaugeRelated leftC rightC ->
            leftC.CutNonzero ->
              forall transition : Index -> Index -> Atom -> Atom,
                Not (Nonempty (TransitionCoherentAtlasData right transition))) /\
      selectedEdgeNoisyFrontierFlatAtlasSkeleton.edge
        SelectedSemanticOverlapIndex.flat
        SelectedSemanticOverlapIndex.repairFrontier /\
      Not
        (selectedFrontierFlatAtlasSkeleton.edge
          SelectedSemanticOverlapIndex.flat
          SelectedSemanticOverlapIndex.repairFrontier) /\
      Not
        (IsResidualTransitionCutPair
          selectedEdgeNoisyFrontierFlatAtlasSkeleton
          (SelectedSemanticOverlapIndex.flat,
            SelectedSemanticOverlapIndex.repairFrontier)) /\
      SameResidualCutLocus
        selectedFrontierFlatAtlasSkeleton
        selectedEdgeNoisyFrontierFlatAtlasSkeleton /\
      SameResidualCutClassGaugeRelated
        (canonicalResidualCutCochain selectedFrontierFlatAtlasSkeleton)
        (canonicalResidualCutCochain
          selectedEdgeNoisyFrontierFlatAtlasSkeleton) /\
      (canonicalResidualCutCochain
        selectedEdgeNoisyFrontierFlatAtlasSkeleton).CutNonzero /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (AtlasResidualTransitionClosed
            selectedEdgeNoisyFrontierFlatAtlasSkeleton
            transition)) /\
      (forall
        transition :
          SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
            RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom,
        Not
          (Nonempty
            (TransitionCoherentAtlasData
              selectedEdgeNoisyFrontierFlatAtlasSkeleton
              transition))) := by
  exact
    ⟨fun {_Index} {_Atom} {_atlas} =>
        sameResidualCutLocus_refl _,
      fun {_Index} {_Atom} {_left} {_right} hsame =>
        sameResidualCutLocus_symm hsame,
      fun {_Index} {_Atom} {_left} {_middle} {_right} hleft hright =>
        sameResidualCutLocus_trans hleft hright,
      fun {_Index} {_Atom} {_left} {_right} {_leftC} {_rightC}
          hsame hrelated =>
        sameResidualCutClassGaugeRelated_preserves_cutVanishes
          hsame hrelated,
      fun {_Index} {_Atom} {_left} {_right} {_leftC} {_rightC}
          hsame hrelated =>
        sameResidualCutClassGaugeRelated_preserves_cutNonzero
          hsame hrelated,
      fun {_Index} {_Atom} {_left} {_right} hsame =>
        sameResidualCutLocus_gaugeRelated_canonical hsame,
      fun {_Index} {_Atom} {_left} {_right} hsame =>
        sameResidualCutLocus_preserves_canonicalCutVanishes hsame,
      fun {_Index} {_Atom} {_left} {_right} hsame =>
        sameResidualCutLocus_preserves_canonicalCutNonzero hsame,
      fun {_Index} {_Atom} {_left} {_right} {_leftC} {_rightC}
          hsame hrelated hnonzero transition =>
        gaugeRelated_nonzero_obstructs_targetTransitionClosure
          hsame hrelated hnonzero transition,
      fun {_Index} {_Atom} {_left} {_right} {_leftC} {_rightC}
          hsame hrelated hnonzero transition =>
        gaugeRelated_nonzero_obstructs_targetTransitionCoherentData
          hsame hrelated hnonzero transition,
      selectedEdgeNoisy_rawEdge_differs_from_selected.1,
      selectedEdgeNoisy_rawEdge_differs_from_selected.2,
      selectedEdgeNoisy_reverse_not_residualCutPair,
      selectedEdgeNoisy_sameResidualCutLocus_selected,
      selectedEdgeNoisy_canonicalGaugeRelated_selected,
      selectedEdgeNoisy_canonicalCutClass_nonzero,
      selectedEdgeNoisy_canonicalCutClass_obstructs_transitionClosure,
      selectedEdgeNoisy_canonicalCutClass_obstructs_transitionCoherentData⟩

end SemanticResidualAtlasGauge
end QualitySurface
end Formal.AG.Research
