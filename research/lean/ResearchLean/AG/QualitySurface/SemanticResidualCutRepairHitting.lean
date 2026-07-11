import ResearchLean.AG.QualitySurface.SemanticResidualAtlasMapLaws

/-!
Cycle 96 evidence for `G-aat-quality-surface-01`.

This file turns the residual cut obstruction class into a repair-hitting
necessity theorem.  For same-carrier old/new finite semantic repair atlas
skeletons, explicit hit predicates mark the places a repair touched: active
edges, residual-present source indices, and residual-free target indices.  If
old residual cuts persist outside those hit loci, then vanishing of the new
canonical residual cut class forces every old residual cut to be hit somewhere.

The result is a necessary condition only.  It does not assert that hitting a
cut synthesizes a repair, that vanishing implies transition closure, that the
hit set is globally minimal, that an arbitrary atlas category exists, that a
true Cech/H1 quotient has been constructed, or that source extraction,
ArchMap correctness, runtime repair synthesis, tooling runtime extraction, UI
correctness, or whole-codebase quality has been established.
-/

universe u w

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualCutRepairHitting

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
open SemanticResidualAtlasMorphism
open SemanticResidualAtlasMapLaws

/-! ## Repair-hit predicates for residual cut loci -/

/--
A residual cut is hit when it is not simultaneously untouched at the edge,
source-index, and target-index loci.  This constructive form avoids building a
classical disjunction from the impossibility of all three misses.
-/
def ResidualCutHit
    {Index : Type w}
    (edgeHit : Index × Index -> Prop)
    (sourceHit targetHit : Index -> Prop)
    (pair : Index × Index) : Prop :=
  Not
    (Not (edgeHit pair) /\
      Not (sourceHit pair.1) /\
        Not (targetHit pair.2))

/-- An explicit edge hit hits the residual cut. -/
theorem residualCutHit_of_edgeHit
    {Index : Type w}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    {pair : Index × Index}
    (hhit : edgeHit pair) :
    ResidualCutHit edgeHit sourceHit targetHit pair := by
  intro hunhit
  exact hunhit.1 hhit

/-- An explicit source-index hit hits the residual cut. -/
theorem residualCutHit_of_sourceHit
    {Index : Type w}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    {pair : Index × Index}
    (hhit : sourceHit pair.1) :
    ResidualCutHit edgeHit sourceHit targetHit pair := by
  intro hunhit
  exact hunhit.2.1 hhit

/-- An explicit target-index hit hits the residual cut. -/
theorem residualCutHit_of_targetHit
    {Index : Type w}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    {pair : Index × Index}
    (hhit : targetHit pair.2) :
    ResidualCutHit edgeHit sourceHit targetHit pair := by
  intro hunhit
  exact hunhit.2.2 hhit

/--
Old residual cuts persist into the new atlas when no repair hit touches their
edge, residual-present source, or residual-free target loci.
-/
def UnhitResidualCutPersists
    {Index : Type w}
    {Atom : Type u}
    (old new : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (edgeHit : Index × Index -> Prop)
    (sourceHit targetHit : Index -> Prop) : Prop :=
  forall pair,
    IsResidualTransitionCutPair old pair ->
      Not (edgeHit pair) ->
        Not (sourceHit pair.1) ->
          Not (targetHit pair.2) ->
            IsResidualTransitionCutPair new pair

/-- Every old residual cut is hit by the supplied repair-hit predicates. -/
def AllOldResidualCutsHit
    {Index : Type w}
    {Atom : Type u}
    (old : FiniteSemanticRepairAtlasSkeleton Index Atom)
    (edgeHit : Index × Index -> Prop)
    (sourceHit targetHit : Index -> Prop) : Prop :=
  forall pair,
    IsResidualTransitionCutPair old pair ->
      ResidualCutHit edgeHit sourceHit targetHit pair

/-! ## Persistence and repair necessity -/

/-- An unhit old residual cut persists as a new residual cut. -/
theorem unhit_oldResidualCut_persists_newCut
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    (hpersist :
      UnhitResidualCutPersists old new edgeHit sourceHit targetHit)
    {pair : Index × Index}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (edgeHit pair))
    (hsource : Not (sourceHit pair.1))
    (htarget : Not (targetHit pair.2)) :
    IsResidualTransitionCutPair new pair := by
  exact hpersist pair hcut hedge hsource htarget

/--
If an old residual cut is untouched at all three repair loci, the new canonical
residual cut class is nonzero.
-/
theorem unhit_oldResidualCut_preserves_newCanonicalNonzero
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    (hpersist :
      UnhitResidualCutPersists old new edgeHit sourceHit targetHit)
    {pair : Index × Index}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (edgeHit pair))
    (hsource : Not (sourceHit pair.1))
    (htarget : Not (targetHit pair.2)) :
    (canonicalResidualCutCochain new).CutNonzero := by
  have hnewCut :
      IsResidualTransitionCutPair new pair :=
    unhit_oldResidualCut_persists_newCut
      hpersist hcut hedge hsource htarget
  exact ⟨pair, hnewCut, hnewCut⟩

/--
If the new canonical residual cut class vanishes, each old residual cut must be
hit at its edge, source, or target locus.
-/
theorem newCanonicalVanishes_forces_oldResidualCutHit
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    (hpersist :
      UnhitResidualCutPersists old new edgeHit sourceHit targetHit)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes)
    {pair : Index × Index}
    (hcut : IsResidualTransitionCutPair old pair) :
    ResidualCutHit edgeHit sourceHit targetHit pair := by
  intro hunhit
  have hnewCut :
      IsResidualTransitionCutPair new pair :=
    hpersist pair hcut hunhit.1 hunhit.2.1 hunhit.2.2
  exact hvanish pair hnewCut hnewCut

/-- Vanishing of the new canonical class forces all old residual cuts to be hit. -/
theorem newCanonicalVanishes_forces_allOldResidualCutsHit
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    (hpersist :
      UnhitResidualCutPersists old new edgeHit sourceHit targetHit)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes) :
    AllOldResidualCutsHit old edgeHit sourceHit targetHit := by
  intro pair hcut
  exact newCanonicalVanishes_forces_oldResidualCutHit
    hpersist hvanish hcut

/-- An unhit old residual cut obstructs new transition closure. -/
theorem unhit_oldResidualCut_obstructs_newTransitionClosure
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    (hpersist :
      UnhitResidualCutPersists old new edgeHit sourceHit targetHit)
    {pair : Index × Index}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (edgeHit pair))
    (hsource : Not (sourceHit pair.1))
    (htarget : Not (targetHit pair.2))
    (transition : Index -> Index -> Atom -> Atom) :
    Not (AtlasResidualTransitionClosed new transition) := by
  exact
    residualCutClass_nonzero_obstructs_atlasTransitionClosure
      (canonicalResidualCutCochain new)
      (unhit_oldResidualCut_preserves_newCanonicalNonzero
        hpersist hcut hedge hsource htarget)
      transition

/-- An unhit old residual cut rules out new transition-coherent atlas data. -/
theorem unhit_oldResidualCut_obstructs_newTransitionCoherentData
    {Index : Type w}
    {Atom : Type u}
    {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
    {edgeHit : Index × Index -> Prop}
    {sourceHit targetHit : Index -> Prop}
    (hpersist :
      UnhitResidualCutPersists old new edgeHit sourceHit targetHit)
    {pair : Index × Index}
    (hcut : IsResidualTransitionCutPair old pair)
    (hedge : Not (edgeHit pair))
    (hsource : Not (sourceHit pair.1))
    (htarget : Not (targetHit pair.2))
    (transition : Index -> Index -> Atom -> Atom) :
    Not (Nonempty (TransitionCoherentAtlasData new transition)) := by
  exact
    residualCutClass_nonzero_obstructs_transitionCoherentData
      (canonicalResidualCutCochain new)
      (unhit_oldResidualCut_preserves_newCanonicalNonzero
        hpersist hcut hedge hsource htarget)
      transition

/-! ## Selected frontier-to-flat witness -/

/-- The selected frontier-to-flat residual cut pair. -/
def selectedFrontierFlatResidualCutPair :
    SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex :=
  (SelectedSemanticOverlapIndex.repairFrontier,
    SelectedSemanticOverlapIndex.flat)

/-- The selected frontier-to-flat pair is a residual cut. -/
theorem selectedFrontierFlatResidualCutPair_isCut :
    IsResidualTransitionCutPair
      selectedFrontierFlatAtlasSkeleton
      selectedFrontierFlatResidualCutPair := by
  exact
    residualTransitionCut_pair_isCut
      selectedFrontierFlatResidualTransitionCut

/-- No selected edge is hit. -/
def selectedNoEdgeHit
    (_pair : SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex) :
    Prop :=
  False

/-- No selected residual-present source index is hit. -/
def selectedNoSourceHit
    (_index : SelectedSemanticOverlapIndex) :
    Prop :=
  False

/-- No selected residual-free target index is hit. -/
def selectedNoTargetHit
    (_index : SelectedSemanticOverlapIndex) :
    Prop :=
  False

/-- With no hit loci and identical old/new atlas, every old cut persists. -/
theorem selectedNoHit_unhitResidualCutPersists :
    UnhitResidualCutPersists
      selectedFrontierFlatAtlasSkeleton
      selectedFrontierFlatAtlasSkeleton
      selectedNoEdgeHit
      selectedNoSourceHit
      selectedNoTargetHit := by
  intro pair hcut _hedge _hsource _htarget
  exact hcut

/-- With no hit loci, the selected canonical residual cut class remains nonzero. -/
theorem selectedNoHit_preserves_canonicalNonzero :
    (canonicalResidualCutCochain
      selectedFrontierFlatAtlasSkeleton).CutNonzero := by
  exact
    unhit_oldResidualCut_preserves_newCanonicalNonzero
      selectedNoHit_unhitResidualCutPersists
      selectedFrontierFlatResidualCutPair_isCut
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)

/--
For any same-carrier new selected atlas, vanishing of the new canonical class
requires the selected frontier-to-flat cut to be hit somewhere.
-/
theorem selected_newCanonicalVanishes_requires_frontierFlatCutHit
    {new :
      FiniteSemanticRepairAtlasSkeleton
        SelectedSemanticOverlapIndex
        RefinedSemanticRepairAtom}
    {edgeHit :
      SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
    {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop}
    (hpersist :
      UnhitResidualCutPersists
        selectedFrontierFlatAtlasSkeleton
        new
        edgeHit
        sourceHit
        targetHit)
    (hvanish : (canonicalResidualCutCochain new).CutVanishes) :
    ResidualCutHit
      edgeHit
      sourceHit
      targetHit
      selectedFrontierFlatResidualCutPair := by
  exact
    newCanonicalVanishes_forces_oldResidualCutHit
      hpersist
      hvanish
      selectedFrontierFlatResidualCutPair_isCut

/-- No-hit persistence obstructs selected transition closure. -/
theorem selectedNoHit_obstructs_transitionClosure
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (AtlasResidualTransitionClosed
        selectedFrontierFlatAtlasSkeleton
        transition) := by
  exact
    unhit_oldResidualCut_obstructs_newTransitionClosure
      selectedNoHit_unhitResidualCutPersists
      selectedFrontierFlatResidualCutPair_isCut
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-- No-hit persistence rules out selected transition-coherent atlas data. -/
theorem selectedNoHit_obstructs_transitionCoherentData
    (transition :
      SelectedSemanticOverlapIndex -> SelectedSemanticOverlapIndex ->
        RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom) :
    Not
      (Nonempty
        (TransitionCoherentAtlasData
          selectedFrontierFlatAtlasSkeleton
          transition)) := by
  exact
    unhit_oldResidualCut_obstructs_newTransitionCoherentData
      selectedNoHit_unhitResidualCutPersists
      selectedFrontierFlatResidualCutPair_isCut
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      transition

/-! ## Theorem package -/

/--
Cycle-96 theorem package: if old residual cuts persist outside explicit repair
hit loci, then vanishing of the new canonical residual cut class forces every
old residual cut to be hit; otherwise an unhit old cut persists as a nonzero
new obstruction.
-/
theorem semanticResidualCutRepairHitting_package :
    (forall {Index : Type w}
      {Atom : Type u}
      {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
      {edgeHit : Index × Index -> Prop}
      {sourceHit targetHit : Index -> Prop},
      UnhitResidualCutPersists old new edgeHit sourceHit targetHit ->
        forall pair : Index × Index,
          IsResidualTransitionCutPair old pair ->
            Not (edgeHit pair) ->
              Not (sourceHit pair.1) ->
                Not (targetHit pair.2) ->
                  (canonicalResidualCutCochain new).CutNonzero) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {edgeHit : Index × Index -> Prop}
        {sourceHit targetHit : Index -> Prop},
        UnhitResidualCutPersists old new edgeHit sourceHit targetHit ->
          (canonicalResidualCutCochain new).CutVanishes ->
            AllOldResidualCutsHit old edgeHit sourceHit targetHit) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {edgeHit : Index × Index -> Prop}
        {sourceHit targetHit : Index -> Prop},
        UnhitResidualCutPersists old new edgeHit sourceHit targetHit ->
          forall pair : Index × Index,
            IsResidualTransitionCutPair old pair ->
              Not (edgeHit pair) ->
                Not (sourceHit pair.1) ->
                  Not (targetHit pair.2) ->
                    forall transition : Index -> Index -> Atom -> Atom,
                      Not (AtlasResidualTransitionClosed new transition)) /\
      (forall {Index : Type w}
        {Atom : Type u}
        {old new : FiniteSemanticRepairAtlasSkeleton Index Atom}
        {edgeHit : Index × Index -> Prop}
        {sourceHit targetHit : Index -> Prop},
        UnhitResidualCutPersists old new edgeHit sourceHit targetHit ->
          forall pair : Index × Index,
            IsResidualTransitionCutPair old pair ->
              Not (edgeHit pair) ->
                Not (sourceHit pair.1) ->
                  Not (targetHit pair.2) ->
                    forall transition : Index -> Index -> Atom -> Atom,
                      Not
                        (Nonempty
                          (TransitionCoherentAtlasData new transition))) /\
      UnhitResidualCutPersists
        selectedFrontierFlatAtlasSkeleton
        selectedFrontierFlatAtlasSkeleton
        selectedNoEdgeHit
        selectedNoSourceHit
        selectedNoTargetHit /\
      (canonicalResidualCutCochain
        selectedFrontierFlatAtlasSkeleton).CutNonzero /\
      (forall
        {new :
          FiniteSemanticRepairAtlasSkeleton
            SelectedSemanticOverlapIndex
            RefinedSemanticRepairAtom}
        {edgeHit :
          SelectedSemanticOverlapIndex × SelectedSemanticOverlapIndex -> Prop}
        {sourceHit targetHit : SelectedSemanticOverlapIndex -> Prop},
        UnhitResidualCutPersists
          selectedFrontierFlatAtlasSkeleton
          new
          edgeHit
          sourceHit
          targetHit ->
            (canonicalResidualCutCochain new).CutVanishes ->
              ResidualCutHit
                edgeHit
                sourceHit
                targetHit
                selectedFrontierFlatResidualCutPair) /\
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
    ⟨fun {_Index} {_Atom} {_old} {_new} {_edgeHit}
        {_sourceHit} {_targetHit} hpersist pair hcut hedge hsource htarget =>
        unhit_oldResidualCut_preserves_newCanonicalNonzero
          hpersist hcut hedge hsource htarget,
      fun {_Index} {_Atom} {_old} {_new} {_edgeHit}
        {_sourceHit} {_targetHit} hpersist hvanish =>
        newCanonicalVanishes_forces_allOldResidualCutsHit
          hpersist hvanish,
      fun {_Index} {_Atom} {_old} {_new} {_edgeHit}
        {_sourceHit} {_targetHit} hpersist pair hcut hedge hsource htarget
        transition =>
        unhit_oldResidualCut_obstructs_newTransitionClosure
          hpersist hcut hedge hsource htarget transition,
      fun {_Index} {_Atom} {_old} {_new} {_edgeHit}
        {_sourceHit} {_targetHit} hpersist pair hcut hedge hsource htarget
        transition =>
        unhit_oldResidualCut_obstructs_newTransitionCoherentData
          hpersist hcut hedge hsource htarget transition,
      selectedNoHit_unhitResidualCutPersists,
      selectedNoHit_preserves_canonicalNonzero,
      fun {_new} {_edgeHit} {_sourceHit} {_targetHit} hpersist hvanish =>
        selected_newCanonicalVanishes_requires_frontierFlatCutHit
          hpersist hvanish,
      selectedNoHit_obstructs_transitionClosure,
      selectedNoHit_obstructs_transitionCoherentData⟩

end SemanticResidualCutRepairHitting
end QualitySurface
end ResearchLean.AG
